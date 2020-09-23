''' apiscraper.py - log all Tesla data available from the
    Mothership API to Influx.

    Origianl Author: Bastian Maeuser
    https://github.com/lephisto/tesla-apiscraper

    Modified version: https://github.com/djbadders/tesla-apiscraper
    Author: Dave Baddeley

    Changed to:
    * remove web server for mobile app
    * enhanced sleep behaviour
    * Auto log rotation and limited disk usage

    Please note that the use of the Tesla REST API in general
    and the use of this software in particular is not endorsed by Tesla.
    You use this software at your own risk.
    The author does not take responsibility for anything related
    to the use of this software.

    Thanks go to cko from the german tff-forum for a basic version of the
    script.

    Configuration is taken from config.py - a sample file is distributed as
    config.py.dist. Rename it and configure it according your needs.
'''

import json
import coloredlogs
import logging
import logging.handlers
import sys
import threading
import time
import teslajson
import polling

from influxdb import InfluxDBClient
from urllib.error import URLError
from urllib3.exceptions import HTTPError
from config import *
from teslajson import ContinuePollingError
from srtmread import elevationtoinflux

# Initialise
a_vin = ''
a_display_name = ''
a_ignore = ['media_state', 'software_update', 'speed_limit_mode']

a_validity_checks = {
    'charger_voltage':
        {
            'eval': 'new_value < 0',
            'set': 0
        }
}

poll_interval = a_awake_poll_secs  # Set to -1 to wakeup the Car on Scraper start
asleep_since = int(time.time())
next_wakeup = int(time.time()) + a_maximum_sleep
scheduled_charge_time = None
previous_car_state = ''
busy_since = 0
car_active_status = None
last_data_from_tesla = None

# Tesla API scraper version
scraper_api_version = 2020.9

# Database initialise
influx_client = None
if not a_dry_run:
    influx_client = InfluxDBClient(a_influx_host, a_influx_port, a_influx_user, a_influx_pass, a_influx_db)

# Logger
def setup_custom_logger(name):
    coloredlogs.install(a_loglevel)
    custom_logger = logging.getLogger(name)
    custom_logger.setLevel(a_loglevel)

    # Add file logger if required
    if a_max_log_files_size > 0:    
        formatter = logging.Formatter(fmt='%(asctime)s %(levelname)-8s %(message)s', datefmt='%Y-%m-%d %H:%M:%S')
        handler = logging.handlers.RotatingFileHandler(a_logfile, 'a', int((a_max_log_files_size * 1024) / 2), 2, None, False)
        handler.setFormatter(formatter)        
        custom_logger.addHandler(handler)

    return custom_logger

logger = setup_custom_logger('apiscraper')

# Functions
def calculate_next_wakeup(current_wake_up_time, state_monitor):
    wakeup_time = int(time.time()) + a_maximum_sleep            

    # If we have scheduled charging, lets wake up just in time to catch that activity.
    if state_monitor.old_values['charge_state'].get('scheduled_charging_pending', False):
        scheduled_charge_time = state_monitor.old_values['charge_state'].get('scheduled_charging_start_time', 0)

        if scheduled_charge_time > 0 and scheduled_charge_time < wakeup_time:
            wakeup_time = scheduled_charge_time

            if scheduled_charge_time != current_wake_up_time:
                logger.info('Scheduled charging due at {0} will wake up then!'.format(time.ctime(wakeup_time)))

    return wakeup_time

# Tesla car state monitor
class StateMonitor(object):
    # Monitor all Tesla states.
    def __init__(self, tesla_email, tesla_password, vehicle_index):
        self.requests = ('charge_state', 'climate_state', 'drive_state',
                         'gui_settings', 'vehicle_state')
        self.priority_requests = {1: ('drive_state',),
                                  2: ('drive_state',),
                                  4: ('charge_state', 'drive_state',)}
        self.old_values = dict([(r, {}) for r in self.requests])

        self.connection = teslajson.Connection(tesla_email, tesla_password)
        self.vehicle = self.connection.vehicles[vehicle_index]
        self.vehicle_index = vehicle_index
        self.pollTimes = [ 2, 5, 15, 30, 45, 60, 120, 120, 120, 120, 120, 120, 120, 120, 120, 120, 2000, 120 ]
        self.noChangesPollCount = 0

    def refresh_vehicle(self):
        # refreshes the vehicle object
        logger.debug('>> self.connection.refresh_vehicle()')
        self.vehicle = self.connection.vehicles[self.vehicle_index]

    def ongoing_activity_status(self):
        # True if the car is not in park, or is actively charging ...
        shift = self.old_values['drive_state'].get('shift_state', '')
        old_speed = self.old_values['drive_state'].get('speed', 0) or 0

        if shift == 'R' or shift == 'D' or shift == 'N' or old_speed > 0:
            return 'driving'

        # Check charging status
        if self.old_values['charge_state'].get('charging_state', '').lower() in ['charging', 'starting']:
            return 'charging'

        # If we just completed the charging, need to wait for voltage to
        # go down to zero too to avoid stale value in the DB.
        if (self.old_values['charge_state'].get('charger_voltage', 0) > 10 and \
            self.old_values['charge_state'].get('charger_actual_current', 0) > 0):
            return 'charging'

        # When it's about time to start charging, we want to perform
        # several polling attempts to ensure we catch it starting even
        # when scraping is otherwise disabled
        if self.old_values['charge_state'].get('scheduled_charging_pending', False):
            scheduled_time = self.old_values['charge_state'].get('scheduled_charging_start_time', 0)
            if abs(scheduled_time - int(time.time())) <= 2:
                return 'charging'

        # Pre-conditioning?
        if self.old_values['climate_state'].get('is_climate_on', False):
            return 'conditioning'        

        # If screen is on, the car is definitely not sleeping so no
        # harm in polling it as long as values are changing
        if self.old_values['vehicle_state'].get('center_display_state', 0) not in [0, 5]:
            if self.old_values['vehicle_state'].get('center_display_state') == 2:
                return 'screen on (normal)'
            if self.old_values['vehicle_state'].get('center_display_state') == 3:
                return 'screen on (charging)'
            if self.old_values['vehicle_state'].get('center_display_state') == 7:
                return 'screen on (sentry)' 
            if self.old_values['vehicle_state'].get('center_display_state') == 8:
                return 'screen on (dog mode)'
            else:
                return 'screen on'

        return 'idle'

    def wake_up(self):
        # Request wake up of car. #
        logger.debug('wake_up')
        try:
            self.vehicle.wake_up()
            return True
        except (polling.TimeoutException):
            logger.debug('Vehicle not waking up')
            return False

    def update_vehicle_from_response(self, response):
        # The other vehicle items are pretty much static.
        # We don't need to do any db insertions here, the main loop
        # would perform those for us.
        for item in ['state', 'display_name']:
            self.vehicle[item] = response[item]

    def request_state_group(self):
        global a_vin
        global a_display_name
        global a_ignore
        global last_data_from_tesla
        a_lat = None
        a_long = None

        # Request and process all Tesla states
        logger.debug('>> Request vehicle data')
        r = self.vehicle.get('vehicle_data')

        self.update_vehicle_from_response(r['response'])

        for request in self.requests:
            result = r['response'][request]
            timestamp = result['timestamp']
            last_data_from_tesla = timestamp
            if self.old_values[request].get('timestamp', '') == timestamp:
                break
            self.old_values[request]['timestamp'] = timestamp
            json_body = {
                'measurement': request,
                'tags': {
                    'vin': a_vin,
                    'display_name': a_display_name,
                },
                'fields': {
                },
                'time': int(timestamp) * 1000000,
            }
            for element in sorted(result):

                if element not in ('timestamp', 'gps_as_of', 'left_temp_direction', 'right_temp_direction', 'charge_port_latch'):
                    old_value = self.old_values[request].get(element, '')
                    new_value = result[element]

                    # Location
                    if element == 'native_latitude':
                        a_lat = new_value

                    if element == 'native_longitude':
                        a_long = new_value

                    # Skip vehicle name
                    if element == 'vehicle_name' and not new_value:
                        continue
                    
                    # Speed
                    elif element == 'speed' and new_value == None:
                        # Non speed reading so assume 0
                        new_value = 0
                                                                       
                    # Catch changes to other values        
                    elif new_value != old_value:
                        if (new_value == None):
                            # Should we use the old value instead?
                            if element in ['shift_state']:
                                logger.debug('Failed to read {}, will assume it hasn\'t changed for now'.format(element))
                                new_value = old_value            

                    # Write new values
                    if new_value is not None:
                        if element not in a_ignore:
                            if element in a_validity_checks and eval(a_validity_checks[element]['eval']):
                                logger.debug(
                                    'VALIDITY CHECK VIOLATED >>> ' + element + ':' + a_validity_checks[element]['eval'])
                                new_value = a_validity_checks[element]['set']
                            row = {element: new_value}
                            json_body['fields'].update(row)
                    self.old_values[request][element] = new_value

                if a_lat is not None and a_long is not None and a_resolve_elevation:
                    # Fire and forget Elevation retrieval..
                    logger.debug('starting thread elevator: ' + str(a_lat) + '/' + str(a_long) + '/' + str(timestamp))
                    elevator = threading.Thread(target=elevationtoinflux,
                                                args=(a_lat, a_long, a_vin, a_display_name,
                                                    timestamp, influx_client, a_dry_run, logger))
                    # elevator.daemon = True
                    elevator.setName('elevator')
                    if not elevator.is_alive():
                        elevator.start()
                    a_lat = None
                    a_long = None

            if not a_dry_run and len(json_body['fields']) > 0:
                logger.info('Writing Points to Influx: ' + json_body['measurement'])
                influx_client.write_points([json_body])

        # What state are we in?
        current_state = self.ongoing_activity_status()

        return (current_state.lower() != 'idle')

    def check_states(self, interval):
        # Check all Tesla States
        any_change = False

        try:
            # Get latest states
            any_change = self.request_state_group()

            # Check for driving
            shift = self.old_values['drive_state'].get('shift_state', '')
            if shift == 'R' or shift == 'D':
                # We are actively driving, does not matter we are
                # stopped at a traffic light or whatnot,
                # keep polling
                interval = a_awake_poll_secs
                any_change = True

        except ContinuePollingError:
            # Timeouts trying to talk to the vehicle
            logger.info('Timeout contacting vehicle will try again, assuming asleep now')
            self.vehicle['state'] = 'asleep'

        except HTTPError as ex:
            logger.info('Error calling Tesla API: {0}'.format(ex))
            if a_allow_sleep == 1:
                return interval
            else:
                return -1  # re-initialize.

        if interval == 0:
            interval = a_awake_poll_secs

        # If we are charging at a supercharger, it's worth polling frequently
        # since the changes are fast. 
        if self.old_values['charge_state'].get('charging_state', '').lower() == 'charging':
            if self.old_values['charge_state'].get('fast_charger_present', '') == 'true':
                interval = 5
            else:
                interval = 15

        # If we are not charging (and not moving), then we can use the
        # usual logic to determine how often to poll based on how much
        # activity we see.
        else:
            if any_change:  # there have been changes, reduce interval
                interval = a_awake_poll_secs
                self.noChangesPollCount = 0

            else:  # there haven't been any changes, increase interval to allow the car to fall asleep
                self.noChangesPollCount += 1
                if (self.noChangesPollCount - 1) < len(self.pollTimes):
                    interval = self.pollTimes[(self.noChangesPollCount - 1)]
                else:
                    interval = self.pollTimes[(len(self.pollTimes) - 1)]

        return interval

if __name__ == '__main__':
    # Create Tesla API Interface
    try:
        state_monitor = StateMonitor(a_tesla_email, a_tesla_password, a_tesla_car_idx)
    except:
        logger.error('Failed to initialize Owner API; please check your Tesla account details in the config.py file: ' + str(sys.exc_info()[0]))
        sys.exit('Failed to initialize Owner API; please check your Tesla account details in the config.py file')

# Main Program Loop
first_run = True
while True:
    # Initialise loop    
    busy_since = int(time.time())

    # Get vehicle details and state
    state_monitor.refresh_vehicle()

    # Get latest data from vehicle
    poll_interval = state_monitor.check_states(poll_interval)   
    car_active_status = state_monitor.ongoing_activity_status()

    # Should be forcing a refresh? 
    if (int(time.time()) > next_wakeup) or first_run:
        # Wake up the vehicle
        logger.info('Waking the vehicle to check status')

        # Set next wake up time
        next_wakeup = calculate_next_wakeup(next_wakeup, state_monitor)

        # Call Wake_up
        if state_monitor.wake_up():
            # Car awake
            logger.info('Vehicle awake')
            poll_interval = a_awake_poll_secs            
        else:
            # Car didn't wake
            logger.info('Vehicle didn\'t wake up :(')

    # Car woke up
    if previous_car_state == 'asleep' and state_monitor.vehicle['state'] == 'online':
        poll_interval = a_awake_poll_secs
        asleep_since = None

    # Car gone to sleep
    if state_monitor.vehicle['state'] == 'asleep' and previous_car_state == 'online':
        asleep_since = int(time.time())

        # Set next wake up time
        next_wakeup = calculate_next_wakeup(next_wakeup, state_monitor)

    # Car awake
    if state_monitor.vehicle['state'] == 'online':
        # Set next wake up time
        next_wakeup = calculate_next_wakeup(next_wakeup, state_monitor)        
        
    # Car details tracking
    previous_car_state = state_monitor.vehicle['state']
    a_vin = state_monitor.vehicle['vin']
    a_display_name = state_monitor.vehicle['display_name']
    ts = int(time.time()) * 1000000000

    state_body = [
        {
            'measurement': 'vehicle_state',
            'tags': {
                'vin': a_vin,
                'display_name': a_display_name
            },
            'time': ts,
            'fields': {
                'state': previous_car_state
            }
        }
    ]

    if not a_dry_run:
        # Write to DB
        influx_client.write_points(state_body)

    # Calculate poll time
    if previous_car_state == 'asleep' and a_allow_sleep:
        logger.debug('Car is probably asleep, we will let it sleep...')
        #poll_interval = a_sleep_poll_secs

    processing_time = int(time.time()) - busy_since

    # If we spent too much time in processing, warn here
    # Reasons might be multiple like say slow DB or slow tesla api
    if processing_time > 120:
        logger.warning('Too long processing loop: ' + str(processing_time) + ' seconds... Tesla server or DB slow?')

    # Update console
    logger.info('Current state: {0}{1} - next check {2} secs - next wake up scheduled for {3}'.format(previous_car_state, ' and {}'.format(car_active_status) if previous_car_state != 'asleep' else ' since {}'.format(time.ctime(asleep_since)), str(poll_interval), time.ctime(next_wakeup)))        

    # Flush logging
    sys.stdout.flush()

    first_run = False

    # Sleep as long as we need to
    if poll_interval != None:
        # Check we don't have a wake up due before the next normal poll
        if (int(time.time()) + poll_interval) > next_wakeup:
            poll_interval = next_wakeup - int(time.time())
        
        # Sleep
        time.sleep(poll_interval)