# ChangeLog

## v3.2.1 - 2024-6-17

### bugfix

- Fixed ignored ADC button tied to GND.

## v3.2.0 - 2023-11-13

### Enhancements:

* The power consumption of GPIO buttons is lower during light sleep mode.

## v3.1.3 - 2023-11-13

* Resolved issue 'ADC_ATTEN_DB_11 is deprecated'.

## v3.1.2 - 2023-10-24

### bugfix

* Fixed a bug where iot_button_delete feature crashes for custom button

## v3.1.1 - 2023-10-18

### bugfix

* Fixed a bug where multiple callbacks feature crashes for BUTTON_MULTIPLE_CLICK

## v3.1.0 - 2023-10-9

### Enhancements:

* Support matrix keypad

## v3.0.1 - 2023-9-1

### Enhancements:

* Resolves bug for iot_button_unregister_event function returned error when reallocating with 0 byte.
* Update Test cases to test iot_button_unregister_event_cb
* Add api iot_button_stop & iot_button_resume for power save.

## v3.0.0 - 2023-8-15

### Enhancements:

* Add support to register multiple callbacks for a button_event

    * Update iot_button_unregister_cb, to unregister all the callbacks for that event
    * Add iot_button_unregister_event to unregister specific callbacks of that event
    * Add iot_button_count_event to return number of callbacks registered for the event.
    * Update iot_button_count_cb, to return sum of number of registered callbacks.

* Add support for Long press on specific time

    * Add iot_button_register_event, which takes specific event_config_t data as input.
    * Add BUTTON_LONG_PRESS_UP to trigger callback at the latest time of button release
    * Update BUTTON_LONG_PRESS_START to trigger callback as the time passes for long_press.

* Add support to trigger callback for specified number of clicks.

## v2.5.6 - 2023-8-22

### bugfix

* Fixed a bug where the Serial trigger interval in button_long_press_hold event fires at an incorrect time

## v2.5.5 - 2023-8-3

* Add modify api which can change long_press_time and short_press_time

## v2.5.4 - 2023-7-27

### Enhancements:

* Add test apps and ci auto test

## v2.5.3 - 2023-7-26

### Enhancements:

* `repeat` defined in struct button_dev_t is reset to 0 after event `BUTTON_PRESS_REPEAT_DONE`

## v2.5.2 - 2023-7-18

### Enhancements:

* Set "event" member to BUTTON_PRESS_REPEAT before calling the BUTTON_PRESS_REPEAT callback

## v2.5.1 - 2023-3-14

### Enhancements:

* Update doc and code specification
* Avoid overwriting callback by @franz-ms-muc in #252

## v2.5.0 - 2023-2-1

### Enhancements:

* Support custom button
* Add BUTTON_PRESS_REPEAT_DONE event
