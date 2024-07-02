# Changelog

## v1.2.0

### Features

- Add IDF v5.3 support  
  Using new i2c driver `esp_driver_i2c`, add `bus_handle` configuration for `audio_codec_i2c_cfg_t`.  
  User need create the `bus_handle` using API `i2c_new_master_bus` instead of `i2c_driver_install`.
- Change test code to standalone application, user can directly build it under folder [codec_dev_test](test_apps/codec_dev_test)

### Bug Fixes

- Fix I2S work in PDM mode record or play mono channel audio wrongly


## v1.1.0

### Features

- Add driver for AW88298, see detail datasheet [AW88298](https://datasheetspdf.com/download_new.php?id=1513778)

### Bug Fixes

- Fix ES8311 playback fade in for long time


## v1.0.3

### Bug Fixes

- Fix I2S TX and RX work in share mode, need enable TX before RX


## v1.0.2

### Features

- Add I2S TDM support
- Add API to `esp_codec_dev_set_in_channel_gain` to set input channel gain dependently


## v1.0.1

### Bug Fixes

- Fix ES8388 volume register set incorrectly


## v1.0.0

- Initial version of `esp_codec_dev`
