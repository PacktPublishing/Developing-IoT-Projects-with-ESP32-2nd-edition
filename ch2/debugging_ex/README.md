# Hardware setup

The devkit of this example is ESP32-S3-BOX-3. To access the pins, use this extension board of the devkit: https://github.com/espressif/esp-box/blob/master/docs/_static/box_3_hardware_overview/pinlayout_box_3_bread.png

Pins to be used on the devkit extension: 5V0(IN), GND, USB-, USB+

# Troubleshooting

## Accessing USB via openocd on Linux

Do not forget to copy the udev rules:
```
$ sudo cp -n ~/.espressif/tools/openocd-esp32/v0.12.0-esp32-20240318/openocd-esp32/share/openocd/contrib/60-openocd.rules /etc/udev/rules.d/
```

## Running gdbgui

If you've installed ESP-IDF from the Espressif extension, it will not install the components for gdbgui. You can install it with the following command:
```
$ cd ~/esp/v5.2.2/esp-idf
$ ./install.sh --enable-gdbgui
```

When you start a new IDF terminal, the gdbgui option will be available.

