# Minimal Diagnostics example
- [What to expect in this example](#what-to-expect-in-this-example)
- [Prerequisites](#prerequisites)
- [Try out the example](#try-out-the-example)
- [Insights Dashboard](#insights-dashboard)
- [ESP Insights Over MQTT](#esp-insights-over-mqtt)
- [Understanding the example](#understanding-the-example)

## What to expect in this example?
- This example demonstrates the use of ESP Insights framework in minimal way
- Device will try to connect with the configured WiFi network
- ESP Insights is enabled in this example, so any error/warning logs, crashes will be reported to cloud
- This example collects heap and wifi metrics every 10 minutes and network variables are collected when they change

## Prerequisites
- Before moving ahead please make sure you have already set up ESP IDF and ESP Insights. If not, please check [getting started guide](examples/README.md).
- In order to report crashes, [Save core dump to flash](https://docs.espressif.com/projects/esp-idf/en/latest/esp32/api-guides/core_dump.html#save-core-dump-to-flash) config option must be enabled.
- Also, there must be a partition table entry for coredump and factory partition.
- In this example, sdkconfig.defaults has the required configuration and partition table is modified accordingly.

## Try out the example
> Below mentioned steps are for using HTTPS protocol. If you want to use ESP Insights over MQTT(TLS) protocol, [click here](#esp-insights-over-mqtt).

### Facilitate the Auth Key
In this example we will be using the auth key that we downloaded while [setting up ESP Insights account](../README.md#set-up-esp-insights-account).

Copy Auth Key to the example
```
cp /path/to/auth/key.txt path/to/esp-insights/examples/minimal_diagnostics/main/insights_auth_key.txt
```

> NOTE: This example uses _insights_auth_key.txt_ as an auth key filename. If you want to use different filename for auth key, please make appropriate changes in `examples/minimal_diagnostics/main/CMakeLists.txt` and `examples/minimal_diagnostics/main/app_main.c`.

### Configure, Build, and Flash
```
cd path/to/esp-insights/examples/minimal_diagnostics
```

- Configure Wi-Fi SSID and Password (Example Configuration -> WiFi SSID/WiFi Password)
```
idf.py menuconfig
```

- Erase the flash, build and flash the example
```
idf.py -p <serial-port> erase_flash build flash
```

### Get the Node ID
- Start the IDF monitor
```
idf.py -p <serial-port> monitor
```

- Once the device boots, it will connect to the Wi-Fi network, look for logs similar to below and make a note of Node ID.
```
I (4161) esp_insights: =========================================
I (4171) esp_insights: Insights enabled for Node ID 246F2880371C
I (4181) esp_insights: =========================================
```


## Insights Dashboard
Once everything is set up, any diagnostics information reported will show up on the [Insights Dashboard](https://dashboard.insights.espressif.com). Sign in using the your credentials.

### Upload the Firmware Package
To get better insights into the diagnostics information, you also need to upload the Firmware package, which consists of the binary, elf, map file and other information useful for analysis. Please upload the package `build/minimal_diagnostics-v1.0.zip` (name format: `build/<project_name>-<fw_version>.zip`) by navigating to the _Firmware Images_ section of the dashboard.

**Important Note**

Commands like `idf.py build`, `idf.py flash`, etc. rebuild the firmware even if there is no change in the code and this also causes the Firmware Package to change. Please make sure that the binary flashed on your board and the firmware package uploaded on the dashboard are in sync. 

### Monitor the device diagnostics
Visit [Nodes](https://dashboard.insights.espressif.com/home/nodes) section on the dashboard and click on the Node ID to monitor device diagnostics information.

---
---

## ESP Insights Over MQTT
ESP Insights with MQTT transport protocol is facilitated through RaimMaker Claiming.
If you are already using ESP RainMaker, you can check out the documentation [here](https://rainmaker.espressif.com/docs/esp-insights.html) and get started with enabling Insights in your ESP RainMaker examples. However, if you have never used RainMaker and just want to use Insights with MQTT transport protocol, continue with the steps below.

### Set up the CLI (for claiming)
Set up the esp-rainmaker CLI by following the steps [here](https://rainmaker.espressif.com/docs/cli-setup.html).

- Create account using the CLI
```
cd path/to/esp-insights/cli
./rainmaker.py signup <email>
./rainmaker.py login [--email <email>]
```
> If you prefer using 3rd party login options like Google, Apple or GitHub, please use `./rainmaker.py login` command directly (without the --email option). This will open a page in web browser which has various login options.

### Try out example using MQTT transport protocol
```
cd path/to/esp-insights/examples/minimal_diagnostics
```

- Claiming requires an additional partition table entry, make sure you have `fctry` partition in your partition table.
```
fctry, data, nvs, 0x340000, 0x6000,
```

- Configure the example
    - Configure the Wi-Fi SSID and Password (Example Configuration -> WiFi SSID/WiFi Password)
    - Configure the default insights transport to MQTT (Component config → ESP Insights → Insights default transport)
```
idf.py menuconfig
```

- Erase the flash, build and flash the example
```
idf.py -p <serial-port> erase_flash build flash
```

- Claim the device

In order to access the ESP Insights information, you need to have administrator access to a node, which you get by claiming the node. Please use the RainMaker CLI for claiming
```
cd path/to/esp-insights/cli
./rainmaker.py claim <serial-port>
```
> Claiming is required even if you are using ESP32-S2 which supports the self claiming feature.

- [Get the Node ID](#get-the-node-id) from device console

### RainMaker Dashboard
- Visit the [RainMaker Dashboard](https://dashboard.rainmaker.espressif.com/login) and sign in using the same credentials you used for the RainMaker CLI Login.
- Upload the firmware package as described in [this section](#upload-the-firmware-package).
- Visit the _Nodes_ section section and click on the Node ID to monitor the device diagnostics information.

## Understanding the example

### Code

As you can see in the example's `app_main.c` file, only a single API call is required to enable ESP Insights.

User has to provide the log types to enable and the Auth Key if default transport is set to HTTPS. 

```c
#include <esp_insights.h>

{
	...
	...
	esp_insights_config_t config = {
		.log_type = ESP_DIAG_LOG_TYPE_ERROR,
#ifdef CONFIG_ESP_INSIGHTS_TRANSPORT_HTTPS
        .auth_key = insights_auth_key_start,
#endif
	};
	esp_insights_init(&config);
	...
	...
}
```

> Note: Diagnostics data is reported dynamically or when the buffers are filled to configured threshold. So, it can take some time for the logs to reflect on the dashboard. Moreover, if a large number of logs are generated then data will be sent to cloud but, if it fails(eg reasons: Wi-Fi failure, No internet) then any newer logs will be dropped.

### Configurations

One important functionality of ESP Insights (though optional) is capturing the core dump information into flash memory whenever the firmware crashes, and reporting it to the cloud backend whenever possible in the subsequent boot. This needs setting up some config options. You can find these config options in the sdkconfig.defaults file which you may add in your own example using the below command:

```
cat <<EOF>> sdkconfig.defaults
CONFIG_ESP32_ENABLE_COREDUMP=y
CONFIG_ESP32_ENABLE_COREDUMP_TO_FLASH=y
CONFIG_ESP32_COREDUMP_DATA_FORMAT_ELF=y
CONFIG_ESP32_COREDUMP_CHECKSUM_CRC32=y
CONFIG_ESP32_CORE_DUMP_MAX_TASKS_NUM=64
CONFIG_ESP32_CORE_DUMP_STACK_SIZE=1024
EOF
```

Reconfigure your project using the following

```
rm sdkconfig
idf.py reconfigure
```

### Partition Table

In order to store the core dump into flash in case of a crash (only if you have enabled the relevant config options as mentioned in the above section), an additional coredump partition is required in the partition table. You can see that the partitions.csv file for this example has this line at the end, which you too should add for core dump feature:

```
coredump, data, coredump, ,         64K
```
