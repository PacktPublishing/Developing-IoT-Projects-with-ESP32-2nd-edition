# Minimal Diagnostics example

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

### Configure the project

```
idf.py menuconfig
```

* Set WiFi SSID and WiFi Password

### Claim the device

```
cd /path/to/esp-insights/cli
./rainmaker.py claim <port>
```

### Build and Flash

Build the project and flash it to the board, then run monitor tool to view serial output.

```
cd /path/to/esp-insights/examples/minimal_diagnostics
idf.py build flash monitor
```

## Understanding the example

### Code

As you can see in the example's `app_main.c` file, only a single API call is required to enable ESP Insights

```c
#include <esp_insights.h>

{
	...
	...
	esp_insights_config_t config = {
		.log_type = ESP_DIAG_LOG_TYPE_ERROR | ESP_DIAG_LOG_TYPE_WARNING | ESP_DIAG_LOG_TYPE_EVENT,
	};
	esp_insights_init(&config);
	...
	...
}
```

> Note: By default, the logs will get reported every 5 minutes after the device first connects to the cloud. So, it can take upto 5min for the logs to reflect on the dashboard. Moreover, if a large number of logs are generated within that time, filling up the buffers, any newer logs will be dropped.

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
