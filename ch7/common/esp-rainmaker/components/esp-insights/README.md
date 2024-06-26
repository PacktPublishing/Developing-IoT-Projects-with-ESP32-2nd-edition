# ESP Insights (Beta)

ESP Insights is a remote diagnostics solution that allows users to remotely monitor the health of ESP devices in the field.

## Introduction

Developers normally prefer debugging issues by physically probing them using gdb or observing the logs. This surely helps debug issues, but there are often cases wherein issues are seen only in specific environments under specific conditions. Even things like casings and placement of the product can affect the behaviour. A few examples are

- Wi-Fi disconnections for a smart switch concealed in a wall.
- Smart speakers crashing during some specific usage pattern.
- Appliance frequently rebooting due to power supply issues.

Having remote diagnostics facility helps in identifying such issues faster. ESP Insights includes a firmware agent (the Insights agent) that captures some of the vital pieces of diagnostics information from the device during runtime and uploads them to the ESP Insights cloud. The cloud then processes this data for easy visualisation. Developers can log in to a web-based dashboard to look at the health and issues reported by their devices in the field. A sample screen is shown here.

![Insights Overview](docs/_static/overview.png)

Developers can monitor the following information from the web-based dashboard:

- Error logs: Anything that is logged on console with calls with ESP_LOGE by any component in the firmware
- Warning logs: Anything that is logged on console with calls with ESP_LOGW by any component in the firmware
- Custom Events: Application specific custom events that the firmware wishes to track via calls to ESP_DIAG_EVENT
- Reset reason: The reason why the device was reset (power on, watchdog, brownout, etc.)
- Coredump summary: In case of a crash, the register contents as well as the stack backtrace of the offending thread (wherever possible)
- Metrics: Time-varying data like the free heap size, the Wi-Fi signal strength that is plotted over a period of time
- Variables: Variable values like the IP Address or state variables that report their current value
- Group analytics: Insights into how group of devices are performing

All of this information should help the developer understand better how their device is performing in the field.

You can find more details on [Insights Features](FEATURES.md) page.

> ESP Insights currently works with the ESP Insights cloud and ESP RainMaker cloud. Support for other cloud services will be available in a subsequent release.

## Getting Started
Following code should get you started, and your application can start reporting ESP Insights data to the Insights cloud.

### Enabling ESP-Insights
By default, `ESP-Insights` is disabled. User need to enable it via menuconfig option.
`(Component config → ESP Insights)`

To select transport to be used, please follow next step.

### Enabling Insights with HTTPS
For Insights agent HTTPS is configure as the default transport.

```c
#include <esp_insights.h>
#define ESP_INSIGHTS_AUTH_KEY "<Paste-Auth-Key-Here>"

{
    esp_insights_config_t config  = {
        .log_type = ESP_DIAG_LOG_TYPE_ERROR,
        .auth_key = ESP_INSIGHTS_AUTH_KEY,
    };

    esp_insights_init(&config);

    /* Rest of the application initialization */
}
```

As you may have noticed, all you will need is the unique ESP_INSIGHTS_AUTH_KEY to be embedded in your firmware.
Here is how you can obtain the ESP Insights Auth Key:
* Sign up or Sign in on [ESP Insights Dashboard](https://dashboard.insights.espressif.com/)
* Visit [Manage Auth Keys](https://dashboard.insights.espressif.com/home/manage-auth-keys) and generate an Auth Key
* Copy the Auth Key to your firmware


### Enabling Insights with MQTT
Configure the default insights transport to MQTT (Component config → ESP Insights → Insights default transport → MQTT).
Alternatively, you can add `CONFIG_ESP_INSIGHTS_TRANSPORT_MQTT=y` to `sdkconfig.defaults`.

```c
#include <esp_insights.h>

{
    esp_insights_config_t config  = {
        .log_type = ESP_DIAG_LOG_TYPE_ERROR,
    };

    esp_insights_init(&config);

    /* Rest of the application initialization */
}
```
You will require the MQTT certs which you can obtain by performing [Claiming](examples/minimal_diagnostics#esp-insights-over-mqtt).

For more details please head over to [examples](examples).

## Behind the Scenes

  - As described in the overview section, ESP-Insights collects data of your choice and stores it in storage, the storage currently used is RTC store.
  - The data is split into two sections, and the size is configurable via menuconfig:
    - Critical: Errors, Warnings and Events
    - Non-Critical: Metrics and Variables
  - This data is then periodically encoded in CBOR format and is sent over the transport.
  - The data send algorithm is dynamic withing a range. It adapts to the need of the reporting.

### RTC data store
ESP-Insight currently uses RTC memory to store the messages until it is sent to the cloud. Unlike, normal RAM, RTC store makes data available across soft resets. Thus, it brodens the usefulness of the data across reboot.

Messages in Critical data take `121` bytes per message. Hence, one can calculate, say a `2048` bytes of critical section can hold `16` messages before it starts dropping new messages.
Likewise Non-critical messages take `49` bytes per message and hence a `1024` bytes storage can hold `21` messages.

The RTC memory is limited and flooding too many messages, makes RTC storage full. Once full, the framework has to drop the messages.
One solution is to increase the data reporting frequency to cloud, and thereby emptying the RTC store frequently.
> **_Note_**
This however comes with the network cost. It is advisable for a developer to keep Insights logging concise and not overdo it.

## Contributing

If you find an issue with ESP-Insights, or wish to submit an enhancement request, please use the Issues section on Github.
For ESP-IDF related issues please use [esp-idf](https://github.com/espressif/esp-idf) repo.

## License

ESP-Insights code is covered under Apache2 license. Submodules and other third party repos have their own license.
