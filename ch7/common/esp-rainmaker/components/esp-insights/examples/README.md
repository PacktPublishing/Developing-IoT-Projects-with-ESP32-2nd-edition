# Getting Started

- [Get the ESP Insights Agent](#get-the-esp-insights-agent)
- [Set up ESP IDF](#set-up-esp-idf)
- [Set up ESP Insights account](#set-up-esp-insights-account)

## Get the ESP Insights Agent
Please clone this repository using the below command:

```
git clone --recursive https://github.com/espressif/esp-insights.git
```

> Note the --recursive option. This is required to pull in various dependencies. In case you have already cloned the repository without this option, execute this to pull in the submodules: `git submodule update --init --recursive`


## Set up ESP IDF
ESP Insights works out of the box onwards esp-idf [`release v4.4`](https://github.com/espressif/esp-idf/releases/tag/v4.4)
and [release/v4.3 branch](https://github.com/espressif/esp-idf/tree/release/v4.3).

We also support Insights on [`release v4.1.2`](https://github.com/espressif/esp-idf/releases/tag/v4.1.2) and
[`release v4.2.2`](https://github.com/espressif/esp-idf/releases/tag/v4.2.2) with the help of patches.

Set up ESP IDF, if not done already using the steps
[here](https://docs.espressif.com/projects/esp-idf/en/latest/esp32/get-started/index.html)
and switch to the appropriate branch or release tag.
The below example shows steps for master branch.
Just replace `master` with your branch name/tag if you are using any of the other supported IDF versions.

```
cd $IDF_PATH
git checkout master
git pull origin master
git submodule update --init --recursive
```

### For ESP-IDF release v4.1.2 and release v4.2.2
```
git apply -v path/to/esp-insights/idf-patches/Diagnostics-support-in-esp-idf-tag-v4.1.2-and-tag-v4.2.2.patch
```


## Set up ESP Insights account
First time user must create an user account.

> Insights agent supports sending data over HTTPS and MQTT(TLS) protocol. Default transport is HTTPS so, below mentioned steps are for using HTTPS protocol. If you want to use ESP Insights over MQTT(TLS) protocol, [click here](minimal_diagnostics/README.md#esp-insights-over-mqtt).

- Sign up or Sign in on [ESP Insights Dashboard](https://dashboard.insights.espressif.com)
- Visit [Manage Auth Keys](https://dashboard.insights.espressif.com/home/manage-auth-keys) and generate an Auth Key. You can use any previously generated Auth Key or generate a new one.
- Download the Auth Key.

## Try the minimal_diagnostics example
Please check the [minimal_diagnostics](minimal_diagnostics/README.md) example.
