# Getting Started

## Setting up ESP Insights

### Get the ESP Insights Agent

Please clone this repository using the below command:

```
git clone --recursive https://github.com/espressif/esp-insights.git
```

> Note the --recursive option. This is required to pull in various dependencies. In case you have already cloned the repository without this option, execute this to pull in the submodules: `git submodule update --init --recursive`


### Set up the CLI (for claiming)

Set up the esp-rainmaker CLI by following the steps [here](https://rainmaker.espressif.com/docs/cli-setup.html).

- Create your account using the CLI

```text
./rainmaker.py signup <email>
./rainmaker.py login [--email <email>]
```

> If you prefer using 3rd party login options like Google, Apple or GitHub, please use `./rainmaker.py login` command directly (without the --email option). This will open a page in web browser which has various login options.

### Set up ESP IDF

Using the ESP Insights requires either the [`master branch`](https://github.com/espressif/esp-idf/tree/master), [`release v4.3`](https://github.com/espressif/esp-idf/releases/tag/v4.3), [`release v4.2.2`](https://github.com/espressif/esp-idf/releases/tag/v4.2.2) or [`release v4.1.1`](https://github.com/espressif/esp-idf/releases/tag/v4.1.1) of esp-idf. Set up ESP IDF, if not done already using the steps [here](https://docs.espressif.com/projects/esp-idf/en/latest/esp32/get-started/index.html) and switch to the appropriate branch or release tag. The below example shows steps for master branch. Just replace `master` with your branch name/tag if you are using any of the other supported IDF versions.

ESP Insights works out of the box with esp-idf `master` branch.

```text
cd $IDF_PATH
git checkout master
git pull origin master
git submodule update --init --recursive
```

However on `release v4.3`, `release v4.2.2`, and `release v4.1.1` it is supported with the help of a patch.

#### For ESP-IDF release v4.3

```
git apply -v <path/to/esp-insights>/idf-patches/Diagnostics-support-in-esp-idf-tag-v4.3.patch
```

#### For ESP-IDF release v4.1.1 and release v4.2.2

```
git apply -v <path/to/esp-insights>/idf-patches/Diagnostics-support-in-esp-idf-tag-v4.1.1-and-tag-v4.2.2.patch
```


## Try out the example

The [minimal_diagnostics](minimal_diagnostics/README.md) example can be used as a starting point to get started.

#### Configure, Build and Flash

```text
cd /path/to/esp-insights/examples/minimal_diagnostics
idf.py menuconfig # Example Configuration -> WiFi SSID/WiFi Password
idf.py build
idf.py -p <serial-port> erase_flash flash
```

## Claiming

In order to access the ESP Insights information, you need to have administrator access to a node, which you get by claiming the node. Please use the RainMaker CLI for claiming

```
cd <path/to/esp-insights>/cli
./rainmaker.py claim <serial-port>
```

> Claiming is required even if you are using ESP32-S2 which supports the self claiming feature.

## Insights Dashboard

Once everything is done, just boot up your device and let it run. Once it connects to the Wi-Fi network, it will start reporting diagnostics information.

Once done, any diagnostics information reported will then show up on the [Insights dashboard](https://dashboard.rainmaker.espressif.com/). Sign in using the same credentials you used for the RainMaker CLI Login.

### Uploading the Firmware Package

To get better insights into the diagnostics information, you also need to upload the Firmware package, which consists of the binary, elf, map file and other information useful for analysis. Please upload the package, (named `<project_name>-<fw_version>.zip`) which you can find in the `build/` folder of your project by navigating to the "Firmware Images" section of the dashboard.

**Important Note**

Commands like `idf.py build`, `idf.py flash`, etc. rebuild the firmware even if there is no change in the code and this also causes the Firmware Package to change. Please take care that the binary flashed on your board and the firmware package uploaded on the dashboard are in sync. 

## Enabling Insights in Your Own Project

If you want to understand how to enable insights in your own project, please checkout this [example README](minimal_diagnostics/README.md).
