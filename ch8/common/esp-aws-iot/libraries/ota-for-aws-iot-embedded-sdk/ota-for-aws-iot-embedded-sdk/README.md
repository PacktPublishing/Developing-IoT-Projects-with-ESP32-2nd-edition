# AWS IoT Over-the-air Update Library

The OTA library enables you to manage the notification of a newly available update, download the update, and perform cryptographic verification of the firmware update. Using the library, you can logically separate firmware updates from the application running on your devices. The OTA library can share a network connection with the application, saving memory in resource-constrained devices. In addition, the OTA library lets you define application-specific logic for testing, committing, or rolling back a firmware update. The library supports different application protocols like Message Queuing Telemetry Transport (MQTT) and Hypertext Transfer Protocol (HTTP), and provides various configuration options you can fine tune depending on network type and conditions. This library is distributed under the [MIT Open Source License](LICENSE).

This library has gone through code quality checks including verification that no function has a [GNU Complexity](https://www.gnu.org/software/complexity/manual/complexity.html) score over 8. This library has also undergone static code analysis from [Coverity static analysis](https://scan.coverity.com/).

See memory requirements for this library [here](./docs/doxygen/include/size_table.md).

**AWS IoT Over-the-air Update Library v3.4.0 [source code](https://github.com/aws/ota-for-aws-iot-embedded-sdk/tree/v3.4.0/source) is part of the [FreeRTOS 202210.00 LTS](https://github.com/FreeRTOS/FreeRTOS-LTS/tree/202210.00-LTS) release.**

**AWS IoT Over-the-air Update Library v3.3.0 [source code](https://github.com/aws/ota-for-aws-iot-embedded-sdk/tree/v3.3.0/source) is part of the [FreeRTOS 202012.01 LTS](https://github.com/FreeRTOS/FreeRTOS-LTS/tree/202012.01-LTS) release.**

## AWS IoT Over-the-air Updates Config File

The AWS IoT Over-the-air Updates library exposes configuration macros that are required for building the library. A list of all the configurations and their default values are defined in [ota_config_defaults.h](source/include/ota_config_defaults.h). To provide custom values for the configuration macros, a custom config file named `ota_config.h` can be provided by the user application to the library.

By default, a `ota_config.h` custom config is required to build the library. To disable this requirement and build the library with default configuration values, provide `OTA_DO_NOT_USE_CUSTOM_CONFIG` as a compile time preprocessor macro.

## Building the Library
The [otaFilePaths.cmake](otaFilePaths.cmake) file contains the information of all source files and the header include paths required to build the AWS IoT Over-the-air Updates library.

As mentioned in the previous section, either a custom config file (i.e. `ota_config.h`) OR the `OTA_DO_NOT_USE_CUSTOM_CONFIG` macro needs to be provided to build the AWS IoT Over-the-air Updates library.

For a CMake example of building the AWS IoT Over-the-air Updates library with the `otaFilePaths.cmake` file, refer to the `coverity_analysis` library target in the [test/CMakeLists.txt](test/CMakeLists.txt) file.

## Building Unit Tests
### Checkout CMock Submodule
By default, the submodules in this repository are configured with `update=none` in [.gitmodules](.gitmodules) to avoid increasing clone time and disk space usage of other repositories (like [AWS IoT Device SDK for Embedded C](https://github.com/aws/aws-iot-device-sdk-embedded-C) that submodules this repository).

To build unit tests, the submodule dependency of CMock is required. Use the following command to clone the submodule:
```
git submodule update --checkout --init --recursive test/unit-test/CMock
```

### Platform Prerequisites

- For building the library, **CMake 3.13.0** or later and a **C90 compiler**.
- For running unit tests, **Ruby 2.0.0** or later is additionally required for the CMock test framework (that we use).
- For running the coverage target, **gcov** and **lcov** are additionally required.

### Steps to build unit tests

1. Go to the root directory of this repository. (Make sure that the **CMock** submodule is cloned as described [above](#checkout-cmock-submodule).)

1. Run the *cmake* command: `cmake -S test -B build`

1. Run this command to build the library and unit tests: `make -C build all`

1. The generated test executables will be present in `build/bin/tests` folder.

1. Run `cd build && ctest` to execute all tests and view the test run summary.

## Migration Guide

### How to migrate from v2.0.0 (Release Candidate) to v3.4.0

The following table lists equivalent API function signatures in v2.0.0 (Release Candidate) and v3.4.0 declared in [ota.h](source/include/ota.h)

| v2.0.0 (Release Candidate) | v3.4.0 | Notes |
| :-: | :-: | :-: |
| `OtaState_t OTA_Shutdown( uint32_t ticksToWait );` | `OtaState_t OTA_Shutdown( uint32_t ticksToWait, uint8_t unsubscribeFlag );` | `unsubscribeFlag` indicates if unsubscribe operations should be performed from the job topics when shutdown is called. Set this as 1 to unsubscribe, 0 otherwise. |

### How to migrate from version 1.0.0 to version 3.4.0 for OTA applications

Refer to [OTA Migration document](https://docs.aws.amazon.com/freertos/latest/portingguide/porting-migration-ota.html) for the summary of updates to the API.
[Migration document for OTA PAL](https://docs.aws.amazon.com/freertos/latest/portingguide/porting-migration-ota-pal.html) also provides a summary of updates required for upgrading the OTA-PAL to work with v3.4.0 of the library.

## Porting

In order to support AWS IoT Over-the-air Updates on your device, it is necessary to provide the following components:
1. [Port for the OTA Portable Abstraction Layer (PAL).](https://docs.aws.amazon.com/embedded-csdk/202103.00/lib-ref/libraries/aws/ota-for-aws-iot-embedded-sdk/docs/doxygen/output/html/ota_porting.html#ota_porting_pal)

1. [OS Interface](https://docs.aws.amazon.com/embedded-csdk/202103.00/lib-ref/libraries/aws/ota-for-aws-iot-embedded-sdk/docs/doxygen/output/html/ota_porting.html#ota_porting_os)

1. [MQTT Interface](https://docs.aws.amazon.com/embedded-csdk/202103.00/lib-ref/libraries/aws/ota-for-aws-iot-embedded-sdk/docs/doxygen/output/html/ota_porting.html#ota_porting_mqtt)

For enabling data transfer over HTTP dataplane the following component should also be provided:

1. [HTTP Interface](https://docs.aws.amazon.com/embedded-csdk/202103.00/lib-ref/libraries/aws/ota-for-aws-iot-embedded-sdk/docs/doxygen/output/html/ota_porting.html#ota_porting_http)

**NOTE** When using OTA over HTTP dataplane, MQTT is required for control plane operations and should also be provided.

## CBMC

To learn more about CBMC and proofs specifically, review the training material [here](https://model-checking.github.io/cbmc-training).

The `test/cbmc/proofs` directory contains CBMC proofs.

In order to run these proofs you will need to install CBMC and other tools by following the instructions [here](https://model-checking.github.io/cbmc-training/installation.html).

## Reference examples

Please refer to the demos of the AWS IoT Over-the-air Updates library in the following location for reference examples on POSIX and FreeRTOS:

| Platform | Location |
| :-: | :-: |
| POSIX | [AWS IoT Device SDK for Embedded C](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/main/demos/ota) |
| FreeRTOS | [FreeRTOS/FreeRTOS](https://github.com/FreeRTOS/FreeRTOS/tree/main/FreeRTOS-Plus/Demo/AWS/Ota_Windows_Simulator) | 
| FreeRTOS | [FreeRTOS AWS Reference Integrations](https://github.com/aws/amazon-freertos/tree/main/demos/ota) |

## Documentation

### Existing Documentation

For pre-generated documentation, please see the documentation linked in the locations below:

| Location |
| :-: |
| [AWS IoT Device SDK for Embedded C](https://github.com/aws/aws-iot-device-sdk-embedded-C#releases-and-documentation) |
| [FreeRTOS.org](https://freertos.org/Documentation/api-ref/ota-for-aws-iot-embedded-sdk/docs/doxygen/output/html/index.html) |

Note that the latest included version of coreMQTT may differ across repositories.
### Generating documentation

The Doxygen references were created using Doxygen version 1.9.2. To generate the
Doxygen pages, please run the following command from the root of this repository:

```shell
doxygen docs/doxygen/config.doxyfile
```

## Contributing

See [CONTRIBUTING.md](./.github/CONTRIBUTING.md) for information on contributing.
