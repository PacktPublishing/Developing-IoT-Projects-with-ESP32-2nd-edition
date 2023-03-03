
#include "AppDriver.hpp"
#include "AppNode.hpp"
#include "AppSensor.hpp"
#include "AppSensorClient.hpp"

namespace
{
    app::AppDriver app_driver;
    app::AppNode app_node;
    app::AppSensor app_sensor;
}

extern "C" void app_main()
{
    app_driver.init();
    app_node.init();
    app_sensor.init(dynamic_cast<app::AppSensorClient *>(&app_node));

    app_sensor.start();
    app_node.start();
    app_driver.start();
}