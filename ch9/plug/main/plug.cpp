
#include "AppDriver.hpp"
#include "AppPlug.hpp"

namespace
{
    app::AppDriver app_driver;
    app::AppPlug app_plug;
}

extern "C" void app_main(void)
{
    app_driver.init();
    app_plug.init();

    app_plug.start();
    app_driver.start();
}
