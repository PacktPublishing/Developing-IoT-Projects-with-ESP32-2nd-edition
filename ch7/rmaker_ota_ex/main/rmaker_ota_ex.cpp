
#include "AppDriver.hpp"
#include "AppNode.hpp"

namespace
{
    app::AppDriver app_driver;
    app::AppNode app_node;
}

extern "C" void app_main()
{
    app_driver.init();
    app_node.init();

    app_node.start();
    app_driver.start();
}