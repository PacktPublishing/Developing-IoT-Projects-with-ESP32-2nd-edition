#include "AppDoorLogger.hpp"

namespace
{
    app::AppDoorLogger door_logger;
}

extern "C" void app_main(void)
{
    door_logger.init();
}
