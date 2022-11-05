#include "AppNavigator.hpp"

namespace
{
    app::AppNavigator nav;
}

extern "C" void app_main(void)
{
    nav.init();
}
