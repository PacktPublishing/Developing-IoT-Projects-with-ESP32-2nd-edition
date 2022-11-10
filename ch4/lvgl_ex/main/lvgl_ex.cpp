#include "bsp_board.h"

#include "AppUi.hpp"
#include "AppButton.hpp"

namespace
{
    app::AppUi m_app_ui;
    app::AppButton m_app_btn;
}

extern "C" void app_main(void)
{
    bsp_board_init();
    m_app_ui.init();

    auto l = [](void *param)
    {
        m_app_ui.buttonLeftClick(param);
    };
    auto m = [](void *param)
    {
        m_app_ui.buttonMiddleClick(param);
    };
    auto r = [](void *param)
    {
        m_app_ui.buttonRightClick(param);
    };

    m_app_btn.init(l, m, r);
}
