cmake_minimum_required(VERSION 3.15)

set(BOOK_REPO ../..)
set(RMAKER_PATH ${BOOK_REPO}/ch7/common/esp-rainmaker)

set(EXTRA_COMPONENT_DIRS 
  ${BOOK_REPO}/ch10/components/esp-skainet-extra-components
  ${BOOK_REPO}/ch10/components/esp-skainet/components
  ${BOOK_REPO}/ch9/common/ch9_common
	${RMAKER_PATH}/components/esp-insights/components 
	${RMAKER_PATH}/components
	${RMAKER_PATH}/examples/common/app_wifi
  ${RMAKER_PATH}/examples/common/qrcode
  ${RMAKER_PATH}/examples/common/app_insights)

include($ENV{IDF_PATH}/tools/cmake/project.cmake)
project(baby_monitor)

idf_build_set_property(COMPILE_OPTIONS "-fdiagnostics-color=always" APPEND)
idf_build_set_property(COMPILE_OPTIONS "-Wno-uninitialized" APPEND)
idf_build_set_property(COMPILE_OPTIONS "-Wno-unused-variable" APPEND)
idf_build_set_property(COMPILE_OPTIONS "-Wno-maybe-uninitialized" APPEND)
idf_build_set_property(COMPILE_OPTIONS "-Wno-error=format=" APPEND)
idf_build_set_property(COMPILE_OPTIONS "-Wno-unused-but-set-parameter" APPEND)
idf_build_set_property(COMPILE_OPTIONS "-Wno-error=nonnull-compare" APPEND)
idf_build_set_property(COMPILE_OPTIONS "-Wno-error=stringop-truncation" APPEND)
idf_build_set_property(COMPILE_OPTIONS "-DEI_PORTING_ESPRESSIF=1" APPEND)
