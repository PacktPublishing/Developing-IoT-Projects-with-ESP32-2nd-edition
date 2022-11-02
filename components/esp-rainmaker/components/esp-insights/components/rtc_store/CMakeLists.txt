set(srcs "src/rtc_store.c"
         "src/rbuf.c")

idf_component_register(SRCS "${srcs}"
                    INCLUDE_DIRS "include")
