# MISRA Compliance

The AWS IoT Over-the-air Update library files conform to the [MISRA C:2012](https://www.misra.org.uk)
guidelines, with some noted exceptions. Compliance is checked with Coverity static analysis.
Deviations from the MISRA standard are listed below:

### Suppressed with Coverity Comments
To find the violation references in the source files run grep on the source code
with ( Assuming rule 21.3 violation; with justification in point 2 ):
```
grep 'MISRA Ref 21.3.2' . -rI
```

#### Rule 8.6
_Ref 8.6.1_

- MISRA C-2012 Rule 8.6 requires identifier with external linkage to have exact one external definition.
    However, this variable is defined in OTA platform abstraction layer implementation, which is
    not in this repository but in C-SDK and amazon-freertos repo, so it's a false positive.

#### Rule 8.13
_Ref 8.13.1_

- MISRA C-2012 Rule 8.13 There are multiple functions that all use the same function header so that
    they can be assigned to function pointers in a seamless manner. There are a few that modify the
    OtaAgentContext_t that gets passed in. In order to allow convienent assignment of these function pointers
    we supress this rule on this function that can't have const added.

#### Rule 10.1
_Ref 10.1.1_

- MISRA C-2012 Rule 10.1 requires bitwise operand to be unsigned type. However, O_CREAT and O_RDWR
    flags are from standard linux header, and this is the normal way of using them. Hence we
    silence the warning here.

#### Rule 10.8
_Ref 10.8.1_

- MISRA C-2012 Rule 10.8 requires not casting a value from an unsigned to signed type. Since OTA_PAL_SUB_ERR()
    ands the input with 0xffffffuL, it removes the possibility of there being any bits in the first byte of the
    variable, removing the ability for the cast to lead to integer overflow.

#### Rule 11.8
_Ref 11.8.1_

- Misra C-2012 Rule 11.8  will raise an error if certain variables are not marked as const, even if the variables do get
    modified in that function. As such there are two occurences where to get around that error, we supress these.

#### Rule 19.2
_Ref 19.2.1_

- MISRA C-2012 Rule 19.2 Unions are used to reduce the memory footprint and to represent packet formats in the FreeRTOS network stack.

#### Rule 21.5
_Ref 21.5.1_

- MISRA rule 21.5 prohibits the use of signal.h because of undefined behavior. However, this
    implementation is on POSIX, which has well defined behavior. We're using the timer functionality
    from POSIX so we deviate from this rule.

#### Rule 21.10
_Ref 21.10.1_

- MISRA rule 21.10 prohibits the use of time.h because it is implementation dependent or unspecified.
    However, this implementation is on POSIX, which has well defined behavior.

#### Rule 21.3
_Ref 21.3.1_

- MISRA C-2012 Rule 21.3 prohibits the use of malloc and free from stdlib.h because of
    undefined behavior. The library has checks in place to make sure that the memory is
    allocated before accessing it. Additionally, the library makes sure that the memory is
    written to before it is read from thereby not returning garbage data. Furthermore, the
    library is tested with address sanitizer to verify that memory being freed has been
    dynamically allocated and that there is no memory leak. After free-ing the memory pointed
    to by a pointer, the pointer is changed to NULL to prevent use-after-free bugs.

_Ref 21.3.2_

- MISRA C-2012 Rule 21.3 prohibits the use of malloc and free from stdlib.h, however, we're only
    defining the interface here. On FreeRTOS this is implemented with pvPortMalloc and vPortFree,
    and on Linux it's implemented with standard C malloc and free. This is a false positive.

#### Rule 21.8
_Ref 21.8.1_

- MISRA C-2012 Rule 21.8 Does not allow the use of some of the functions in stdlib.h. One of the OTA platform 
    abstraction layer interfaces `abort` is flagged for this violation. This is implemented by a platform
    abstraction layer and always called through the OTA PAL interface.
