CBMC proofs
===========

This directory contains memory safety proofs for the functions of the
Jobs library from the AWS IoT Device SDK for Embedded C.  Together, the
proofs cover the entire library with no errors reported.  Each proof is
in its own directory, and runs in a few seconds.

Two functions, strnAppend() and strnEq(), are proven in isolation, and
then replaced by stubs in the remaining proofs.

To run the proofs
-------------

* Add cbmc, goto-cc, goto-instrument, goto-analyzer, and cbmc-viewer
  to your path.
* cd to the proof directory
* Run "make".
* Open html/index.html in a web browser.
