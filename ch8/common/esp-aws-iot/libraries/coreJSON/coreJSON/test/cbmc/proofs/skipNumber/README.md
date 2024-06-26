skipNumber proof
==============

This directory contains a memory safety proof for skipNumber.

This function requires non-NULL arguments and a buffer with length > 0.
The proof runs in a few seconds and provides complete coverage of:
* skipDecimals()
* skipDigits()
* skipExponent()
* skipNumber()

The function hexToInt() is partially covered in this proof, but is
fully covered in the skipEscape proof.

To run the proof.
* Add cbmc, goto-cc, goto-instrument, goto-analyzer, and cbmc-viewer
  to your path.
* Run "make".
* Open html/index.html in a web browser.
