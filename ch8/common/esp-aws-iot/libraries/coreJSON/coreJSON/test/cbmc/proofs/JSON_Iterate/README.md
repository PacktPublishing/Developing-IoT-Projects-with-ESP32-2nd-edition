JSON_Iterate proof
==============

This directory contains a memory safety proof for JSON_Iterate.

The proof runs in a few seconds.  It provides complete coverage of:
* JSON_Iterate()
* iterate()

For this proof, the following functions are replaced with mocks.
These functions have separate proofs.
* skipAnyScalar()
* skipCollection()
* skipDigits()
* skipSpace()
* skipSpaceAndComma()
* skipString()

To run the proof.
* Add cbmc, goto-cc, goto-instrument, goto-analyzer, and cbmc-viewer
  to your path.
* Run "make".
* Open html/index.html in a web browser.
