JSON_Search proof
==============

This directory contains a memory safety proof for JSON_Search and JSON_SearchT.

The proof runs in 15 minutes on a t3.medium.  It provides complete coverage of:
* JSON_Search()
* JSON_SearchT()
* JSON_SearchTc()
* arraySearch()
* multiSearch()
* nextKeyValuePair()
* nextValue()
* objectSearch()
* skipQueryPart()

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
