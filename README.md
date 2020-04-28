# Generating induction principles and subterm relations for inductive types using MetaCoq

Bohdan Liesnikov, Marcel Ullrich, Yannick Forster

Saarland University

## Installation

Clone this repository with `git clone --recursive https://github.com/uds-psl/metacoq-examples-coqws.git`.

To install and test the plugins you have to install MetaCoq and the 3 plugins separately. 
You need `Coq 8.11`. 

If you are using `opam`, typing `make` will build all 4 subdirectories and install them to the `user-contrib` directory of Coq.

If you are not using opam, you have to type `make` and afterwards `sudo make install` in the directories `metacoq`, `metacoq-translations`, `metacoq-generalized-constructors`, `metacoq-induction`, and `metacoq-subterm` (in this order).
