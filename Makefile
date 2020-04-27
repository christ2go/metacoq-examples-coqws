all:
	cd metacoq && ./configure.sh local && make -j 4 && make install
	cd metacoq/translations && make -j 4 && make install
	cd metacoq-generalized-constructors && make -j 4 && make install
	cd metacoq-nested-induction && make install && make install
	cd metacoq-subterm && make install && make install
