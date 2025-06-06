



comp: CoqMakefile
	make -f CoqMakefile


CoqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o CoqMakefile


clean: 
	make clean -f CoqMakefile
