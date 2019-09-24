include Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

# all:mt

mt: mt.c mt_generated.c
	gcc -g -Wall mt.c -o mt

# mt_generated.c: mt.v
# 	coqc mt.v

# clean:
# 	rm -rf mt mt.glob mt.vo mt_generated.c mt.dSYM/
