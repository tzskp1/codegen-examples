include Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

# all:mt

mt: mt19937_generated.c
	gcc -g -Wall $< -o $@

inv: inversive_decimation.c inversive_decimation_generated.c
	gcc -g -Wall $< -o $@

# mt_generated.c: mt.v
# 	coqc mt.v

# clean:
# 	rm -rf mt mt.glob mt.vo mt_generated.c mt.dSYM/
