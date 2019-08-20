all:mt.c mt_generated.c
	gcc -g -Wall mt.c -o mt

mt_generated.c: mt.v
	coqc mt.v

clean:
	rm -rf mt mt.glob mt.vo mt_generated.c mt.dSYM/
