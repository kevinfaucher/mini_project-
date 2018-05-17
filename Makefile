all: ttt
ttt: ttt.c
	frama-c -wp -wp-prover "alt-ergo, z3" ttt.c
