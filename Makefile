all: ttt
ttt: ttt.c
	frama-c -wp -wp-rte -wp-skip-fct main -wp-prover "alt-ergo, z3" ttt.c