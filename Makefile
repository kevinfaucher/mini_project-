all: ttt
ttt: ttt.c
	frama-c -wp-skip-fct maxNum -wp ttt.c
    frama-c -wp-fct maxNum -wp -wp-prover "z3" ttt.c