all: ttt
ttt: ttt.c
	frama-c -wp ttt.c
