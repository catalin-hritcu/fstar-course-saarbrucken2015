FSTAR=fstar.exe

all : swap factorial fibonacci
# wp -- fails on universes

swap : swap.fst
	$(FSTAR) $^

factorial : factorial.fst
	$(FSTAR) $^

fibonacci : fibonacci.fst
	$(FSTAR) $^

wp : expressions.fst weakestprecondition.fst
	$(FSTAR) --__temp_no_proj WeakestPrecondition $^
