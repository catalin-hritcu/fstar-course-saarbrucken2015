FSTAR=fstar.exe

all : stlc_state stlc_sub

stlc_strong : stlc_strong.fst
	$(FSTAR) constr.fst classical.fst ext.fst stlc_strong.fst

stlc_state : stlc_state.fst
	$(FSTAR) constr.fst classical.fst ext.fst stlc_state.fst

stlc_sub : stlc_sub.fst
	$(FSTAR) constr.fst classical.fst ext.fst stlc_sub.fst
