COQLIB= #where is coq8.2pl1 ?
COQC =$(COQLIB)coqc
COQDEP =$(COQLIB)coqdep
#INCLUDECOQ =-I .
COQSRC =EqBoolAux.v ListAux.v PosAux.v \
	MapSignatures.v MapList.v BinArrayBot.v BinArray.v \
	Tactics.v MapList.v Ffun.v Lib.v \
        DEX_Domain.v DEX_BigStepType.v \
        DEX_BigStep.v LoadBicolano.v \
	DEX_Program.v Numeric.v Axioms.v \
	Level.v \
	DEX_ImplemProgramWithMap.v DEX_ImplemDomain.v DEX_BigStepAnnot.v Annotated.v \
        cdr.v check_cdr.v DEX_Framework.v \
        DEX_step.v DEX_typing_rules.v DEX_BigStepWithTypes.v DEX_IndistRelations.v \
  DEX_ProofBigStepWithType.v DEX_ElemLemmas.v \
        DEX_ElemLemmaNormalIntra2.v DEX_ElemLemmaNormalIntra3.v \
        DEX_ElemLemmaIntra.v DEX_ElemLemmaReturn.v \
	DEX_Final.v #Example.v

all : $(COQSRC:.v=.vo) depend

depend: 
	$(COQDEP) $(COQSRC) > .depend

.SUFFIXES: .v .vo

.v.vo:
	$(COQC) $(OPTION) $<

clean::
	rm -fr *~ $(COQSRC:.v=.vo) $(COQSRC:.v=.glob) 

include .depend





