#######################################################################
#                                                                     #
#              The Compcert verified compiler                         #
#                                                                     #
#          Xavier Leroy, INRIA Paris-Rocquencourt                     #
#                                                                     #
#  Copyright Institut National de Recherche en Informatique et en     #
#  Automatique.  All rights reserved.  This file is distributed       #
#  under the terms of the GNU General Public License as published by  #
#  the Free Software Foundation, either version 2 of the License, or  #
#  (at your option) any later version.  This file is also distributed #
#  under the terms of the INRIA Non-Commercial License Agreement.     #
#                                                                     #
#######################################################################

include Makefile.config

ifeq ($(wildcard $(ARCH)_$(BITSIZE)),)
ARCHDIRS=$(ARCH)
else
ARCHDIRS=$(ARCH)_$(BITSIZE) $(ARCH)
endif

DIRS=lib common $(ARCHDIRS) backend cfrontend driver \
  flocq/Core flocq/Prop flocq/Calc flocq/Appli exportclight \
  cparser cparser/MenhirLib demo compcertm

RECDIRS=lib common $(ARCHDIRS) backend cfrontend driver flocq exportclight cparser demo compcertm

COQINCLUDES=$(foreach d, $(RECDIRS), -R $(d) compcert.$(d))

COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQDOC="$(COQBIN)coqdoc"
COQEXEC="$(COQBIN)coqtop" $(COQINCLUDES) -batch -load-vernac-source
COQCHK="$(COQBIN)coqchk" $(COQINCLUDES)
MENHIR=menhir
CP=cp

VPATH=$(DIRS)
GPATH=$(DIRS)

# Flocq

FLOCQ=\
  Fcore_Raux.v Fcore_Zaux.v Fcore_defs.v Fcore_digits.v                     \
  Fcore_float_prop.v Fcore_FIX.v Fcore_FLT.v Fcore_FLX.v                    \
  Fcore_FTZ.v Fcore_generic_fmt.v Fcore_rnd.v Fcore_rnd_ne.v                \
  Fcore_ulp.v Fcore.v                                                       \
  Fcalc_bracket.v Fcalc_digits.v Fcalc_div.v Fcalc_ops.v                    \
  Fcalc_round.v Fcalc_sqrt.v                                                \
  Fprop_div_sqrt_error.v Fprop_mult_error.v Fprop_plus_error.v              \
  Fprop_relative.v Fprop_Sterbenz.v                                         \
  Fappli_rnd_odd.v Fappli_double_round.v Fappli_IEEE.v Fappli_IEEE_bits.v

# General-purpose libraries (in lib/)

VLIB=Axioms.v Coqlib.v Intv.v Maps.v Heaps.v Lattice.v Ordered.v \
  Iteration.v Integers.v Archi.v Fappli_IEEE_extra.v Floats.v \
  Parmov.v UnionFind.v Wfsimpl.v \
  Postorder.v FSetAVLplus.v IntvSets.v Decidableplus.v BoolEqual.v \
  sflib.v

# Parts common to the front-ends and the back-end (in common/)

COMMON=Errors.v AST.v Linking.v \
  Events.v Globalenvs.v Memdata.v Memtype.v Memory.v \
  Values.v Smallstep.v Behaviors.v Switch.v Determinism.v Unityping.v \
  Unreach.v \
  Separation.v SimMemInj.v SimMemInjInv.v

# Back-end modules (in backend/, $(ARCH)/)

BACKEND=\
  Cminor.v Op.v CminorSel.v \
  SelectOp.v SelectDiv.v SplitLong.v SelectLong.v Selection.v \
  SelectOpproof.v SelectDivproof.v SplitLongproof.v \
  SelectLongproof.v Selectionproof.v \
  Registers.v RTL.v \
  RTLgen.v RTLgenspec.v RTLgenproof.v \
  Tailcall.v Tailcallproof.v \
  Inlining.v Inliningspec.v Inliningproof.v \
  Renumber.v Renumberproof.v \
  RTLtyping.v \
  Kildall.v Liveness.v \
  ValueDomain.v ValueAOp.v ValueAnalysis.v \
  ConstpropOp.v Constprop.v ConstpropOpproof.v Constpropproof.v \
  CSEdomain.v CombineOp.v CSE.v CombineOpproof.v CSEproof.v \
  NeedDomain.v NeedOp.v Deadcode.v Deadcodeproof.v \
  Unusedglob.v Unusedglobproof.v \
  Unreadglob.v Unreadglobproof.v \
  Machregs.v Locations.v Conventions1.v Conventions.v LTL.v \
  Allocation.v Allocproof.v \
  Tunneling.v Tunnelingproof.v \
  Linear.v Lineartyping.v \
  Linearize.v Linearizeproof.v \
  CleanupLabels.v CleanupLabelsproof.v \
  Debugvar.v Debugvarproof.v \
  Mach.v \
  Bounds.v Stacklayout.v Stacking.v Stackingproof.v \
  Asm.v Asmgen.v Asmgenproof0.v Asmgenproof1.v Asmgenproof.v \

COMPCERTM=\
  ASTC.v CSEproofC.v CopC.v DemoHeader.v IdSimClight.v \
  JunkBlock.v MachExtra.v ModSemProps.v Preservation.v \
  SimMem.v SimSymbDrop.v \
  StacklayoutC.v UpperBound_B.v \
  AdequacyLocal.v CleanupLabelsproofC.v CoqlibC.v \
  DemoSpec.v IdSimClightDropInv.v LTLC.v \
  MutrecA.v \
  RTLC.v \
  SimMemExt.v \
  SimSymbDropInv.v \
  StoreArguments.v \
  ValueAnalysisC.v \
  AdequacySound.v \
  ClightC.v \
  CsemC.v \
  DemoSpecProof.v IdSimClightExtra.v LiftDummy.v MutrecABproof.v \
  RTLgenproofC.v SimMemId.v SimSymbId.v StoreArgumentsProps.v ValueDomainC.v \
  AllocproofC.v ClightStepExt.v CsharpminorC.v DemoTarget.v IdSimClightIdInv.v \
  LinearC.v MapsC.v \
  MutrecABspec.v RTLtypingC.v SimMemInjC.v SimplExprproofC.v \
  Syntax.v \
  ValuesC.v \
  AsmC.v ClightStepInj.v \
  CshmgenproofC.v ErrorsC.v \
  IdSimDemoSpec.v LinearizeproofC.v MatchSimModSem.v \
  MutrecAproof.v RUSC.v SimMemInjInvC.v \
  SimplLocalsproofC.v System.v \
  AsmExtra.v       CminorC.v              CstrategyC.v       EventsC.v \
  IdSimExtra.v          LineartypingC.v    MatchSimModSemExcl.v   MutrecAspec.v \
  RenumberproofC.v   SimMemLift.v     Simulation.v         TailcallproofC.v       mktac.v \
  AsmStepExt.v     CminorSelC.v           CstrategyproofC.v  GlobalenvsC.v \
  IdSimInvExtra.v       LinkingC.v         MatchSimModSemExcl2.v  MutrecB.v \
  SelectionproofC.v  SimMod.v         Skeleton.v           TunnelingproofC.v \
  AsmStepInj.v     CminorgenproofC.v      CtypesC.v          IdSim.v \
  IdSimMutrecAB.v       LinkingC2.v        MatchSimModSemSR.v     MutrecBproof.v      Sem.v \
  SimModSem.v      SmallstepC.v         UnreachC.v \
  AsmgenproofC.v   CompilerC.v            CtypingC.v         IdSimAsm.v \
  IdSimMutrecAIdInv.v   LocationsC.v       MemdataC.v \
  MutrecBspec.v       SemProps.v         SimModSemLift.v  Sound.v \
  UnreadglobproofC.v \
  AsmregsC.v       ConstpropproofC.v      DeadcodeproofC.v   IdSimAsmDropInv.v \
  IdSimMutrecBIdInv.v   LowerBound.v       MemoryC.v \
  MutrecHeader.v      SemiLattice.v      SimModSemSR.v    SoundProduct.v       UnusedglobproofC.v \
  AxiomsC.v        Conventions1C.v \
  DebugvarproofC.v   IdSimAsmExtra.v \
  InliningproofC.v      LowerBoundExtra.v  Mod.v \
  MutrecRefinement.v  SepComp.v          SimProg.v \
  SoundTop.v           UpperBound_A.v \
  BehaviorsC.v     ConventionsC.v \
  DemoExtract.v      IdSimAsmIdInv.v \
  IntegersC.v           MachC.v \
  ModSem.v               Ord.v \
  SeparationC.v      SimSymb.v \
  StackingproofC.v     UpperBound_AExtra.v

# C front-end modules (in cfrontend/)

CFRONTEND=Ctypes.v Cop.v Csyntax.v Csem.v Ctyping.v Cstrategy.v Cexec.v \
  Initializers.v Initializersproof.v \
  SimplExpr.v SimplExprspec.v SimplExprproof.v \
  Clight.v ClightBigstep.v SimplLocals.v SimplLocalsproof.v \
  Cshmgen.v Cshmgenproof.v \
  Csharpminor.v Cminorgen.v Cminorgenproof.v Cstrategyproof.v

# LR(1) parser validator

PARSERVALIDATOR=Alphabet.v Interpreter_complete.v Interpreter.v \
  Validator_complete.v Automaton.v Interpreter_correct.v Main.v \
  Validator_safe.v Grammar.v Interpreter_safe.v Tuples.v

# Parser

PARSER=Cabs.v Parser.v

# Putting everything together (in driver/)

DRIVER=Compopts.v Compiler.v Complements.v

# All source files

FILES=$(VLIB) $(COMMON) $(BACKEND) $(CFRONTEND) $(DRIVER) $(FLOCQ) \
  $(PARSERVALIDATOR) $(PARSER) $(COMPCERTM) exportclight/Clightdefs.v

# Generated source files

GENERATED=\
  $(ARCH)/ConstpropOp.v $(ARCH)/SelectOp.v $(ARCH)/SelectLong.v \
  backend/SelectDiv.v backend/SplitLong.v \
  cparser/Parser.v

all:
	rm -f .depend
	$(MAKE) depend
	$(MAKE) proof
	$(MAKE) extraction
	$(MAKE) ccomp
ifeq ($(HAS_RUNTIME_LIB),true)
	$(MAKE) runtime
endif
ifeq ($(CLIGHTGEN),true)
	$(MAKE) clightgen
endif


proof: $(FILES:.v=.vo)

proof-quick-aux: $(FILES:.v=.vio)

proof-quick:
	rm -f .depend
	$(MAKE) depend
	$(MAKE) proof-quick-aux

# Turn off some warnings for compiling Flocq
flocq/%.vo: COQCOPTS+=-w -compatibility-notation

extraction: extraction/STAMP

extraction/STAMP: $(FILES:.v=.vo) extraction/extraction.v $(ARCH)/extractionMachdep.v
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/extraction.v
	touch extraction/STAMP

.depend.extr: extraction/STAMP tools/modorder driver/Version.ml
	$(MAKE) -f Makefile.extr depend

ccomp: .depend.extr compcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr ccomp
ccomp.byte: .depend.extr compcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr ccomp.byte

clightgen: .depend.extr compcert.ini exportclight/Clightdefs.vo driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr clightgen
clightgen.byte: .depend.extr compcert.ini exportclight/Clightdefs.vo driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr clightgen.byte

runtime:
	$(MAKE) -C runtime

FORCE:

.PHONY: proof extraction runtime FORCE

documentation: $(FILES)
	mkdir -p doc/html
	rm -f doc/html/*.html
	coq2html -d doc/html/ -base compcert -short-names doc/*.glob \
          $(filter-out doc/coq2html cparser/Parser.v, $^)

tools/ndfun: tools/ndfun.ml
	ocamlopt -o tools/ndfun str.cmxa tools/ndfun.ml
tools/modorder: tools/modorder.ml
	ocamlopt -o tools/modorder str.cmxa tools/modorder.ml

latexdoc:
	cd doc; $(COQDOC) --latex -o doc/doc.tex -g $(FILES)

%.vo: %.v
	@rm -f doc/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

%.vio: %.v
	@rm -f doc/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -quick -dump-glob doc/$(*F).glob $*.v

%.v: %.vp tools/ndfun
	@rm -f $*.v
	@echo "Preprocessing $*.vp"
	@tools/ndfun $*.vp > $*.v || { rm -f $*.v; exit 2; }
	@chmod a-w $*.v

compcert.ini: Makefile.config
	(echo "stdlib_path=$(LIBDIR)"; \
         echo "prepro=$(CPREPRO)"; \
         echo "linker=$(CLINKER)"; \
         echo "asm=$(CASM)"; \
	 echo "prepro_options=$(CPREPRO_OPTIONS)";\
	 echo "asm_options=$(CASM_OPTIONS)";\
	 echo "linker_options=$(CLINKER_OPTIONS)";\
         echo "arch=$(ARCH)"; \
         echo "model=$(MODEL)"; \
         echo "abi=$(ABI)"; \
         echo "endianness=$(ENDIANNESS)"; \
         echo "system=$(SYSTEM)"; \
         echo "has_runtime_lib=$(HAS_RUNTIME_LIB)"; \
         echo "has_standard_headers=$(HAS_STANDARD_HEADERS)"; \
         echo "asm_supports_cfi=$(ASM_SUPPORTS_CFI)"; \
	 echo "response_file_style=$(RESPONSEFILE)";) \
        > compcert.ini

driver/Version.ml: VERSION
	cat VERSION \
	| sed -e 's|\(.*\)=\(.*\)|let \1 = \"\2\"|g' \
	>driver/Version.ml

cparser/Parser.v: cparser/Parser.vy
	@rm -f $@
	$(MENHIR) $(MENHIR_FLAGS) --coq cparser/Parser.vy
	@chmod a-w $@

depend: $(GENERATED) depend1

depend1: $(FILES) exportclight/Clightdefs.v
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend

install:
	install -d $(BINDIR)
	install -m 0755 ./ccomp $(BINDIR)
	install -d $(SHAREDIR)
	install -m 0644 ./compcert.ini $(SHAREDIR)
	install -d $(MANDIR)/man1
	install -m 0644 ./doc/ccomp.1 $(MANDIR)/man1
	$(MAKE) -C runtime install
ifeq ($(CLIGHTGEN),true)
	install -m 0755 ./clightgen $(BINDIR)
endif
ifeq ($(INSTALL_COQDEV),true)
	install -d $(COQDEVDIR)
	for d in $(DIRS); do \
          install -d $(COQDEVDIR)/$$d && \
          install -m 0644 $$d/*.vo $(COQDEVDIR)/$$d/; \
	done
	install -m 0644 ./VERSION $(COQDEVDIR)
	@(echo "To use, pass the following to coq_makefile or add the following to _CoqProject:"; echo "-R $(COQDEVDIR) compcert") > $(COQDEVDIR)/README
endif


NORMAL_BULID_DIR=.normal_build

all-rsync:
	rsync -av --copy-links --delete \
	--exclude "$(NORMAL_BULID_DIR)" --exclude '.git/*' \
	--include '*/' \
	--filter=':- .gitignore' \
	'./' "$(NORMAL_BULID_DIR)/"
	cp Makefile.config "$(NORMAL_BULID_DIR)/Makefile.config"
	$(MAKE) -C $(NORMAL_BULID_DIR)
	$(MAKE) -C $(NORMAL_BULID_DIR)/compcomp-linking proof
	rsync -av \
	--include '*/' --include "ccomp" --include "compcert.ini" --include "*.ml" --include "*.mli" \
	--exclude '*' \
 "$(NORMAL_BULID_DIR)/" './'

clean:
	rm -f $(patsubst %, %/*.vo, $(DIRS))
	rm -f $(patsubst %, %/.*.aux, $(DIRS))
	rm -rf doc/html doc/*.glob
	rm -f driver/Version.ml
	rm -f compcert.ini
	rm -f extraction/STAMP extraction/*.ml extraction/*.mli .depend.extr
	rm -f tools/ndfun tools/modorder tools/*.cm? tools/*.o
	rm -f $(GENERATED) .depend
	rm -f .lia.cache
	$(MAKE) -f Makefile.extr clean
	$(MAKE) -C runtime clean
	$(MAKE) -C test clean

distclean:
	$(MAKE) clean
	rm -f Makefile.config

check-admitted: $(FILES)
	@grep -w 'admit\|Admitted\|ADMITTED' $^ || echo "Nothing admitted."

check-proof: $(FILES)
	$(COQCHK) compcert.driver.Complements

print-includes:
	@echo $(COQINCLUDES)

-include .depend

FORCE:
