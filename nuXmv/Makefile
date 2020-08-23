NUXMV ?= nuXmv
EXPANDER ?= expander.py
TIME ?= time

ifeq ($V, 1)
	VERBOSE =
else
	VERBOSE = @
endif

# defs must be the 1st so that preprocessor sees them
SRC_SMV := \
	defs.smv \
	main.smv \
	core.smv \
	inst.smv \
	memory.smv \
	wr_buf.smv \
	v_core.smv \
	prog_local_consistency.smv \
	prog_slow_consistency.smv \
	prog_slow_reordered.smv

PYEXP_EVAL ?= \"\"

NUXMV_RC := nuXmv.rc
NUXMV_READ_RC := nuXmv_read.rc
NUXMV_INVAR_RC := nuXmv_invar.rc
NUXMV_LTL_RC := nuXmv_ltl.rc
NUXMV_CTL_RC := nuXmv_ctl.rc
NUXMV_CONS_RC := nuXmv_cons.rc
NUXMV_LTL_BMC_RC := nuXmv_ltl_bmc.rc

NUXMV_CONS_RC := check_consistency.rc
BENCHMARK_RC ?= benchmark.rc
TARGET := build/model.pp.smv

INVAR_CEX = invar_cex
LTL_CEX = ltl_cex
CTL_CEX = ctl_cex
CONS_CEX = cons_cex

all: $(TARGET) | read

.PHONY: clean all run benchmark check
.SUFFIXES:

build:
	@mkdir -p build

$(TARGET): $(SRC_SMV) | build
	@echo preprocess $(notdir $@)
	$(VERBOSE) $(ENV) $(EXPANDER) --eval $(PYEXP_EVAL) -s -a -f $^ > $@

read: $(TARGET) $(NUXMV_READ_RC)
	@echo nuXmv $(notdir $@)
	$(VERBOSE) $(ENV) cd build && $(NUXMV) -source ../$(NUXMV_READ_RC)

invar: $(TARGET) $(NUXMV_INVAR_RC)
	@echo nuXmv $(notdir $@)
	$(VERBOSE) $(ENV) cd build && rm -f *$(INVAR_CEX)*.xml && $(NUXMV) -source ../$(NUXMV_INVAR_RC)

ltl: $(TARGET) $(NUXMV_LTL_RC)
	@echo nuXmv $(notdir $@)
	$(VERBOSE) $(ENV) cd build && rm -f *$(INVAR_LTL)*.xml && $(NUXMV) -source ../$(NUXMV_LTL_RC)

ltl_bmc: $(TARGET) $(NUXMV_LTL_RC)
	@echo nuXmv $(notdir $@)
	$(VERBOSE) $(ENV) cd build && rm -f *$(INVAR_LTL)*.xml && $(NUXMV) -source ../$(NUXMV_LTL_BMC_RC)

ctl: $(TARGET) $(NUXMV_CTL_RC)
	@echo nuXmv $(notdir $@)
	$(VERBOSE) $(ENV) cd build && rm -f *$(INVAR_CTL)*.xml && $(NUXMV) -source ../$(NUXMV_CTL_RC)

check: invar ltl ctl

benchmark: $(TARGET) $(BENCHMARK_RC)
	@echo nuXmv $(notdir $@)
	$(VERBOSE) $(ENV) cd build && time $(NUXMV) -source ../$(BENCHMARK_RC)

cons: $(TARGET) $(NUXMV_CONS_RC)
	@echo nuXmv $(notdir $@)
	$(VERBOSE) $(ENV) cd build && rm -f *$(INVAR_CONS)*.xml && $(NUXMV) -source ../$(NUXMV_CONS_RC)

clean:
	@rm -fr build
