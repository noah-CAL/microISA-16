default:
	@echo "USAGE: make [build, test, write_bitstream, program, check_connectivity, clean, clean_all]"

# Tools
VIVADO = vivado
VERILATOR = verilator

# Directories
SRC_DIR   := sources
RTL_DIR   := $(SRC_DIR)/rtl
IF_DIR    := $(SRC_DIR)/interfaces
PKG_DIR   := $(SRC_DIR)/packages
TEST_DIR  := test
BUILD_DIR := build

# Source files
RTL_SRCS   := $(wildcard $(RTL_DIR)/*.sv)
PACKAGES   := $(wildcard $(PKG_DIR)/*.sv) $(wildcard $(PKG_DIR)/*.svh)
INTERFACES := $(wildcard $(IF_DIR)/*.sv)

TESTS      := $(wildcard $(TEST_DIR)/*.sv)
SRCS       := $(PACKAGES) $(INTERFACES) $(RTL_SRCS)

###################
# RTL Simulation  #
###################
VIVADO = vivado

VFLAGS := --cc --trace --timing
VFLAGS += -Wall -Wno-UNUSEDSIGNAL
VFLAGS += --assert --coverage --coverage-line --coverage-toggle
VFLAGS += -j 0  # Auto-detect CPU cores

VOUTPUT := $(BUILD_DIR)/sims
VTOP := tb_fifo

sim_fifo:
	@mkdir -p build
	@echo "Building simulation..."
	@$(VERILATOR) $(VFLAGS) --build                   	 \
		--top-module $(VTOP) 							 \
		--exe $(PWD)/test/tb_main.cpp					 \
		-Mdir $(VOUTPUT)    						  	 \
		$(SRCS) $(TESTS) 2>&1 | bash scripts/colorize.sh 
	@echo "Running simulation..." 
	@$(VOUTPUT)/V$(VTOP) 2>&1 | bash scripts/colorize.sh

coverage:
	@$(VERILATOR)_coverage $(VOUTPUT)/coverage.dat --write-info $(VOUTPUT)/coverage.info
	@lcov --summary $(VOUTPUT)/coverage.info

.PHONY: sim_fifo coverage

##########################################
# FPGA Synthesis & Programming Synthesis #
##########################################
VIVADO      = vivado
VIVADO_LOG  = logging/vivado.log
VIVADO_JOU  = logging/vivado.jou
VIVADO_OPTS = -mode batch -log $(VIVADO_LOG) -journal $(VIVADO_JOU)

BITSTREAM   = output/design.bit
CHECKPOINTS = output/post_route.dcp \
						output/post_place.dcp

CNSTRS      = sources/basys3_main.xdc

build:
	$(VIVADO) $(VIVADO_OPTS) -source scripts/synthesis.tcl

check_connectivity:
	$(VIVADO) $(VIVADO_OPTS) -source scripts/check_connectivity.tcl

write_bitstream:
	$(VIVADO) $(VIVADO_OPTS) -source scripts/write_bitstream.tcl

program:
	$(VIVADO) $(VIVADO_OPTS) -source scripts/program.tcl

$(RTL_SRCS) $(INTERFACES) $(PACKAGES) $(CONSTRS) $(SRCS) $(CHECKPOINTS) $(BITSTREAM): write_bitstream

clean:
	rm -f clockInfo.txt logging/*.log logging/*.jou /build/sims/*

clean_all: clean
	rm -f output/*

.PHONY: default build test check_connectivity write_bitstream program clean clean_all
