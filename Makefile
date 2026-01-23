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
PACKAGES   := $(wildcard $(PKG_DIR)/*.sv)
PACKAGES   += $(wildcard $(PKG_DIR)/*.svh)
INTERFACES := $(wildcard $(IF_DIR)/*.sv)

TESTS      := $(wildcard $(TEST_DIR)/*.sv)
SRCS       := $(RTL_SRCS) $(PACKAGES) $(INTERFACES)

###################
# RTL Simulation  #
###################
VIVADO = vivado

VFLAGS := --binary --trace --timing
VFLAGS += -Wall
VFLAGS += --assert
VFLAGS += --coverage
VFLAGS += -j 0  # Auto-detect CPU cores

VOUTPUT := $(BUILD_DIR)/sims
VTOP := tb_fifo

sim_fifo:
	@mkdir -p build
	@echo "Building simulation..."
	$(VERILATOR) $(VFLAGS)  \
		--top-module $(VTOP) \
		-Mdir $(VOUTPUT)    \
		$(SRCS) $(TESTS) 2>&1 | bash scripts/colorize.sh
	@echo "Running simulation..."
	@$(VOUTPUT)/V$(VTOP) 2>&1 | bash scripts/colorize.sh

.PHONY: sim_fifo

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
