# μISA-16 -- Microcoded 16-bit CPU with Assertion-Based Verification
# Copyright (C) 2026  Noah Sedlik
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU Affero General Public License as published
# by the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU Affero General Public License for more details.
#
# You should have received a copy of the GNU Affero General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.
default:
	@echo "USAGE: make [build, sim_fifo, sim_cpu, write_bitstream, program, check_connectivity, clean, clean_all]"

# Tools
VIVADO = vivado
VERILATOR = verilator

# Directories
SRC_DIR    := sources
RTL_DIR    := $(SRC_DIR)/rtl
IF_DIR     := $(SRC_DIR)/interfaces
PKG_DIR    := $(SRC_DIR)/packages
TEST_DIR   := $(SRC_DIR)/test
BUILD_DIR  := build

# Source files
RTL_SRCS   := $(wildcard $(RTL_DIR)/*.sv)
PACKAGES   := $(wildcard $(PKG_DIR)/*.sv) $(wildcard $(PKG_DIR)/*.svh)
INTERFACES := $(wildcard $(IF_DIR)/*.sv)

# Tests and Assertions
TESTS      := $(wildcard $(TEST_DIR)/*.sv)
ASSERTS    := $(wildcard $(TEST_DIR)/assertions/*.sv)
BINDS      := $(wildcard $(TEST_DIR)/bind/*.sv)
SRCS       := $(PACKAGES) $(INTERFACES) $(RTL_SRCS)

###################
# RTL Simulation  #
###################
VIVADO = vivado

VFLAGS := --cc --trace --timing
VFLAGS += -Wall
VFLAGS += -Wno-UNUSEDSIGNAL -Wno-UNUSEDPARAM
VFLAGS += --assert --coverage --coverage-line --coverage-toggle
VFLAGS += -j 0

VOUTPUT := $(BUILD_DIR)/sims
TB_MAIN := $(PWD)/$(TEST_DIR)/tb_main.cpp

# A helper function to build/run a selected TB top
define verilate_and_run
	@rm -r $(BUILD_DIR)
	@mkdir -p $(BUILD_DIR)
	@echo "Building simulation (top=$(1))..."
	@$(VERILATOR) $(VFLAGS) --build \
		--top-module $(1) \
		--exe $(TB_MAIN) \
		-CFLAGS -DTOP_CLASS=V$(1) \
		-Mdir $(VOUTPUT) \
		$(SRCS) $(ASSERTS) $(BINDS) $(TESTS) 2>&1 | bash scripts/colorize.sh
	@echo "Running simulation..."
	@$(VOUTPUT)/V$(1) 2>&1 | bash scripts/colorize.sh
endef

sim_fifo:
	$(call verilate_and_run,tb_fifo)

sim_cpu:
	$(call verilate_and_run,tb_cpu)

coverage:
	@mkdir -p $(BUILD_DIR)/coverage/
	@$(VERILATOR)_coverage $(VOUTPUT)/coverage.dat --annotate $(BUILD_DIR)/coverage/
	@echo "Writing coverage results to $(BUILD_DIR)/coverage/"
	@$(VERILATOR)_coverage $(VOUTPUT)/coverage.dat --write-info $(VOUTPUT)/coverage.info
	@lcov --summary $(VOUTPUT)/coverage.info

.PHONY: sim_fifo sim_cpu coverage

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
	rm -f clockInfo.txt logging/*.log logging/*.jou build/sims/*

clean_all: clean
	rm -f output/*

.PHONY: default build test check_connectivity write_bitstream program clean clean_all
