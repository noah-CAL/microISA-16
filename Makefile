default:
	@echo "USAGE: make [build, test, write_bitstream, program, check_connectivity, clean, clean_all]"

################
#    Vivado    #
################
VIVADO_LOG  = logging/vivado.log
VIVADO_JOU  = logging/vivado.jou
VIVADO_OPTS = -mode batch -log $(VIVADO_LOG) -journal $(VIVADO_JOU)

###################
# Program Outputs #
###################
BITSTREAM   = output/design.bit
CHECKPOINTS = output/post_route.dcp \
							output/post_place.dcp

###################
# Program Sources #
###################
CNSTRS      = sources/basys3_main.xdc
SRCS        = sources/ztop.v

##############
# Verilator  #
##############
VERILATOR = verilator
VERILATOR_FLAGS = --binary --trace -Wall --timing
VERILATOR_OUTPUT = build/obj_dir
VERILATOR_SRC = sources/ztop.sv \
				sources/fifo.sv
VERILATOR_TESTS = test/tb_fifo.sv
VERILATOR_TOP = tb_fifo

sim_fifo:
	@mkdir -p build
	@echo "Building simulation..."
	@$(VERILATOR) $(VERILATOR_FLAGS) \
		--top-module $(VERILATOR_TOP) \
		-Mdir build/obj_dir \
		$(VERILATOR_SRC) $(VERILATOR_TESTS) 2>&1 | bash scripts/colorize.sh
	@echo "Running simulation..."
	@./build/obj_dir/V$(VERILATOR_TOP) 2>&1 | bash scripts/colorize.sh

.PHONY: sim_fifo

#####################
# Building Source   #
#####################
build:
	vivado $(VIVADO_OPTS) -source scripts/synthesis.tcl

test:
	@echo "TODO: set up Verilator"

clean:
	rm -f clockInfo.txt logging/*.log logging/*.jou $(VERILATOR_OUTPUT)/*

clean_all: clean
	rm -f output/*

######################
# Programming FPGA   #
######################
check_connectivity:
	vivado $(VIVADO_OPTS) -source scripts/check_connectivity.tcl

write_bitstream:
	vivado $(VIVADO_OPTS) -source scripts/write_bitstream.tcl

program:
	vivado $(VIVADO_OPTS) -source scripts/program.tcl

$(CONSTRS) $(SRCS) $(CHECKPOINTS) $(BITSTREAM): write_bitstream

.PHONY: default build test check_connectivity write_bitstream program clean clean_all
