# write_bitstream.tcl
# A Vivado script that demonstrates a very simple RTL-to-bitstream non-project batch flow
# from https://docs.amd.com/r/en-US/ug892-vivado-design-flows-overview/Non-Project-Mode-Tcl-Script-Example

# STEP 0: define output directory area.
set outputDir ./output             
file mkdir $outputDir

# STEP 1: setup design sources and constraints
read_verilog [ glob ./sources/*.v ]         
read_xdc ./sources/basys3_main.xdc

# STEP 2: run synthesis, report utilization and timing estimates, write checkpoint design
synth_design -top ztop -part xc7a35tcpg236-1
write_checkpoint -force $outputDir/post_synth
report_timing_summary -file $outputDir/post_synth_timing_summary.rpt
report_power -file $outputDir/post_synth_power.rpt
