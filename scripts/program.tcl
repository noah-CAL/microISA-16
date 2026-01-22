# program.tcl
# 
# Opens the HW manager and programs the connected 
# device with the bitstream located
# at ./output/design.bit (generated with write_bitstream.tcl)
set bitstream ./output/design.bit

open_hw_manager
connect_hw_server
current_hw_target
open_hw_target
current_hw_device

set_property PROGRAM.FILE $bitstream [current_hw_device]
program_hw_devices [current_hw_device]
