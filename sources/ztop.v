// Basic Top Module for Basys 3 Board, ARTIX-7 FPGA Module
module ztop(
  input clk,
  input rst_n,
  output led
);

assign led = rst_n;

endmodule
