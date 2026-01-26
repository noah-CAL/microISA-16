// SPDX-License-Identifier: AGPL-3.0-or-later
// Copyright (C) 2026 Noah Sedlik
// Basic Top Module for Basys 3 Board, ARTIX-7 FPGA Module
module ztop(
  input clk,
  input rst_n,
  output led
);

assign led = rst_n;

endmodule
