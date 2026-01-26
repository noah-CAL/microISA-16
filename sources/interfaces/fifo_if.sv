//==============================================================================
// SPDX-License-Identifier: AGPL-3.0-or-later
// Copyright (C) 2026 Noah Sedlik
// 
// Module: fifo_if
// Description: FIFO protocol interface defining signals and modports for
//              synchronous FIFO communication between producer and consumer
//==============================================================================
import fifo_pkg::DATA_WIDTH;

interface fifo_if (
  input clk, 
  input rst_n
);
  // Write channel
  logic [DATA_WIDTH-1:0] wr_data;
  logic                  wr_en;

  // Read channel
  logic [DATA_WIDTH-1:0] rd_data;
  logic                  rd_en;

  // Status
  logic                  full;
  logic                  empty;

  // Producer/Consumer interfaces
  modport prod (
    input  clk, rst_n,
    input  full, empty,
    output wr_data, wr_en
  );
  modport cons (
    input  clk, rst_n, 
    input  rd_data, full, empty,
    output rd_en
  );
  modport fifo (
    input  clk, rst_n, 
    input  wr_en, wr_data, rd_en,
    output rd_data, full, empty
  );
endinterface
