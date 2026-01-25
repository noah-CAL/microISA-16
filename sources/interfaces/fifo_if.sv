//==============================================================================
// Copyright (C) 2026 Noah Sedlik
// 
// Module: fifo_if
// Description: FIFO protocol interface defining signals and modports for
//              synchronous FIFO communication between producer and consumer
//==============================================================================
`include "sources/packages/assert_macros.svh"

import fifo_pkg::DATA_WIDTH;

/** FIFO Interface - defines the protocol between producer and consumer */
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

  property full_empty_exclusion;
    @(posedge clk) disable iff (!rst_n)
    !(full && empty);
  endproperty

  property clear_on_reset;
    @(posedge clk) disable iff (!rst_n)
    $rose(rst_n) |-> (!full && empty);
              
  endproperty

  a_full_empty: assert property (full_empty_exclusion) else `ERR("a_full_empty_exclusion");
  a_clear_on_reset: assert property (clear_on_reset) else `ERR("a_clear_on_reset");
  cover property (full_empty_exclusion);
  cover property (clear_on_reset);
endinterface
