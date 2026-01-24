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
  modport prod (input wr_data, input wr_en, output full, output empty);
  modport cons (input rd_data, input rd_en, output full, output empty);
  modport fifo (
    input  clk, 
    input  rst_n, 
    input  wr_en, 
    input  wr_data, 
    input  rd_en,
    output full, 
    output empty, 
    output rd_data
  );

  property full_empty_exclusion;
    @(posedge clk) disable iff (!rst_n)
    !(full && empty);
  endproperty

  property clear_on_reset;
    @(posedge clk) disable iff (!rst_n)
    $fell(rst_n) |-> ((!full && empty)
              && rd_data == 0);
  endproperty

  Full_empty: assert property (full_empty_exclusion) else `ERR("Full empty exclusion");
  Clear_on: assert property (clear_on_reset) else `ERR("Clear on reset");
  cover property (full_empty_exclusion);
  cover property (clear_on_reset);
endinterface
