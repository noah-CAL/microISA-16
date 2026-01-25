//==============================================================================
// Copyright (C) 2026 Noah Sedlik
// 
// Description: Synchronous FIFO with configurable width and depth
// Features:
//   - Power-of-2 depth requirement
//   - Combinational read data
//   - Combinational full/empty flags
//   - Assertion-based verification
//==============================================================================
`include "sources/packages/assert_macros.svh"

import fifo_pkg::FIFO_DEPTH;
import fifo_pkg::DATA_WIDTH;

module fifo (
  fifo_if.fifo bus
);
  localparam POINTER_WIDTH = $clog2(FIFO_DEPTH);

  // Declare BRAM memory
  logic [DATA_WIDTH-1:0] mem [FIFO_DEPTH];

  // Read/Write pointers intentionally larger than FIFO_DEPTH
  logic [POINTER_WIDTH:0] r;
  logic [POINTER_WIDTH:0] w;
  logic [POINTER_WIDTH-1:0] r_idx;
  logic [POINTER_WIDTH-1:0] w_idx;
  logic [POINTER_WIDTH:0] occupancy;

  assign r_idx = r[POINTER_WIDTH-1:0];
  assign w_idx = w[POINTER_WIDTH-1:0];
  assign occupancy = (w - r);

  // Compile-time checks
  initial begin : fifo_compile_time_checks
    if (FIFO_DEPTH == 0) 
      $fatal(1, "FIFO_DEPTH must be > 0");
    if ((FIFO_DEPTH & (FIFO_DEPTH - 1)) != 0)
      $fatal(1, "FIFO_DEPTH must be power of 2, got %0d", FIFO_DEPTH);
    if (DATA_WIDTH == 0)
      $fatal(1, "DATA_WIDTH must be > 0");
  end

  always_ff @(posedge bus.clk) begin
    if (~bus.rst_n) begin
      mem[0] <= 'd0;
      r   <= 0;
      w   <= 0;
    end else begin
      if (bus.wr_en && !bus.full) begin
        mem[w_idx] <= bus.wr_data;
        w <= w + 1;
      end
      if (bus.rd_en && !bus.empty) begin
        r <= r + 1;
      end
    end
  end

  always_comb begin
    bus.full  = ((w - r) == FIFO_DEPTH);
    bus.empty = (r == w);
    bus.rd_data = mem[r_idx];
  end

  property a_fifo_clear_on_reset;
    @(posedge bus.clk)
    $rose(bus.rst_n) |-> (!bus.full
                          && bus.empty
                          && r == 0
                          && w == 0);
  endproperty

  property a_full_blocks_wptr;
    @(posedge bus.clk) disable iff (!bus.rst_n)
    (bus.wr_en && bus.full) |-> $stable(w);
  endproperty

  property a_empty_blocks_rptr;
    @(posedge bus.clk) disable iff (!bus.rst_n)
    (bus.rd_en && bus.empty) |-> $stable(r);
  endproperty

  property a_advance_on_read;
    @(posedge bus.clk) disable iff (!bus.rst_n)
    (bus.rd_en && !bus.empty) |=> !$stable(r);
  endproperty

  property a_advance_on_write;
    @(posedge bus.clk) disable iff (!bus.rst_n)
    (bus.wr_en && !bus.full) |=> !$stable(w);
  endproperty

  property a_fifo_overflow;
    @(posedge bus.clk) disable iff (!bus.rst_n)
    occupancy <= FIFO_DEPTH;
  endproperty

  a_check_fifo_clear_on_reset: assert property (a_fifo_clear_on_reset) else `ERR("fifo_clear_on_reset");
  a_check_full_blocks_wptr: assert property (a_full_blocks_wptr) else `ERR("full_blocks_wptr");
  a_check_empty_blocks_rptr: assert property (a_empty_blocks_rptr) else `ERR("empty_blocks_rptr");
  a_check_advance_on_read: assert property (a_advance_on_read) else `ERR("advance_on_read");
  a_check_advance_on_write: assert property (a_advance_on_write) else `ERR("advance_on_write");
  a_check_fifo_overflow: assert property (a_fifo_overflow) else `ERR("fifo_overflow");
  cover property (a_fifo_clear_on_reset);
  cover property (a_full_blocks_wptr);
  cover property (a_empty_blocks_rptr);
  cover property (a_advance_on_read);
  cover property (a_advance_on_write);
  cover property (a_fifo_overflow);
endmodule
