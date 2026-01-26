//==============================================================================
// SPDX-License-Identifier: AGPL-3.0-or-later
// Copyright (C) 2026 Noah Sedlik
// 
// Description: Synchronous FIFO with configurable width and depth
// Features:
//   - Power-of-2 depth requirement
//   - Combinational read data
//   - Combinational full/empty flags
//   - Assertion-based verification
//==============================================================================
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

  assign r_idx = r[POINTER_WIDTH-1:0];
  assign w_idx = w[POINTER_WIDTH-1:0];

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
endmodule
