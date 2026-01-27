//==============================================================================
// SPDX-License-Identifier: AGPL-3.0-or-later
// Copyright (C) 2026 Noah Sedlik
//
// Description: CPU testbench
// Notes:
//==============================================================================
module tb_cpu;
  import tb_pkg::CLK_PERIOD;
  import tb_pkg::TIMEOUT_CYCLES;
  import tb_pkg::tb_log;

  logic clk, rst_n;

  //----------------------------------------------------------------------------
  // Clock generation
  //----------------------------------------------------------------------------
  initial begin
    clk = 1'b0;
    forever #(CLK_PERIOD/2) clk = ~clk;
  end

  //----------------------------------------------------------------------------
  // DUT instantiation
  //----------------------------------------------------------------------------
  cpu_if cpu_if (.clk(clk), .rst_n(rst_n));
  cpu    dut    (.cpu(cpu_if.cpu));

  //----------------------------------------------------------------------------
  // Utilities
  //----------------------------------------------------------------------------
  task automatic reset_dut();
    rst_n = 1'b0;
    repeat (5) @(posedge clk);

    @(negedge clk);
    rst_n = 1'b1;
    @(posedge clk);
  endtask
  //----------------------------------------------------------------------------
  // Tests
  //----------------------------------------------------------------------------
  task automatic do_nothing;
  endtask

  //----------------------------------------------------------------------------
  // Main
  //----------------------------------------------------------------------------
  initial begin : main_test
    reset_dut();
    tb_log("No tests yet. ", tb_pkg::SUCCESS);
    $finish;
  end

  //----------------------------------------------------------------------------
  // Testing Utils
  //----------------------------------------------------------------------------
  initial begin
    tb_pkg::dump_waveforms("build/sims/tb_fifo.vcd");
    tb_pkg::timeout_countdown(clk);
  end
endmodule

