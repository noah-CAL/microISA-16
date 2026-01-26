//==============================================================================
// μISA-16 -- Microcoded 16-bit CPU with Assertion-Based Verification
// Copyright (C) 2026  Noah Sedlik
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published
// by the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.
//
// Description: Synchronous FIFO testbench
// Notes:
//   - Push/pop tasks
//   - Uses test_data[] and received_data[] arrays for checking
//==============================================================================
`define ARRAY_SIZE (fifo_pkg::FIFO_DEPTH << 1)

module tb_fifo;
  import fifo_pkg::DATA_WIDTH;
  import fifo_pkg::FIFO_DEPTH;
  import fifo_pkg::CLK_PERIOD;

  import tb_pkg::TIMEOUT_CYCLES;
  import tb_pkg::tb_log;

  logic clk, rst_n;

  logic [DATA_WIDTH-1:0] test_data    [`ARRAY_SIZE];
  logic [DATA_WIDTH-1:0] received_data[`ARRAY_SIZE];

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
  fifo_if bus (.clk(clk), .rst_n(rst_n));
  fifo    dut (.bus(bus.fifo));

  //----------------------------------------------------------------------------
  // Utilities
  //----------------------------------------------------------------------------
  task automatic initialize_test_vector();
    for (int i = 0; i < `ARRAY_SIZE; i++) begin
      test_data[i]     = DATA_WIDTH'($random);
      received_data[i] = '0;
    end
  endtask

  task automatic reset_dut();
    bus.wr_en   = 1'b0;
    bus.rd_en   = 1'b0;
    bus.wr_data = '0;
    rst_n = 1'b0;
    repeat (5) @(posedge clk);

    @(negedge clk);
    rst_n = 1'b1;
    @(posedge clk);

    if (!bus.empty) tb_log("After reset, FIFO not empty.", tb_pkg::FATAL);
    if (bus.full)   tb_log("After reset, FIFO unexpectedly full.", tb_pkg::FATAL);
  endtask

  //----------------------------------------------------------------------------
  // FIFO primitives (blocking until accepted)
  // - Drive wr_en/rd_en on negedge so they are stable before the next posedge.
  // - Read rd_data in the same cycle rd_en is asserted.
  //----------------------------------------------------------------------------
  task automatic push_one(input logic [DATA_WIDTH-1:0] data, input int idle_cycles = 0);
    // Wait for space
    while (bus.full) @(negedge clk);
    // Drive write for one cycle
    bus.wr_en = 1'b1;
    bus.wr_data = data;

    // Wait for stability before posedge
    @(negedge clk);
    bus.wr_en   = 1'b0;

    repeat (idle_cycles) @(negedge clk);
  endtask

  task automatic pop_one(output logic [DATA_WIDTH-1:0] data, input int idle_cycles = 0);
    // Wait for data
    while (bus.empty) @(negedge clk);
    // Assert read for one cycle
    // Data is combinational from current r_idx
    bus.rd_en = 1'b1;
    data = bus.rd_data;

    // Wait for stability after posedge
    @(negedge clk);
    bus.rd_en = 1'b0;

    repeat (idle_cycles) @(negedge clk);
  endtask

  //----------------------------------------------------------------------------
  // Tests
  //----------------------------------------------------------------------------
  task automatic test_sync_write_read();
    tb_log("Test: Sync write/read (Push one block -> Pop one block -> ...)", tb_pkg::INFO);
    reset_dut();
    initialize_test_vector();

    for (int i = 0; i < `ARRAY_SIZE; i++) begin
      push_one(test_data[i], 0);
      pop_one(received_data[i], 0);

      if (received_data[i] != test_data[i]) begin
        tb_log($sformatf("Expected received data == test_data (exp 0x%0h, got 0x%0h", 
          test_data[i], received_data[i]), tb_pkg::FATAL);
      end
    end

    if (!bus.empty) tb_log("Expected empty at end of sync write/read test.", tb_pkg::FATAL);
  endtask

  task automatic test_full_condition();
    logic [DATA_WIDTH-1:0] data;

    tb_log("Test: Full condition (Fill, then empty)", tb_pkg::INFO);
    reset_dut();
    initialize_test_vector();

    // Fill exactly to FIFO_DEPTH
    for (int i = 0; i < FIFO_DEPTH; i++) begin
      push_one(test_data[i], 0);
    end

    if (!bus.full) tb_log("Expected full after filling to FIFO_DEPTH.", tb_pkg::FATAL);
    if (bus.empty) tb_log("Empty asserted while full.", tb_pkg::FATAL);

    fork
      begin : writer_thread
        push_one(test_data[FIFO_DEPTH % `ARRAY_SIZE], 0);
      end
      begin : reader_thread
        repeat (5) @(negedge clk);
        pop_one(data, 0);
      end
    join

    if (!bus.full) tb_log("Expected full after pop and push at full boundary.", tb_pkg::FATAL);
    
    for (int i = 1; i < FIFO_DEPTH; i++) begin
      pop_one(data, 0);
      if (data != test_data[i]) begin
        tb_log($sformatf("Expected received data == test_data (exp 0x%0h, got 0x%0h", 
          test_data[i], data[i]), tb_pkg::FATAL);
      end
    end
    pop_one(data, 0);
    if (!bus.empty) tb_log("Expected empty after draining FIFO in full test.", tb_pkg::FATAL);
  endtask

  task automatic test_empty_condition();
    logic [DATA_WIDTH-1:0] data;

    tb_log("Test: Empty condition (read blocks until write)", tb_pkg::INFO);
    reset_dut();
    initialize_test_vector();

    if (!bus.empty) tb_log("Expected empty at start of empty test.", tb_pkg::FATAL);

    // Wait a few cycles before pushing and reading one item
    fork
      begin : reader_thread
        pop_one(data, 0);
      end
      begin : writer_thread
        repeat (5) @(negedge clk);
        push_one(test_data[0], 0);
      end
    join

    if (data != test_data[0]) begin
      tb_log($sformatf("Expected data == test_data (exp 0x%0h, got 0x%0h", test_data[0], data), tb_pkg::FATAL);
    end

    if (!bus.empty) tb_log("Expected empty after single push/pop in empty test.", tb_pkg::FATAL);
  endtask

  //----------------------------------------------------------------------------
  // Main
  //----------------------------------------------------------------------------
  initial begin : main_test
    if (`ARRAY_SIZE < FIFO_DEPTH) begin
        tb_log($sformatf("Array of size %d should be >= FIFO depth of %d for proper full / empty testing.",
          `ARRAY_SIZE, FIFO_DEPTH), tb_pkg::FATAL);
    end
    tb_log($sformatf("FIFO testing with FIFO depth=%0d, FIFO data width=%0d, test array size=%0d",
                      FIFO_DEPTH, DATA_WIDTH, `ARRAY_SIZE), tb_pkg::INFO);
    rst_n = 1'b1;
    reset_dut();

    test_sync_write_read();
    test_full_condition();
    test_empty_condition();

    tb_log("All tests passed", tb_pkg::SUCCESS);
    $finish;
  end

  //----------------------------------------------------------------------------
  // Testing Utils
  //----------------------------------------------------------------------------
  initial begin
    tb_pkg::dump_waveforms("build/sims/tb_fifo.vcd", "tb_fifo");
    tb_pkg::timeout_countdown(bus.clk);
  end
endmodule

