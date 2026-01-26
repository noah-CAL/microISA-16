//==============================================================================
// SPDX-License-Identifier: AGPL-3.0-or-later
// Copyright (C) 2026 Noah Sedlik
// 
// Description: Package for testbench utility functions
//==============================================================================
package tb_pkg;
  parameter int TIMEOUT_CYCLES = 1000;

  typedef enum logic [1:0] {
    INFO,
    ERROR,
    FATAL,
    SUCCESS
  } level_t;

  task automatic tb_log(string msg, level_t level);
    unique case (level)
    INFO:  $display("[%0t] [TESTBENCH] INFO : %s", $time, msg);
    ERROR: $display("[%0t] [TESTBENCH] ERROR : %s", $time, msg);
    FATAL: begin
      $display("[%0t] [TESTBENCH] FATAL: %s", $time, msg);
      $finish;
    end
    SUCCESS: $display("[%0t] [TESTBENCH] SUCCESS : %s", $time, msg);
    endcase
  endtask

  task automatic timeout_countdown(input logic clk);
    int timeout = 0;
    forever @(posedge clk) begin : timeout_watchdog
      timeout++;
      if (timeout >= TIMEOUT_CYCLES) begin
        $display("[%0t] [TESTBENCH] ERROR: Timeout reached (%0d cycles)", $time, TIMEOUT_CYCLES);
        $finish;
      end
    end
  endtask

  task automatic dump_waveforms(string vcd_dump_path, string scope);
    $dumpfile(vcd_dump_path);
    $dumpvars(0, scope);
  endtask
endpackage
