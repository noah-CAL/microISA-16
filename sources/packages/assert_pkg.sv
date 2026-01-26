//==============================================================================
// SPDX-License-Identifier: AGPL-3.0-or-later
// Copyright (C) 2026 Noah Sedlik
// 
// Description: FIFO package for assertion macros
//==============================================================================
package assert_pkg;
  parameter FAIL_DELAY = 50;

  task automatic err(string name, string msg);
    $display("[t=%0t] [Assertion %s] failed: %s", $time, name, msg);
    if (FAIL_DELAY > 0)
      #(FAIL_DELAY);
    $finish;
  endtask

endpackage
