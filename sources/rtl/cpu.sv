//==============================================================================
// SPDX-License-Identifier: AGPL-3.0-or-later
// Copyright (C) 2026 Noah Sedlik
// 
// Description: 
// Features:
//==============================================================================
module cpu (
  cpu_if.cpu cpu
);
  always_ff @(posedge cpu.clk) begin
    cpu.arch   <= 'd0;
    cpu.commit <= 'd0;
    cpu.decode <= 'd0;
    cpu.debug  <= 'd0;
  end
endmodule
