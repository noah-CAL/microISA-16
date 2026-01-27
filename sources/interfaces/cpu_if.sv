//==============================================================================
// SPDX-License-Identifier: AGPL-3.0-or-later
// Copyright (C) 2026 Noah Sedlik
// 
// Module: cpu_if
// Description: CPU interface defining signals and modports for internal and 
// external architectural signals.
//==============================================================================
interface cpu_if (
  input clk, 
  input rst_n
);
  import cpu_pkg::arch_state_t;
  import cpu_pkg::commit_t;
  import cpu_pkg::decode_t;
  import cpu_pkg::debug_t;

  // Architectural observation
  arch_state_t arch;
  commit_t     commit;
  decode_t     decode;
  debug_t      debug;

  modport cpu (
    input  clk, rst_n,
    output arch, commit, decode, debug
  );

  modport testing (
    input clk, rst_n, arch, commit, decode, debug
  );
endinterface
