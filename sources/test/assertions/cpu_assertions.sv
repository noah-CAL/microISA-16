//==============================================================================
// SPDX-License-Identifier: AGPL-3.0-or-later
// Copyright (C) 2026 Noah Sedlik
//
// Description:
//
// Notes:
//==============================================================================
module cpu_assertions (cpu_if.cpu cpu);
  import assert_pkg::err;

  import cpu_pkg::GPR_N;
  import cpu_pkg::PC_DEFAULT;

  import cpu_pkg::TR_NONE;
  import cpu_pkg::TR_ILLEGAL_OPCODE;
  import cpu_pkg::TR_MISALIGNED_MEM;
  import cpu_pkg::TR_RESERVED;
  
  //--------------------------------------------------------------------------
  // Encoding / Decoding Invariants
  //--------------------------------------------------------------------------
  // INV-DEC-001 (Decode field consistency)
  property p_inv_dec_001;
    @(posedge cpu.clk) disable iff (!cpu.rst_n)
      cpu.decode.ir_valid |-> (
        cpu.decode.opcode == cpu.decode.ir[15:12] &&
        cpu.decode.rd     == cpu.decode.ir[11:9] &&
        cpu.decode.rs1    == cpu.decode.ir[8:6]  &&
        cpu.decode.rs2    == cpu.decode.ir[5:3]  &&
        cpu.decode.imm8   == cpu.decode.ir[7:0]
      );
  endproperty

  //--------------------------------------------------------------------------
  // Architectural Invariants
  //--------------------------------------------------------------------------
  // INV-ARCH-001 (R0 invariant)
  property p_inv_arch_001;
    @(posedge cpu.clk) disable iff (!cpu.rst_n)
      cpu.arch.gpr[0] == '0;
  endproperty

  // INV-ARCH-002 (Reset initialization)
  property p_inv_arch_002;
    @(posedge cpu.clk)
      $rose(cpu.rst_n) |-> (
        cpu.arch.csr.PC   == PC_DEFAULT &&
        cpu.arch.csr.TRPC == '0 &&
        cpu.arch.csr.TRH  == '0 &&
        cpu.arch.csr.TRAP == TR_NONE &&
        cpu.arch.gpr      == '0 &&
        cpu.arch.flag_z   == 1'b0 &&
        cpu.arch.flag_n   == 1'b0
      );
  endproperty

  //--------------------------------------------------------------------------
  // Commit and Control Invariants
  //--------------------------------------------------------------------------
  // INV-COMMIT-000 (Architectural boundary)
  property p_inv_commit_000;
    @(posedge cpu.clk) disable iff (!cpu.rst_n)
      !cpu.commit.valid |-> $stable(cpu.arch);
  endproperty

  // INV-COMMIT-001 (Commit is a pulse)
  property p_inv_commit_001;
    @(posedge cpu.clk) disable iff (!cpu.rst_n)
      cpu.commit.valid |-> !$past(cpu.commit.valid);
  endproperty

  // INV-COMMIT-002 (State change gating)
  property p_inv_commit_002;
    @(posedge cpu.clk) disable iff (!cpu.rst_n)
      !cpu.commit.valid |-> $stable(cpu.arch);
  endproperty

  // INV-COMMIT-003 (PC update exclusivity)
  property p_inv_commit_003;
    @(posedge cpu.clk) disable iff (!cpu.rst_n)
      cpu.commit.valid |-> !$stable(cpu.arch.csr.PC);
  endproperty

  // Derived (PC must not change without commit)
  property p_inv_commit_pc_gate;
    @(posedge cpu.clk) disable iff (!cpu.rst_n)
      !$stable(cpu.arch.csr.PC) |-> cpu.commit.valid;
  endproperty

  // Derived (GPR change implies commit + gpr_we)
  property p_inv_commit_gpr_gate;
    @(posedge cpu.clk) disable iff (!cpu.rst_n)
      !$stable(cpu.arch.gpr) |-> (cpu.commit.valid && cpu.commit.gpr_we);
  endproperty

  // Derived (no gpr_we ⇒ GPR stable)
  property p_inv_commit_gpr_stable;
    @(posedge cpu.clk) disable iff (!cpu.rst_n)
      !(cpu.commit.valid && cpu.commit.gpr_we) |-> $stable(cpu.arch.gpr);
  endproperty

  // INV-COMMIT-004 (TRAP encoding consistency, non-trap)
  property p_inv_commit_004;
    @(posedge cpu.clk) disable iff (!cpu.rst_n)
      (cpu.commit.valid && !cpu.commit.is_trap) |-> (
        cpu.commit.trap_code == TR_NONE &&
        cpu.arch.csr.TRAP    == TR_NONE
      );
  endproperty

  // Trap consistency (trap commit)
  property p_inv_trap_consistency;
    @(posedge cpu.clk) disable iff (!cpu.rst_n)
      (cpu.commit.valid && cpu.commit.is_trap) |-> (
        cpu.commit.trap_code != TR_NONE &&
        cpu.arch.csr.TRAP    != TR_NONE
      );
  endproperty

  //--------------------------------------------------------------------------
  // Microarchitectural / Signal Integrity Invariants
  //--------------------------------------------------------------------------
  // INV-UOP-005 (Signal integrity)
  property p_inv_uop_005;
    @(posedge cpu.clk) disable iff (!cpu.rst_n)
      !$isunknown(cpu.commit.valid)   &&
      !$isunknown(cpu.commit.is_trap) &&
      !$isunknown(cpu.arch.csr.PC)    &&
      !$isunknown(cpu.arch.csr.TRAP)  &&
      !$isunknown(cpu.arch.flag_z)    &&
      !$isunknown(cpu.arch.flag_n);
  endproperty


  //--------------------------------------------------------------------------
  // Debug (simulation-only) Invariants
  //--------------------------------------------------------------------------
  // INV-SW-001 (SP alignment)
  property p_inv_sw_001;
    @(posedge cpu.clk) disable iff (!cpu.rst_n)
      cpu.arch.gpr[GPR_N-1][0] == 1'b0;
  endproperty

  // INV-SW-003 (TRH initialization)
  property p_inv_sw_003;
    @(posedge cpu.clk) disable iff (!cpu.rst_n)
      (cpu.commit.valid && cpu.commit.is_trap) |-> cpu.arch.csr.TRH != '0;
  endproperty

  //--------------------------------------------------------------------------
  // Assertions
  //--------------------------------------------------------------------------
  a_dec_001: assert property (p_inv_dec_001)
    else err("INV-DEC-001", "decode fields inconsistent with IR");

  a_arch_001: assert property (p_inv_arch_001)
    else err("INV-ARCH-001", $sformatf("R0 != 0 (0x%0h)", cpu.arch.gpr[0]));

  a_arch_002: assert property (p_inv_arch_002)
    else err("INV-ARCH-002", "architectural state not initialized on reset");

  a_commit_000: assert property (p_inv_commit_000)
    else err("INV-COMMIT-000", "arch changed outside commit");

  a_commit_001: assert property (p_inv_commit_001)
    else err("INV-COMMIT-001", "commit.valid not a pulse");

  a_commit_002: assert property (p_inv_commit_002)
    else err("INV-COMMIT-002", "arch changed without commit");

  a_commit_003: assert property (p_inv_commit_003)
    else err("INV-COMMIT-003", "commit without PC update");

  a_commit_pc_gate: assert property (p_inv_commit_pc_gate)
    else err("INV-COMMIT-PC-GATE", "PC changed without commit");

  a_commit_gpr_gate: assert property (p_inv_commit_gpr_gate)
    else err("INV-COMMIT-GPR-WE", "GPR changed without gpr_we");

  a_commit_gpr_stable: assert property (p_inv_commit_gpr_stable)
    else err("INV-COMMIT-GPR-STABLE", "GPR changed spuriously");

  a_commit_004: assert property (p_inv_commit_004)
    else err("INV-COMMIT-004", "non-trap commit with TRAP set");

  a_trap_consistency: assert property (p_inv_trap_consistency)
    else err("INV-TRAP-CONS-T", "trap commit missing TRAP");

  a_uop_005: assert property (p_inv_uop_005)
    else err("INV-UOP-005", "X/Z on core signals");

  a_sw_001: assert property (p_inv_sw_001)
    else err("INV-SW-001", "stack pointer misaligned");

  a_sw_003: assert property (p_inv_sw_003)
    else err("INV-SW-003", "trap with TRH==0");

  //--------------------------------------------------------------------------
  // Covers
  //--------------------------------------------------------------------------
  c_commit: cover property (@(posedge cpu.clk) disable iff (!cpu.rst_n) cpu.commit.valid);
  c_trap:   cover property (@(posedge cpu.clk) disable iff (!cpu.rst_n) cpu.commit.is_trap);
  c_gpr_we: cover property (@(posedge cpu.clk) disable iff (!cpu.rst_n) cpu.commit.gpr_we);
  c_ir_v:   cover property (@(posedge cpu.clk) disable iff (!cpu.rst_n) cpu.decode.ir_valid);
endmodule
