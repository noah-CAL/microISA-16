//==============================================================================
// SPDX-License-Identifier: AGPL-3.0-or-later
// Copyright (C) 2026 Noah Sedlik
// 
// Description: CPU package defining structs and constants
//==============================================================================
package cpu_pkg;
  //---------------------------------------------------------------------------
  // Global parameters
  //----------------------------------------------------------------------------
  localparam int unsigned WORD_W     = 16;
  localparam int unsigned GPR_N      = 8;
  localparam int unsigned GPR_AW     = $clog2(GPR_N);
  localparam logic [WORD_W-1:0] PC_DEFAULT = '0;

  //----------------------------------------------------------------------------
  // Trap codes
  //----------------------------------------------------------------------------
  typedef enum logic [3:0] {
    TR_NONE           = 4'd0,
    TR_ILLEGAL_OPCODE = 4'd1,
    TR_MISALIGNED_MEM = 4'd2,
    TR_RESERVED       = 4'd3
  } trap_code_t;

  //----------------------------------------------------------------------------
  // Architectural CSRs (for controlling execution)
  //----------------------------------------------------------------------------
  typedef struct packed {
    logic [WORD_W-1:0] PC;        // instruction-word address
    logic [WORD_W-1:0] TRPC;      // saves PC+1 on trap entry
    logic [WORD_W-1:0] TRH;       // trap handler entry point
    trap_code_t        TRAP;      // TRAP code register value
  } arch_csr_t;

  //----------------------------------------------------------------------------
  // Architectural state: this supplies a stable snapshot of my CPU
  //----------------------------------------------------------------------------
  typedef struct packed {
    arch_csr_t                        csr;
    logic [GPR_N-1:0][WORD_W-1:0]     gpr;    // e.g. gpr[0] is R0
    logic                             flag_z;
    logic                             flag_n;
  } arch_state_t;

  //----------------------------------------------------------------------------
  // Commit event details: updates exactly once per instruction on a commit 
  // or trap
  //----------------------------------------------------------------------------
  typedef struct packed {
    // CTRL signals asserted during the same cycle of a change in the 
    // architectural state
    logic              valid;        // asserted in the same cycle of a commit / trap
    logic              is_trap;      // 1 => trap outcome, 0 => normal commit
    trap_code_t        trap_code;    

    logic [WORD_W-1:0] pc_before;
    logic [WORD_W-1:0] pc_after;

    // GPR writeback
    logic              gpr_we;
    logic [GPR_AW-1:0] gpr_waddr;
    logic [WORD_W-1:0] gpr_wdata;

    // Mark whether flags updated at commit (e.g. only cmp)
    logic              flags_we;
    logic              flag_z_next;
    logic              flag_n_next;
  } commit_t;

  //----------------------------------------------------------------------------
  // Instruction decode visibility
  //----------------------------------------------------------------------------
  typedef struct packed {
    logic [WORD_W-1:0] ir;            // latched instruction word
    logic              ir_valid;      // asserted when ir holds a valid instruction in-flight

    logic [3:0]        opcode;
    logic [2:0]        rd;
    logic [2:0]        rs1;
    logic [2:0]        rs2;
    logic [7:0]        imm8;
  } decode_t;

  //----------------------------------------------------------------------------
  // Internal Microarchitecture signals
  // Keeping these separate so architectural checkers don't depend on them.
  //----------------------------------------------------------------------------
  typedef struct packed {
    logic [WORD_W-1:0] uPC;
    logic [WORD_W-1:0] uPC_entry;
    logic              in_fetch;
    logic              in_execute;
  } debug_t;
endpackage
