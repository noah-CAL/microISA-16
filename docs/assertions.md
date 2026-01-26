# μISA-16 Assertions and Invariants (v1)

> SPDX-License-Identifier: AGPL-3.0-or-later
>
> Copyright (C) 2026 Noah Sedlik

Each of these invariants is intended to be encoded as SystemVerilog Assertions (SVA) in the RTL implementation to ensure correctness of the CPU design regardless of implementation details.

## Assertions Organization
Assertions are specific to the current testbench/module/interface and so that they only rely on specific behavior. This is designed so that implementation specifics allowed to change while modifying the appropriate levels of abstraction as confirmed through assertions. 

Example with an SPSC FIFO implementation (current repo style):

```
┌─────────────────────────────────────┐
│ Testbench (tb_fifo.sv)              │ ← Directed tests + end-to-end checks
│ - Push/pop sequences                │
│ - Data integrity checks             │
└─────────────────────────────────────┘
                ↓ drives
┌─────────────────────────────────────┐
│ RTL (fifo.sv)                       │ ← Synthesizable DUT (assertion-free)
└─────────────────────────────────────┘
                ↑ bound in simulation
┌─────────────────────────────────────┐
│ Checker (fifo_assertions.sv)        │ ← Protocol + black-box functional SVA
│ Bind (bind_fifo.sv)                 │ ← Attach checkers using bind
└─────────────────────────────────────┘
```
The intent is to keep synthesizable RTL clean while keeping verification properties reusable and tool-friendly.

> Note: No ##N SVA delays are used to ensure Verilator compatibility. Procedural #(time) delays exist in testbench / simulation-only non-SVA components.

## Verilator-Compatible SVA

This project targets Verilator as the primary simulation engine. As a result:

- No `##N` SVA delays are used as it is unsupported in Verilator. Temporal relationships are expressed using `$past()` and explicit state variables.
- Checkers avoid concurrent assertions that reference mutable dynamic objects (e.g. `queue.size()`) which caused problems starting with `tb_fifo.sv`. Values are instead captured procedurally and/or mirrored in a stable reference counter.
- Synthesizable RTL is assertion-free. Assertions live in checker modules compiled only for simulation and attached via `bind`.

## Encoding Invariants
- **INV-ENC-001 (RESERVED field invariant):**  
    All fields marked RESERVED or UNUSED in the instruction encoding must be zero.

- **INV-ENC-002 (Illegal instruction handling):**  
    Any illegal instruction encoding (unrecognized opcode or non-zero RESERVED/UNUSED fields) must raise a precise trap:
    `TRAP ← 0x01, TRPC ← PC + 1`, and `PC ← TRH`, and the faulting instruction must not modify architectural state (GPRs, memory, flags).


## Architectural Invariants
- **INV-ARCH-001 (R0 invariant):**  
    R0 always reads as zero. Writes to R0 have no architectural effect.

- **INV-ARCH-002 (Reset initialization):**  
    On reset deassertion, PC and all general-purpose registers (R0–R7) are initialized to zero.

- **INV-ARCH-003 (NOP state):**  
    NOP instructions do not modify architectural state (registers, memory) aside from PC.

- **INV-ARCH-004 (NOP increment):**  
    NOP instructions increment the PC by 1 instruction word.

- **INV-ARCH-005 (CMP GPR modification):**  
    CMP instructions do not modify any general-purpose registers.

- **INV-ARCH-006 (CMP flags modification):**  
    The condition flags `Z` and `N` are only modified by CMP instructions.

- **INV-ARCH-007 (CMP flags):**  
    After `cmp rs1, rs2`: `Z == (rs1 == rs2)`, `N == (rs1 < rs2)` (signed comparison).

## Instruction-semantic Invariants
- **INV-INST-002 (Misaligned memory access handling):**  
    If a load/store accesses an address not aligned to 2 bytes, the instruction must raise a precise trap:
    `TRAP ← 0x02`, `TRPC ← PC + 1`, and `PC ← TRH`, and the faulting instruction must not modify architectural state (GPRs, memory, flags).

- **INV-INST-003 (ADDI sign-extension):**  
    The immediate value in ADDI instructions must be sign-extended to 16 bits before addition.

- **INV-INST-004 (LUI immediate zero-extension):**  
    The immediate value in LUI instructions must be zero-extended to the upper bits of the destination register.

- **INV-INST-005 (Shift amount range):**  
    `imm8[7:4] == 0` for SLLI/SRLI/SRAI instructions.

- **INV-INST-008 (I-type zero-extension):**  
    The immediate value in ANDI/ORI/XORI instructions must be zero-extended to 16 bits.

## Commit and Control Invariants
- **INV-COMMIT-001 (Single commit per instruction):**
    Each macro-instruction causes exactly one architectural commit event, or a trap event, but not both.

- **INV-COMMIT-002 (Architectural state changes only at commit or trap):**
    GPR writes, PC updates, memory writes, flag updates, and special-register updates (`TRAP/TRPC/TRH`) occur only at 
        (a) commit boundaries or 
        (b) trap entry/CRT as defined by the ISA.

- **INV-COMMIT-003 (PC update exclusivity):**
    On any cycle where `PC` changes, the change must be attributable to exactly one of:
        (a) Sequential commit (`PC_next = PC + 1`), 
        (b) Branch taken, jump, `jalr`, trap entry (`PC_next = TRH`), or `CRT` (`PC_next = TRPC`).

## Special Register Invariants (S-type)
- **INV-SREG-001 (SR semantics):**
    For `SR sr, rs1`, at commit: `sr_next == rs1_value` and no other architectural state changes except those implied by commit (e.g., PC update).

- **INV-SREG-002 (LR semantics):**
    For `LR rd, sr`, at commit: `rd_next == sr_value` (unless `rd == R0`, in which case no GPR changes), and no other architectural state changes except PC update.

- **INV-SREG-003 (CRT semantics):**
    Executing `CRT` sets `PC_next == TRPC` and `TRAP_next == 0x00`. No other architectural state changes.

- **INV-SREG-004 (Invalid sr encoding → illegal trap):**
    If an S-type encoding selects an undefined `sr`, it must raise an illegal opcode trap (`TRAP = 0x01`) with precise-trap semantics.

## Trap Invariants (Precise Exceptions)
- **INV-TRAP-001 (Trap is precise):**
    When a trap is taken, the faulting instruction must not modify GPRs, memory, or flags.

- **INV-TRAP-002 (Trap state updates):**
    On trap entry:
    `TRAP_next == trap_code, TRPC_next == PC + 1, PC_next == TRH`.

- **INV-TRAP-003 (`TRAP` nonzero implies in-trap state):**
    If `TRAP != 0x00`, execution must be within the trap handler until CRT clears it.
    (If you do not want to enforce “in-trap mode” in v1, drop this one.)

- **INV-TRAP-004 (`TRAP` clearing):**
    If a call to is made `CRT`, `TRAP` must be reset to `0x00`.

## Microcode Invariants
- **INV-UOP-001 (Bounded completion):**
    Each instruction completes (commit or trap) within `N=10` cycles.
- **INV-UOP-002 (uPC validity):**
    uPC must always remain within the valid instructions of microcode ROM.
- **INV-UOP-003 (Fetch/execute separation):**
    Instruction register (IR) is only updated during fetch and remains stable until commit/trap.

## Debug (simulation-only) assertions
- **INV-SW-001 (SP alignment):**  
    Stack pointer (R7) must always be aligned to a 2-byte boundary.

- **INV-SW-002 (R7 initialization):**  
    Stack pointer must be non-zero before any stack operations are performed.

- **INV-SW-003 (TRH initialization):**
    If a trap occurs and `TRH == 0`, flag an error.

## FIFO Invariants (Warm-up Component)

These invariants specify the expected black-box behavior of the synchronous FIFO (`sources/rtl/fifo.sv`)
and are enforced by the checker module (`sources/test/assertions/fifo_assertions.sv`) bound in simulation.

> Note: FIFO invariants use the namespace `FIFO-INV-*` to avoid mixing component specs with μISA-16 architectural invariants.

### FIFO Control/Signal Integrity

- **FIFO-INV-CTRL-001 (No X controls):**
  `wr_en`, `rd_en`, `full`, and `empty` are never X/Z after reset.

- **FIFO-INV-CTRL-002 (Write data known when writing):**
  If `wr_en==1`, then `wr_data` must be known (not X/Z).

- **FIFO-INV-CTRL-003 (No push when full):**
  It is illegal to assert `wr_en` while `full==1`.

- **FIFO-INV-CTRL-004 (No pop when empty):**
  It is illegal to assert `rd_en` while `empty==1`.

### FIFO Status Correctness

- **FIFO-INV-STAT-001 (Full/empty mutual exclusion):**
  `full && empty` must never be true.

- **FIFO-INV-STAT-002 (Empty matches occupancy):**
  `empty == (occupancy == 0)` where occupancy is tracked by the checker.

- **FIFO-INV-STAT-003 (Full matches occupancy):**
  `full == (occupancy == FIFO_DEPTH)` where occupancy is tracked by the checker.

- **FIFO-INV-STAT-004 (No overflow):**
  Occupancy must never exceed `FIFO_DEPTH`.

- **FIFO-INV-STAT-005 (No underflow):**
  Occupancy must never go below 0.

**Implementation note:** The assertion checker mirrors occupancy in a counter rather than asserting on `q.size()` because concurrent assertions of the queue state cause sampling issues in Verilator.

### FIFO Reset

- **FIFO-INV-RST-001 (Reset release state):**
  Immediately after reset deassertion, `empty==1`, `full==0`, and occupancy is 0.

### FIFO Data Ordering

- **FIFO-INV-DATA-001 (Pop ordering):**
  If a pop is accepted at a rising edge (`rd_en && !empty`), then the value sampled on the immediately preceding falling edge equals the head value predicted by the checker's reference model.
