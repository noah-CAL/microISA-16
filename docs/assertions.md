# μISA-16 Assertions and Invariants (v1)

Each of these invariants is intended to be encoded as SystemVerilog Assertions (SVA) in the RTL implementation to ensure correctness of the CPU design regardless of implementation details.

## Assertions Organization
Assertions are specific to the current testbench/module/interface and so that they only rely on specific behavior. This is designed so that implementation specifics allowed to change while modifying the appropriate levels of abstraction as confirmed through assertions. 

Example with an SPSC FIFO implementation:

```
┌─────────────────────────────────────┐
│   Testbench (tb_fifo.sv)            │  ← End-to-end functional behavior
│   - Data integrity                  │  ← Cross-module properties
│   - Ordering guarantees             │
└─────────────────────────────────────┘
            ↓ uses
┌─────────────────────────────────────┐
│   Module (fifo.sv)                  │  ← Implementation correctness
│   - Pointer bounds                  │  ← Internal state invariants
│   - Full/empty logic                │  ← Module-specific rules
└─────────────────────────────────────┘
            ↓ implements
┌─────────────────────────────────────┐
│   Interface (fifo_if.sv)            │  ← Protocol rules
│   - Handshake timing                │  ← Implementation-agnostic
│   - Signal stability                │  ← Reusable across modules
└─────────────────────────────────────┘
```

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

- **INV-INST-008 (R-type zero-extension):**  
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
