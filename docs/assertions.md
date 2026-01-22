# μISA-16 Assertions and Invariants (v1)

Each of these invariants is intended to be encoded as SystemVerilog Assertions (SVA) in the RTL implementation to ensure correctness of the CPU design regardless of implementation details.

## Encoding Invariants
- **INV-ENC-001 (RESERVED field invariant):**  
    All fields marked RESERVED or UNUSED in the instruction encoding must be zero.

- **INV-ENC-002 (Illegal instruction handling):**  
    Any illegal instruction must behave as a NOP, leaving architectural state (GPRs, memory, flags) unchanged except for PC increment.


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
    If a load or store instruction attempts to access a misaligned address, the instruction must be treated as a NOP (no state change except PC increment).

- **INV-INST-003 (ADDI sign-extension):**  
    The immediate value in ADDI instructions must be sign-extended to 16 bits before addition.

- **INV-INST-004 (LUI immediate zero-extension):**  
    The immediate value in LUI instructions must be zero-extended to the upper bits of the destination register.

- **INV-INST-005 (Shift amount range):**  
    `imm8[7:4] == 0` for SLLI/SRLI/SRAI instructions.

- **INV-INST-008 (R-type zero-extension):**  
    The immediate value in ANDI/ORI/XORI instructions must be zero-extended to 16 bits.

## Microcode Invariants
TBD

## Debug (simulation-only) assertions
- **INV-SW-001 (SP alignment):**  
    Stack pointer (R7) must always be aligned to a 2-byte boundary.

- **INV-SW-002 (R7 initialization):**  
    Stack pointer must be non-zero before any stack operations are performed.

