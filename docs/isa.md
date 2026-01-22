# μISA-16 Instruction Set Architecture (v1)

## Architectural Overview

- **Word size:** 16 bits (2 bytes)
- **Instruction size:** 16 bits (fixed length)
- **Registers:** 8 general-purpose registers (`R0–R7`)
  - `R0` is hardwired to 0
  - `R7` is stack pointer by convention
- **Control state:** 
  - Architectural Program Counter (`PC`), instruction-word addressed 
  - Internal micro-program counter (`uPC`)
- **Execution model:** multi-cycle, microcoded (one instruction at a time)

Immediate fields are intentionally small in v1. Larger constants are constructed using `lui` combined with I-type operations.

---

## Program Counter Semantics
- PC holds the index of the current instruction.
- Normal sequential execution increments PC ← PC + 1.
- All branch and jump targets are computed relative to PC + 1.

## Instruction Classes

- **R-type:** register–register ALU operations
- **I-type:** register–immediate ALU operations (8-bit immediate, two-operand)
- **B-type:** comparisons and conditional branches
- **J-type:** unconditional PC-relative jump
- **M-type:** load/store memory access

---

## R-type Instructions (register–register)
Format: `rd ← f(rs1, rs2)`
- `add rd, rs1, rs2`
- `and rd, rs1, rs2`
- `or  rd, rs1, rs2`
- `xor rd, rs1, rs2`

**Shift operations** 
Shift amount is the lower 4 bits of `rs2`:
- `sll rd, rs1, rs2`
- `srl rd, rs1, rs2`
- `sra rd, rs1, rs2`

---

## I-type Instructions (8-bit immediate, two-operand)

All I-type instructions implicitly use `rd` as both source and destination (to support 8-bit immediates):

```rd ← f(rd, imm8)```

**Arithmetic operations**:
- `addi rd, imm8` - imm8 sign-extended
- `andi rd, imm8` - imm8 zero-extended
- `ori  rd, imm8` - imm8 zero-extended
- `xori rd, imm8` - imm8 zero-extended

**Shift immediates** 
Shift amount is the lower 4 bits of `imm8`. Upper bits must be zero.
- `slli rd, imm8`
- `srli rd, imm8`
- `srai rd, imm8`

**Load Upper Immediate** 
Format: `rd ← (imm8 << 8)`
- `lui  rd, imm8`

---

## B-type Instructions (comparisons and branches)

### `cmp`

- `cmp rs1, rs2`

The `cmp` instruction performs `rs1 - rs2` and updates the internal condition flags:
- Z (zero) flag: set if `rs1 == rs2`
- N (negative) flag: set if `rs1 < rs2` (signed comparison

### Conditional branches

Branch immediates are **9-bit signed word offsets** relative to `PC + 1`.

- `beq label` — branch if `Z == 1`
- `bne label` — branch if `Z == 0`
- `blt label` — branch if `N == 1`

Example:
```asm
cmp r1, r2
beq label
```
---

## J-type Instructions

- `j label` — unconditional PC-relative jump with 12-bit signed immediate offset

---

## M-type Instructions

Memory is word-addressed. All memory accesses must be aligned to 2-byte boundaries.

- `load  rt, M[rs2]` — load 16-bit word from absolute address in rs1 into rt
- `store rt, M[rs2]` — store 16-bit word from rt to absolute address in rs1

---

## Pseudo-instructions

### Stack Operations

Stack grows downwards in memory.

- `push rs` — push register onto stack
  ```asm
  addi R7, -2
  store rs, R7
  ```
- `pop rd` — pop register from stack
  ```asm
    load rd, R7
    addi R7, 2
  ```
### Load Immediate
- `li rd, imm16` — load 16-bit immediate into register
  ```asm
  lui rd, hi8(imm16)
  ori rd, lo8(imm16)
  ```
---

## Programming Notes
- Branch and jump targets are PC-relative calculated from the address of the current instruction (i.e. `PC`, not `PC+1`).
- Function call/return conventions are not defined in v1, but can be implemented by defining stack conventions.
