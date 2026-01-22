# μISA-16 Instruction Set Architecture (v1)

## Architectural Overview

- **Word size:** 16 bits (2 bytes)
- **Instruction size:** 16 bits (fixed length)
- **Registers:** 8 general-purpose registers (`R0–R7`)
  - `R0` is hardwired to 0
  - `R7` is stack pointer by convention
- **Control state:** architectural Program Counter (`PC`) and internal micro-program counter (`uPC`)
- **Execution model:** multi-cycle, microcoded (one instruction at a time)

Immediate fields are intentionally small in v1. Larger constants are constructed using `lui` combined with I-type operations.

---

## Instruction Classes

- **R-type:** register–register ALU operations
- **I-type:** register–immediate ALU operations (8-bit immediate, two-operand)
- **B-type:** comparisons and conditional branches
- **J-type:** PC-relative jump
- **M-type:** load/store memory access

---

## R-type Instructions (register–register)
`rd ← f(rs1, rs2)`
- `add rd, rs1, rs2`
- `and rd, rs1, rs2`
- `or  rd, rs1, rs2`
- `xor rd, rs1, rs2`

**Shifts** (shift amount = lower 4 bits of `rs2`):
- `sll rd, rs1, rs2`
- `srl rd, rs1, rs2`
- `sra rd, rs1, rs2`

---

## I-type Instructions (8-bit immediate, two-operand)

All I-type instructions implicitly use `rd` as both source and destination (to support 8-bit immediates):
`rd ← f(rd, imm8)`

**Arithmetic operations**:
- `addi rd, imm8`
- `andi rd, imm8`
- `ori  rd, imm8`
- `xori rd, imm8`

**Shift immediates** (shift amount = lower 4 bits of `imm8`):
- `slli rd, imm8`
- `srli rd, imm8`
- `srai rd, imm8`

**Load Upper Immediate** rd ← (imm8 << 8)
- `lui  rd, imm8`

> Immediate values are sign-extended to 16-bits unless otherwise specified.

---

## B-type Instructions (comparisons and branches)

- `cmp rs1, rs2`

The `cmp` instruction updates internal condition flags used by subsequent branch instructions.

Branch immediates are 9-bit signed values representing a word-aligned offset from the address of the current instruction.

**Branches** (PC-relative):
- `beq label` — branch if equal
- `bne label` — branch if not equal
- `blt label` — branch if signed less-than

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

- `load  rs1, M[rs2]` — load 16-bit word from absolute address in rs2 into rs1
- `store rs1, M[rs2]` — store 16-bit word from rs1 to absolute address in rs2

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

## Encoding Summary


