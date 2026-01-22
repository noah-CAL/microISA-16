# μISA-16 Instruction Set Architecture (v1)

## Architectural Overview

- **Word size:** 16 bits (2 bytes)
- **Instruction size:** 16 bits (fixed length)
- **Registers:** 8 general-purpose registers (`R0–R7`)
  - `R0` is hardwired to 0
  - `R7` is stack pointer by convention
- **Control state:** 
  - Architectural Program Counter (`PC`), word-addressed 
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

## Encoding Summary
- All fields marked RESERVED or UNUSED must be encoded as zero.
- Behavior of illegal instructions must execute as a NOP (in v1).

| Instruction Type | Opcode `[15:12]` | `[11:9]`    | `[8:6]`    | `[5:3]`    | `[2:0]`    |
| ---------------- | ---------------- | ----------- | ---------- | ---------- | ---------- |
| **R-type**       | `0000`           | `rd`        | `rs1`      | `rs2`      | `funct3`   |
| **I-type**       | `1000–1111`      | `rd`        | `0`        | `imm[7:5]` | `imm[4:0]` |
| **CMP**          | `0001`           | `000`       | `rs1`      | `rs2`      | `000`      |
| **Branch**       | `0010`           | `cond3`     | `imm[8:6]` | `imm[5:3]` | `imm[2:0]` |
| **Jump**         | `0011`           | `imm[11:9]` | `imm[8:6]` | `imm[5:3]` | `imm[2:0]` |
| **Memory (M)**   | `0100`           | `rt`        | `rs1`      | `000`      | `dir,00`   |

Notes:
- All fields marked 0 or 000 are RESERVED and must be zero in v1.0.
- Branch and jump immediates are signed, PC-relative word offsets.
- In M-type, dir = 0 → load, dir = 1 → store.

### R-type Instructions (`opcode == 0x0`)
| Instruction | `[15:12]` | `[11:9]` | `[8:6]` | `[5:3]` | `[2:0]` |
| ----------- | --------- | -------- | ------- | ------- | ------- |
| `add`       | `0000`    | `rd`     | `rs1`   | `rs2`   | `000`   |
| `and`       | `0000`    | `rd`     | `rs1`   | `rs2`   | `001`   |
| `or`        | `0000`    | `rd`     | `rs1`   | `rs2`   | `010`   |
| `xor`       | `0000`    | `rd`     | `rs1`   | `rs2`   | `011`   |
| `sll`       | `0000`    | `rd`     | `rs1`   | `rs2`   | `100`   |
| `srl`       | `0000`    | `rd`     | `rs1`   | `rs2`   | `101`   |
| `sra`       | `0000`    | `rd`     | `rs1`   | `rs2`   | `110`   |

### I-type Instructions (`opcode == 0x8` to `0xF`)
| Instruction | Opcode `[15:12]` | `[11:9]` | `[8]` | `[7:0]` |
| ----------- | ---------------- | -------- | ----- | ------- |
| `addi`      | `1000`           | `rd`     | `0`   | `imm8`  |
| `andi`      | `1001`           | `rd`     | `0`   | `imm8`  |
| `ori`       | `1010`           | `rd`     | `0`   | `imm8`  |
| `xori`      | `1011`           | `rd`     | `0`   | `imm8`  |
| `slli`      | `1100`           | `rd`     | `0`   | `imm8`  |
| `srli`      | `1101`           | `rd`     | `0`   | `imm8`  |
| `srai`      | `1110`           | `rd`     | `0`   | `imm8`  |
| `lui`       | `1111`           | `rd`     | `0`   | `imm8`  |

### Compare Instruction

| Instruction | Opcode `[15:12]` | `[11:9]` | `[8:6]` | `[5:3]` | `[2:0]` |
| ----------- | ---------------- | -------- | ------- | ------- | ------- |
| `cmp`       | `0001`           | `000`    | `rs1`   | `rs2`   | `000`   |

### Branch Instructions (`opcode == 0x2`)
| Instruction | `[15:12]` | `[11:9] (cond)` | `[8:0] (imm)` |
| ----------- | --------- | --------------- | ------------- |
| `beq`       | `0010`    | `000`           | `off9`        |
| `bne`       | `0010`    | `001`           | `off9`        |
| `blt`       | `0010`    | `010`           | `off9`        |

### Jump Instruction
| Instruction | Opcode `[15:12]` | `[11:0]` |
| ----------- | ---------------- | -------- |
| `j`         | `0011`           | `off12`  |

### Memory Instructions (`opcode == 0x4`)
| Instruction | `[15:12]` | `[11:9]` | `[8:6]` | `[5:3]` | `[2]` | `[1:0]` |
| ----------- | --------- | -------- | ------- | ------- | ----- | ------- |
| `load`      | `0100`    | `rt`     | `rs1`   | `000`   | `0`   | `00`    |
| `store`     | `0100`    | `rt`     | `rs1`   | `000`   | `1`   | `00`    |

