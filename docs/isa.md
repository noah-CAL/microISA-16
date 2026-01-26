# μISA-16 Instruction Set Architecture (v1)

> SPDX-License-Identifier: AGPL-3.0-or-later
> Copyright (C) 2026 Noah Sedlik 

## Architectural Overview

- **Word size:** 16 bits (2 bytes)
- **Instruction size:** 16 bits (fixed length)
- **Registers:** 8 general-purpose registers (`R0–R7`) and trap handler registers `TRAP`, `TRPC`, and `TRH`
  - `R0` is hardwired to 0
  - `R1–R5` are general-purpose
  - `R6` is return address register by convention
  - `R7` is stack pointer by convention
  - `TRAP` is a special register that latches for illegal opcodes or memory access violations. See S-type instructions.
- **Control state:** 
  - Architectural Program Counter (`PC`), instruction-word addressed 
  - Internal micro-program counter (`uPC`)
- **Execution model:** multi-cycle, microcoded (one instruction at a time)
- **Memory:** byte-addressed, up to 32KiB
- **Endianness:** little-endian

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
- **J-type:** unconditional PC-relative jump and register-indirect jump
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

The `cmp` instruction performs `rs1 - rs2` and updates the internal-only condition flags:
- Z (zero) flag: set if `rs1 == rs2`
- N (negative) flag: set if `rs1 < rs2` (signed comparison, two's complement)

### Conditional branches

Branch immediates are **9-bit signed instruction offsets** relative to `PC + 1`. This allows branching to targets within [-256, +255] instructions of `PC + 1`.

- `beq label` — branch if `Z == 1`
- `bne label` — branch if `Z == 0`
- `blt label` — branch if `N == 1`

Example:
```asm
cmp r1, r2
beq label
```

Internal flags are only affected by the `cmp` instruction. Other instructions do not modify the flags, and branch instructions do not automatically clear the flags.

---

## J-type Instructions
Control-flow targets use instruction-word addresses (PC indices).
- `j` uses a **12-bit signed instruction offset** relative to `PC + 1`, enabling targets within [-2048, +2047] instructions.
- `jalr` jumps to a **16-bit instruction-word address** provided in a register.

- `j label` — unconditional PC-relative jump with 12-bit signed **instruction offset** relative to PC_next (i.e. `PC + 1`)
- `jalr rd, rs1` — `rd ← PC_next; PC ← rs1` where `rs1` holds the instruction-word address

---

## M-type Instructions

Memory is byte-addressed. All memory accesses must be aligned to 2-byte boundaries. On an unaligned access, a precise trap is raised and no memory or register state is modified.

- `load  rt, M[rs1]` — load 16-bit word from byte-addressed `M[rs1]` into `rt`
- `store rt, M[rs1]` — store 16-bit word in `rt` to byte-addressed `M[rs1]`

`rt` is the target/source register for load/store.

---

## S-type Instructions (Special Register Access and Trap Handling)

S-type instructions provide controlled access to architectural special registers
used for trap handling and system control.

- `SR sr, rs1` — Store to Special Register
    - Writes the value in general-purpose register `rs1` to the special register `sr`.
    - `sr` must be one of: 
        - `TRAP`
        - `TRPC`
        - `TRH`
    - Writing `TRAP` is permitted but software is expected to use `CRT` to clear traps.
    Semantics:
    ```asm
    sr ← rs1
    ```
- `LR rd, sr` — Load from Special Register
    - Reads the value of special register `sr` into general-purpose register `rd`.
    - `rd` may be any GPR except `R0` (writes to `R0` are ignored).
    Semantics:
    ```asm
    rd ← sr
    ```
- `CRT` — Clear and Return from Trap
    Returns from a trap handler.

    Semantics:
    ```asm
    PC ← TRPC
    TRAP ← 0x00
    ```
No other architectural state is modified by `CRT`.

### Trap Model (Precise Traps)

μISA-16 provides precise, non-maskable traps for illegal operations and memory access violations (e.g., unaligned memory access).

A trap is taken when the current instruction detects a fault during decode or execution. On a trap:

- The faulting instruction does not commit architectural state (register file, memory, or flags).
- `TRAP ← trap_code`
- `TRPC ← PC + 1`
- `PC ← TRH` (trap handler entry point)
- Execution resumes at the trap handler entry point.

At most one trap may be taken per instruction.

#### Trap Registers

- `TRAP` — trap cause code:
  - `0x00` — no trap
  - `0x01` — illegal opcode (including invalid special-register encodings)
  - `0x02` — unaligned memory access
  - `0x03` — other faults (reserved)
- `TRPC` — saved return PC (`PC + 1` at time trap is taken), instruction-word address
- `TRH` — trap handler entry point, instruction-word address

Trap registers are initialized to zero on reset.

### Trap Handler Register Preservation (Convention)

Trap handlers may freely use general-purpose registers. However, to allow the interrupted program to resume transparently, the default trap-handler convention is:

- Preserve `R1–R6` across trap handling.
- `R7` is the stack pointer and must remain valid (stack grows downward in memory).

Trap handlers may implement preservation using the pseudo-instructions below.

If a trap occurs while executing the trap handler itself, behavior is undefined in v1.

### Trap Pseudo-instructions

#### `SETTRH tmp, label`
Sets the trap handler entry point.

```asm
li tmp, label
SR TRH, tmp
```

#### `save_state`
Save the preserved GPRs (`R1-R6`) at the time of the trap onto the stack.

```asm
push R1
push R2
push R3
push R4
push R5
push R6
```
#### `restore_state`
Restore the preserved GPRs (`R1-R6`) at the time of the trap from the stack.

```asm
pop R6
pop R5
pop R4
pop R3
pop R2
pop R1
```

### Trap Handler Skeleton
A trap handler should have the following structure:

```asm
trap_entry:
    save_state
    # Handle the trap (inspect TRAP, take action, etc.)
    restore_state
    CRT
```

---

## Pseudo-instructions

### Stack Operations

Stack grows downwards in memory. `R7` conventionally points to the top of the stack (address of the most recently pushed item).

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

### Jumps
- `jal rd, tmp, label` — jump to `label` and store return address (`PC + 1`) in `rd` using `tmp` as a temporary register.
  ```asm
  li tmp, label
  jalr rd, tmp
  ```
- `jr rs1` — unconditional jump to address in `rs1`
  ```asm
  jalr R0, rs1
  ```
- `ret` — unconditional jump to address in `R6` (return address register)
  ```asm
  jalr R0, R6
  ```

### Trap Handling
See S-type Instructions section for trap handling pseudo-instructions.

---

## Programming Notes
- Function call/return conventions are not defined in v1, but can be implemented by defining stack conventions.
- Assembler code labels denote instruction-word addresses (PC indices). Data labels evaluate to byte addresses.

## Illegal Behavior
- Unaligned memory accesses raise a precise trap.
