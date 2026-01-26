# μISA-16 ISA Encoding (v1)

> SPDX-License-Identifier: AGPL-3.0-or-later
> Copyright (C) 2026 Noah Sedlik

## Encoding Summary
- All fields marked RESERVED or UNUSED must be encoded as zero.
- Illegal instructions (unrecognized opcodes or non-zero RESERVED fields) cause a precise trap (see [/docs/isa.md](/docs/isa.md)).

| Instruction Type | Opcode `[15:12]` | `[11:9]`    | `[8:6]`      | `[5:3]`    | `[2:0]`    |
| ---------------- | ---------------- | ----------- | ------------ | ---------- | ---------- |
| **R-type**       | `0000`           | `rd`        | `rs1`        | `rs2`      | `funct3`   |
| **I-type**       | `1000–1111`      | `rd`        | `0,imm[7:6]` | `imm[5:3]` | `imm[2:0]` |
| **CMP**          | `0001`           | `000`       | `rs1`        | `rs2`      | `000`      |
| **Branch**       | `0010`           | `cond3`     | `imm[8:6]`   | `imm[5:3]` | `imm[2:0]` |
| **Jump (`j`)**   | `0011`           | `imm[11:9]` | `imm[8:6]`   | `imm[5:3]` | `imm[2:0]` |
| **Jump (`jalr`)**| `0110`           | `rd`        | `rs1`        | `000`      | `000`      |
| **Memory (M)**   | `0100`           | `rt`        | `rs1`        | `000`      | `dir,00`   |
| **S-type**       | `0101`           | `a`         | `b`          | `subop3`   | `000`      |

Notes:
- All fields marked 0 or 000 are RESERVED and must be zero in v1.0.
- Branch and jump immediates are signed, PC-relative instruction offsets.
- In M-type, dir = 0 → load, dir = 1 → store.

### R-type Instructions (`opcode == 0x0`)
| Instruction | `Opcode [15:12]` | `[11:9]` | `[8:6]` | `[5:3]` | `[2:0]` |
| ----------- | ---------------- | -------- | ------- | ------- | ------- |
| `add`       | `0000`           | `rd`     | `rs1`   | `rs2`   | `000`   |
| `and`       | `0000`           | `rd`     | `rs1`   | `rs2`   | `001`   |
| `or`        | `0000`           | `rd`     | `rs1`   | `rs2`   | `010`   |
| `xor`       | `0000`           | `rd`     | `rs1`   | `rs2`   | `011`   |
| `sll`       | `0000`           | `rd`     | `rs1`   | `rs2`   | `100`   |
| `srl`       | `0000`           | `rd`     | `rs1`   | `rs2`   | `101`   |
| `sra`       | `0000`           | `rd`     | `rs1`   | `rs2`   | `110`   |

### I-type Instructions (`opcode == 0x8` to `0xF`)
| Instruction |  `[15:12]`       | `[11:9]` | `[8]` | `[7:0]` |
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

| Instruction | `[15:12]` | `[11:9]` | `[8:6]` | `[5:3]` | `[2:0]` |
| ----------- | --------- | -------- | ------- | ------- | ------- |
| `cmp`       | `0001`    | `000`    | `rs1`   | `rs2`   | `000`   |

### Branch Instructions (`opcode == 0x2`)
| Instruction | `[15:12]` | `[11:9] (cond)` | `[8:0] (imm)` |
| ----------- | --------- | --------------- | ------------- |
| `beq`       | `0010`    | `000`           | `off9`        |
| `bne`       | `0010`    | `001`           | `off9`        |
| `blt`       | `0010`    | `010`           | `off9`        |

### Jump Instruction
| Instruction | `[15:12]` | `[11:9]`    | `[8:6]`    | `[5:0]`    |
| ----------- | --------- | ----------- | ---------- | ---------- |
| `j`         | `0011`    | `off[11:9]` | `off[8:6]` | `off[5:0]` |
| `jalr`      | `0110`    | `rd`        | `rs1`      | `000000`   |

### Memory Instructions (`opcode == 0x4`)
| Instruction | `[15:12]` | `[11:9]` | `[8:6]` | `[5:3]` | `[2]` | `[1:0]` |
| ----------- | --------- | -------- | ------- | ------- | ----- | ------- |
| `load`      | `0100`    | `rt`     | `rs1`   | `000`   | `0`   | `00`    |
| `store`     | `0100`    | `rt`     | `rs1`   | `000`   | `1`   | `00`    |


### S-type Instructions (`opcode == 0x5`)
| Instruction | `[15:12]` | `[11:9]` | `[8:6]` | `[5:3]` | `[2:0]` | 
| ----------- | --------- | -------- | ------- | ------- | ------- |
| `SR`        | `0101`    | `sr`     | `rs1`   | `000`   | `000`   |
| `LR`        | `0101`    | `rd`     | `sr`    | `001`   | `000`   |
| `CRT`       | `0101`    | `000`    | `000`   | `010`   | `000`   |

