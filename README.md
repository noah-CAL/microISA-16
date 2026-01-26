# μISA-16

Microcoded 16-bit CPU with Assertion-Based Verification

## Overview

This project implements a simple 16-bit CPU using a **microcoded control architecture**, written in SystemVerilog and verified using **assertion-based verification (SystemVerilog Assertions, SVA)** and directed / randomized testbenches.

The primary goal of the project is **verification-focused design**, rather than performance or ISA complexity. The CPU executes one instruction at a time using a microcode ROM and micro-program counter (µPC), making control flow explicit and well-suited for writing strong temporal assertions.

This project is fully self-contained and publishable, and was developed to complement prior work on pipelined ASIC CPUs by exploring a contrasting execution model and verification-centric design practices.

## Architecture Summary

- **Word size:** 16-bit  
- **Execution model:** Microcoded, multi-cycle (no pipeline)  
- **Registers:** 8 general-purpose registers  
- **Control:** Microcode ROM + micro-program counter (µPC)  
- **PC model:** Separate architectural PC and µPC  
- **Memory model:** Unified instruction/data memory (single-ported in FPGA BRAM)
- **Trap handling:** Supports precise traps with architectural trap registers (`TRAP`, `TRPC`, `TRH`) for illegal instructions, memory violations, and other architectural exceptions.

Each macro-instruction is decoded into a microcode entry point and executed as a sequence of micro-instructions. Architectural state (PC and registers) updates only at explicit instruction commit points. The ISA is intentionally minimal and designed to support strong, compositional correctness properties.

Architectural correctness is defined solely in terms of architected state (PC, GPRs, and trap CSRs) at instruction boundaries, and all assertions are written against this architectural interface rather than microcode internals.

## Documentation
- [Instruction Set Architecture](docs/isa.md)
- [Instruction Encoding](docs/encoding.md)
- [Assertions and System Invariants](docs/assertions.md)
- [FIFO Module Contract](docs/modules/fifo.md)

## Verification Strategy

Verification is centered around **assertion-based invariants**. These properties define the intended correctness model and will be incrementally encoded as assertions as the RTL and microcode are developed.

Key properties enforced using SystemVerilog Assertions include:
- Architectural PC updates only at instruction commit boundaries
- Exactly one commit per instruction
- Microcode execution always makes forward progress and terminates
- Register file writes occur only at commit
- On traps, no architectural state commits (precise exception guarantee)

Assertions are written with explicit temporal intent (cycle-accurate, non-ambiguous timing) and are treated as executable specifications of the ISA and trap model. They are complemented by testbenches that execute directed and randomized instruction streams and check architectural state at instruction boundaries.

## How to Run

### Requirements

- Xilinx Vivado (used for RTL synthesis and preprocessing)
- Verilator (used for simulation and assertion checking)
- GNU Make
- C++ compiler (for Verilator harness)
- (Optional) GTKWave (for Waveform viewing)

The simulation flow uses Vivado for RTL preprocessing and FPGA-specific inference, followed by cycle-accurate simulation and assertion checking using Verilator.

### Build and Simulate
To build and simulate the CPU, run the following commands in the project root directory:
```bash
> make build
> make sim
```
Outputs will be generated in the `build/` directory.

For more detailed instructions and programming the FPGA, refer to the `Makefile` and `docs/` directory.

Programming an Artix-7 FPGA can be done with:

```bash
> make build
> make check_connectivity
> make program
> make write_bitstream
```

## Project Structure
```
root
 ├── build/                 # Build and simulation outputs
 ├── sources/
 │   ├── interfaces/        # SystemVerilog interfaces for clean module boundaries
 │   ├── rtl/               # Synthesizable RTL modules (assertion-free)
 │   ├── packages/          # Shared types, parameters, and constants
 │   ├── test/              
 │       ├── assertions/    # Simulation-only assertion modules
 │       ├── bind/          # Simulation-only bind statements
 │       ...        
 │       └── tb_fifo.sv     # Directed testbench(s)
 ├── docs/                  # Architecture, design, and module documentation
 ├── scripts/               # Synthesis, simulation, and programming scripts
 └── README.md              # You are here!
```

**Design Principles:**
- One module per file for maintainability and version control
- Interfaces for clean module boundaries and reduced port clutter
- Packages for shared types to ensure consistency
- Comprehensive inline documentation
- Assertion-based verification at every level

## Project Status / Roadmap

Completed:
- ✅ ISA design
- ✅ FIFO Verification

Current focus:
- Core microcoded execution + instruction commit semantics
- Assertion-based verification of control/commit + precise trap behavior
- Tooling: minimal assembler (labels + encoding) and ISA reference model for testbenches

Planned extensions:
- Tooling: macro/pseudo-instruction expansion, disassembler, and debug trace format
- Expanded instruction set
- Constrained-random instruction generation + self-checking scoreboards
- SystemVerilog functional coverage
- Optional memory wait-state modeling

## Verification Showcase: FIFO (Warm-up Component)

Before progressing to the CPU core, this repo includes a synchronous FIFO used to establish project “house style” for
SystemVerilog + Verilator-compatible assertion-based verification:

- Synthesizable RTL is kept assertion-free (`sources/rtl/fifo.sv`)
- Protocol and functional invariants are encoded in a single, unified assertions module (`sources/test/assertions/fifo_assertions.sv`)
- Assertions are attached using `bind` statements compiled only in simulation (`sources/test/bind/bind_fifo.sv`)
- Verilator constraints are respected (i.e. no `##N` SVA delays)

The FIFO checker includes:
- Control/status X-checks
- Full/empty mutual exclusion and occupancy consistency (via a reference counter)
- Ordering check using a simulation-only SV queue and an explicit data sampling point (negedge)

## License
This project is licensed under the GNU Affero General Public License v3.0. If you distribute or deploy a modified version of this software, you must make the corresponding source code available under the same license.

See [LICENSE](LICENSE) for details.

---

> μISA-16 -- Microcoded 16-bit CPU with Assertion-Based Verification
>
> Copyright (C) 2026  Noah Sedlik
>
> This program is free software: you can redistribute it and/or modify it under the terms of the GNU Affero General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.
>
> This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Affero General Public License for more details.
>
> You should have received a copy of the GNU Affero General Public License along with this program.  If not, see <https://www.gnu.org/licenses/>.
