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

## Documentation
- [Instruction Set Architecture](docs/isa.md)
- [Instruction Encoding](docs/encoding.md)
- [Assertions and System Invariants](docs/assertions.md)

## Verification Strategy

Verification is centered around **assertion-based invariants**. These properties define the intended correctness model and will be incrementally encoded as assertions as the RTL and microcode are developed.

Key properties enforced using SystemVerilog Assertions include:
- Architectural PC updates only at instruction commit boundaries
- Exactly one commit per instruction
- Microcode execution always makes forward progress and terminates
- Register file writes occur only at commit
- On traps, no architectural state commits (precise exception guarantee)

Assertions are complemented by testbenches that execute directed and randomized instruction streams and check architectural state at instruction boundaries.

## How to Run

### Requirements

- Xilinx Vivado (used for RTL synthesis and preprocessing)
- Verilator (used for simulation and assertion checking)
- GNU Make
- C++ compiler (for Verilator harness)

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
 ├── docs        // ISA and Architecture Documentation
 │               // and design notes
 ├── output      // Build outputs
 ├── README.md   // You are here!
 ├── scripts     // Synthesis, simulation, and programming scripts
 ├── test        // Testbenches, assertions, and verification code
 └── sources     // RTL source code
```

## Project Status / Roadmap

Completed:
- ✅ ISA design

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
