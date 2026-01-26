# Synchronous FIFO Module `sources/rtl/fifo.sv`

> SPDX-License-Identifier: AGPL-3.0-or-later
>
> Copyright (C) 2026 Noah Sedlik

## FIFO Protocol and Sampling Semantics (Warm-up Component)

The FIFO is a synchronous single-clock FIFO with combinational status and read data.

### Rules
- A write is accepted on a rising edge when `wr_en && !full`.
- A read is accepted on a rising edge when `rd_en && !empty`.
- `wr_en` must only be asserted when `full==0`.
- `rd_en` must only be asserted when `empty==0`.
- `rd_data` is invalid when `empty==1`.
- A read is only considered successful (a "pop") when `rd_en && !empty` at the rising edge.

### Show-ahead read data
`rd_data` is combinational and reflects the current head element (`mem[r_idx]`). When `empty==0`, `rd_data` is valid even if `rd_en==0`. When `empty==1`, `rd_data` is not semantically meaningful and must not be relied upon.

### Sampling point
To avoid tool-dependent ordering around rising edges, the FIFO ordering property samples `rd_data` on the falling edge (`negedge clk`). If a pop was accepted on the preceding rising edge, then the sampled data matches the model’s expected head element.

This is intentional and treated as part of the verification contract for the FIFO.

### Reset behavior
On reset deassertion (`rst_n` rising), the FIFO is empty (`empty==1`), not full (`full==0`), and internal pointers are reset.

