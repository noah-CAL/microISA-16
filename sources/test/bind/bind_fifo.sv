//==============================================================================
// SPDX-License-Identifier: AGPL-3.0-or-later
// Copyright (C) 2026 Noah Sedlik
//
// Description: Bind file attaching fifo_assertions to fifo instances.
//
// Notes:
// - `.bus(bus)` refers to the fifo instance port named `bus`.
// - Compiled for simulation only.
//==============================================================================
bind fifo fifo_assertions u_fifo_assertions (.bus(bus));
