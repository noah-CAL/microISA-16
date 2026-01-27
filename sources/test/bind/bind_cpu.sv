//==============================================================================
// SPDX-License-Identifier: AGPL-3.0-or-later
// Copyright (C) 2026 Noah Sedlik
//
// Description: Bind file attaching cpu_assertions to cpu instances.
//
// Notes:
// - `.cpu(cpu)` refers to the fifo instance port named `cpu`.
// - Compiled for simulation only.
//==============================================================================
bind cpu cpu_assertions u_cpu_assertions (.cpu(cpu));
