//==============================================================================
// SPDX-License-Identifier: AGPL-3.0-or-later
// Copyright (C) 2026 Noah Sedlik
//
// Description: Black-box model and golden reference (SV Queue) for 
//              FIFO assertions + scoreboard model
//
// Enforces FIFO correctness without accessing internal implementation by
// using SV's non-synthesizable, simulation-only queue model.
//
// Notes:
//   - Uses SV queue as the golden model (simulation-only).
//   - No ## delays (Verilator-friendly).
//==============================================================================
import fifo_pkg::FIFO_DEPTH;
import fifo_pkg::DATA_WIDTH;
import assert_pkg::err;

module fifo_assertions (fifo_if.fifo bus);
  // Reference model queue (simulation-only)
  logic [DATA_WIDTH-1:0] q[$];
  logic [DATA_WIDTH-1:0] rd_data_sample;
  logic [DATA_WIDTH-1:0] pop_val;
  int   queue_count;

  wire push_ok = bus.wr_en && !bus.full;
  wire  pop_ok = bus.rd_en && !bus.empty;

  // $past() is invalid on first reset
  // so include a guard against it
  logic past_guard;
  always_ff @(posedge bus.clk) begin
    if (!bus.rst_n) 
      past_guard <= 1'b0;
    else
      past_guard <= 1'b1;
  end

  // --------------------------------------------------------------------------
  // A) SV Queue (golden reference model)
  // --------------------------------------------------------------------------
  always_ff @(posedge bus.clk) begin
    if (!bus.rst_n) begin
      q.delete();
      pop_val <= 'd0;
    end else begin
      if (pop_ok) begin
        pop_val <= q[0];
        q.pop_front();
      end
      if (push_ok) begin
        q.push_back(bus.wr_data);
      end
    end
  end

  always_ff @(posedge bus.clk) begin
    if (!bus.rst_n)
      queue_count <= 'd0;
    else begin
      unique case ({push_ok, pop_ok})
        2'b10: queue_count <= queue_count + 1;
        2'b01: queue_count <= queue_count - 1;
      default: queue_count <= queue_count;
      endcase
    end
  end

  // FIFO data sampling point occurs at negedge of the bus clk
  always_ff @(negedge bus.clk) begin
    if (!bus.rst_n)
      rd_data_sample <= '0;
    else
      rd_data_sample <= bus.rd_data;
  end

  // --------------------------------------------------------------------------
  // B) Black-box invariants
  // --------------------------------------------------------------------------
   property p_no_x_controls;
    @(posedge bus.clk) disable iff (!bus.rst_n)
      !$isunknown(bus.wr_en) &&
      !$isunknown(bus.rd_en) &&
      !$isunknown(bus.full)  &&
      !$isunknown(bus.empty);
  endproperty

  property p_wdata_known_when_wr_en;
    @(posedge bus.clk) disable iff (!bus.rst_n)
      bus.wr_en |-> !$isunknown(bus.wr_data);
  endproperty

  property p_no_push_when_full;
    @(posedge bus.clk) disable iff (!bus.rst_n)
      !(bus.wr_en && bus.full);
  endproperty

  property p_no_pop_when_empty;
    @(posedge bus.clk) disable iff (!bus.rst_n)
      !(bus.rd_en && bus.empty);
  endproperty

  property p_full_empty_mutual_exclusion;
    @(posedge bus.clk) disable iff (!bus.rst_n)
      !(bus.full && bus.empty);
  endproperty

  property p_empty_matches_model;
    @(posedge bus.clk) disable iff (!bus.rst_n)
      (bus.empty == (queue_count == 0));
  endproperty

  property p_full_matches_model;
    @(posedge bus.clk) disable iff (!bus.rst_n)
      (bus.full == (queue_count == FIFO_DEPTH));
  endproperty

  property p_reset_release_state;
    @(posedge bus.clk)
      ($rose(bus.rst_n)) |-> (bus.empty && !bus.full && (queue_count == 0));
  endproperty

  property p_no_overflow;
    @(posedge bus.clk) disable iff (!bus.rst_n)
    (queue_count <= FIFO_DEPTH);
  endproperty

  property p_no_underflow;
    @(posedge bus.clk) disable iff (!bus.rst_n)
    (queue_count >= 0);
  endproperty

  property p_pop_ordering;
    @(negedge bus.clk) disable iff (!bus.rst_n)
      (past_guard && $past(pop_ok)) |-> (rd_data_sample == pop_val);
  endproperty

  // --------------------------------------------------------------------------
  // C) Assertions
  // --------------------------------------------------------------------------
  a_no_x_controls: assert property (p_no_x_controls)
    else err("fifo_no_x_control", "wr_en/rd_en/full/empty is X");

  a_wdata_known: assert property (p_wdata_known_when_wr_en)
    else err("fifo_wdata_known_when_wr_en", "wr_data is X when wr_en asserted");

  a_no_push_full: assert property (p_no_push_when_full)
    else err("fifo_no_push_full", "push attempted while full");

  a_no_pop_empty: assert property (p_no_pop_when_empty)
    else err("fifo_no_pop_empty", "pop attempted while empty");

  a_full_empty_mutex: assert property (p_full_empty_mutual_exclusion)
    else err("fifo_full_empty_mutex", "full && empty both asserted");

  a_empty_matches: assert property (p_empty_matches_model)
    else err("fifo_empty_matches", $sformatf("empty flag incorrect (empty=%0b, queue count=%0d)", bus.empty, queue_count));

  a_full_matches: assert property (p_full_matches_model)
    else err("fifo_full_matches", $sformatf("full flag incorrect (full=%0b, queue count=%0d)", bus.full, queue_count));

  a_reset_release: assert property (p_reset_release_state)
    else err("fifo_reset_release_state", "expected empty=1 full=0 and q empty immediately after reset release");

  a_no_overflow: assert property (p_no_overflow)
    else err("fifo_no_overflow", $sformatf("queue size of %0d exceeded FIFO depth %0d", queue_count, FIFO_DEPTH));

  a_no_underflow: assert property (p_no_underflow)
    else err("fifo_no_underflow", $sformatf("queue underflowed to size %0d", queue_count));

  a_pop_ordering: assert property (p_pop_ordering)
    else err("fifo_pop_ordering", $sformatf("data mismatch on pop (exp=0x%0h, got=0x%0h)", pop_val, rd_data_sample));

  c_no_x_controls:    cover property (p_no_x_controls);
  c_wdata_known:      cover property (p_wdata_known_when_wr_en);
  c_no_push_full:     cover property (p_no_push_when_full);
  c_no_pop_empty:     cover property (p_no_pop_when_empty);
  c_full_empty_mutex: cover property (p_full_empty_mutual_exclusion);
  c_empty_matches:    cover property (p_empty_matches_model);
  c_full_matches:     cover property (p_full_matches_model);
  c_reset_release:    cover property (p_reset_release_state);
  c_no_overflow:      cover property (p_no_overflow);
  c_no_underflow:     cover property (p_no_underflow);
  c_pop_ordering:     cover property (p_pop_ordering);

  // --------------------------------------------------------------------------
  // D) Condition Coverages
  // --------------------------------------------------------------------------
  c_push: cover property (@(posedge bus.clk) disable iff (!bus.rst_n) push_ok);
  c_pop:  cover property (@(posedge bus.clk) disable iff (!bus.rst_n) pop_ok);
  c_both: cover property (@(posedge bus.clk) disable iff (!bus.rst_n) (push_ok && pop_ok));
  c_full: cover property (@(posedge bus.clk) disable iff (!bus.rst_n) bus.full);
  c_empty:cover property (@(posedge bus.clk) disable iff (!bus.rst_n) bus.empty);
endmodule
