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
  int   queue_count;

  wire push_ok = bus.wr_en && !bus.full;
  wire  pop_ok = bus.rd_en && !bus.empty;

  // --------------------------------------------------------------------------
  // A) SV Queue (golden reference model)
  // --------------------------------------------------------------------------
  always_ff @(posedge bus.clk) begin
    if (!bus.rst_n) begin
      q.delete();
    end else begin
      if (pop_ok) begin
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

  // Data sampling for FIFO-INV-DATA-001
  // Sample on the negedge *preceding* the pop-accepting posedge.
  // This matches the TB drive/sample discipline and avoids full-boundary
  // read/write same-address ambiguity.
  logic [DATA_WIDTH-1:0] rd_data_pre;
  logic [DATA_WIDTH-1:0] exp_head_pre;
  always_ff @(negedge bus.clk) begin
    if (!bus.rst_n) begin
      rd_data_pre   <= '0;
      exp_head_pre  <= '0;
    end else begin
      rd_data_pre  <= bus.rd_data;
      // q is still the "pre-pop" model at this negedge (next posedge will pop)
      exp_head_pre <= (queue_count > 0) ? q[0] : 'd0;
    end
  end


  // --------------------------------------------------------------------------
  // B) Black-box invariants
  // --------------------------------------------------------------------------
  // FIFO-INV-CTRL-001
  property p_no_x_controls;
    @(posedge bus.clk) disable iff (!bus.rst_n)
      !$isunknown(bus.wr_en) &&
      !$isunknown(bus.rd_en) &&
      !$isunknown(bus.full)  &&
      !$isunknown(bus.empty);
  endproperty

  // FIFO-INV-CTRL-002
  property p_wdata_known_when_wr_en;
    @(posedge bus.clk) disable iff (!bus.rst_n)
      bus.wr_en |-> !$isunknown(bus.wr_data);
  endproperty

  // FIFO-INV-CTRL-003
  property p_no_push_when_full;
    @(posedge bus.clk) disable iff (!bus.rst_n)
      !(bus.wr_en && bus.full);
  endproperty

  // FIFO-INV-CTRL-004
  property p_no_pop_when_empty;
    @(posedge bus.clk) disable iff (!bus.rst_n)
      !(bus.rd_en && bus.empty);
  endproperty

  // FIFO-INV-STAT-001
  property p_full_empty_mutual_exclusion;
    @(posedge bus.clk) disable iff (!bus.rst_n)
      !(bus.full && bus.empty);
  endproperty

  // FIFO-INV-STAT-002
  property p_empty_matches_model;
    @(posedge bus.clk) disable iff (!bus.rst_n)
      (bus.empty == (queue_count == 0));
  endproperty

  // FIFO-INV-STAT-003
  property p_full_matches_model;
    @(posedge bus.clk) disable iff (!bus.rst_n)
      (bus.full == (queue_count == FIFO_DEPTH));
  endproperty

  // FIFO-INV-STAT-004
  property p_no_overflow;
    @(posedge bus.clk) disable iff (!bus.rst_n)
    (queue_count <= FIFO_DEPTH);
  endproperty

  // FIFO-INV-STAT-005
  property p_no_underflow;
    @(posedge bus.clk) disable iff (!bus.rst_n)
    (queue_count >= 0);
  endproperty

  // FIFO-INV-RST-001
  property p_reset_release_state;
    @(posedge bus.clk)
      ($rose(bus.rst_n)) |-> (bus.empty && !bus.full && (queue_count == 0));
  endproperty

  // FIFO-INV-DATA-001
  // If a pop is accepted at posedge, the value observed on the immediately
  // preceding negedge must equal the model head.
  //
  // Note: negedge sampling is documented in docs/modules/fifo.md.
  property p_pop_ordering;
    @(posedge bus.clk) disable iff (!bus.rst_n)
      pop_ok |-> (rd_data_pre == exp_head_pre);
  endproperty

  // --------------------------------------------------------------------------
  // C) Assertions
  // --------------------------------------------------------------------------
  a_no_x_controls: assert property (p_no_x_controls)
    else err("FIFO-INV-CTRL-001", "wr_en/rd_en/full/empty is X");

  a_wdata_known: assert property (p_wdata_known_when_wr_en)
    else err("FIFO-INV-CTRL-002", "wr_data is X when wr_en asserted");

  a_no_push_full: assert property (p_no_push_when_full)
    else err("FIFO-INV-CTRL-003", "push attempted while full");

  a_no_pop_empty: assert property (p_no_pop_when_empty)
    else err("FIFO-INV-CTRL-004", "pop attempted while empty");

  a_full_empty_mutex: assert property (p_full_empty_mutual_exclusion)
    else err("FIFO-INV-STAT-001", "full && empty both asserted");

  a_empty_matches: assert property (p_empty_matches_model)
    else err("FIFO-INV-STAT-002", $sformatf("empty flag incorrect (empty=%0b, queue count=%0d)", bus.empty, queue_count));

  a_full_matches: assert property (p_full_matches_model)
    else err("FIFO-INV-STAT-003", $sformatf("full flag incorrect (full=%0b, queue count=%0d)", bus.full, queue_count));

  a_reset_release: assert property (p_reset_release_state)
    else err("FIFO-INV-RST-001", "expected empty=1 full=0 and q empty immediately after reset release");

  a_no_overflow: assert property (p_no_overflow)
    else err("FIFO-INV-STAT-004", $sformatf("queue size of %0d exceeded FIFO depth %0d", queue_count, FIFO_DEPTH));

  a_no_underflow: assert property (p_no_underflow)
    else err("FIFO-INV-STAT-005", $sformatf("queue underflowed to size %0d", queue_count));

  a_pop_ordering: assert property (p_pop_ordering)
    else err("FIFO-INV-DATA-001", $sformatf("data mismatch on pop (exp=0x%0h, got=0x%0h)", exp_head_pre, rd_data_pre));

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
