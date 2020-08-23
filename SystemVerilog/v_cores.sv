import txb_defs::*;
import ni_defs::*;
import mem_top_cfg::*;

module v_cores (input clk, rst,
    link cores2wpath[0:mem_top_cfg::NCORES-1],
    link rpath2cores[0:mem_top_cfg::NCORES-1]);

logic wrote_to_val [0:NCORES-1][0:NMEMS-1][0:DATA_MAX]; // did core write val to addr?

for (genvar c = 0; c < NCORES; c++) begin : wrote_to_val_cores
for (genvar a = 0; a < NMEMS; a++) begin : wrote_to_val_addrs
for (genvar v = 0; v <= DATA_MAX; v++) begin : wrote_to_val_vals
always_ff @(posedge clk) begin
    if (rst) begin
        wrote_to_val[c][a][v] = 0;
    end else begin
        if (cores2wpath[c].src_rdy && cores2wpath[c].tgt_rdy &&
            cores2wpath[c].tx.kind == TX_WR && cores2wpath[c].tx.mem_addr == a &&
            cores2wpath[c].tx.data == v)
            wrote_to_val[c][a][v] = 1;
    end
end
end
end
end

// is write of val to addr on core the latest update of addr on that core?
logic [0:NCORES-1][0:NMEMS-1][0:DATA_MAX] last_wr;

`define CHK_WR(c, a, v)\
if (cores2wpath[c].src_rdy && cores2wpath[c].tgt_rdy && \
    cores2wpath[c].tx.kind == TX_WR && cores2wpath[c].tx.mem_addr == a && \
    cores2wpath[c].tx.data == v) begin \
    last_wr[c][a] <= '0; \
    last_wr[c][a][v] <= 1; \
end


always_ff @(posedge clk) begin
if (rst) begin
    last_wr <= '0;
end else begin
    `CHK_WR(0, 0, 0);
    `CHK_WR(0, 0, 1);
    `CHK_WR(0, 0, 2);
    `CHK_WR(0, 0, 3);

    `CHK_WR(0, 1, 0);
    `CHK_WR(0, 1, 1);
    `CHK_WR(0, 1, 2);
    `CHK_WR(0, 1, 3);

    `CHK_WR(1, 0, 0);
    `CHK_WR(1, 0, 1);
    `CHK_WR(1, 0, 2);
    `CHK_WR(1, 0, 3);

    `CHK_WR(1, 1, 0);
    `CHK_WR(1, 1, 1);
    `CHK_WR(1, 1, 2);
    `CHK_WR(1, 1, 3);
end
end

// If last_wr[c][a][v], forall v' != v, !last_wr[c][a][v']
// Ternary here to avoid generating preconditions for the implication
property p_last_wr_sane(c, a, v);
last_wr[c][a][v] implies (
    (v != 0 ? !last_wr[c][a][0] : 1) and
    (v != 1 ? !last_wr[c][a][1] : 1) and
    (v != 2 ? !last_wr[c][a][2] : 1) and
    (v != 3 ? !last_wr[c][a][3] : 1));
endproperty

for (genvar c = 0; c < NCORES; c++) begin : a_last_wr_save_cores
for (genvar a = 0; a < NMEMS; a++) begin : a_last_wr_sane_addrs
for (genvar v = 0; v <= DATA_MAX; v++) begin : a_last_wr_sane_vals
    a_last_wr_sane: assert property (
    @(posedge clk) disable iff (rst) p_last_wr_sane(c, a, v));
end
end
end

property is_tx(tx_t tx, c, m, kind, data, ar);
(tx.core_addr == c && tx.mem_addr == m && tx.kind == kind && tx.data == data && tx.acq_rel == ar);
endproperty

/**
 * If core performs a load of val from addr, then on this core last write to addr was with val, or
 * any other core wrote val to addr or will write val to addr.
 */

// OK to check rpath sr&tr since TX_RD stalls, so <p is maintained
property p_local_consistency(core, addr, val);
(rpath2cores[core].src_rdy and rpath2cores[core].tgt_rdy and
is_tx(rpath2cores[core].tx, core, addr, TX_RD, val, 'x)) implies
(last_wr[core][addr][val] or
(core != 0 and (wrote_to_val[0][addr][val] or s_eventually wrote_to_val[0][addr][val])) or
(core != 1 and (wrote_to_val[1][addr][val] or s_eventually wrote_to_val[1][addr][val]))
);
endproperty

a_lc: assert property (
    @(posedge clk) disable iff (rst)
    p_local_consistency(0, 0, 1));

// for (genvar c = 0; c < NCORES; c++) begin : a_local_consistency_cores
// for (genvar a = 0; a < NMEMS; a++) begin : a_local_consistency_addrs
// for (genvar v = 1; v <= DATA_MAX; v++) begin : a_local_consistency_vals
//     a_lc: assert property (
//     @(posedge clk) disable iff (rst)
//     p_local_consistency(c, a, v));
// end
// end
// end

endmodule
