import txb_defs::*;
import ni_defs::*;

module txb_pool(input clk, rst,
    link cores2wpath[0:mem_top_cfg::NCORES-1],
    link mems2wpath[0:mem_top_cfg::NMEMS-1],
    link rpath2cores[0:mem_top_cfg::NCORES-1],
    link rpath2mems[0:mem_top_cfg::NMEMS-1]);

link wpath2txbs[0:NTXBS-1] ();
link txbs2rpath[0:NTXBS-1] ();

txb_defs::status_t [NTXBS-1:0] txb_status;

for (genvar i = 0; i < NTXBS; i++) begin : txbs
    txb#(.TXB_ADDR(i)) txb(clk, rst, txb_status[i], wpath2txbs[i], txbs2rpath[i]);
end

// Could use a bit per TXB to indicate it is allocated to some core at this cycle; the
// index is for debugging
logic [CORE_ADDR_W:0][NTXBS-1:0] core_for_txb;

// Cores for which at least one TXB has an acq_rel TX buffered
logic [NCORES-1:0] cores_acq;
logic [NCORES-1:0] cores_rel;

// Unfortunately, the following logic cannot be generated using SV alone, since we need a loop
// in always_comb context

/**
 * Allocate TXBs for incoming core TX
 * Arbitrate memory for TXB-to-mem I/O
 * Arbitrate core for TXB-to-core I/O
 */

// If memory i is addressed by some txb, forward tx from that txb to mem, and from mem to that txb
`define MEM_SRC_SEL(i) \
    if (txb_status[0] == TXB_STATUS_CORE2TXB && txbs2rpath[0].tx.mem_addr == i) begin \
        txbs2rpath[0].tgt_rdy = rpath2mems[i].tgt_rdy; \
        rpath2mems[i].src_rdy = txbs2rpath[0].src_rdy; \
        rpath2mems[i].tx = txbs2rpath[0].tx; \
        wpath2txbs[0].src_rdy = mems2wpath[i].src_rdy; \
        mems2wpath[i].tgt_rdy = wpath2txbs[0].tgt_rdy; \
        wpath2txbs[0].tx = mems2wpath[i].tx; \
    end else if (txb_status[1] == TXB_STATUS_CORE2TXB && txbs2rpath[1].tx.mem_addr == i) begin \
        txbs2rpath[1].tgt_rdy = rpath2mems[i].tgt_rdy; \
        rpath2mems[i].src_rdy = txbs2rpath[1].src_rdy; \
        rpath2mems[i].tx = txbs2rpath[1].tx; \
        wpath2txbs[1].src_rdy = mems2wpath[i].src_rdy; \
        mems2wpath[i].tgt_rdy = wpath2txbs[1].tgt_rdy; \
        wpath2txbs[1].tx = mems2wpath[i].tx; \
    end

// If core i is addressed by some txb, forward tx from that txb to core
`define CORE_SRC_SEL(i) \
    if (txb_status[0] == TXB_STATUS_TXB2CORE && txbs2rpath[0].src_rdy && txbs2rpath[0].tx.core_addr == i) begin \
        txbs2rpath[0].tgt_rdy = rpath2cores[i].tgt_rdy; \
        rpath2cores[i].src_rdy = txbs2rpath[0].src_rdy; \
        rpath2cores[i].tx = txbs2rpath[0].tx; \
    end else if (txb_status[1] == TXB_STATUS_TXB2CORE && txbs2rpath[1].src_rdy && txbs2rpath[1].tx.core_addr == i) begin \
        txbs2rpath[1].tgt_rdy = rpath2cores[i].tgt_rdy; \
        rpath2cores[i].src_rdy = txbs2rpath[1].src_rdy; \
        rpath2cores[i].tx = txbs2rpath[1].tx; \
    end

// If core i is producing a TX, forward it to a free TXB
// NOTE: We need to ensure that the nested if-clauses evaluate true for at most one core.
// Otherwise we may end up choosing the same TXB for two different cores, which results in only
// one TX propagating, and the other falsely reported to the core as propagated.
`define CORE_DST_SEL(i) \
    if (cores2wpath[i].src_rdy) begin \
        if (txb_status[0] == TXB_STATUS_FREE && core_for_txb[0] == '0) begin \
            wpath2txbs[0].src_rdy = cores2wpath[i].src_rdy; \
            cores2wpath[i].tgt_rdy = wpath2txbs[0].tgt_rdy; \
            wpath2txbs[0].tx = cores2wpath[i].tx; \
            core_for_txb[0] = i + 1; \
        end else if (txb_status[1] == TXB_STATUS_FREE && core_for_txb[1] == '0) begin \
            wpath2txbs[1].src_rdy = cores2wpath[i].src_rdy; \
            cores2wpath[i].tgt_rdy = wpath2txbs[1].tgt_rdy; \
            wpath2txbs[1].tx = cores2wpath[i].tx; \
            core_for_txb[1] = i + 1; \
        end \
    end

`define INIT_PATH(i) \
    wpath2txbs[i].src_rdy = 0; \
    txbs2rpath[i].tgt_rdy = 0; \
    rpath2mems[i].src_rdy = 0; \
    rpath2cores[i].src_rdy = 0; \
    cores2wpath[i].tgt_rdy = 0; \
    mems2wpath[i].tgt_rdy = 0; \
    wpath2txbs[i].tx = 'x; \
    rpath2mems[i].tx = 'x; \
    rpath2cores[i].tx = 'x; \
    core_for_txb[i] = '0;

`define CHK_CORE_ACQ_REL(i) \
    cores_acq[i] = \
    (txb_status[0] != TXB_STATUS_FREE && txbs2rpath[0].src_rdy && \
        txbs2rpath[0].tx.core_addr == i && txbs2rpath[0].tx.acq_rel && txbs2rpath[0].tx.kind == TX_RD) || \
    (txb_status[1] != TXB_STATUS_FREE && txbs2rpath[1].src_rdy && \
        txbs2rpath[1].tx.core_addr == i && txbs2rpath[1].tx.acq_rel && txbs2rpath[1].tx.kind == TX_RD); \
    cores_rel[i] = \
    (txb_status[0] != TXB_STATUS_FREE && txbs2rpath[0].src_rdy && \
        txbs2rpath[0].tx.core_addr == i && txbs2rpath[0].tx.acq_rel && txbs2rpath[0].tx.kind == TX_WR) || \
    (txb_status[1] != TXB_STATUS_FREE && txbs2rpath[1].src_rdy && \
        txbs2rpath[1].tx.core_addr == i && txbs2rpath[1].tx.acq_rel && txbs2rpath[1].tx.kind == TX_WR);

always_comb begin
    `INIT_PATH(0)
    `INIT_PATH(1)

    `CHK_CORE_ACQ_REL(0)
    `CHK_CORE_ACQ_REL(1)

    `CORE_DST_SEL(0)
    `MEM_SRC_SEL(0)
    `CORE_SRC_SEL(0)

    `CORE_DST_SEL(1)
    `MEM_SRC_SEL(1)
    `CORE_SRC_SEL(1)
end

// Both buffers may be occupied by a TX from the same core
// We need this for checking properties like p_sync_rel on TXB pool level
property p_all_occupied(core);
    @(posedge clk) disable iff (rst)
    txb_status[0] != TXB_STATUS_FREE && txb_status[1] != TXB_STATUS_FREE &&
    txbs2rpath[0].src_rdy && txbs2rpath[0].tx.core_addr == core &&
    txbs2rpath[1].src_rdy && txbs2rpath[1].tx.core_addr == core;
endproperty

c_both_occupied0: cover property (p_all_occupied('0));
c_both_occupied1: cover property (p_all_occupied(1'b1));

// TXB pool level check of sync correctness
//
// If the TXB pool receives tx_i now from core c this cycle, and tx_j is the next write release
// after tx_i, then no TXB may be allowed to perform memory access for tx_j until tx_i is complete.
//
// In order to identify tx_i, we use check core_addr and mem_addr of an outgoing transaction for
// each TXB.

property is_tx(tx_t tx, c, m, kind, data, ar);
(tx.core_addr == c && tx.mem_addr == m && tx.kind == kind && tx.data == data && tx.acq_rel == ar);
endproperty

// NOTE: This breaks with tx_i == tx_j
property p_sync_rel(c, m_i, m_j, kind_i, val_i, val_j);
// no tx_j in TXB now
((txb_status[0] != TXB_STATUS_FREE implies
    not is_tx(txbs2rpath[0].tx, c, m_j, TX_WR, val_j, 1'b1)) and
(txb_status[1] != TXB_STATUS_FREE implies
    not is_tx(txbs2rpath[1].tx, c, m_j, TX_WR, val_j, 1'b1)) and
// tx_i incoming
cores2wpath[c].src_rdy and cores2wpath[c].tgt_rdy and is_tx(cores2wpath[c].tx, c, m_i, kind_i, val_i, 1'b0) and
// eventually tx_j arrives
s_eventually (cores2wpath[c].src_rdy and cores2wpath[c].tgt_rdy and is_tx(cores2wpath[c].tx, c, m_j, TX_WR, val_j, 1'b1)))
implies
// tx_j does not access its memory
(((rpath2mems[m_j].src_rdy and rpath2mems[m_j].tgt_rdy) implies not is_tx(rpath2mems[m_j].tx, c, m_j, TX_WR, val_j, 1'b1))
    until_with
// until tx_i accesses its memory
((rpath2mems[m_i].src_rdy and rpath2mems[m_i].tgt_rdy) and is_tx(rpath2mems[m_i].tx, c, m_i, kind_i, val_i, 1'b0))
)
;
endproperty

a_sync_rel: assert property (
    @(posedge clk) disable iff (rst)
    p_sync_rel(0, '0, '0, TX_WR, '0, '0)
);

endmodule
