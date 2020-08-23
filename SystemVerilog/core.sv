import mem_top_cfg::*;

package ni_defs;

parameter CORE_ADDR_W = $clog2(mem_top_cfg::NCORES);
parameter MEM_ADDR_W = $clog2(mem_top_cfg::NMEMS);
parameter DATA_W = 2;
parameter DATA_MAX = (2**DATA_W)-1;

typedef enum logic {
    TX_WR, // write data from core_addr to mem_addr
    TX_RD // read from mem_addr to core_addr, resulting in data
} tx_kind_t;

// For convenience, we always use fixed size TX structure.
// In order to reduce traffic, it would make sense to omit parts of this structure for traffic
// in some direction.
typedef struct packed {
    tx_kind_t kind;
    logic [CORE_ADDR_W-1:0] core_addr;
    logic [MEM_ADDR_W-1:0] mem_addr;
    logic [DATA_W-1:0] data;
    logic acq_rel;
} tx_t;

// parameter PKT_SZ = $size(tx_t);
endpackage : ni_defs

/* A one-directional link */
interface link;
    logic src_rdy, tgt_rdy;
    ni_defs::tx_t tx;

    modport ingress(input tx, src_rdy, output tgt_rdy);
    modport egress(input tgt_rdy, output src_rdy, tx);
endinterface : link

/**
 * Core produces an arbitrary TX into wpath. It only stalls for TX_RD.
 */
module core
    import ni_defs::*;
    #(parameter CORE_ADDR = -1)
    (input clk, rst,
    link.ingress rpath, link.egress wpath
    /*output stalled */); // set to true after TX_RD submission and until its completion

logic stalled;

assign rpath.tgt_rdy = !CORE_STALL_RD | stalled; // ready to accept TX if we sent something previously
// assign wpath.src_rdy = !CORE_STALL_RD | !stalled; // ready to output TX if we have no TX_RD in flight
assign wpath.src_rdy = CORE_STALL_RD ? !stalled : 'x; // do not output TX if stalled, otherwise non detterministic

always_ff @(posedge clk) begin
    if (rst) begin
        stalled <= 0;
    end else if (CORE_STALL_RD) begin
        // Initiated a TX_RD
        if (!stalled & wpath.tgt_rdy & wpath.tx.kind == TX_RD) begin
                stalled <= 1;
            // Done with a TX_RD
            end else if (stalled & rpath.src_rdy) begin
                stalled <= 0;
            end
        end
end

assign wpath.tx = '{core_addr: CORE_ADDR, acq_rel: TX_ACQ_REL_SUPPORT ? 'x : 0, default:'x}; // don't care about the rest of TX fields

// Check incoming TX address sanity
a_core_sane_addr: assert property (@(posedge clk)
    disable iff (rst)
         rpath.src_rdy & rpath.tgt_rdy |-> rpath.tx.core_addr == CORE_ADDR);

// We only expect to get a TX_RD back
a_core_rd_returned: assert property (@(posedge clk)
    disable iff (rst)
         rpath.src_rdy & rpath.tgt_rdy |-> rpath.tx.kind == TX_RD);

// Deadlock freedom for core
// Without guaranteed request handling from the underlying hierarchy this is unlikely to hold.
// In general, this is because resource arbitration is unfair, so a request may be delayed infinitely
// often. However, some configurations (small memory delay, sufficiently many TXBs, few cores) are
// able to compensate for unfair arbitration.
if (CORE_STALL_RD) begin
    a_core_ev_unstall: assert property (@(posedge clk)
        disable iff (rst)
            stalled |-> s_eventually !stalled);
end

endmodule
