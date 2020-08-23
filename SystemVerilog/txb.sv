package txb_defs;

typedef enum logic [1:0] {
    TXB_STATUS_FREE, // ready to be used, can buffer a TX
    TXB_STATUS_CORE2TXB, // got a TX from core, access mem now
    TXB_STATUS_TXB2CORE // got data from mem, forward TX to core
} status_t;

endpackage : txb_defs

module txb
    import txb_defs::*;
    import ni_defs::*;
    #(parameter TXB_ADDR = -1)
    (input clk, rst,
    output status_t ostatus,
    link.ingress wpath, link.egress rpath);

tx_t tx; // buffered TX
status_t status; // current status of TXB and tx

assign ostatus = status; // report status to pool

assign wpath.tgt_rdy = 1; // we are ready to either accept input from core or from mem
assign rpath.src_rdy = status != TXB_STATUS_FREE; // we have a TX to send

assign rpath.tx = tx; // output buffered TX

always_ff @(posedge clk) begin
    if (rst) begin
        status <= TXB_STATUS_FREE;
        tx <= 'x;
    end else begin
        if (status == TXB_STATUS_FREE && wpath.src_rdy) begin // can buffer a TX from core
            status <= TXB_STATUS_CORE2TXB;
            tx <= wpath.tx;
        end else if (status == TXB_STATUS_CORE2TXB && rpath.tgt_rdy && tx.kind == TX_WR) begin
            // can output to mem
            status <= TXB_STATUS_FREE;
        end else if (status == TXB_STATUS_CORE2TXB && wpath.src_rdy && rpath.tgt_rdy && tx.kind == TX_RD) begin
            // can output and receive from mem
            status <= TXB_STATUS_TXB2CORE;
            tx.data <= wpath.tx.data; // only care about data output from mem
        end else if (status == TXB_STATUS_TXB2CORE && rpath.tgt_rdy) begin
            // return read TX to core
            status <= TXB_STATUS_FREE;
        end
    end
end

// No need to check for core address integrity for individual components here:
// if these two properties are covered successfully, then we know packets are forwarded,
// so the integrity checks in those components should detect it.
c_status_core2txb: cover property (@(posedge clk) disable iff (rst)
    status == TXB_STATUS_CORE2TXB && rpath.tgt_rdy && wpath.src_rdy);
c_status_txb2core: cover property (@(posedge clk) disable iff (rst)
    tx.kind == TX_RD && status == TXB_STATUS_TXB2CORE && rpath.tgt_rdy);

// Deadlock freedom at TXB level
a_ev_free: assert property (@(posedge clk) disable iff (rst)
    status != TXB_STATUS_FREE |-> s_eventually status == TXB_STATUS_FREE);
endmodule
