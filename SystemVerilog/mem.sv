module mem#(parameter MEM_ADDR = -1)(input clk, rst,
    link.ingress rpath, link.egress wpath);

logic [ni_defs::DATA_W-1:0] data;

localparam MEM_RSP_DELAY_W = MEM_RSP_DELAY > 1 ? $clog2(MEM_RSP_DELAY) : 1;
localparam MEM_RSP_DELAY_M = MEM_RSP_DELAY > 0 ? MEM_RSP_DELAY - 1 : 0;

logic [MEM_RSP_DELAY_W-1:0] rsp_delay_cur;

always_ff @(posedge clk) begin
    if (rst) begin
        data <= '0;
        rsp_delay_cur <= '0;
    end else begin
        if (rpath.src_rdy /* && rpath.tgt_rdy */ && rpath.tx.kind == ni_defs::TX_WR) // incoming TX
            data <= rpath.tx.data;

        if (MEM_RSP_DELAY_M > 0 && rpath.src_rdy)
            rsp_delay_cur <= rsp_delay_cur + 1'b1;

        // Non-deterministically respond early
        if (rsp_delay_cur > '0 && 1'bx) begin
            rsp_delay_cur <= MEM_RSP_DELAY_M;
        end

        if (rsp_delay_cur == MEM_RSP_DELAY_M) begin
            rsp_delay_cur <= '0;
        end
    end
end

assign wpath.src_rdy = 1;
assign rpath.tgt_rdy = rsp_delay_cur == MEM_RSP_DELAY_M;

assign wpath.tx.data = data;

a_sane_mem_addr: assert property (@(posedge clk)
    disable iff (rst)
        rpath.src_rdy |-> rpath.tx.mem_addr == MEM_ADDR);

endmodule
