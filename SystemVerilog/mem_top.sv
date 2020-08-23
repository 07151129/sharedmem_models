package mem_top_cfg;
parameter NCORES = 2; // cores
parameter NMEMS = 2; // memories
parameter NTXBS = 2; // transaction buffers
parameter MEM_RSP_DELAY = 2; // max. number of cycles it takes to respond; 0 for immediate
parameter CORE_STALL_RD = 1; // should core stall for read TX?
parameter TX_ACQ_REL_SUPPORT = 1; // support acquire/release sync
endpackage : mem_top_cfg

module mem_top
    import mem_top_cfg::*;
    (input clk, rst);

link cores2wpath[0:NCORES-1] ();
link mems2wpath[0:NMEMS-1] ();

link rpath2mems[0:NMEMS-1] ();
link rpath2cores[0:NCORES-1] ();

// logic cores_stalled[0:NCORES-1];

for (genvar i = 0; i < NCORES; i++) begin : cores
    core#(.CORE_ADDR(i)) core(clk, rst, rpath2cores[i], cores2wpath[i]/*, cores_stalled[i]*/);
end

for (genvar i = 0; i < NMEMS; i++) begin : mems
    mem#(.MEM_ADDR(i)) mem(clk, rst, rpath2mems[i], mems2wpath[i]);
end

txb_pool txb_pool(clk, rst, cores2wpath, mems2wpath, rpath2cores, rpath2mems);

v_cores v_cores(clk, rst, cores2wpath, rpath2cores);

endmodule
