`default_nettype none

module fv_apb_top #(
    parameter ADDR_WIDTH = 8,
    parameter DATA_WIDTH = 16,
    parameter DEPTH      = 2**ADDR_WIDTH
)();

    // Default clocking for assertions
    default clocking @(posedge apb_top.pclk); endclocking
    default disable iff (!apb_top.presetn);

    // ========================================
    // RESET BEHAVIOR CHECKS
    // ========================================
    
    // Check that pselx is low after reset
    property p_reset_pselx;
        !apb_top.presetn |=> !apb_top.pselx;
    endproperty
    a_reset_pselx: assert property(p_reset_pselx);

    // Check that penable is low after reset
    property p_reset_penable;
        !apb_top.presetn |=> !apb_top.penable;
    endproperty
    a_reset_penable: assert property(p_reset_penable);

    // Check that pwrite is low after reset
    property p_reset_pwrite;
        !apb_top.presetn |=> !apb_top.pwrite;
    endproperty
    a_reset_pwrite: assert property(p_reset_pwrite);

    // Check that pready is high after reset
    property p_reset_pready;
        !apb_top.presetn |=> apb_top.pready;
    endproperty
    a_reset_pready: assert property(p_reset_pready);

    // Check that pslverr is low after reset
    property p_reset_pslverr;
        !apb_top.presetn |=> !apb_top.pslverr;
    endproperty
    a_reset_pslverr: assert property(p_reset_pslverr);

    // Check that paddr is zero after reset
    property p_reset_paddr;
        !apb_top.presetn |=> (apb_top.paddr == '0);
    endproperty
    a_reset_paddr: assert property(p_reset_paddr);

    // Check that pwdata is zero after reset
    property p_reset_pwdata;
        !apb_top.presetn |=> (apb_top.pwdata == '0);
    endproperty
    a_reset_pwdata: assert property(p_reset_pwdata);

    // Check that prdata is zero after reset
    property p_reset_prdata;
        !apb_top.presetn |=> (apb_top.prdata == '0);
    endproperty
    a_reset_prdata: assert property(p_reset_prdata);

    // Check that read_data output is zero after reset
    property p_reset_read_data;
        !apb_top.presetn |=> (apb_top.read_data == '0);
    endproperty
    a_reset_read_data: assert property(p_reset_read_data);

endmodule

// Bind statement
bind apb_top fv_apb_top #(
    .ADDR_WIDTH(ADDR_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .DEPTH(DEPTH)
) fv_inst (.*);

