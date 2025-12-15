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



        // NEW APPROACH (Auxiliary Registers)
logic fv_write_valid;
logic [ADDR_WIDTH-1:0] fv_write_addr;
logic [DATA_WIDTH-1:0] fv_write_data;
logic fv_write_pending;

always_ff @(posedge APB_pclk or negedge APB_presetn) begin
    if (!APB_presetn) begin
        fv_write_valid   <= 1'b0;
        fv_write_addr    <= '0;
        fv_write_data    <= '0;
        fv_write_pending <= 1'b0;
    end else begin
        // Capture write transaction in SETUP phase
        if (m_ps == SETUP && m_pwrite && 
            (m_paddr != 8'h10) && (m_paddr != 8'h11)) begin
            fv_write_valid   <= 1'b1;
            fv_write_addr    <= m_paddr;
            fv_write_data    <= m_pwdata;
            fv_write_pending <= 1'b1;
        end
        // Clear when transaction completes
        else if (fv_write_pending && m_ps == ACCESS && m_pready && !m_pslverr) begin
            fv_write_valid   <= 1'b0;
            fv_write_pending <= 1'b0;
        end
    end
end

property p_write_data_integrity;
    fv_write_pending && (m_ps == ACCESS) && m_pready && !m_pslverr
    |->
    (apb_top.slave_inst.mem[fv_write_addr] == fv_write_data);
endproperty



    // ========================================
    // DATA INTEGRITY CHECKS - READ OPERATIONS
    // ========================================
    
    // Auxiliary logic for read transaction tracking
    logic                    fv_read_valid;
    logic [ADDR_WIDTH-1:0]   fv_read_addr;
    logic [DATA_WIDTH-1:0]   fv_expected_rdata;
    logic                    fv_read_pending;
    
    // Track read transaction initiation
    always_ff @(posedge APB_pclk or negedge APB_presetn) begin
        if (!APB_presetn) begin
            fv_read_valid      <= 1'b0;
            fv_read_addr       <= '0;
            fv_expected_rdata  <= '0;
            fv_read_pending    <= 1'b0;
        end else begin
            // Capture read transaction in SETUP phase
            if (m_ps == SETUP && !m_pwrite) begin
                fv_read_valid      <= 1'b1;
                fv_read_addr       <= m_paddr;
                fv_expected_rdata  <= apb_top.slave_inst.mem[m_paddr];
                fv_read_pending    <= 1'b1;
            end
            // Clear when transaction completes
            else if (fv_read_pending && m_ps == ACCESS && m_pready) begin
                fv_read_valid      <= 1'b0;
                fv_read_pending    <= 1'b0;
            end
            // Clear on idle
            else if (m_ps == IDLE) begin
                fv_read_valid      <= 1'b0;
                fv_read_pending    <= 1'b0;
            end
        end
    end
    
    // Read data integrity check - slave must return expected data
    property p_read_data_integrity;
        fv_read_pending && (m_ps == ACCESS) && m_pready
        |->
        (s_prdata == fv_expected_rdata);
    endproperty
    a_read_data_integrity: assert property(p_read_data_integrity);
    
endmodule

// Bind statement
bind apb_top fv_apb_top #(
    .ADDR_WIDTH(ADDR_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .DEPTH(DEPTH)
) fv_inst (.*);

