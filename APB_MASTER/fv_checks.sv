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


            // ========================================
    // END-TO-END DATA INTEGRITY (TOP-LEVEL PORTS)
    // ========================================
    
    // Auxiliary logic for tracking complete write-read cycles at top level
    logic                    fv_e2e_write_done;
    logic [ADDR_WIDTH-1:0]   fv_e2e_write_addr;
    logic [DATA_WIDTH-1:0]   fv_e2e_write_data;
    logic                    fv_e2e_read_pending;
    
    // Track completed write transactions from APB top interface
    always_ff @(posedge APB_pclk or negedge APB_presetn) begin
        if (!APB_presetn) begin
            fv_e2e_write_done    <= 1'b0;
            fv_e2e_write_addr    <= '0;
            fv_e2e_write_data    <= '0;
            fv_e2e_read_pending  <= 1'b0;
        end else begin
            // Capture write transaction from top-level ports
            if (m_ps == SETUP && APB_rd_wr && APB_transfer) begin
                fv_e2e_write_addr <= APB_write_addr;
                fv_e2e_write_data <= APB_write_data;
            end
            
            // Mark write as complete when transaction finishes successfully
            if (fv_write_pending && m_ps == ACCESS && m_pready && !m_pslverr) begin
                fv_e2e_write_done <= 1'b1;
            end
            
            // Track if a read is initiated to the same address
            if (fv_e2e_write_done && m_ps == SETUP && !APB_rd_wr && 
                APB_transfer && (APB_read_addr == fv_e2e_write_addr)) begin
                fv_e2e_read_pending <= 1'b1;
            end
            
            // Clear when read completes
            if (fv_e2e_read_pending && m_ps == ACCESS && m_pready) begin
                fv_e2e_write_done   <= 1'b0;
                fv_e2e_read_pending <= 1'b0;
            end
            
            // Clear if write to different address occurs
            if (fv_e2e_write_done && m_ps == SETUP && APB_rd_wr && 
                (APB_write_addr != fv_e2e_write_addr)) begin
                fv_e2e_write_done <= 1'b0;
            end
        end
    end
    
    // ========================================
    // CRITICAL: TOP-LEVEL DATA INTEGRITY ASSERTIONS
    // ========================================
    
    // Property 1: Master write data reaches slave write data bus
    property p_master_write_to_slave;
        (m_ps == SETUP && m_pwrite) 
        |->
        (m_pwdata == APB_write_data);
    endproperty
    a_master_write_to_slave: assert property(p_master_write_to_slave);
    
    // Property 2: Master write address reaches slave address bus
    property p_master_write_addr_to_slave;
        (m_ps == SETUP && m_pwrite)
        |->
        (m_paddr == APB_write_addr);
    endproperty
    a_master_write_addr_to_slave: assert property(p_master_write_addr_to_slave);
    
    // Property 3: Master read address reaches slave address bus
    property p_master_read_addr_to_slave;
        (m_ps == SETUP && !m_pwrite)
        |->
        (m_paddr == APB_read_addr);
    endproperty
    a_master_read_addr_to_slave: assert property(p_master_read_addr_to_slave);
    
    // Property 4: Slave read data reaches master read data output
    property p_slave_read_to_master;
        (m_ps == ACCESS && !m_pwrite && m_pready)
        |=>
        (APB_read_data == $past(s_prdata));
    endproperty
    a_slave_read_to_master: assert property(p_slave_read_to_master);
    
    // Property 5: MAIN END-TO-END CHECK
    // Data written via APB_write_data is read back via APB_read_data
    property p_e2e_write_then_read_data_match;
        fv_e2e_read_pending && (m_ps == ACCESS) && m_pready
        |=>
        (APB_read_data == fv_e2e_write_data);
    endproperty
    a_e2e_write_then_read_data_match: assert property(p_e2e_write_then_read_data_match);
   
endmodule

// Bind statement
bind apb_top fv_apb_top #(
    .ADDR_WIDTH(ADDR_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .DEPTH(DEPTH)
) fv_inst (.*);

