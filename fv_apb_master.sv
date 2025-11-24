module apb_master_assertions
    import apb_pkg::*
(
    input logic Pclk,
    input logic Presetn,
    input logic [`ADDR_WIDTH-1:0] APB_write_paddr,
    input logic [`ADDR_WIDTH-1:0] APB_read_paddr,
    input logic WRITE_READ,
    input logic [`DATA_WIDTH-1:0] APB_write_data,
    input logic transfer,
    input logic [`DATA_WIDTH-1:0] Prdata_in,
    input logic Pslverr,
    input logic Pready,
    input logic [`DATA_WIDTH-1:0] Prdata_out,
    input logic slverr_out,
    input logic [`ADDR_WIDTH-1:0] Paddr,
    input logic [`DATA_WIDTH-1:0] Pwdata,
    input logic Pwrite,
    input logic Psel,
    input logic Penable,
    input logic [1:0] current_state,
    input logic [1:0] next_state
);

    // State parameters
    localparam [1:0] IDLE   = 2'b00;
    localparam [1:0] SETUP  = 2'b01;
    localparam [1:0] ACCESS = 2'b10;

    // ============================================================================
    // Reset Assertions
    // ============================================================================
    
    // Assert that all outputs are reset properly
    property reset_outputs;
        @(posedge Pclk) !Presetn |-> (Penable == 0 && Psel == 0 && 
                                       Paddr == 0 && Pwrite == 0 && 
                                       Pwdata == 0 && Prdata_out == 0 && 
                                       slverr_out == 0);
    endproperty
    assert_reset_outputs: assert property(reset_outputs)
        else $error("Reset assertion failed: Outputs not reset properly");

    // Assert reset drives state to IDLE
    property reset_state;
        @(posedge Pclk) !Presetn |=> (current_state == IDLE);
    endproperty
    assert_reset_state: assert property(reset_state)
        else $error("Reset assertion failed: State not IDLE after reset");

    // ============================================================================
    // State Transition Assertions
    // ============================================================================
    
    // IDLE to SETUP transition when transfer is asserted
    property idle_to_setup;
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == IDLE && transfer) |=> (current_state == SETUP);
    endproperty
    assert_idle_to_setup: assert property(idle_to_setup)
        else $error("State transition failed: IDLE->SETUP with transfer");

    // IDLE remains in IDLE when no transfer
    property idle_to_idle;
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == IDLE && !transfer) |=> (current_state == IDLE);
    endproperty
    assert_idle_to_idle: assert property(idle_to_idle)
        else $error("State transition failed: IDLE should remain in IDLE");

    // SETUP always transitions to ACCESS
    property setup_to_access;
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == SETUP) |=> (current_state == ACCESS);
    endproperty
    assert_setup_to_access: assert property(setup_to_access)
        else $error("State transition failed: SETUP->ACCESS");

    // ACCESS to IDLE on error
    property access_to_idle_on_error;
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == ACCESS && Pslverr) |=> (current_state == IDLE);
    endproperty
    assert_access_to_idle_error: assert property(access_to_idle_on_error)
        else $error("State transition failed: ACCESS->IDLE on error");

    // ACCESS to SETUP when ready and transfer
    property access_to_setup;
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == ACCESS && !Pslverr && Pready && transfer) |=> 
        (current_state == SETUP);
    endproperty
    assert_access_to_setup: assert property(access_to_setup)
        else $error("State transition failed: ACCESS->SETUP");

    // ACCESS to IDLE when ready and no transfer
    property access_to_idle;
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == ACCESS && !Pslverr && Pready && !transfer) |=> 
        (current_state == IDLE);
    endproperty
    assert_access_to_idle: assert property(access_to_idle)
        else $error("State transition failed: ACCESS->IDLE");

    // ACCESS remains in ACCESS when not ready
    property access_to_access;
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == ACCESS && !Pslverr && !Pready) |=> 
        (current_state == ACCESS);
    endproperty
    assert_access_to_access: assert property(access_to_access)
        else $error("State transition failed: ACCESS should remain in ACCESS");

    // ============================================================================
    // APB Protocol Assertions
    // ============================================================================
    
    // Penable is 0 in IDLE state
    property penable_idle;
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == IDLE) |-> (Penable == 0);
    endproperty
    assert_penable_idle: assert property(penable_idle)
        else $error("Protocol violation: Penable should be 0 in IDLE");

    // Penable is 0 in SETUP state
    property penable_setup;
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == SETUP) |-> (Penable == 0);
    endproperty
    assert_penable_setup: assert property(penable_setup)
        else $error("Protocol violation: Penable should be 0 in SETUP");

    // Penable is 1 in ACCESS state
    property penable_access;
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == ACCESS) |-> (Penable == 1);
    endproperty
    assert_penable_access: assert property(penable_access)
        else $error("Protocol violation: Penable should be 1 in ACCESS");

    // Psel is 0 in IDLE state
    property psel_idle;
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == IDLE) |-> (Psel == 0);
    endproperty
    assert_psel_idle: assert property(psel_idle)
        else $error("Protocol violation: Psel should be 0 in IDLE");

    // Psel is 1 in SETUP and ACCESS states
    property psel_active;
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == SETUP || current_state == ACCESS) |-> (Psel == 1);
    endproperty
    assert_psel_active: assert property(psel_active)
        else $error("Protocol violation: Psel should be 1 in SETUP/ACCESS");

    // ============================================================================
    // Address and Control Signal Assertions
    // ============================================================================
    
    // Address stability during ACCESS phase
    property addr_stable_in_access;
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == SETUP) |=> 
        (current_state == ACCESS) throughout ($stable(Paddr));
    endproperty
    assert_addr_stable: assert property(addr_stable_in_access)
        else $error("Protocol violation: Paddr changed during ACCESS");

    // Pwrite stability during ACCESS phase
    property pwrite_stable_in_access;
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == SETUP) |=> 
        (current_state == ACCESS) throughout ($stable(Pwrite));
    endproperty
    assert_pwrite_stable: assert property(pwrite_stable_in_access)
        else $error("Protocol violation: Pwrite changed during ACCESS");

    // Address matches write address when WRITE_READ is 1
    property addr_write_match;
        @(posedge Pclk) disable iff(!Presetn)
        (next_state == SETUP && WRITE_READ) |=> (Paddr == APB_write_paddr);
    endproperty
    assert_addr_write: assert property(addr_write_match)
        else $error("Address mismatch: Paddr != APB_write_paddr");

    // Address matches read address when WRITE_READ is 0
    property addr_read_match;
        @(posedge Pclk) disable iff(!Presetn)
        (next_state == SETUP && !WRITE_READ) |=> (Paddr == APB_read_paddr);
    endproperty
    assert_addr_read: assert property(addr_read_match)
        else $error("Address mismatch: Paddr != APB_read_paddr");

    // Pwrite matches WRITE_READ in SETUP state
    property pwrite_match;
        @(posedge Pclk) disable iff(!Presetn)
        (next_state == SETUP) |=> (Pwrite == WRITE_READ);
    endproperty
    assert_pwrite: assert property(pwrite_match)
        else $error("Control mismatch: Pwrite != WRITE_READ");

    // ============================================================================
    // Data Assertions
    // ============================================================================
    
    // Write data stability during ACCESS phase
    property wdata_stable_in_access;
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == SETUP && Pwrite) |=> 
        (current_state == ACCESS) throughout ($stable(Pwdata));
    endproperty
    assert_wdata_stable: assert property(wdata_stable_in_access)
        else $error("Protocol violation: Pwdata changed during ACCESS");

    // Write data matches input data
    property wdata_match;
        @(posedge Pclk) disable iff(!Presetn)
        (next_state == SETUP && WRITE_READ) |=> (Pwdata == APB_write_data);
    endproperty
    assert_wdata: assert property(wdata_match)
        else $error("Data mismatch: Pwdata != APB_write_data");

    // Read data captured when Pready and read operation
    property rdata_capture;
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == ACCESS && Pready && !Pwrite) |=> 
        (Prdata_out == $past(Prdata_in));
    endproperty
    assert_rdata_capture: assert property(rdata_capture)
        else $error("Read data not captured properly");

    // Slave error captured when Pready
    property slverr_capture;
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == ACCESS && Pready) |=> 
        (slverr_out == $past(Pslverr));
    endproperty
    assert_slverr: assert property(slverr_capture)
        else $error("Slave error not captured properly");

    // ============================================================================
    // Coverage Properties
    // ============================================================================
    
    // Cover all state transitions
    cover_idle_to_setup: cover property(
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == IDLE && transfer) ##1 (current_state == SETUP)
    );

    cover_setup_to_access: cover property(
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == SETUP) ##1 (current_state == ACCESS)
    );

    cover_access_to_idle: cover property(
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == ACCESS && Pready && !transfer) ##1 (current_state == IDLE)
    );

    cover_back_to_back_transfers: cover property(
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == ACCESS && Pready && transfer) ##1 (current_state == SETUP)
    );

    cover_write_operation: cover property(
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == SETUP && Pwrite) ##1 (current_state == ACCESS)
    );

    cover_read_operation: cover property(
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == SETUP && !Pwrite) ##1 (current_state == ACCESS)
    );

    cover_slave_error: cover property(
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == ACCESS && Pslverr)
    );

    cover_wait_states: cover property(
        @(posedge Pclk) disable iff(!Presetn)
        (current_state == ACCESS && !Pready) [*3:5] ##1 (Pready)
    );

endmodule

// ============================================================================
// Bind Statement
// ============================================================================

bind apb_master apb_master_assertions u_apb_assertions (
    .Pclk(Pclk),
    .Presetn(Presetn),
    .APB_write_paddr(APB_write_paddr),
    .APB_read_paddr(APB_read_paddr),
    .WRITE_READ(WRITE_READ),
    .APB_write_data(APB_write_data),
    .transfer(transfer),
    .Prdata_in(Prdata_in),
    .Pslverr(Pslverr),
    .Pready(Pready),
    .Prdata_out(Prdata_out),
    .slverr_out(slverr_out),
    .Paddr(Paddr),
    .Pwdata(Pwdata),
    .Pwrite(Pwrite),
    .Psel(Psel),
    .Penable(Penable),
    .current_state(current_state),
    .next_state(next_state)
);
