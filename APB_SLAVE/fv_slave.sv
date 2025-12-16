// =========================================================================
// APB SLAVE FORMAL VERIFICATION ASSERTIONS
// =========================================================================
// This module contains SVA assertions for formal verification of the
// APB slave module following VCF (VC Formal) guidelines
// =========================================================================

module apb_slave_assertions #(
    parameter N = 4  // Must match the DUT parameter
)(
    input PCLK,
    input PRESETn,
    input PSEL,
    input PENABLE,
    input PWRITE,
    input [7:0] PADDR,
    input [7:0] PWDATA,
    input [7:0] PRDATA,
    input PREADY,
    input PSLVERR,
    // Internal signals from DUT (accessed via bind)
    input [2:0] wait_counter,
    input transaction_active
);

    // =====================================================================
    // CLOCK AND RESET ASSERTIONS
    // =====================================================================
    
    // A1: Reset must clear all outputs to known states
    property reset_clears_outputs;
        @(posedge PCLK) !PRESETn |-> (PREADY == 0 && PSLVERR == 0 && PRDATA == 0);
    endproperty
    assert_reset_outputs: assert property(reset_clears_outputs)
        else $error("Reset failed to clear outputs");

    // A2: Internal state cleared on reset
    property reset_clears_internal;
        @(posedge PCLK) !PRESETn |-> (transaction_active == 0 && wait_counter == 0);
    endproperty
    assert_reset_internal: assert property(reset_clears_internal)
        else $error("Reset failed to clear internal state");

    // =====================================================================
    // APB PROTOCOL COMPLIANCE ASSERTIONS
    // =====================================================================
    
    // A3: PREADY must be low during SETUP phase (when PENABLE is low)
    property pready_low_during_setup;
        @(posedge PCLK) disable iff(!PRESETn)
            (PSEL && !PENABLE && transaction_active) |-> (PREADY == 0);
    endproperty
    assert_setup_phase: assert property(pready_low_during_setup)
        else $error("PREADY must be low during SETUP phase");

    // A4: Transaction only starts when both PSEL and PENABLE are high
    property transaction_start_condition;
        @(posedge PCLK) disable iff(!PRESETn)
            (!transaction_active && PSEL && PENABLE) |=> transaction_active;
    endproperty
    assert_transaction_start: assert property(transaction_start_condition)
        else $error("Transaction should start when PSEL && PENABLE");

    // A6: PSEL must remain stable during transaction
    property psel_stable_during_transaction;
        @(posedge PCLK) disable iff(!PRESETn)
            (transaction_active && !PREADY) |=> $stable(PSEL);
    endproperty
    assume_psel_stable: assume property(psel_stable_during_transaction)
        else $error("PSEL changed during active transaction");

    // A7: PADDR must remain stable during transaction
    property paddr_stable_during_transaction;
        @(posedge PCLK) disable iff(!PRESETn)
            (transaction_active && !PREADY) |=> $stable(PADDR);
    endproperty
    assume_paddr_stable: assume property(paddr_stable_during_transaction)
        else $error("PADDR changed during active transaction");

    // A8: PWRITE must remain stable during transaction
    property pwrite_stable_during_transaction;
        @(posedge PCLK) disable iff(!PRESETn)
            (transaction_active && !PREADY) |=> $stable(PWRITE);
    endproperty
    assume_pwrite_stable: assume property(pwrite_stable_during_transaction)
        else $error("PWRITE changed during active transaction");

    // A9: PWDATA must remain stable during write transaction
    property pwdata_stable_during_write;
        @(posedge PCLK) disable iff(!PRESETn)
            (transaction_active && !PREADY && PWRITE) |=> $stable(PWDATA);
    endproperty
    assume_pwdata_stable: assume property(pwdata_stable_during_write)
        else $error("PWDATA changed during active write transaction");

    // =====================================================================
    // WAIT STATE ASSERTIONS
    // =====================================================================
    
    // A10: Wait counter increments correctly until N-1
    property wait_counter_increments;
        @(posedge PCLK) disable iff(!PRESETn)
            (transaction_active && wait_counter < N-1) |=> 
                (wait_counter == $past(wait_counter) + 1);
    endproperty
    assert_wait_increment: assert property(wait_counter_increments)
        else $error("Wait counter did not increment properly");

    // A11: Wait counter resets at transaction start
    property wait_counter_reset_on_start;
        @(posedge PCLK) disable iff(!PRESETn)
            (!$past(transaction_active) && transaction_active) |-> (wait_counter == 0);
    endproperty
    assert_wait_reset: assert property(wait_counter_reset_on_start)
        else $error("Wait counter not reset at transaction start");

    // A12: PREADY asserted exactly after N wait states
    property pready_after_n_waits;
        @(posedge PCLK) disable iff(!PRESETn)
            (transaction_active && wait_counter == N-1) |=> PREADY;
    endproperty
    assert_pready_timing: assert property(pready_after_n_waits)
        else $error("PREADY not asserted after N wait states");

    // A13: PREADY remains low during wait states
    property pready_low_during_waits;
        @(posedge PCLK) disable iff(!PRESETn)
            (transaction_active && wait_counter < N-1) |-> !PREADY;
    endproperty
    assert_pready_during_wait: assert property(pready_low_during_waits)
        else $error("PREADY asserted prematurely during wait states");
/*
    // A14: Transaction ends when PREADY is asserted
    property transaction_ends_with_pready;
        @(posedge PCLK) disable iff(!PRESETn)
            (transaction_active && PREADY) |=> !transaction_active;
    endproperty
    assert_transaction_end: assert property(transaction_ends_with_pready)
        else $error("Transaction did not end when PREADY asserted");
*/
    // =====================================================================
    // ERROR HANDLING ASSERTIONS
    // =====================================================================
    
    // A15: Error asserted for invalid write addresses (0x10, 0x11)
/*
    property error_on_invalid_write_addr;
        @(posedge PCLK) disable iff(!PRESETn)
            (transaction_active && PWRITE && PREADY && 
             (PADDR == 8'h10 || PADDR == 8'h11)) |-> PSLVERR;
    endproperty
    assert_write_error: assert property(error_on_invalid_write_addr)
        else $error("PSLVERR not asserted for invalid write address");

    // A16: No error for valid addresses (0x00-0x07 using lower 3 bits)
    property no_error_on_valid_addr;
        @(posedge PCLK) disable iff(!PRESETn)
            (transaction_active && PREADY && 
             PADDR != 8'h10 && PADDR != 8'h11) |-> !PSLVERR;
    endproperty
    assert_no_error_valid: assert property(no_error_on_valid_addr)
        else $error("PSLVERR incorrectly asserted for valid address");
*/
    // A17: PSLVERR defaults to 0 when no transaction
    property pslverr_default_zero;
        @(posedge PCLK) disable iff(!PRESETn)
            !transaction_active |-> ##1 !PSLVERR;
    endproperty
    assert_pslverr_default: assert property(pslverr_default_zero)
        else $error("PSLVERR not zero when no transaction active");

    // A18: Error should not prevent PREADY assertion
    property error_with_pready;
        @(posedge PCLK) disable iff(!PRESETn)
            (transaction_active && wait_counter == N-1) |=> PREADY;
    endproperty
    assert_error_and_pready: assert property(error_with_pready)
        else $error("Error prevented PREADY assertion");

    // =====================================================================
    // DATA INTEGRITY ASSERTIONS
    // =====================================================================
    
    // A19: PRDATA stable when PREADY is high during read
    property prdata_stable_when_ready;
        @(posedge PCLK) disable iff(!PRESETn)
            (PREADY && !PWRITE && PSEL) |=> PSEL || $stable(PRDATA);
    endproperty
    assert_prdata_stable: assert property(prdata_stable_when_ready)
        else $error("PRDATA changed while PREADY was high");

    // =====================================================================
    // MUTEX AND STATE CONSISTENCY ASSERTIONS
    // =====================================================================
    
    // A20: Transaction cannot restart while already active
    property no_transaction_restart;
        @(posedge PCLK) disable iff(!PRESETn)
            (transaction_active && !PREADY && apb_slave.wait_counter < N-1 ) |=> transaction_active;
    endproperty
    assert_no_restart: assert property(no_transaction_restart)
        else $error("New transaction started before current one completed");

    // A21: PREADY must eventually be asserted (liveness - bounded)
    property pready_eventually_asserted;
        @(posedge PCLK) disable iff(!PRESETn)
            (PSEL && PENABLE) |-> ##[1:N+2] PREADY;
    endproperty
    assert_pready_liveness: assert property(pready_eventually_asserted)
        else $error("PREADY never asserted within expected time");

    // =====================================================================
    // COVER PROPERTIES (for verification completeness)
    // =====================================================================
    
    // C1: Cover successful write transaction
    cover_write_transaction: cover property (
        @(posedge PCLK) disable iff(!PRESETn)
            (PSEL && PENABLE && PWRITE && !PSLVERR) ##[1:N+1] PREADY
    );

    // C2: Cover successful read transaction
    cover_read_transaction: cover property (
        @(posedge PCLK) disable iff(!PRESETn)
            (PSEL && PENABLE && !PWRITE) ##[1:N+1] PREADY
    );

    // C3: Cover error transaction
    cover_error_transaction: cover property (
        @(posedge PCLK) disable iff(!PRESETn)
            (PSEL && PENABLE && PWRITE && (PADDR == 8'h10 || PADDR == 8'h11)) 
            ##[1:N+1] (PREADY && PSLVERR)
    );

    // C4: Cover back-to-back transactions
    cover_back_to_back: cover property (
        @(posedge PCLK) disable iff(!PRESETn)
            (PREADY && PSEL) ##1 (PSEL && !PENABLE) ##1 (PSEL && PENABLE)
    );

    // C5: Cover reset during transaction
    cover_reset_during_transaction: cover property (
        @(posedge PCLK) transaction_active ##1 !PRESETn
    );

endmodule

// =========================================================================
// BIND STATEMENT
// =========================================================================
// This bind statement connects the assertion module to the DUT
// Place this in your testbench or in a separate bind file

bind apb_slave apb_slave_assertions #(
    .N(N)
) apb_assertions_inst (
    .PCLK(PCLK),
    .PRESETn(PRESETn),
    .PSEL(PSEL),
    .PENABLE(PENABLE),
    .PWRITE(PWRITE),
    .PADDR(PADDR),
    .PWDATA(PWDATA),
    .PRDATA(PRDATA),
    .PREADY(PREADY),
    .PSLVERR(PSLVERR),
    // Internal signals for enhanced verification
    .wait_counter(wait_counter),
    .transaction_active(transaction_active)
);
