`timescale 1ns/1ps

`define ADDR_WIDTH 32
`define DATA_WIDTH 8
`define MEM_DEPTH  256

module apb_slave_tb;

    reg PCLK;
    reg PRESETn;
    reg PSELx;
    reg PENABLE;
    reg PWRITE;
    reg [`ADDR_WIDTH-1:0] PADDR;
    reg [`DATA_WIDTH-1:0] PWDATA;

    wire [`DATA_WIDTH-1:0] PRDATA;
    wire PREADY;
    wire PSLVERR;

    // DUT instantiation
    apb_slave dut (
        .PCLK(PCLK),
        .PRESETn(PRESETn),
        .PADDR(PADDR),
        .PENABLE(PENABLE),
        .PSELx(PSELx),
        .PWRITE(PWRITE),
        .PWDATA(PWDATA),
        .PRDATA(PRDATA),
        .PREADY(PREADY),
        .PSLVERR(PSLVERR)
    );


    // Clock generation
    initial begin
        PCLK = 0;
        forever #5 PCLK = ~PCLK;
    end

    // Write Task  (setup → access)

    task apb_write(input [31:0] addr, input [7:0] data);
    begin
        @(posedge PCLK);
        PSELx  = 1;
        PWRITE = 1;
        PENABLE = 0;      // setup phase
        PADDR  = addr;
        PWDATA = data;

        @(posedge PCLK);
        PENABLE = 1;      // access phase

        @(posedge PCLK);
        while (!PREADY) @(posedge PCLK);

        @(posedge PCLK);
        PSELx = 0;
        PENABLE = 0;
    end
    endtask

    // Read Task
    task apb_read(input [31:0] addr);
    begin
        @(posedge PCLK);
        PSELx  = 1;
        PWRITE = 0;
        PENABLE = 0;       // setup
        PADDR  = addr;

        @(posedge PCLK);
        PENABLE = 1;       // access

        @(posedge PCLK);
        while (!PREADY) @(posedge PCLK);

        @(posedge PCLK);
        $display("READ @ %0d = %0d (0x%0h)", addr, PRDATA, PRDATA);

        PSELx = 0;
        PENABLE = 0;
    end
    endtask

    // Test Sequence
    initial begin
        $dumpfile("apb_tb.vcd");
        $dumpvars(0, apb_slave_tb);

        // Init defaults
        PSELx = 0;
        PENABLE = 0;
        PWRITE = 0;
        PADDR = 0;
        PWDATA = 0;

        // Apply reset
        PRESETn = 0;
        repeat (3) @(posedge PCLK);
        PRESETn = 1;

        // WRITE operations
        apb_write(10, 8'hAA);
        apb_write(11, 8'h55);
        apb_write(12, 8'hF0);

        // READ operations
        apb_read(10);
        apb_read(11);
        apb_read(12);

        // Invalid address read 
        apb_read(`MEM_DEPTH + 5);

        $display("Simulation Completed.");
        #10 $finish;
    end

endmodule

