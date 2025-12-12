`default_nettype none

module apb_top #(
    parameter ADDR_WIDTH = 8,
    parameter DATA_WIDTH = 16,
    parameter DEPTH = 2**ADDR_WIDTH
)(
    // Clock and Reset
    input  logic                   pclk,
    input  logic                   presetn,

    // Inputs for the master
    input  logic [ADDR_WIDTH-1:0]  write_addr,
    input  logic [ADDR_WIDTH-1:0]  read_addr,
    input  logic [DATA_WIDTH-1:0]  write_data,
    input  logic                   rd_wr,
    input  logic                   transfer,

    // Output from master
    output logic [DATA_WIDTH-1:0]  read_data
);

    // -------------------------------------------------------
    // Internal APB signals (names EXACTLY match master/slave)
    // -------------------------------------------------------
    logic          pselx;
    logic          penable;
    logic          pwrite;
    logic          pready;
    logic          pslverr;

    logic [ADDR_WIDTH-1:0] paddr;
    logic [DATA_WIDTH-1:0] pwdata;
    logic [DATA_WIDTH-1:0] prdata;

    // -------------------------------------------------------
    // Master Instance
    // -------------------------------------------------------
    apb_master master_inst (
        .pclk       (pclk),
        .presetn    (presetn),

        .pready     (pready),
        .pslverr    (pslverr),
        .prdata     (prdata),

        .write_addr (write_addr),
        .read_addr  (read_addr),
        .write_data (write_data),
        .rd_wr      (rd_wr),
        .transfer   (transfer),

        .penable    (penable),
        .pwrite     (pwrite),
        .pselx      (pselx),
        .paddr      (paddr),
        .pwdata     (pwdata),
        .read_data  (read_data)
    );

    // -------------------------------------------------------
    // Slave Instance
    // -------------------------------------------------------
    apb_slave slave_inst (
        .PCLK    (pclk),
        .PRESETn (presetn),

        .PSEL    (pselx),
        .PENABLE (penable),
        .PWRITE  (pwrite),

        // NOTE: Your slave RTL uses 8-bit PADDR/PWDATA.
        // If DATA_WIDTH or ADDR_WIDTH > 8, tools will truncate automatically.
        .PADDR   (paddr[7:0]),
        .PWDATA  (pwdata[7:0]),

        .PRDATA  (prdata),
        .PREADY  (pready),
        .PSLVERR (pslverr)
    );

endmodule

`default_nettype wire
