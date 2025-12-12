`default_nettype none

module apb_top #(
    parameter ADDR_WIDTH = 8,
    parameter DATA_WIDTH = 16,
    parameter DEPTH      = 2**ADDR_WIDTH
)(
    input  logic                   pclk,
    input  logic                   presetn,

    input  logic [ADDR_WIDTH-1:0]  write_addr,
    input  logic [ADDR_WIDTH-1:0]  read_addr,
    input  logic [DATA_WIDTH-1:0]  write_data,
    input  logic                   rd_wr,
    input  logic                   transfer,

    output logic [DATA_WIDTH-1:0]  read_data
);

    // Internal APB signals (exact same naming as master/slave)
    logic                    pselx;
    logic                    penable;
    logic                    pwrite;
    logic                    pready;
    logic                    pslverr;

    logic [ADDR_WIDTH-1:0]   paddr;
    logic [DATA_WIDTH-1:0]   pwdata;
    logic [DATA_WIDTH-1:0]   prdata;

    // ---------------------------
    // APB MASTER INSTANCE
    // ---------------------------
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

    // ---------------------------
    // APB SLAVE INSTANCE
    // ---------------------------
    apb_slave #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .DEPTH      (DEPTH)
    ) slave_inst (
        .PCLK    (pclk),
        .PRESETn (presetn),

        .PSEL    (pselx),
        .PENABLE (penable),
        .PWRITE  (pwrite),

        .PADDR   (paddr),
        .PWDATA  (pwdata),

        .PRDATA  (prdata),
        .PREADY  (pready),
        .PSLVERR (pslverr)
    );

endmodule

`default_nettype wire
