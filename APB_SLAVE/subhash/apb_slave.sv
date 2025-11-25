`define ADDR_WIDTH 32
`define DATA_WIDTH 32
`define MEM_DEPTH 1024 

module apb_slave(
    input  wire                     PCLK,
    input  wire                     PRESETn,
    input  wire [`ADDR_WIDTH-1:0]   PADDR,
    input  wire                     PENABLE,
    input  wire                     PSELx,
    input  wire                     PWRITE,
    input  wire [`DATA_WIDTH-1:0]   PWDATA,
    output reg  [`DATA_WIDTH-1:0]   PRDATA,
    output wire                     PREADY,
    output reg                      PSLVERR
);

    // ---------------------------------------------------------
    // Memory
    // ---------------------------------------------------------
    reg [`DATA_WIDTH-1:0] mem [`MEM_DEPTH-1:0];

    // ---------------------------------------------------------
    // PREADY is purely combinational for zero-wait APB slave
    // ---------------------------------------------------------
    assign PREADY = PSELx & PENABLE;

    integer i;

    // ---------------------------------------------------------
    // Write + reset logic (sequential)
    // ---------------------------------------------------------
    always @(posedge PCLK or negedge PRESETn) begin
        if (!PRESETn) begin
            for (i = 0; i < `MEM_DEPTH; i=i+1)
                mem[i] <= 0;
        end 
        else begin
            // Valid write at ACCESS phase
            if (PSELx && PENABLE && PWRITE) begin
                mem[PADDR] <= PWDATA;
            end
        end
    end

    // ---------------------------------------------------------
    // Combinational read (same cycle output)
    // ---------------------------------------------------------
    always @(*) begin
        if (PSELx && PENABLE && !PWRITE)
            PRDATA = mem[PADDR];
        else
            PRDATA = '0;
    end


    // ---------------------------------------------------------
    // Combinational slverr(same cycle output)
    // ---------------------------------------------------------
	always @(*) begin
	    if (!PRESETn)
	        PSLVERR = 0;
	
	    else if (PSELx && PENABLE) begin
	        // ACCESS phase
	        if (PADDR >= `MEM_DEPTH)
	            PSLVERR = 1;        // same cycle error
	        else
	            PSLVERR = 0;
	    end
	
	    else begin
	        PSLVERR = 0;            // default
	    end
	end


endmodule

