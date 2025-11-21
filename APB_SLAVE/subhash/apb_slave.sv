`define ADDR_WIDTH 32
`define DATA_WIDTH 8
`define MEM_DEPTH 256      

module apb_slave(
    input  wire                     PCLK,
    input  wire                     PRESETn,
    input  wire [`ADDR_WIDTH-1:0]   PADDR,
    input  wire                     PENABLE,
    input  wire                     PSELx,
    input  wire                     PWRITE,
    input  wire [`DATA_WIDTH-1:0]   PWDATA,
    output reg  [`DATA_WIDTH-1:0]   PRDATA,
    output reg                      PREADY,
    output reg                      PSLVERR
);


    reg [`DATA_WIDTH-1:0] mem [0:`MEM_DEPTH-1];

    integer i;

 
    always @(posedge PCLK or negedge PRESETn) begin
        if(!PRESETn) begin
            PREADY  <= 1'b0;
            PSLVERR <= 1'b0;
            PRDATA  <= '0;

            for(i=0; i<`MEM_DEPTH; i=i+1)
                mem[i] <= '0;
        end 

        else begin
            // default values
            PREADY  <= 1'b0;
            PSLVERR <= 1'b0;

            // ACCESS phase (PSEL=1, PENABLE=1)
            if(PSELx && PENABLE) begin
                PREADY <= 1'b1;      

                if(PADDR >= `MEM_DEPTH) begin
                    PSLVERR <= 1'b1;
                end
                else begin
                    if(PWRITE) begin
                        mem[PADDR] <= PWDATA;       // WRITE
                    end
                    else begin
                        PRDATA <= mem[PADDR];       // READ
                    end
                end
            end

            // SETUP phase (PSEL=1, PENABLE=0)
            else if(PSELx && !PENABLE) begin
                // Setup phase is idle; no action needed
                PSLVERR <= 1'b0;
                PREADY  <= 1'b0;
            end

            // Idle or protocol error conditions
            else begin 
                // Protocol Error: PENABLE=1 without PSELx
                if(PENABLE && !PSELx) begin
                    PSLVERR <= 1'b1;
                    PREADY  <= 1'b1;
                end
            end
        end
    end

endmodule
















