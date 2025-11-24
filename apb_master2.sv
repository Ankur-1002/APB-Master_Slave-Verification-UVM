module apb_master 
	import apb_pkg::*;
(
    // Global Signals
    input logic Pclk,
    input logic Presetn,
    
    // Input from Previous System
    input logic [`ADDR_WIDTH-1:0] APB_write_paddr,
    input logic [`ADDR_WIDTH-1:0] APB_read_paddr,
    input logic WRITE_READ,
    input logic [`DATA_WIDTH-1:0] APB_write_data,
    input logic transfer,
    
    // Input from Slave
    input logic [`DATA_WIDTH-1:0] Prdata_in,
    input logic Pslverr,
    input logic Pready,
    
    // Output to Previous System
    output logic [`DATA_WIDTH-1:0] Prdata_out,
    output logic slverr_out,
    
    // Output to Slave
    output logic [`ADDR_WIDTH-1:0] Paddr,
    output logic [`DATA_WIDTH-1:0] Pwdata,
    output logic Pwrite,
    output logic Psel,
    output logic Penable
);

    logic [2:0] next_state, current_state;
    
     //Declaration of States (One-Hot Encoding)
     localparam [1:0] IDLE   = 2'b00;
     localparam [1:0] SETUP  = 2'b01;
     localparam [1:0] ACCESS = 2'b10;

    // Next State Logic
    always_comb begin
        case (current_state)
            IDLE: begin
                if (transfer) begin
                    next_state = SETUP;
                end
                else begin
                    next_state = IDLE;
                end
            end
            SETUP: begin
                next_state = ACCESS;
            end
            ACCESS: begin
                if (Pslverr) begin
                    next_state = IDLE;
                end 
                else begin
                    if (Pready & transfer) begin
                        next_state = SETUP;
                    end 
                    else if (Pready & !transfer) begin
                        next_state = IDLE;
                    end
                    else begin
                        next_state = ACCESS;
                    end
                end
            end
            default: begin
                next_state = IDLE;
            end
        endcase
    end

    // State Memory
    always_ff @(posedge Pclk or negedge Presetn) begin
        if (!Presetn) begin
            current_state <= IDLE;
        end else begin
            current_state <= next_state;
        end
    end

    // Output Logic
    always_ff @(posedge Pclk or negedge Presetn) begin
        if (!Presetn) begin
            Penable    <= 1'b0;
            Paddr      <= {`ADDR_WIDTH{1'b0}}; 
            Pwrite     <= 1'b0;
            Prdata_out <= {`DATA_WIDTH{1'b0}};
            slverr_out <= 1'b0;
            Pwdata     <= {`DATA_WIDTH{1'b0}};
        end
        else if (next_state == SETUP) begin
            Penable <= 1'b0;
            Paddr   <= WRITE_READ ? APB_write_paddr : APB_read_paddr; 
            Pwrite  <= WRITE_READ;
            if (WRITE_READ == 1'b1) begin // WRITE
                Pwdata <= APB_write_data;
            end else if (WRITE_READ == 1'b0) begin // READ 
                // No action needed for read data setup
            end
        end
        else if (next_state == ACCESS) begin
            Penable <= 1'b1;
            if (Pready == 1'b1) begin
                if (WRITE_READ == 1'b0) begin
                    Prdata_out <= Prdata_in;
                end
                slverr_out <= Pslverr;
            end
        end
        else begin
            Penable <= 1'b0;
        end
    end

    // Psel Logic
    always_ff @(posedge Pclk or negedge Presetn) begin
        if (!Presetn) begin
            Psel <= 1'b0;
        end
        else if (next_state == IDLE) begin
            Psel <= 1'b0;
        end
        else begin
            Psel <= 1'b1;
        end
    end

endmodule
