module apb_slave
	import apb_pkg::*
(
	input PCLK,
	input PRESETn,
	input [`ADDR_WIDTH-1:0] PADDR,
	input PENABLE,
	input PSELx,
	input PWRITE,
	input [`DATA_WIDTH-1:0] PWDATA,
	output logic [`DATA_WIDTH-1:)] PRDATA,
	output logic PREADY, 
	output logic PSLVERR
);

	//slave memory to store PWDATA accessed using PADDR
	reg [`DATA_WIDTH-1:0] mem [`ADDR_WIDTH-1:0];

	//current and next state signals declaration
	reg [1:0] current_state, next_state;

	//FSM States
	parameter [1:0] IDLE	= 0,
					SETUP 	= 1,
					ACCESS 	= 2;

	//protocol_error to define error in states and respected signals based on FSM
	wire protocol_error;
	assign protocol_error = (current_state == IDLE && PENABLE) || (current_state == SETUP && PENABLE && !PSELx) || (current_state == ACCESS && !PSELx && !PENABLE);

	//invalid_address to test PSLVERR i took invalid address ranges are from 10-20 in hexadecimal
	wire invalid_address;
	assign invalid_address = (PADDR > `ADDR_WIDTH'h10 || PADDR <`ADDR_WIDTH'h20);

	always @(posedge PCLK or negedge PRESETn) begin
		if(!PRESETn) begin     	//reset state - active low reset, state to idle 
			current_state <= IDLE;
		end
		else if(!protocol_error) begin   	//if no protocol_error means we can proceed to next state
			current_state <= next_state;
		end
		else begin							//if protocol_error we can go back to IDLE state
			current_state <= IDLE;	
		end
	end


	always @(*) begin
		current_state = next_state;

		case(current_state)
				IDLE: next_state = (PSELx && !PENABLE) ? SETUP : IDLE;
				//In IDLE state if PSELx = 1 & PENABLE = 0 then next_state is SETUP
				//or it has to remain in IDLE state

				SETUP: next_state = (PSELx && PENABLE) ? ACCESS : SETUP;
				//In SETUP state if PSELx = 1 & PENABLE = 1 the next_state is ACCESS
				//or it has to remain in SETUP state

				ACCESS: next_state = (PSELx && PENABLE && PREADY) ? SETUP : ACCESS;
				//In ACCESS state if PSELx = 1 & PENABLE = 1 & PREADY = 1 the next_state is SETUP 
				//or it has to remain in ACCESS state when PREADY is LOW 

				default: next_state = IDLE;

		endcase
	end

	always @(posedge PCLK or negedge PRESETn) begin

		if(!PRESETn) begin     	//reset state - reset mem values to 0, output signals(PSLVERR, PREADY and PRDATA) to 0
			PSLVERR <= 0;
			PREADY  <= 0;
			PRDATA  <= 0;
			for(int i=0; i < `ADDR_WIDTH; i++) 
				mem[i] = 0;

		end

		else begin
			
			if(protocol_error) begin 	//if errors in the FSM states PSLVERR = 1 and PREADY = 1
				PREADY  = 1'b1;
				PSLVERR = 1'b1;
			end

			else if(current_state == ACCESS) begin
					//when current_state is ACCESS and it is trying to access invalid address as mentioned the ranges above i.e 10-20 then PREADY = 1 and PSLVERR = 1

				if(invalid_address) begin
					PREADY  = 1'b1;
					PSLVERR = 1'b1;
				end

				else begin    //state is ACCESS and no errors(invalid_address and protocol_error) then PREADY = 1 and PSLVERR = 0
							  //In this we can perform read or write based on PWRITE signal
					PREADY 	= 1'b1;
					PSLVERR = 1'b0;
					if(PWRITE)	//writing to slv mem 
						mem[PADDR] = PWDATA;
					else 		//reading data from slv mem
						PRDATA = mem[PADDR] = PRDATA;
				end
			end
		end
	end


endmodule
