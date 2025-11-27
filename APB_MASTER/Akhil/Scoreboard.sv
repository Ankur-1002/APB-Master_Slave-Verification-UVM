class apb_scoreboard extends uvm_scoreboard;
	`uvm_component_utils(apb_scoreboard)

uvm_tlm_analysis_fifo #(apb_transaction) fifo_apb;
apb_transaction apb_trans;

function new(string name = "apb_scoreboard", uvm_component parent);
	super.new(name, parent);
endfunction

function void build_phase(uvm_phase phase);
	fifo_apb = new("fifo_apb", this);
    foreach (mem[i]) 
      mem[i] = 0;
	super.build_phase(phase);
endfunction

task run_phase(uvm_phase phase);
	fork 
		begin
			forever
				begin
					fifo_apb.get(apb_trans);
					mem_read_write(apb_trans);
					check_data(apb_trans);
				end
		end
	join
endtask

bit [`DATA_WIDTH - 1 : 0] mem[255:0];
bit [`DATA_WIDTH - 1 : 0] pref;
bit pslv_exp;

task mem_read_write(apb_transaction apb_trans);
	begin
		if(apb_trans.write_read == 1)
			begin
				`uvm_info(get_type_name(),"entered into the fifo", UVM_MEDIUM)							
              mem[apb_trans.read_paddr] = apb_trans.write_data;
			end
		else
			begin 
              if(apb_trans.read_paddr <= 255)
					begin
                      pref = mem[apb_trans.read_paddr];
						pslv_exp = 0;
					end
				else
					pslv_exp = 1;
			end
	end
endtask

task check_data(apb_transaction apb_trans);
	begin
		if(apb_trans.write_read == 0)
			begin
				if(pref == apb_trans.read_data)
                  begin
					`uvm_info(get_type_name()," matched the read data ", UVM_MEDIUM)
					$display("PREF = %0d, READ_DATA = %0d", pref, apb_trans.read_data);
                  end
				else
                  begin
					`uvm_info(get_type_name()," mismatched the read data ", UVM_MEDIUM)
					$display("PREF = %0d, READ_DATA = %0d", pref, apb_trans.read_data);
                  end
			end
		if(pslv_exp == apb_trans.slverr)
			begin
				if(apb_trans.slverr == 0)
                  begin
					`uvm_info(get_type_name()," matched the error response and gives the 0", UVM_MEDIUM)
					$display("PSLV_EXP = %0d, SLVERR = %0d", apb_trans.slverr, pslv_exp);
                  end
				else
                  begin
					`uvm_info(get_type_name()," matched the error response and gives the 1", UVM_MEDIUM)
					$display("PSLV_EXP = %0d, SLVERR = %0d", apb_trans.slverr, pslv_exp);
                  end
			end
	end
endtask
endclass


