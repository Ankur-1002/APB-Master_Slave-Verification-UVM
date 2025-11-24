class apb_transaction extends uvm_sequence_item;
    
    // Transaction fields
    rand bit [31:0] write_paddr;
    rand bit [31:0] read_paddr;
    rand bit        write_read;  // 1=write, 0=read
    rand bit [31:0] write_data;
    rand bit        transfer;
    
    // Response fields (from slave)
    bit [31:0] read_data;
    bit        slverr;
    bit        pready;
    rand int   pready_delay; // Number of cycles slave takes to respond
    
    // Constraints
    constraint valid_addr_c {
        write_paddr inside {[0:32'hFF]};
        read_paddr inside {[0:32'hFF]};
    }
    
    constraint pready_delay_c {
        pready_delay inside {[0:3]}; // 0 to 3 wait states
    }
    
    constraint transfer_c {
        transfer == 1'b1;
    }
    
    `uvm_object_utils_begin(apb_transaction)
        `uvm_field_int(write_paddr, UVM_ALL_ON)
        `uvm_field_int(read_paddr, UVM_ALL_ON)
        `uvm_field_int(write_read, UVM_ALL_ON)
        `uvm_field_int(write_data, UVM_ALL_ON)
        `uvm_field_int(transfer, UVM_ALL_ON)
        `uvm_field_int(read_data, UVM_ALL_ON)
        `uvm_field_int(slverr, UVM_ALL_ON)
        `uvm_field_int(pready, UVM_ALL_ON)
        `uvm_field_int(pready_delay, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "apb_transaction");
        super.new(name);
    endfunction
    
endclass
