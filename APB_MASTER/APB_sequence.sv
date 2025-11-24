// Base Sequence
class apb_base_sequence extends uvm_sequence #(apb_transaction);
    
    `uvm_object_utils(apb_base_sequence)
    
    function new(string name = "apb_base_sequence");
        super.new(name);
    endfunction
    
endclass

// Single Write Sequence
class apb_single_write_seq extends apb_base_sequence;
    
    `uvm_object_utils(apb_single_write_seq)
    
    function new(string name = "apb_single_write_seq");
        super.new(name);
    endfunction
    
    task body();
        apb_transaction trans;
        trans = apb_transaction::type_id::create("trans");
        
        start_item(trans);
        assert(trans.randomize() with {
            write_read == 1'b1;
            transfer == 1'b1;
            slverr == 1'b0;
            pready_delay == 0;
        });
        finish_item(trans);
        
        `uvm_info(get_type_name(), $sformatf("Write: Addr=0x%0h, Data=0x%0h", 
                  trans.write_paddr, trans.write_data), UVM_LOW)
    endtask
    
endclass

// Single Read Sequence
class apb_single_read_seq extends apb_base_sequence;
    
    `uvm_object_utils(apb_single_read_seq)
    
    function new(string name = "apb_single_read_seq");
        super.new(name);
    endfunction
    
    task body();
        apb_transaction trans;
        trans = apb_transaction::type_id::create("trans");
        
        start_item(trans);
        assert(trans.randomize() with {
            write_read == 1'b0;
            transfer == 1'b1;
            slverr == 1'b0;
            pready_delay == 0;
        });
        finish_item(trans);
        
        `uvm_info(get_type_name(), $sformatf("Read: Addr=0x%0h", 
                  trans.read_paddr), UVM_LOW)
    endtask
    
endclass

// Multiple Write Sequence
class apb_multiple_write_seq extends apb_base_sequence;
    
    `uvm_object_utils(apb_multiple_write_seq)
    
    rand int num_writes;
    
    constraint num_writes_c {
        num_writes inside {[5:10]};
    }
    
    function new(string name = "apb_multiple_write_seq");
        super.new(name);
    endfunction
    
    task body();
        apb_transaction trans;
        
        repeat(num_writes) begin
            trans = apb_transaction::type_id::create("trans");
            start_item(trans);
            assert(trans.randomize() with {
                write_read == 1'b1;
                transfer == 1'b1;
                slverr == 1'b0;
            });
            finish_item(trans);
            
            `uvm_info(get_type_name(), $sformatf("Write: Addr=0x%0h, Data=0x%0h", 
                      trans.write_paddr, trans.write_data), UVM_LOW)
        end
    endtask
    
endclass

// Multiple Read Sequence
class apb_multiple_read_seq extends apb_base_sequence;
    
    `uvm_object_utils(apb_multiple_read_seq)
    
    rand int num_reads;
    
    constraint num_reads_c {
        num_reads inside {[5:10]};
    }
    
    function new(string name = "apb_multiple_read_seq");
        super.new(name);
    endfunction
    
    task body();
        apb_transaction trans;
        
        repeat(num_reads) begin
            trans = apb_transaction::type_id::create("trans");
            start_item(trans);
            assert(trans.randomize() with {
                write_read == 1'b0;
                transfer == 1'b1;
                slverr == 1'b0;
            });
            finish_item(trans);
            
            `uvm_info(get_type_name(), $sformatf("Read: Addr=0x%0h", 
                      trans.read_paddr), UVM_LOW)
        end
    endtask
    
endclass

// Random Mixed Operations
class apb_random_seq extends apb_base_sequence;
    
    `uvm_object_utils(apb_random_seq)
    
    rand int num_trans;
    
    constraint num_trans_c {
        num_trans inside {[10:15]};
    }
    
    function new(string name = "apb_random_seq");
        super.new(name);
    endfunction
    
    task body();
        apb_transaction trans;
        
        repeat(num_trans) begin
            trans = apb_transaction::type_id::create("trans");
            start_item(trans);
            assert(trans.randomize() with {
                transfer == 1'b1;
                slverr == 1'b0;
            });
            finish_item(trans);
            
            if(trans.write_read)
                `uvm_info(get_type_name(), $sformatf("Write: Addr=0x%0h, Data=0x%0h", 
                          trans.write_paddr, trans.write_data), UVM_LOW)
            else
                `uvm_info(get_type_name(), $sformatf("Read: Addr=0x%0h", 
                          trans.read_paddr), UVM_LOW)
        end
    endtask
    
endclass
