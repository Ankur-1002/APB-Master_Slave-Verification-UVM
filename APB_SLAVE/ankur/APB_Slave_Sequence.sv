class apb_slave_base_sequence extends uvm_sequence #(apb_slave_transaction);

	`uvm_object_utils(apb_slave_base_sequence)

  function new(string name = "apb_slave_sequence");
    super.new(name);
  endfunction

  virtual task body();

	  //create seq_item
	  req = apb_seq_item :: type_id :: create("req");
	  start_item(req);
	  assert(req.randomize());
	  finish_item(req);
  endtask

endclass: apb_sequence



//==============================================================================
//  WRITE-READ-VERIFY SEQUENCE
// Write data, read back, verify
//==============================================================================
class apb_slave_write_read_verify_seq extends apb_slave_base_sequence;
    `uvm_object_utils(apb_slave_write_read_verify_seq)
    
    rand bit [`ADDR_WIDTH-1:0] addr;
    rand bit [`DATA_WIDTH-1:0] data;
    bit [`DATA_WIDTH-1:0] read_data;
    
    constraint addr_valid_c {
        addr < `ADDR_WIDTH'h10 || addr > `ADDR_WIDTH'h20;
    }
    
    function new(string name = "apb_slave_write_read_verify_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        apb_slave_transaction req;
        
        // Write Transaction
        // IDLE
        `uvm_do_with(req, {req.PSELx == 0; req.PENABLE == 0;})
        // SETUP
        `uvm_do_with(req, {
            req.PSELx == 1; req.PENABLE == 0;
            req.PWRITE == 1; req.PADDR == addr; req.PWDATA == data;
        })
        // ACCESS
        `uvm_do_with(req, {
            req.PSELx == 1; req.PENABLE == 1;
            req.PWRITE == 1; req.PADDR == addr; req.PWDATA == data;
        })
        
        // Read Transaction
        // IDLE
        `uvm_do_with(req, {req.PSELx == 0; req.PENABLE == 0;})
        // SETUP
        `uvm_do_with(req, {
            req.PSELx == 1; req.PENABLE == 0;
            req.PWRITE == 0; req.PADDR == addr;
        })
        // ACCESS
        `uvm_do_with(req, {
            req.PSELx == 1; req.PENABLE == 1;
            req.PWRITE == 0; req.PADDR == addr;
        })
        
        read_data = req.PRDATA;
        
        // Verify
        if (read_data == data) begin
            `uvm_info(get_type_name(), 
                      $sformatf("PASS: Write-Read Match at addr=0x%0h data=0x%0h", 
                                addr, data), UVM_LOW)
        end else begin
            `uvm_error(get_type_name(), 
                       $sformatf("FAIL: Mismatch at addr=0x%0h wrote=0x%0h read=0x%0h", 
                                 addr, data, read_data))
        end
    endtask
    
endclass : apb_slave_write_read_verify_seq

