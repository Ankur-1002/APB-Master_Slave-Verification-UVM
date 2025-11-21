class apb_slave_base_sequence extends uvm_sequence #(apb_slave_txn);

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
class apb_slave_wr_rd_seq extends apb_slave_base_sequence;
    `uvm_object_utils(apb_slave_wr_rd_seq)
    
    rand bit [`ADDR_WIDTH-1:0] addr;
    rand bit [`DATA_WIDTH-1:0] data;
    bit [`DATA_WIDTH-1:0] read_data;
    apb_slave_txn tx1, tx2;		/////////////////
    constraint addr_valid_c {
        addr < `ADDR_WIDTH'h10 || addr > `ADDR_WIDTH'h20;
    }
    
    function new(string name = "apb_slave_wr_rd_seq");
        super.new(name);
    endfunction
    
    virtual task body();
      //  apb_slave_transaction req;
        
        // Write Transaction
        // IDLE
        `uvm_do_with(req, {req.PSELx == 0; req.PENABLE == 0;})
        // SETUP
        `uvm_do_with(req, {
            req.PSELx == 1; req.PENABLE == 0;
            req.PWRITE == 1; req.PADDR == addr; req.PWDATA == data;
        })
			tx1 = new req;
        // ACCESS
        `uvm_do_with(req, {
            req.PSELx == 1; req.PENABLE == 1;
            req.PWRITE == 1; req.PADDR == tx1.addr; req.PWDATA == tx1.data;
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
            req.PWRITE == 0; req.PADDR == tx1.addr;
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
    
endclass : apb_slave_wr_rd_seq

//==============================================================================
// 5. CONTINUOUS READ SEQUENCE
// Reads from multiple addresses one after another
//==============================================================================
class continuous_read_seq extends apb_base_seq;
    `uvm_object_utils(continuous_read_seq)
    
    int num_reads = 10;
    bit [`ADDR_WIDTH-1:0] start_addr = 32'h00;
    bit [`DATA_WIDTH-1:0] read_data[];
    
    function new(string name = "continuous_read_seq");
        super.new(name);
    endfunction
    
    task body();
        apb_slave_txn txn;
        
        read_data = new[num_reads];
        
        `uvm_info(get_type_name(), 
                  $sformatf("Reading %0d locations starting at 0x%0h", num_reads, start_addr), 
                  UVM_LOW)
        
        for (int i = 0; i < num_reads; i++) begin
            txn = apb_slave_txn::type_id::create("txn");
            start_item(txn);
            txn.addr = start_addr + i;
            txn.PWRITE = 0;
            finish_item(txn);
            
			read_data[i] = txn.PRDATA;
            
            `uvm_info(get_type_name(), 
					  $sformatf("  [%0d] Read: addr=0x%0h data=0x%0h", i, txn.PADDR, txn.PRDATA), 
                      UVM_MEDIUM)
        end
        
        `uvm_info(get_type_name(), "Continuous read complete", UVM_LOW)
    endtask
    
endclass


