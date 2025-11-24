class apb_monitor extends uvm_monitor;
    
    `uvm_component_utils(apb_monitor)
    
    virtual apb_if vif;
    uvm_analysis_port #(apb_transaction) item_collected_port;
    apb_transaction trans_collected;
    
    function new(string name = "apb_monitor", uvm_component parent = null);
        super.new(name, parent);
        item_collected_port = new("item_collected_port", this);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual apb_if)::get(this, "", "vif", vif))
            `uvm_fatal(get_type_name(), "Virtual interface not found!")
    endfunction
    
    task run_phase(uvm_phase phase);
        forever begin
            collect_transaction();
        end
    endtask
    
    task collect_transaction();
        trans_collected = apb_transaction::type_id::create("trans_collected");
        
        // Wait for transfer to start
        @(posedge vif.Pclk);
        wait(vif.transfer == 1'b1);
        
        // Capture SETUP phase
        wait(vif.Psel == 1'b1 && vif.Penable == 1'b0);
        @(posedge vif.Pclk);
        
        trans_collected.write_paddr = vif.APB_write_paddr;
        trans_collected.read_paddr  = vif.APB_read_paddr;
        trans_collected.write_read  = vif.WRITE_READ;
        trans_collected.write_data  = vif.APB_write_data;
        trans_collected.transfer    = vif.transfer;
        
        // Verify address and control signals
        if(vif.WRITE_READ) begin
            if(vif.Paddr != vif.APB_write_paddr)
                `uvm_error(get_type_name(), "Write address mismatch!")
            if(vif.Pwdata != vif.APB_write_data)
                `uvm_error(get_type_name(), "Write data mismatch!")
        end else begin
            if(vif.Paddr != vif.APB_read_paddr)
                `uvm_error(get_type_name(), "Read address mismatch!")
        end
        
        if(vif.Pwrite != vif.WRITE_READ)
            `uvm_error(get_type_name(), "Pwrite signal mismatch!")
        
        // Wait for ACCESS phase
        wait(vif.Penable == 1'b1);
        
        // Wait for Pready
        while(!vif.Pready) begin
            @(posedge vif.Pclk);
        end
        
        // Capture response
        trans_collected.pready = vif.Pready;
        trans_collected.slverr = vif.Pslverr;
        
        @(posedge vif.Pclk);
        
        if(!vif.WRITE_READ) begin // Read operation
            trans_collected.read_data = vif.Prdata_out;
            `uvm_info(get_type_name(), $sformatf("Read Data: 0x%0h", vif.Prdata_out), UVM_MEDIUM)
        end
        
        // Send to analysis port
        item_collected_port.write(trans_collected);
        
        `uvm_info(get_type_name(), $sformatf("Transaction Monitored:\n%s", 
                  trans_collected.sprint()), UVM_HIGH)
        
    endtask
    
endclass
