class apb_driver extends uvm_driver #(apb_transaction);
    
    `uvm_component_utils(apb_driver)
    
    virtual apb_if vif;
    
    function new(string name = "apb_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual apb_if)::get(this, "", "vif", vif))
            `uvm_fatal(get_type_name(), "Virtual interface not found!")
    endfunction
    
    task run_phase(uvm_phase phase);
        // Initialize signals
        vif.APB_write_paddr = 0;
        vif.APB_read_paddr = 0;
        vif.WRITE_READ = 0;
        vif.APB_write_data = 0;
        vif.transfer = 0;
        vif.Prdata_in = 0;
        vif.Pslverr = 0;
        vif.Pready = 0;
        
        forever begin
            seq_item_port.get_next_item(req);
            drive_transaction(req);
            seq_item_port.item_done();
        end
    endtask
    
    task drive_transaction(apb_transaction trans);
        // Drive master inputs
        @(posedge vif.Pclk);
        vif.APB_write_paddr <= trans.write_paddr;
        vif.APB_read_paddr  <= trans.read_paddr;
        vif.WRITE_READ      <= trans.write_read;
        vif.APB_write_data  <= trans.write_data;
        vif.transfer        <= trans.transfer;
        
        // Wait for SETUP state
        @(posedge vif.Pclk);
        wait(vif.Psel == 1 && vif.Penable == 0);
        
        // Wait for ACCESS state
        @(posedge vif.Pclk);
        wait(vif.Penable == 1);
        
        // Simulate slave response with delay
        fork
            drive_slave_response(trans);
        join_none
        
        // Wait for Pready
        wait(vif.Pready == 1);
        @(posedge vif.Pclk);
        
        // De-assert transfer
        vif.transfer <= 1'b0;
        
        // Add idle cycle
        @(posedge vif.Pclk);
        
    endtask
    
    task drive_slave_response(apb_transaction trans);
        int delay_count = 0;
        
        // Insert wait states
        repeat(trans.pready_delay) begin
            @(posedge vif.Pclk);
            vif.Pready <= 1'b0;
        end
        
        // Drive response
        vif.Pready <= 1'b1;
        vif.Pslverr <= trans.slverr;
        
        if(!trans.write_read) begin // Read operation
            vif.Prdata_in <= trans.read_data;
        end
        
        @(posedge vif.Pclk);
        vif.Pready <= 1'b0;
        vif.Pslverr <= 1'b0;
        
    endtask
    
endclass
