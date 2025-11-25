class master_drv extends uvm_driver#(master_tx);
  `uvm_component_utils(master_drv)

  virtual master_intf mvif;
  master_tx req;             

  function new(string name = "master_drv", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_config_db#(virtual master_intf)::get(this, "", "MVIF", mvif))
      `uvm_fatal("MASTER_DRIVER","cannot get interface")
  endfunction

  task run_phase(uvm_phase phase);
    wait (top.PRESETn == 1);
    forever begin
      seq_item_port.get_next_item(req);
       //`uvm_info("SLV_DRV","REQ",UVM_NONE);
      drive_tx(req);
       //req.print();
      seq_item_port.item_done();
    end
  endtask

   task drive_tx(master_tx txn);

     // SETUP phase
     @(mvif.mdrv_cb);
     mvif.mdrv_cb.PSELx   <= 1;
     mvif.mdrv_cb.PENABLE <= 0;
     mvif.mdrv_cb.PWRITE  <= txn.PWRITE;
     mvif.mdrv_cb.PADDR   <= txn.PADDR;
     mvif.mdrv_cb.PWDATA  <= txn.PWDATA;

     // ENABLE phase
     @(mvif.mdrv_cb);
     mvif.mdrv_cb.PENABLE <= 1;

     // Wait for slave ready
     @(posedge mvif.PREADY);

     // Return to IDLE
    // @(mvif.mdrv_cb);
    // mvif.mdrv_cb.PSELx   <= 0;
    // mvif.mdrv_cb.PENABLE <= 0;
    // mvif.mdrv_cb.PWRITE  <= 0;
    // mvif.mdrv_cb.PADDR   <= 0;
    // mvif.mdrv_cb.PWDATA  <= 0;
   endtask


endclass : master_drv

