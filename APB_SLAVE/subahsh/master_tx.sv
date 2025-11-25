class master_tx extends uvm_sequence_item;
  rand bit  [`ADDR_WIDTH-1:0] PADDR;
  rand bit                    PENABLE;
  rand bit                    PSELx;
  rand bit                    PWRITE;
  rand bit  [`DATA_WIDTH-1:0] PWDATA;
       bit  [`DATA_WIDTH-1:0] PRDATA;
       bit                    PREADY;
       bit                    PSLVERR;

  `uvm_object_utils_begin(master_tx)
    `uvm_field_int(PADDR,   UVM_ALL_ON)
    `uvm_field_int(PENABLE, UVM_ALL_ON)
    `uvm_field_int(PSELx,   UVM_ALL_ON)
    `uvm_field_int(PWRITE,  UVM_ALL_ON)
    `uvm_field_int(PWDATA,  UVM_ALL_ON)
    `uvm_field_int(PRDATA,  UVM_ALL_ON)
    `uvm_field_int(PREADY,  UVM_ALL_ON)
    `uvm_field_int(PSLVERR,  UVM_ALL_ON)
  `uvm_object_utils_end

  function new(string name = "master_tx");
    super.new(name);
  endfunction
endclass

