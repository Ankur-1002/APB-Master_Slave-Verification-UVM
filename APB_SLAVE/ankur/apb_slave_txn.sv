class apb_slave_txn extends uvm_sequence_item;
  //--------------------------------------------------------------------
  // Data Members
  //--------------------------------------------------------------------
  rand bit [`ADDR_WIDTH-1:0] PADDR;    // Address
  rand bit [`DATA_WIDTH-1:0] PWDATA;   // Write Data
       bit [`DATA_WIDTH-1:0] PRDATA;   // Read Data (from DUT)
       bit PREADY;                     // Ready signal
       bit PSEL;                       // Select signal
       bit PENABLE;                    // Enable signal
       bit PSLVERR;                    // Error response
  rand bit PWRITE;                     // Write control (1=Write, 0=Read)

  //--------------------------------------------------------------------
  // Constructor
  //--------------------------------------------------------------------
  function new(string name = "apb_slave_txn");
    super.new(name);
  endfunction

  //--------------------------------------------------------------------
  // UVM Factory Registration & Field Automation
  //--------------------------------------------------------------------
  `uvm_object_utils_begin(apb_slave_txn)
    `uvm_field_int(PADDR,   UVM_ALL_ON + UVM_DEC)
    `uvm_field_int(PWDATA,  UVM_ALL_ON + UVM_DEC)
    `uvm_field_int(PRDATA,  UVM_ALL_ON + UVM_DEC)
    `uvm_field_int(PSEL,    UVM_ALL_ON + UVM_DEC)
    `uvm_field_int(PENABLE, UVM_ALL_ON + UVM_DEC)
    `uvm_field_int(PSLVERR, UVM_ALL_ON + UVM_DEC)
    `uvm_field_int(PREADY,  UVM_ALL_ON + UVM_DEC)
    `uvm_field_int(PWRITE,  UVM_ALL_ON + UVM_DEC)
  `uvm_object_utils_end
  
  constraint address_range
  {
    soft PADDR inside {[0:16]};
  }  

  constraint PWRITE_logic
  {
    PWRITE dist {1:=70,0:=30};
  }
endclass
