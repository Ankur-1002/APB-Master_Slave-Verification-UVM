class master_sbd extends uvm_component;
  `uvm_component_utils(master_sbd)

  uvm_analysis_imp#(master_tx, master_sbd) sb_imp;

  // Reference memory
  bit [`DATA_WIDTH-1:0] mem_ref [bit [`ADDR_WIDTH-1:0]];

  // Counters
  int write_count;
  int read_count;
  int read_match_count;
  int read_mismatch_count;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    sb_imp = new("sb_imp", this);

    // Initialize counters
    write_count        = 0;
    read_count         = 0;
    read_match_count   = 0;
    read_mismatch_count = 0;
  endfunction

  // Monitor writes into scoreboard
  virtual function void write(master_tx tx);

    bit [`DATA_WIDTH-1:0] expected;

    if (tx.PWRITE) begin
      // WRITE Transaction
      mem_ref[tx.PADDR] = tx.PWDATA;
      write_count++;

      `uvm_info("SBD",$sformatf("WRITE: ADDR=%0h DATA=%0h | WRITE_COUNT=%0d",tx.PADDR, tx.PWDATA, write_count),UVM_LOW)
    end 
    else begin
      // READ Transaction
      read_count++;


      if (mem_ref.exists(tx.PADDR))
        expected = mem_ref[tx.PADDR];
      else
        expected = '0;

      if (tx.PRDATA !== expected) begin
        read_mismatch_count++;

        `uvm_error("SBD",$sformatf("READ MISMATCH: ADDR=%0h EXP=%0h ACT=%0h | MISMATCH_COUNT=%0d",tx.PADDR, expected, tx.PRDATA, read_mismatch_count))

      end else begin
        read_match_count++;

        `uvm_info("SBD",$sformatf("READ MATCH: ADDR=%0h DATA=%0h | MATCH_COUNT=%0d",tx.PADDR, expected, read_match_count),UVM_LOW)
      end
    end
  endfunction

  // Print summary at end of simulation
  function void report_phase(uvm_phase phase);
    `uvm_info("SBD_SUMMARY",
      $sformatf({
        "\n------ Scoreboard Summary ------\n",
        "Total Writes      : %0d\n",
        "Total Reads       : %0d\n",
        "Read Matches      : %0d\n",
        "Read Mismatches   : %0d\n",
        "--------------------------------\n"
      },
      write_count,
      read_count,
      read_match_count,
      read_mismatch_count),
      UVM_NONE)
  endfunction

endclass

