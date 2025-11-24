class apb_master_config extends uvm_object;
    `uvm_object_utils(apb_master)

    virtual apb_if m_vif;
    uvm_active_passive_enum is_active = UVM_ACTIVE;

function new(string name = "apb_master_config");
    super.new(name);
endfunction

endclass
