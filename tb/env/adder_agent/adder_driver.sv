class adder_driver extends uvm_driver #(adder_txn);

  `uvm_component_utils(adder_driver)

  virtual adder_if vif; // full interface

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db #(virtual adder_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", $sformatf("Virtual interface must be set for: %s", get_full_name()))
  endfunction

  task run_phase(uvm_phase phase);
    adder_txn tr;
    forever begin
      seq_item_port.get_next_item(tr);

      // Access driver modport
      vif.drv_mp.valid_in <= 0;
      @(posedge vif.drv_mp.clk);
      vif.drv_mp.valid_in <= tr.valid_in;
      vif.drv_mp.a <= tr.a;
      vif.drv_mp.b <= tr.b;
      vif.drv_mp.cin <= (tr.carry_in_en) ? tr.cin : 1'b0;

      if (tr.valid_in) @(posedge vif.drv_mp.clk);
      vif.drv_mp.valid_in <= 0;

      seq_item_port.item_done();
    end
  endtask

endclass
