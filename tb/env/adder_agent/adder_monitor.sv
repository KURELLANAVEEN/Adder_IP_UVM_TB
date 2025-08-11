class adder_monitor extends uvm_monitor;

  `uvm_component_utils(adder_monitor)

  virtual adder_if vif; // full interface
  uvm_analysis_port#(adder_txn) analysis_port;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    analysis_port = new("analysis_port", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db #(virtual adder_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", $sformatf("Virtual interface must be set for: %s", get_full_name()))
  endfunction

  task run_phase(uvm_phase phase);
    adder_txn tr;
    wait (vif.reset == 0);
    forever begin
      @(posedge vif.mon_mp.clk);
      if (vif.mon_mp.valid_out) begin
        #1;
        tr = adder_txn::type_id::create("tr");
        tr.a = vif.mon_mp.a;
        tr.b = vif.mon_mp.b;
        tr.cin = vif.mon_mp.cin;
        tr.sum = vif.mon_mp.sum;
        tr.overflow  = vif.mon_mp.overflow;
        tr.signed_en = 1;
        tr.carry_in_en = 0;
        tr.carry_out_en = 0;
        tr.saturation_en = 0;
        `uvm_info("MONITOR", $sformatf(
                    "Captured: a=%0h b=%0h cin=%0b sum=%0h ovf=%0b",
                    tr.a, tr.b, tr.cin, tr.sum, tr.overflow), UVM_LOW)
        analysis_port.write(tr);
      end
    end
  endtask

endclass
