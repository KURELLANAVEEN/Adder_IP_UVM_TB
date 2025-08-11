class adder_agent extends uvm_agent;

  `uvm_component_utils(adder_agent)

  adder_driver driver;
  adder_monitor monitor;
  adder_sequencer sequencer;

  virtual adder_if vif;


  bit is_active;
  bit get_status;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(virtual adder_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal("NOVIF", {"Virtual interface must be set for: ", this.get_full_name()})
    end

    sequencer = adder_sequencer::type_id::create("sequencer", this);
    driver = adder_driver::type_id::create("driver", this);
    monitor = adder_monitor::type_id::create("monitor", this);

    driver.vif  = vif;
    monitor.vif = vif;

    get_status = uvm_config_db#(bit)::get(this, "", "is_active", is_active);
    if (!get_status) begin
      // handle error or default
      is_active = 1;
    end

  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    driver.seq_item_port.connect(sequencer.seq_item_export);
  endfunction

  function void start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);
    if (!is_active)
      `uvm_info("AGENT", $sformatf("%s agent is inactive", get_full_name()), UVM_LOW);
  endfunction

endclass