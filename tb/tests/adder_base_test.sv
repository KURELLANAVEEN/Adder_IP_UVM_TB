class adder_base_test extends uvm_test;

  `uvm_component_utils(adder_base_test)
  

  adder_env env;
  int DATA_WIDTH;

  function new(string name = "adder_base_test", uvm_component parent = null);
    super.new(name, parent);
    DATA_WIDTH = 32;
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(int)::get(this, "", "DATA_WIDTH", DATA_WIDTH))
      DATA_WIDTH = 32; // fallback default
    env = adder_env::type_id::create("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    adder_base_seq base_seq;
    phase.raise_objection(this);

    base_seq = adder_base_seq::type_id::create("base_seq");
    base_seq.DATA_WIDTH = DATA_WIDTH;
    base_seq.start(env.agent.sequencer);
    base_seq.join();

    phase.drop_objection(this);
  endtask

endclass
