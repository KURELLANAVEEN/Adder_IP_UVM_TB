// File: adder_smoke_test.sv

class adder_smoke_seq extends uvm_sequence #(adder_txn);

  `uvm_object_utils(adder_smoke_seq)

  int DATA_WIDTH;
  int max_val;

  function new(string name = "adder_smoke_seq");
    super.new(name);
    DATA_WIDTH = 32; // default value, can be overridden externally
  endfunction

  task body();
    adder_txn txn;
    repeat (10) begin
      txn = adder_txn::type_id::create("txn");
      txn.data_width = DATA_WIDTH;
      
      // Random stimulus between 1 and 1000 but limited to max DATA_WIDTH range
      max_val = (1 << DATA_WIDTH) - 1;
      assert(txn.randomize() with {
        a inside {[1:(max_val < 1000 ? max_val : 1000)]};
        b inside {[1:(max_val < 1000 ? max_val : 1000)]};
        cin == 0;
        valid_in == 1;
      });

      start_item(txn);
      finish_item(txn);
      #(10);
    end
  endtask

endclass

class adder_smoke_test extends adder_base_test;

  `uvm_component_utils(adder_smoke_test)

  function new(string name = "adder_smoke_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    adder_smoke_seq smoke_seq;
    phase.raise_objection(this);

    smoke_seq = adder_smoke_seq::type_id::create("smoke_seq");
    smoke_seq.DATA_WIDTH = DATA_WIDTH; // inherited from base_test
    smoke_seq.start(env.agent.sequencer);

    smoke_seq.join();

    phase.drop_objection(this);
  endtask

endclass : adder_smoke_test