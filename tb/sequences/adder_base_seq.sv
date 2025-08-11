class adder_base_seq extends uvm_sequence #(adder_txn);

  `uvm_object_utils(adder_base_seq)
  int DATA_WIDTH;

  function new(string name = "adder_base_seq");
    super.new(name);
    DATA_WIDTH = 32;
  endfunction

  task body();
    adder_txn tr;
    tr = adder_txn::type_id::create("tr");
    tr.data_width = DATA_WIDTH;
    
    // Generate constrained random inputs for a, b limited by data_width
    assert(tr.randomize() with {
      a inside {[0:(1 << DATA_WIDTH) - 1]};
      b inside {[0:(1 << DATA_WIDTH) - 1]};
      cin == 0;  // Assuming carry_in disabled here
      valid_in == 1;
    });
    
    start_item(tr);
    finish_item(tr);
  endtask

endclass
