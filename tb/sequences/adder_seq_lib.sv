class adder_seq_lib;

  static function void register_sequences();
    uvm_registry#(uvm_object_wrapper)::add("adder_base_seq", adder_base_seq::get_type());
    // Add more sequences here later
  endfunction

endclass
