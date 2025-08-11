package adder_tb_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Include your transaction class
  `include "adder_txn.sv"

  // Include UVM agent components
  `include "adder_driver.sv"
  `include "adder_monitor.sv"
  `include "adder_sequencer.sv"
  `include "adder_agent.sv"

  // Include environment and scoreboard
  `include "adder_scoreboard.sv"
  `include "adder_env.sv"

  // Include sequences
  `include "adder_base_seq.sv"
  `include "adder_seq_lib.sv"

  // Include base test and other tests
  `include "adder_base_test.sv"
  `include "adder_smoke_test.sv"   // Example additional test

endpackage : adder_tb_pkg
