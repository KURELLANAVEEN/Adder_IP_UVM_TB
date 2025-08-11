class adder_scoreboard extends uvm_component;

  `uvm_component_utils(adder_scoreboard)

  // Export to receive transactions from monitor
  uvm_analysis_export#(adder_txn) analysis_export;

  // FIFO to store transactions from monitor
  uvm_tlm_analysis_fifo#(adder_txn) fifo;

  int DATA_WIDTH;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    analysis_export = new("analysis_export", this);
    fifo = new("fifo", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(int)::get(this, "", "DATA_WIDTH", DATA_WIDTH)) begin
      DATA_WIDTH = 32; // fallback default
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    // connect export to FIFO so we can use get()
    analysis_export.connect(fifo.analysis_export);
  endfunction

  task run_phase(uvm_phase phase);
    adder_txn tr;
    forever begin
      fifo.get(tr);
      check_transaction(tr);
    end
  endtask

  function void check_transaction(adder_txn tr);
    bit [1023:0] expected_sum;
    bit expected_cout;
    bit expected_ovf;
    bit signed [1024:0] sum_ext;

    sum_ext = $signed({tr.signed_en ? tr.a[DATA_WIDTH-1] : 1'b0, tr.a}) +
              $signed({tr.signed_en ? tr.b[DATA_WIDTH-1] : 1'b0, tr.b}) +
              (tr.carry_in_en ? tr.cin : 1'b0);

    expected_sum  = sum_ext & ((1 << DATA_WIDTH) - 1);
    expected_cout = (sum_ext >> DATA_WIDTH) & 1;
    expected_ovf  = (tr.signed_en) ?
                    (((tr.a >> (DATA_WIDTH-1)) & 1) == ((tr.b >> (DATA_WIDTH-1)) & 1) &&
                    (((expected_sum >> (DATA_WIDTH-1)) & 1) != ((tr.a >> (DATA_WIDTH-1)) & 1)))
                    : expected_cout;

    if (expected_sum !== tr.sum) begin
      `uvm_error("SCOREBOARD", $sformatf("Sum mismatch: expected %0h, got %0h", expected_sum, tr.sum))
    end

    if (tr.carry_out_en && expected_cout !== tr.cout) begin
      `uvm_error("SCOREBOARD", $sformatf("Carry-out mismatch: expected %0b, got %0b", expected_cout, tr.cout))
    end

    if (expected_ovf !== tr.ovf) begin
      `uvm_error("SCOREBOARD", $sformatf("Overflow mismatch: expected %0b, got %0b", expected_ovf, tr.ovf))
    end
  endfunction

endclass
