class adder_txn extends uvm_sequence_item;
	`uvm_object_utils(adder_txn)
    // DUT configuration parameters - fixed per test, not randomized
    bit                   signed_en;       // Signed mode enable
    bit                   carry_in_en;     // Carry-in enabled
    bit                   carry_out_en;    // Carry-out enabled
    bit                   saturation_en;   // Saturation mode enabled
    bit                   pipeline_en;     // Pipelining enabled
    int unsigned          data_width;      // Operand width (8 to 1024)

    // Inputs to DUT - randomized for stimulus coverage
    rand logic [1023:0]   a;
    rand logic [1023:0]   b;
    rand logic            cin;

    // Outputs from DUT - for scoreboard comparison & coverage
    logic [1023:0]        sum;
    logic                 cout;
    logic                 ovf;

    // Valid signals for pipelined operation
    bit                   valid_in;
    bit                   valid_out;

    logic [1023:0] mask;

    // Constructor
    function new(string name = "adder_txn");
        super.new(name);
        data_width    = 32;      // Default, can be overridden by TB or sequences
        signed_en     = 1;
        carry_in_en   = 0;
        carry_out_en  = 0;
        saturation_en = 0;
        pipeline_en   = 0;
        valid_in      = 1;
        valid_out     = 1;
    endfunction

    // Constraint to restrict a,b to data_width bits
    constraint valid_width_c {
      // For bits above data_width-1, force zero
      foreach (a[i]) if (i >= data_width) a[i] == 0;
      foreach (b[i]) if (i >= data_width) b[i] == 0;
  	}

    // Create mask function to get mask based on data_width
    function logic [1023:0] get_mask();
        if (data_width >= 1024)
        return '1;          // All bits 1
        else
        return (1 << data_width) - 1;
    endfunction


    // Copy method override (optional but recommended)
    function void copy(uvm_object rhs);
        adder_txn rhs_;
        if (!$cast(rhs_, rhs)) begin
            `uvm_fatal("COPY_FAIL", "Failed to cast rhs to adder_txn")
        end
        this.signed_en      = rhs_.signed_en;
        this.carry_in_en    = rhs_.carry_in_en;
        this.carry_out_en   = rhs_.carry_out_en;
        this.saturation_en  = rhs_.saturation_en;
        this.pipeline_en    = rhs_.pipeline_en;
        this.data_width     = rhs_.data_width;
        this.a             = rhs_.a;
        this.b             = rhs_.b;
        this.cin           = rhs_.cin;
        this.sum           = rhs_.sum;
        this.cout          = rhs_.cout;
        this.ovf           = rhs_.ovf;
        this.valid_in      = rhs_.valid_in;
        this.valid_out     = rhs_.valid_out;
    endfunction

    // Print method for debug
    function void do_print(uvm_printer printer);
        super.do_print(printer);
        mask = get_mask();
        printer.print_field_int("data_width", data_width, 32);
        printer.print_field_int("signed_en", signed_en, 1);
        printer.print_field_int("carry_in_en", carry_in_en, 1);
        printer.print_field_int("carry_out_en", carry_out_en, 1);
        printer.print_field_int("saturation_en", saturation_en, 1);
        printer.print_field_int("pipeline_en", pipeline_en, 1);
        printer.print_field("a", a & mask, data_width * 8);
        printer.print_field("b", b & mask, data_width * 8);
        printer.print_field("sum", sum & mask, data_width * 8);
        printer.print_field_int("cin", cin, 1);
        printer.print_field_int("cout", cout, 1);
        printer.print_field_int("ovf", ovf, 1);
        printer.print_field_int("valid_in", valid_in, 1);
        printer.print_field_int("valid_out", valid_out, 1);
    endfunction

    // Equality check method
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        adder_txn rhs_;
        if (!$cast(rhs_, rhs)) return 0;

        if (this.data_width != rhs_.data_width) return 0;
        if (this.signed_en != rhs_.signed_en) return 0;
        if (this.carry_in_en != rhs_.carry_in_en) return 0;
        if (this.carry_out_en != rhs_.carry_out_en) return 0;
        if (this.saturation_en != rhs_.saturation_en) return 0;
        if (this.pipeline_en != rhs_.pipeline_en) return 0;

        mask = get_mask();

        if ((this.a & mask) !== (rhs_.a & mask)) return 0;
        if ((this.b & mask) !== (rhs_.b & mask)) return 0;
        if (this.cin !== rhs_.cin) return 0;
        if ((this.sum & mask) !== (rhs_.sum & mask)) return 0;
        if (this.cout !== rhs_.cout) return 0;
        if (this.ovf !== rhs_.ovf) return 0;
        if (this.valid_in !== rhs_.valid_in) return 0;
        if (this.valid_out !== rhs_.valid_out) return 0;

        return 1;
    endfunction

endclass : adder_txn
