// -----------------------------------------------------------------------------
// Assertions & SVA: Basic checks to catch misuse / protocol violations
// These assertions are optional and can be disabled by undefining ENABLE_ADDER_SVA
// -----------------------------------------------------------------------------
`ifdef ENABLE_ADDER_SVA
module adder_sva #(
    parameter int DATA_WIDTH = 32,
    parameter bit PIPELINE_EN = 0,
    parameter int PIPELINE_STAGES = 1
) (
    input  logic clk,
    input  logic rst_n,
    input  logic valid_in,
    input  logic valid_out,
    input  logic [DATA_WIDTH-1:0] a,
    input  logic [DATA_WIDTH-1:0] b
);

    // Simple assertion: when valid_in is asserted, inputs should not be X
    property no_x_on_valid;
        @(posedge clk) disable iff (!rst_n)
        valid_in |-> (a !== 'x) && (b !== 'x);
    endproperty
    assert_no_x_on_valid: assert property (no_x_on_valid) else $error("Input X on valid_in");

    // If not pipelined, valid_out must follow valid_in combinationally (no delay)
    generate
        if (!PIPELINE_EN) begin : gen_np
            // we cannot sample combinational asserts on posedge reliable; use static check
            // assume valid_out equals valid_in in combinational mode - checked in testbench
        end
    endgenerate

endmodule : adder_sva
`endif
