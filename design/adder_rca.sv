// -----------------------------------------------------------------------------
// Module: adder_rca
// Simple structural ripple-carry adder (bit-sliced full-adder chain)
// - parameterized width
// - produces DATA_WIDTH+1 bit sum_ext (MSB is carry-out)
// - synthesizable and straightforward
// -----------------------------------------------------------------------------
module adder_rca #(
    parameter int DATA_WIDTH = 32
) (
    input  logic [DATA_WIDTH-1:0] a,
    input  logic [DATA_WIDTH-1:0] b,
    input  logic                  cin,
    output logic [DATA_WIDTH:0]   sum_ext
);

    logic [DATA_WIDTH:0] carry;
    assign carry[0] = cin;

    genvar i;
    generate
        for (i = 0; i < DATA_WIDTH; i++) begin : gen_bit
            // full adder: sum = a ^ b ^ carry_in
            // carry_out = (a & b) | (a & carry_in) | (b & carry_in)
            assign sum_ext[i] = a[i] ^ b[i] ^ carry[i];
            assign carry[i+1] = (a[i] & b[i]) | (a[i] & carry[i]) | (b[i] & carry[i]);
        end
    endgenerate

    // final carry-out as MSB of sum_ext
    assign sum_ext[DATA_WIDTH] = carry[DATA_WIDTH];

endmodule : adder_rca
