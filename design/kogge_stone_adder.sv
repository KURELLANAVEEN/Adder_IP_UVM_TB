// -----------------------------------------------------------------------------
// Module: kogge_stone_adder
// Parameterized Kogge-Stone parallel-prefix adder implementation.
// - Supports arbitrary DATA_WIDTH (works correctly, uses generate loops)
// - Produces DATA_WIDTH+1 bit sum_ext (MSB is carry-out)
// Note: Kogge-Stone uses propagate/generate prefix tree.
// -----------------------------------------------------------------------------
module kogge_stone_adder #(
    parameter int DATA_WIDTH = 32
) (
    input  logic [DATA_WIDTH-1:0] a,
    input  logic [DATA_WIDTH-1:0] b,
    input  logic                  cin,
    output logic [DATA_WIDTH:0]   sum_ext
);

    // propagate and generate signals
    logic [DATA_WIDTH-1:0] p; // propagate
    logic [DATA_WIDTH-1:0] g; // generate

    // initial propagate/generate
    genvar i;
    generate
        for (i = 0; i < DATA_WIDTH; i++) begin : pg_init
            assign p[i] = a[i] ^ b[i];
            assign g[i] = a[i] & b[i];
        end
    endgenerate

    // Number of levels in prefix tree
    localparam int LEVELS = (adder_pkg::clog2(DATA_WIDTH));

    // prefix arrays: gk[level][bit], pk[level][bit]
    // level 0 is initial p/g
    logic [DATA_WIDTH-1:0] gk [0:LEVELS];
    logic [DATA_WIDTH-1:0] pk [0:LEVELS];

    // assign level 0
    generate
        for (i = 0; i < DATA_WIDTH; i++) begin : level0
            assign gk[0][i] = g[i];
            assign pk[0][i] = p[i];
        end
    endgenerate

    // Build prefix tree
    genvar level, idx;
    generate
        for (level = 1; level <= LEVELS; level++) begin : gen_levels
            localparam int span = (1 << (level-1));
            for (idx = 0; idx < DATA_WIDTH; idx++) begin : gen_bits
                if (idx >= span) begin
                    // combine (gk[level-1][idx], pk[level-1][idx]) with
                    // (gk[level-1][idx-span], pk[level-1][idx-span])
                    assign gk[level][idx] = gk[level-1][idx] | (pk[level-1][idx] & gk[level-1][idx-span]);
                    assign pk[level][idx] = pk[level-1][idx] & pk[level-1][idx-span];
                end else begin
                    assign gk[level][idx] = gk[level-1][idx];
                    assign pk[level][idx] = pk[level-1][idx];
                end
            end
        end
    endgenerate

    // compute carries: carry[0] = cin, carry[i+1] = gk[LEVELS][i] | (pk[LEVELS][i] & cin)
    logic [DATA_WIDTH:0] carry;
    assign carry[0] = cin;

    generate
        for (i = 0; i < DATA_WIDTH; i++) begin : sum_calc
            assign carry[i+1] = gk[LEVELS][i] | (pk[LEVELS][i] & cin);
            assign sum_ext[i] = p[i] ^ carry[i];
        end
    endgenerate

    assign sum_ext[DATA_WIDTH] = carry[DATA_WIDTH];

endmodule : kogge_stone_adder
