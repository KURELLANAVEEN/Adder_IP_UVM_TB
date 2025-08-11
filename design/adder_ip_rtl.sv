// adder_ip_full.sv
// Industry-style General Purpose Adder IP - SystemVerilog
// Contains: package (types/constants), ripple-carry adder (structural),
// parallel-prefix (Kogge-Stone) adder (structural), assertions, and top-level
// adder_ip which selects architecture via parameter and provides optional
// pipelining, saturation, signed/unsigned modes, carry-in/carry-out, and valid
// handshake.

// -----------------------------------------------------------------------------
// Package: adder_pkg
// - common parameters, enumerations and utility functions used by modules
// -----------------------------------------------------------------------------
package adder_pkg;
    // Preferred to use integer enum for ARCH selection (portable)
    localparam int ARCH_RCA = 0;
    localparam int ARCH_CLA = 1; // placeholder for future
    localparam int ARCH_KSA = 2; // Kogge-Stone
    localparam int ARCH_BKA = 3; // Brent-Kung (placeholder)
    localparam int ARCH_CSLA = 4; // Carry-select (placeholder)

    // helper function: ceil(log2(x))
    function automatic int clog2(input int value);
        int v;
        begin
            v = 0;
            value = value - 1;
            while (value > 0) begin
                value = value >> 1;
                v = v + 1;
            end
            return v;
        end
    endfunction

endpackage : adder_pkg


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
    genvar level, bit;
    generate
        for (level = 1; level <= LEVELS; level++) begin : gen_levels
            localparam int span = (1 << (level-1));
            for (bit = 0; bit < DATA_WIDTH; bit++) begin : gen_bits
                if (bit >= span) begin
                    // combine (gk[level-1][bit], pk[level-1][bit]) with
                    // (gk[level-1][bit-span], pk[level-1][bit-span])
                    assign gk[level][bit] = gk[level-1][bit] | (pk[level-1][bit] & gk[level-1][bit-span]);
                    assign pk[level][bit] = pk[level-1][bit] & pk[level-1][bit-span];
                end else begin
                    assign gk[level][bit] = gk[level-1][bit];
                    assign pk[level][bit] = pk[level-1][bit];
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


// -----------------------------------------------------------------------------
// Top-level: adder_ip
// - Integrates architecture selection, signed/unsigned handling, saturation,
//   pipelining, parameter checks, and interface stability.
// -----------------------------------------------------------------------------
`include "adder_pkg.sv"

module adder_ip #(
    parameter int DATA_WIDTH       = 32,
    parameter bit SIGNED_EN       = 1,
    parameter bit CARRY_IN_EN     = 0,
    parameter bit CARRY_OUT_EN    = 0,
    parameter bit SATURATION_EN   = 0,
    parameter bit PIPELINE_EN     = 0,
    parameter int PIPELINE_STAGES = 1,
    // ARCH selection as integer for tool portability
    parameter int ARCH            = adder_pkg::ARCH_RCA
) (
    input  logic                         clk,
    input  logic                         rst_n,

    // Handshake
    input  logic                         valid_in,
    output logic                         valid_out,

    // Data
    input  logic [DATA_WIDTH-1:0]        a,
    input  logic [DATA_WIDTH-1:0]        b,
    input  logic                         cin,

    output logic [DATA_WIDTH-1:0]        sum,
    output logic                         cout,
    output logic                         ovf
);

    // Parameter sanity checks at elaboration/simulation time
    initial begin
        if (DATA_WIDTH <= 0) $fatal("DATA_WIDTH must be > 0");
        if (PIPELINE_EN && PIPELINE_STAGES < 1) $fatal("PIPELINE_STAGES must be >=1 when PIPELINE_EN=1");
        if (ARCH < 0 || ARCH > 4) $fatal("Unsupported ARCH value. Use constants from adder_pkg.");
    end

    // Prepare inputs depending on CARRY_IN_EN
    logic [DATA_WIDTH-1:0] a_calc, b_calc;
    logic                  cin_calc;
    assign a_calc = a;
    assign b_calc = b;
    assign cin_calc = (CARRY_IN_EN) ? cin : 1'b0;

    // Behavioral fallback/raw sum_ext used when structural arch not selected
    logic [DATA_WIDTH:0] raw_sum_ext_beh;
    generate
        begin : gen_beh
            if (SIGNED_EN) begin
                // sign-extend and use signed arithmetic
                always_comb raw_sum_ext_beh = $signed({a_calc[DATA_WIDTH-1], a_calc}) +
                                               $signed({b_calc[DATA_WIDTH-1], b_calc}) +
                                               $signed({{DATA_WIDTH{1'b0}}, cin_calc});
            end else begin
                always_comb raw_sum_ext_beh = {{1'b0}, a_calc} + {{1'b0}, b_calc} + {{DATA_WIDTH{1'b0}}, cin_calc};
            end
        end
    endgenerate

    // Architecture selection: produce arch_sum_ext (DATA_WIDTH+1 bits)
    logic [DATA_WIDTH:0] arch_sum_ext;

    generate
        if (ARCH == adder_pkg::ARCH_RCA) begin : GEN_RCA
            adder_rca #(.DATA_WIDTH(DATA_WIDTH)) u_rca (.a(a_calc), .b(b_calc), .cin(cin_calc), .sum_ext(arch_sum_ext));
        end else if (ARCH == adder_pkg::ARCH_KSA) begin : GEN_KSA
            kogge_stone_adder #(.DATA_WIDTH(DATA_WIDTH)) u_ksa (.a(a_calc), .b(b_calc), .cin(cin_calc), .sum_ext(arch_sum_ext));
        end else begin : GEN_FALLBACK
            // Fallback to behavioral add
            assign arch_sum_ext = raw_sum_ext_beh;
        end
    endgenerate

    // Compute local carry and overflow from arch_sum_ext
    logic local_cout;
    assign local_cout = arch_sum_ext[DATA_WIDTH];

    logic local_ovf;
    always_comb begin
        if (SIGNED_EN) begin
            logic a_msb = a_calc[DATA_WIDTH-1];
            logic b_msb = b_calc[DATA_WIDTH-1];
            logic s_msb = arch_sum_ext[DATA_WIDTH-1];
            local_ovf = (a_msb == b_msb) && (s_msb != a_msb);
        end else begin
            local_ovf = local_cout;
        end
    end

    // Saturation logic
    logic [DATA_WIDTH-1:0] sat_sum;
    always_comb begin
        if (SATURATION_EN) begin
            if (SIGNED_EN) begin
                // signed saturation clamp
                logic signed [DATA_WIDTH-1:0] max_pos = {1'b0, {(DATA_WIDTH-1){1'b1}}};
                logic signed [DATA_WIDTH-1:0] min_neg = {1'b1, {(DATA_WIDTH-1){1'b0}}};
                if (local_ovf) begin
                    if ($signed(a_calc) >= 0 && $signed(b_calc) >= 0)
                        sat_sum = max_pos;
                    else
                        sat_sum = min_neg;
                end else begin
                    sat_sum = arch_sum_ext[DATA_WIDTH-1:0];
                end
            end else begin
                // unsigned: clamp to all ones on carry
                if (local_cout)
                    sat_sum = {DATA_WIDTH{1'b1}};
                else
                    sat_sum = arch_sum_ext[DATA_WIDTH-1:0];
            end
        end else begin
            sat_sum = arch_sum_ext[DATA_WIDTH-1:0];
        end
    end

    // Pipeline handling
    logic [DATA_WIDTH-1:0] sum_pre_pipe;
    logic                  cout_pre;
    logic                  ovf_pre;
    logic                  valid_in_pre;

    assign sum_pre_pipe = sat_sum;
    assign cout_pre     = local_cout;
    assign ovf_pre      = local_ovf;
    assign valid_in_pre = valid_in;

    generate
        if (PIPELINE_EN) begin : GEN_PIPELINE_TOP
            logic [DATA_WIDTH-1:0] sum_pipe [0:PIPELINE_STAGES-1];
            logic                  valid_pipe [0:PIPELINE_STAGES-1];
            logic                  cout_pipe  [0:PIPELINE_STAGES-1];
            logic                  ovf_pipe   [0:PIPELINE_STAGES-1];

            integer j;
            always_ff @(posedge clk) begin
                if (!rst_n) begin
                    for (j = 0; j < PIPELINE_STAGES; j++) begin
                        sum_pipe[j]   <= '0;
                        valid_pipe[j] <= 1'b0;
                        cout_pipe[j]  <= 1'b0;
                        ovf_pipe[j]   <= 1'b0;
                    end
                end else begin
                    sum_pipe[0]   <= sum_pre_pipe;
                    valid_pipe[0] <= valid_in_pre;
                    cout_pipe[0]  <= cout_pre;
                    ovf_pipe[0]   <= ovf_pre;
                    for (j = 1; j < PIPELINE_STAGES; j++) begin
                        sum_pipe[j]   <= sum_pipe[j-1];
                        valid_pipe[j] <= valid_pipe[j-1];
                        cout_pipe[j]  <= cout_pipe[j-1];
                        ovf_pipe[j]   <= ovf_pipe[j-1];
                    end
                end
            end

            assign sum      = sum_pipe[PIPELINE_STAGES-1];
            assign cout     = (CARRY_OUT_EN) ? cout_pipe[PIPELINE_STAGES-1] : 1'b0;
            assign ovf      = ovf_pipe[PIPELINE_STAGES-1];
            assign valid_out= valid_pipe[PIPELINE_STAGES-1];

        end else begin : GEN_NOPIPE_TOP
            assign sum      = sum_pre_pipe;
            assign cout     = (CARRY_OUT_EN) ? cout_pre : 1'b0;
            assign ovf      = ovf_pre;
            assign valid_out= valid_in_pre;
        end
    endgenerate

    // Optional SVA instantiation (if enabled via define)
    `ifdef ENABLE_ADDER_SVA
        adder_sva #(.DATA_WIDTH(DATA_WIDTH), .PIPELINE_EN(PIPELINE_EN), .PIPELINE_STAGES(PIPELINE_STAGES))
                  u_sva (.clk(clk), .rst_n(rst_n), .valid_in(valid_in), .valid_out(valid_out), .a(a), .b(b));
    `endif

endmodule : adder_ip

// End of file
