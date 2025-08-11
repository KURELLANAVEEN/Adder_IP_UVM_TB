interface adder_if #(
    parameter int DATA_WIDTH = 32
)(
    input  logic clk,
    input  logic rst_n
);

    // Handshake
    logic        valid_in;
    logic        valid_out;

    // Data signals
    logic [DATA_WIDTH-1:0] a;
    logic [DATA_WIDTH-1:0] b;
    logic                  cin;
    logic [DATA_WIDTH-1:0] sum;
    logic                  cout;
    logic                  ovf;

    // Optional clocking block for UVM driver/monitor sync
    clocking cb @(posedge clk);
        default input #1ns output #1ns;
        output valid_in, a, b, cin;
        input  valid_out, sum, cout, ovf;
    endclocking


    // Modports for driver and monitor with directions explained below
    modport drv_mp (
        input  clk, rst_n,
        output valid_in, a, b, cin,
        input  valid_out, sum, cout, ovf
    );


    modport mon_mp (
        input clk, rst_n,
        input valid_in, a, b, cin,
        input valid_out, sum, cout, ovf
    );



endinterface
