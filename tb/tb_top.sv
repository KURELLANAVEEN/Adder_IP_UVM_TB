`timescale 1ns/1ps
`include "adder_if.sv"
`include "adder_tb_pkg.sv"
`include "adder_ip.sv"

module tb_top;

    parameter int DATA_WIDTH = 32;
    parameter SIGNED_EN = 1;
    parameter CARRY_IN_EN = 0;
    parameter CARRY_OUT_EN = 0;
    parameter SATURATION_EN = 0;
    parameter PIPELINE_EN = 0;
    parameter PIPELINE_STAGES = 1;
    parameter ARCH = adder_pkg::ARCH_RCA;

    logic clk;
    logic rst_n;

    // Instantiate interface
    adder_if #(.DATA_WIDTH(DATA_WIDTH)) adder_vif (.clk(clk),
    .rst_n(rst_n));

    // DUT instance
    adder_ip #(
        .DATA_WIDTH(DATA_WIDTH),
        .SIGNED_EN(SIGNED_EN),
        .CARRY_IN_EN(CARRY_IN_EN),
        .CARRY_OUT_EN(CARRY_OUT_EN),
        .SATURATION_EN(SATURATION_EN),
        .PIPELINE_EN(PIPELINE_EN),
        .PIPELINE_STAGES(PIPELINE_STAGES),
        .ARCH(adder_pkg::ARCH_RCA)
    ) dut (
        .clk        (clk),
        .rst_n      (rst_n),
        .valid_in   (adder_vif.valid_in),
        .valid_out  (adder_vif.valid_out),
        .a          (adder_vif.a),
        .b          (adder_vif.b),
        .cin        (adder_vif.cin),
        .sum        (adder_vif.sum),
        .cout       (adder_vif.cout),
        .ovf        (adder_vif.ovf)
    );

    // Clock generation
    initial clk = 0;
    always #5 clk = ~clk;

    // Reset
    initial begin
        rst_n = 0;
        #20 rst_n = 1;
    end

    initial begin
        uvm_config_db#(virtual adder_if)::set(null, "*", "vif", adder_vif);
        uvm_config_db #(int)::set(null, "", "DATA_WIDTH", DATA_WIDTH);
        // Pass DATA_WIDTH parameter to env.agent and any other needed paths
        // uvm_config_db #(int)::set(null, "uvm_test_top.env.agent", "DATA_WIDTH", DATA_WIDTH);
        // uvm_config_db #(int)::set(null, "uvm_test_top.env.agent.driver", "DATA_WIDTH", DATA_WIDTH);
        // uvm_config_db #(int)::set(null, "uvm_test_top.env.agent.monitor", "DATA_WIDTH", DATA_WIDTH);
        // ...set others if needed

        run_test("adder_base_test");
    end

endmodule
