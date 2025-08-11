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
