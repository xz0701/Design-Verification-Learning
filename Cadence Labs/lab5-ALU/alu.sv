module alu (
    input logic [7:0] accum,
    input logic [7:0] data,
    input logic [2:0] opcode,
    input logic clk,
    output logic [7:0] out,
    output logic zero
);
    timeunit 1ns;
    timeprecision 1ps;
    import typedefs::*;

    always_ff @( negedge clk ) begin : out_ctrl
        unique case (opcode)
            HLT, SKZ, STP, JMP: out <= accum;
            ADD: out <= data + accum;
            AND: out <= data & accum;
            XOR: out <= data ^ accum;
            LDA: out <= data;
            default: out <= accum;
        endcase
    end
    always_comb begin
        zero = (accum==8'b0);
    end
endmodule