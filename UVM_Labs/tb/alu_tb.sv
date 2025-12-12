`timescale 1ns/1ps
module alu_tb;
  logic [7:0] a, b, y;
  logic [1:0] op;

  alu dut (.a(a), .b(b), .op(op), .y(y));

  initial begin
    a=8'h0A; b=8'h05; op=2'b00; #5;
    $display("ADD: %0d", y);
    op=2'b01; #5;
    $display("SUB: %0d", y);
    $finish;
  end
endmodule
