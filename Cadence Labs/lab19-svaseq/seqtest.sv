///////////////////////////////////////////////////////////////////////////
// (c) Copyright 2013 Cadence Design Systems, Inc. All Rights Reserved.
//
// File name   : seq_test.sv
// Title       : sequence test
// Project     : SystemVerilog Training
// Created     : 2013-4-8
// Description : Defines the initial sequence test with no assertions
// Notes       :
//
///////////////////////////////////////////////////////////////////////////

`timescale 1 ns / 1 ns

module top ;

  parameter PERIOD  = 10; // clock period
  parameter CLENGTH = 30; // command length (maximum)
  integer   breakpoint;

  reg CLK, A, B, C, J, K, X ;

  task do_test;
      input [CLENGTH*8:1] seq;
      reg [7:0] c;
      integer i;
    begin
      @(posedge CLK);
      for (i=1;i<=CLENGTH;i=i+1)
        begin
          c = seq[CLENGTH*8:CLENGTH*8-7];
          seq = seq << 8;
          case (c)
            "A" : A <= 1;
            "B" : B <= 1;
            "C" : C <= 1;
            "J" : J <= 1;
            "K" : K <= 1;
            "X" : X <= 1;
            ";" : begin
                    @(posedge CLK);
                    A<=0; B<=0; C<=0; J<=0; K<=0; X<=0;
                  end
          endcase
        end
      @(posedge CLK);
      A<=0; B<=0; C<=0; J<=0; K<=0; X<=0;
      @(posedge CLK);
      breakpoint=breakpoint+1;
    end
  endtask

  always
    begin
      CLK <= 0 ;
      #(PERIOD/2) ;
      CLK <= 1 ;
      #(PERIOD/2) ;
    end

  initial
    begin : TEST
      $timeformat(-9,0,"ns:",6);
      breakpoint=0;
      @(posedge CLK);
      A<=0; B<=0; C<=0; J<=0; K<=0; X<=0;

      $display("TESTING SIMPLE SEQUENCE");
      $display("%t Testing incomplete enabling condition",$time);
      do_test("A;B;J;K");
      $display("%t Testing normal passing condition",$time);
      do_test("A;B;C;J;K");
      $display("%t Testing failing fulfilling condition",$time);
      do_test("A;B;C;J");
      $display("%t Testing overlapping passing conditions",$time);
      do_test("A;B;CA;JB;KC;J;K");
      $display("%t Testing two simultaneous failing fulfilling conditions",$time);
      do_test("A;BA;CB;JC;J");
      $display("%t Testing aborted fulfilling condition",$time);
      do_test("A;B;C;J;X");

     // $display("TESTING COMPLEX SEQUENCE");
     // $display("%t Testing incomplete enabling sequence",$time);
     // do_test("C;B;B;B");
     // $display("%t Testing passing fulfilling sequence",$time);
     // do_test("C;B;A;J;J;J;J;K");
     // $display("%t Testing passing fulfilling sequence",$time);
     // do_test("C;B;B;B;A;J;J;J;J;K");
     // $display("%t Testing disabled enabling sequence",$time);
     // do_test("C;B;B;B;X;J;J;J;J;;K");
     // $display("%t Testing disabled fulfilling sequence",$time);
     // do_test("C;B;B;A;J;J;J;J;X");
     // $display("%t Testing failing fulfilling sequence",$time);
     // do_test("C;B;A;J;J;J;J;;K");

      $display("TESTING IS COMPLETE");
      $finish;
    end

// define assertions here
//#### EDIT ###
    // ----------------------------------------------------------
  // SIMPLE_SEQ
  // enabling sequence :   A ##1 B ##1 C
  // fulfilling sequence : J ##1 K
  // disable when X is asserted
  // ----------------------------------------------------------

  sequence simple_en;
    A ##1 B ##1 C;
  endsequence

  sequence simple_fulfill;
    J ##1 K;
  endsequence

  property SIMPLE_SEQ;
    @(posedge CLK)
      disable iff (X)
        simple_en |-> simple_fulfill;
  endproperty

  assert property (SIMPLE_SEQ)
    else $error("SIMPLE_SEQ FAILED at time %0t", $time);


  // ----------------------------------------------------------
  // COMPLEX_SEQ
  // enabling sequence :   C ##1 B[*1:3] ##1 A
  // fulfilling sequence : J[*4] ##1 K
  // disable when X is asserted
  // ----------------------------------------------------------

  sequence complex_en;
    C ##1 B[*1:3] ##1 A;
  endsequence

  sequence complex_fulfill;
    J[*4] ##1 K;
  endsequence

  property COMPLEX_SEQ;
    @(posedge CLK)
      disable iff (X)
        complex_en |-> complex_fulfill;
  endproperty

  assert property (COMPLEX_SEQ)
    else $error("COMPLEX_SEQ FAILED at time %0t", $time);

//#### END OF EDIT ###

endmodule