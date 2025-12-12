///////////////////////////////////////////////////////////////////////////
// (c) Copyright 2013 Cadence Design Systems, Inc. All Rights Reserved.
//
// File name   : mux.sv
// Title       : MUX module 
// Project     : SystemVerilog Training
// Created     : 2013-4-8
// Description : Defines the mux module 
// Notes       :
//
///////////////////////////////////////////////////////////////////////////
`timescale 1 ns / 1 ns

module mux
(
  input  logic       clock  ,
  input  logic [3:0] ip1    ,
  input  logic [3:0] ip2    ,
  input  logic [3:0] ip3    ,
  input  logic       sel1   ,
  input  logic       sel2   ,
  input  logic       sel3   ,
  output logic [3:0] mux_op  
) ;

always @(posedge clock)
  if (sel1 == 1)
    mux_op <= ip1 ;
  else
    if (sel2 == 1)
      mux_op <= ip2 ;
    else
      if (sel3 == 1)
        mux_op <= ip3 ;

// assertions go here
//#### edit ###
// -------------------------------------------------
// Incorrect (initial) versions -- WILL FAIL
// -------------------------------------------------
// These match exactly what the lab asks you to do first:
// simple implication using $past, without considering priority.

  property P_SEL1_bad;
    @(posedge clock)
      sel1 |-> (mux_op == $past(ip1));
  endproperty
  assert property (P_SEL1_bad)
    else $error("P_SEL1_bad FAILED: mux_op != $past(ip1)");

  property P_SEL2_bad;
    @(posedge clock)
      sel2 |-> (mux_op == $past(ip2));
  endproperty
  assert property (P_SEL2_bad)
    else $error("P_SEL2_bad FAILED: mux_op != $past(ip2)");

  property P_SEL3_bad;
    @(posedge clock)
      sel3 |-> (mux_op == $past(ip3));
  endproperty
  assert property (P_SEL3_bad)
    else $error("P_SEL3_bad FAILED: mux_op != $past(ip3)");


  // -------------------------------------------------
  // Corrected versions (with priority logic)
  // These WILL PASS and satisfy the RTL logic
  // -------------------------------------------------

  property P_SEL1_ok;
    @(posedge clock)
      sel1 |-> (mux_op == $past(ip1));
  endproperty
  assert property (P_SEL1_ok);

  property P_SEL2_ok;
    @(posedge clock)
      // sel2 only matters when sel1 == 0
      (sel2 && !sel1) |-> (mux_op == $past(ip2));
  endproperty
  assert property (P_SEL2_ok);

  property P_SEL3_ok;
    @(posedge clock)
      // sel3 only matters when sel1==0 and sel2==0
      (sel3 && !sel1 && !sel2) |-> (mux_op == $past(ip3));
  endproperty
  assert property (P_SEL3_ok);

//#### end of edit ###
endmodule