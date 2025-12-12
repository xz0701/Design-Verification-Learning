`include "mem_if.sv"
`include "mem.sv"

//  Class-Based Randomization
class RandItem;

  rand bit [4:0] addr;      
  rand bit [7:0] data;

  function new(bit [4:0] a = 0, bit [7:0] d = 0);
    addr = a;
    data = d;
  endfunction

  constraint c_ascii {
    data inside {[8'h20:8'h7F]};
  }

  constraint c_letters {
    data inside { [8'h41:8'h5A], [8'h61:8'h7A] };
  }

  constraint c_weighted {
    data dist {
      [8'h41:8'h5A] := 80,
      [8'h61:8'h7A] := 20
    };
  }
endclass

//  MemDriver Class (Lab14: Virtual Interface)
class MemDriver;

  virtual mem_if.TEST vif;

  function new(virtual mem_if.TEST vif);
    this.vif = vif;
  endfunction

  task write(input [4:0] addr, input [7:0] data);
    vif.write_mem(addr, data);   // call interface task
  endtask

  task read(input [4:0] addr, output [7:0] data);
    vif.read_mem(addr, data);
  endtask

  task random_data_test(ref int errors, input bit debug = 0);

    RandItem item = new();
    bit ok;
    logic [7:0] rd_val;

    for (int k = 0; k < 32; k++) begin

      ok = item.randomize();
      if (!ok) begin
        $display("CLASS RANDOMIZE FAILED (iteration %0d)", k);
        errors++;
      end

      // Write using driver + interface
      write(item.addr, item.data);

      // Read using driver + interface
      read(item.addr, rd_val);

      if (rd_val !== item.data) begin
        $display("ERROR @ addr %0d: expected %0h (%c) got %0h (%c)",
                 item.addr, item.data, item.data,
                 rd_val, rd_val);
        errors++;
      end
      else if (debug) begin
        $display("OK @ addr %0d: %0h (%c)",
                 item.addr, item.data, item.data);
      end
    end
  endtask

endclass

//  Testbench Module
module mem_test(mem_if.TEST bus);

  logic [7:0] rd_data;
  int errors;

  MemDriver drv;

  task automatic clear_mem(ref int errors);
    logic [7:0] rd_val;
    for (int i = 0; i < 32; i++) begin
      drv.write(i, 8'h00);
      drv.read(i, rd_val);
      if (rd_val !== 8'h00) begin
        $display("ERROR @%0d: expected 00, got %0h", i, rd_val);
        errors++;
      end
    end
  endtask

  task automatic comp_data_addr(ref int errors);
    logic [7:0] rd_val;
    for (int i = 0; i < 32; i++) begin
      drv.write(i, i[7:0]);
      drv.read(i, rd_val);
      if (rd_val !== i[7:0]) begin
        $display("ERROR @%0d: expected %0h, got %0h", i, i[7:0], rd_val);
        errors++;
      end
    end
  endtask

  function void print_status(input int errors);
    if (errors == 0)
      $display("All Memory Tests Passed");
    else
      $display("Memory Test Failed: %0d ERRORS", errors);
  endfunction


  initial begin

    drv = new(bus);

    errors = 0;
    bus.read  = 0;
    bus.write = 0;
    bus.addr  = 0;
    bus.data_in = 0;

    repeat (2) @(posedge bus.clk);

    clear_mem(errors);
    comp_data_addr(errors);

    drv.random_data_test(errors, 1);  // Lab14 update

    print_status(errors);
    $finish;
  end

endmodule
