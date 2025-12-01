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

  // Printable ASCII characters
  constraint c_ascii {
    data inside {[8'h20:8'h7F]};
  }

  // Letters only
  constraint c_letters {
    data inside { [8'h41:8'h5A], [8'h61:8'h7A] };
  }

  // Weighted distribution
  constraint c_weighted {
    data dist {
      [8'h41:8'h5A] := 80,   // A-Z
      [8'h61:8'h7A] := 20    // a-z
    };
  }
endclass

//  MemMonitor
class MemMonitor;

  // Virtual interface to sample DUT signals
  virtual mem_if.TEST vif;

  // Sampled values
  bit [4:0] addr;
  bit [7:0] data;
  bit       is_write;

  // Covergroup for functional coverage
  covergroup cg @(posedge vif.clk);

    // Address coverage: 0~31
    coverpoint addr {
      bins low  = {0};
      bins high = {31};
      bins mid[] = {[1:30]};
    }

    // Data coverage: printable ASCII
    coverpoint data {
      bins ascii[] = {[8'h20:8'h7F]};
    }

    // READ / WRITE coverage
    coverpoint is_write {
      bins WRITE = {1};
      bins READ  = {0};
    }

    // Cross coverage: address × data
    cross addr, data;

  endgroup : cg

  function new(virtual mem_if.TEST vif);
    this.vif = vif;
    cg = new();
  endfunction

  // Called by driver after each read/write
  task sample(bit [4:0] a, bit [7:0] d, bit w);
    addr     = a;
    data     = d;
    is_write = w;
    cg.sample();
  endtask
endclass

//  MemDriver
class MemDriver;

  virtual mem_if.TEST vif;
  MemMonitor monitor; 

  function new(virtual mem_if.TEST vif, MemMonitor m = null);
    this.vif = vif;
    this.monitor = m;
  endfunction

  task write(input [4:0] addr, input [7:0] data);
    vif.write_mem(addr, data);
    if (monitor != null)
      monitor.sample(addr, data, 1);  // WRITE sample
  endtask

  task read(input [4:0] addr, output [7:0] data);
    vif.read_mem(addr, data);
    if (monitor != null)
      monitor.sample(addr, data, 0);  // READ sample
  endtask

  // Randomized memory test
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

      write(item.addr, item.data);
      read(item.addr, rd_val);

      if (rd_val !== item.data) begin
        $display("ERROR @ addr %0d: expected %0h (%c) got %0h (%c)",
                 item.addr, item.data, item.data,
                 rd_val, rd_val);
        errors++;
      end
      else if (debug)
        $display("OK @ addr %0d: %0h (%c)",
                 item.addr, item.data, item.data);
    end
  endtask

endclass

//  Testbench Module
module mem_test(mem_if.TEST bus);

  logic [7:0] rd_data;
  int errors;

  MemDriver  drv;
  MemMonitor mon;  

  // Clear entire memory
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

  // Simple address = data test
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


  // Testbench main sequence
  initial begin

    mon = new(bus);       
    drv = new(bus, mon);  

    errors = 0;
    bus.read    = 0;
    bus.write   = 0;
    bus.addr    = 0;
    bus.data_in = 0;

    repeat (2) @(posedge bus.clk);

    clear_mem(errors);
    comp_data_addr(errors);

    drv.random_data_test(errors, 1);

    print_status(errors);

    // Print functional coverage
    $display("\n---- COVERAGE REPORT ----");
    $display("Coverage = %0.2f%%", mon.cg.get_coverage());

    $finish;
  end

endmodule
