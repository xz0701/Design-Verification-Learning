`include "mem_if.sv"
`include "mem.sv"

// Class-Based Randomization Item
class RandItem;

  // Random address and data
  rand bit [4:0] addr;      // 0–31
  rand bit [7:0] data;

  // Constructor
  function new(bit [4:0] a = 0, bit [7:0] d = 0);
    addr = a;
    data = d;
  endfunction

  // Constraints
  // Printable ASCII
  constraint c_ascii {
    data inside {[8'h20:8'h7F]};
  }

  // Letters A-Z, a-z
  constraint c_letters {
    data inside { [8'h41:8'h5A], [8'h61:8'h7A] };
  }

  // Weighted: 80% uppercase, 20% lowercase
  constraint c_weighted {
    data dist {
      [8'h41:8'h5A] := 80,
      [8'h61:8'h7A] := 20
    };
  }

endclass

// MemDriver Class
class MemDriver;

  virtual mem_if.TEST vif;

  function new(virtual mem_if.TEST vif);
    this.vif = vif;
  endfunction

  // Simple wrappers around interface tasks
  task write(input [4:0] addr, input [7:0] data, input bit debug = 0);
    vif.write_mem(addr, data, debug);
  endtask

  task read(input [4:0] addr, output [7:0] data, input bit debug = 0);
    vif.read_mem(addr, data, debug);
  endtask

endclass

// Testbench Module
module mem_test(mem_if.TEST bus);

  logic [7:0] rd_data;
  int errors;

  MemDriver drv;

  // Utility: print pass/fail status
  function void print_status(input int errors);
    if (errors == 0)
      $display("All Memory Tests Passed");
    else
      $display("Memory Test Failed: %0d ERRORS", errors);
  endfunction


  // 1) Dynamic Array Scoreboard
  //    - Use a dynamic array indexed by address
  //    - Unwritten locations stay 'x and are skipped
  task automatic dyn_array_scoreboard(ref int errors, input bit debug = 0);
    RandItem item = new();
    logic [7:0] rd_val;

    // Dynamic array of 8-bit logic vectors, indexed [0:31]
    logic [7:0] exp_da[];

    // Allocate space for 32 locations
    exp_da = new[32];

    // Initialize to 'x so we can detect unwritten addresses
    foreach (exp_da[i]) begin
      exp_da[i] = 'x;
    end

    $display("\n--- Dynamic Array Scoreboard ---");
    $display("Dynamic array size = %0d", exp_da.size());

    // Write 32 random address/data pairs
    for (int k = 0; k < 32; k++) begin
      if (!item.randomize()) begin
        $display("RANDOMIZE FAILED in dyn_array_scoreboard (iter=%0d)", k);
        errors++;
      end

      // Drive memory write via driver
      drv.write(item.addr, item.data, debug);

      // Save expected data in scoreboard (indexed by address)
      exp_da[item.addr] = item.data;
    end

    // Read back all addresses that have been written
    for (int addr = 0; addr < 32; addr++) begin
      // Only check locations that are not 'x (written at least once)
      if (exp_da[addr] !== 'x) begin
        drv.read(addr[4:0], rd_val, debug);

        if (rd_val !== exp_da[addr]) begin
          $display("DYN ARR ERROR @ addr %0d: expected %0h, got %0h",
                   addr, exp_da[addr], rd_val);
          errors++;
        end
        else if (debug) begin
          $display("DYN ARR OK    @ addr %0d: %0h", addr, rd_val);
        end
      end
    end

  endtask


  // 2) Associative Array Scoreboard
  //    - Only store addresses that were actually written
  //    - Use num() and first()/next() to iterate keys
  task automatic assoc_array_scoreboard(ref int errors, input bit debug = 0);
    RandItem item = new();
    logic [7:0] rd_val;

    // Associative array indexed by address (5-bit)
    logic [7:0] exp_aa [bit [4:0]];

    $display("\n--- Associative Array Scoreboard ---");

    // Write 32 random address/data pairs
    for (int k = 0; k < 32; k++) begin
      if (!item.randomize()) begin
        $display("RANDOMIZE FAILED in assoc_array_scoreboard (iter=%0d)", k);
        errors++;
      end

      drv.write(item.addr, item.data, debug);
      exp_aa[item.addr] = item.data;
    end

    int num_locs = exp_aa.num();
    $display("Associative array: %0d locations to check", num_locs);

    // Iterate over all keys that were written
    bit [4:0] key;
    if (exp_aa.first(key)) begin
      do begin
        // Read back from memory
        drv.read(key, rd_val, debug);

        if (rd_val !== exp_aa[key]) begin
          $display("ASSOC ARR ERROR @ addr %0d: expected %0h, got %0h",
                   key, exp_aa[key], rd_val);
          errors++;
        end
        else if (debug) begin
          $display("ASSOC ARR OK    @ addr %0d: %0h", key, rd_val);
        end

        // Delete location once it has been checked
        exp_aa.delete(key);

      end while (exp_aa.next(key));
    end

  endtask

  // 3) Queue Scoreboard
  //    - Make sure each address is written exactly once
  //    - Store {addr,data} in a queue of structs
  //    - Pop entries in the same order and compare
  typedef struct packed {
    logic [4:0] addr;
    logic [7:0] data;
  } mem_tr_t;

  task automatic queue_scoreboard(ref int errors, input bit debug = 0);
    mem_tr_t q[$];        // queue of address/data pairs
    logic [7:0] rd_val;

    $display("\n--- Queue Scoreboard ---");

    // Write every address exactly once (0..31)
    for (int addr = 0; addr < 32; addr++) begin
      mem_tr_t tr;
      // Randomize only data; address is sequential
      if (!std::randomize(tr.data)) begin
        $display("RANDOMIZE FAILED in queue_scoreboard (addr=%0d)", addr);
        errors++;
      end

      tr.addr = addr[4:0];

      // Write to memory
      drv.write(tr.addr, tr.data, debug);

      // Push expected transaction into queue
      q.push_back(tr);
    end

    // Pop from queue and read/compare
    while (q.size() > 0) begin
      mem_tr_t tr = q.pop_front();

      drv.read(tr.addr, rd_val, debug);

      if (rd_val !== tr.data) begin
        $display("QUEUE ERROR @ addr %0d: expected %0h, got %0h",
                 tr.addr, tr.data, rd_val);
        errors++;
      end
      else if (debug) begin
        $display("QUEUE OK    @ addr %0d: %0h", tr.addr, rd_val);
      end
    end

  endtask

  // Initial block: create driver, init bus, run tests
  initial begin
    // Construct driver with virtual interface handle
    drv = new(bus);

    errors = 0;

    // Initialize bus signals
    bus.read    = 0;
    bus.write   = 0;
    bus.addr    = 0;
    bus.data_in = 0;

    // Wait a couple of clocks before starting
    repeat (2) @(posedge bus.clk);

    // 1) Dynamic array scoreboard
    dyn_array_scoreboard(errors, 0);

    // 2) Associative array scoreboard
    assoc_array_scoreboard(errors, 0);

    // 3) Queue scoreboard
    queue_scoreboard(errors, 0);

    // Final status
    print_status(errors);
    $finish;
  end

endmodule
