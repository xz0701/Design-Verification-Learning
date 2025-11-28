`include "mem_if.sv"
`include "mem.sv"

// Class-Based Randomization
class RandItem;

  rand bit [4:0] addr;      // 0–31
  rand bit [7:0] data;

  // Constructor
  function new(bit [4:0] a = 0, bit [7:0] d = 0);
    addr = a;
    data = d;
  endfunction

  constraint c_ascii {
    data inside {[8'h20:8'h7F]};
  }

  constraint c_letters {
    data inside {
      [8'h41:8'h5A],  // A-Z
      [8'h61:8'h7A]   // a-z
    };
  }

  constraint c_weighted {
    data dist {
      [8'h41:8'h5A] := 80,   // Uppercase 80%
      [8'h61:8'h7A] := 20    // Lowercase 20%
    };
  }

endclass


module mem_test(mem_if.TEST bus);

  logic [7:0] rd_data;
  int errors;

  task automatic random_data_test(ref int errors, input bit debug = 0);

    RandItem item = new();
    bit ok;
    logic [7:0] rd_val;

    for (int k = 0; k < 32; k++) begin

      // Randomize class properties
      ok = item.randomize();
      if (!ok) begin
        $display("CLASS RANDOMIZE FAILED (iteration %0d)", k);
        errors++;
      end

      // Write using item.addr and item.data
      bus.write_mem(item.addr, item.data);

      // Read
      bus.read_mem(item.addr, rd_val);

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

  // Other tests remain unchanged
  task automatic clear_mem(ref int errors);
    logic [7:0] rd_val;
    for (int i = 0; i < 32; i++) begin
      bus.write_mem(i, 8'h00);
      bus.read_mem(i, rd_val);
      if (rd_val !== 8'h00) begin
        $display("ERROR @%0d: expected 00, got %0h", i, rd_val);
        errors++;
      end
    end
  endtask

  task automatic comp_data_addr(ref int errors);
    logic [7:0] rd_val;
    for (int i = 0; i < 32; i++) begin
      bus.write_mem(i, i[7:0]);
      bus.read_mem(i, rd_val);
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

  // Test run sequence
  initial begin
    errors = 0;
    bus.read  = 0;
    bus.write = 0;
    bus.addr  = 0;
    bus.data_in = 0;

    repeat (2) @(posedge bus.clk);

    clear_mem(errors);
    comp_data_addr(errors);

    random_data_test(errors, 1);

    print_status(errors);
    $finish;
  end

endmodule
