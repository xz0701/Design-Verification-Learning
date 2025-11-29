`include "mem_if.sv"
`include "mem.sv"

module mem_test(mem_if.TEST bus);
  logic [7:0] rd_data;
  int errors;

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

  initial begin
    errors = 0;
    bus.read  = 0;
    bus.write = 0;
    bus.addr  = 0;
    bus.data_in = 0;

    repeat (2) @(posedge bus.clk);
    clear_mem(errors);
    comp_data_addr(errors);
    print_status(errors);
    $finish;
  end
endmodule
