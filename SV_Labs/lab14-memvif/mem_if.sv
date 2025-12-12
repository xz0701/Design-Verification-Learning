interface mem_if(input logic clk);

  // DUT Signals
  logic read;
  logic write;
  logic [4:0] addr;
  logic [7:0] data_in;
  logic [7:0] data_out;

  // Write Memory Task
  task automatic write_mem(
      input logic [4:0] wr_addr,
      input logic [7:0] wr_data,
      input bit debug = 0
  );
    // Testbench drives on negedge → safe
    @(negedge clk);
    addr     = wr_addr;
    data_in  = wr_data;
    read     = 0;
    write    = 1;

    @(posedge clk);
    write    = 0;

    if (debug)
      $display("[%0t] WRITE : addr=%0d data=%0h", $time, wr_addr, wr_data);
  endtask : write_mem

  // Read Memory Task
  task automatic read_mem(
      input  logic [4:0] rd_addr,
      output logic [7:0] rd_data,
      input  bit debug = 0
  );
    @(negedge clk);
    addr  = rd_addr;
    read  = 1;
    write = 0;

    @(posedge clk);
    #1 rd_data = data_out;  // Allow data_out to settle
    read  = 0;

    if (debug)
      $display("[%0t] READ  : addr=%0d data=%0h", $time, rd_addr, rd_data);
  endtask : read_mem

  // Modports
  modport DUT  (
      input  clk, read, addr, data_in,
      output data_out
  );

  modport TEST (
      input  clk, data_out,
      output read, write, addr, data_in,
      import write_mem, read_mem
  );

endinterface : mem_if
