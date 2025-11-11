`include "mem.sv"
module mem_test();
    logic clk;
    logic read;
    logic write;
    logic [4:0] addr;
    logic [7:0] data_in;
    logic [7:0] data_out;

    logic [7:0] rd_data;
    int errors;

    mem mem0(
        .clk(clk),
        .read(read),
        .write(write),
        .addr(addr),
        .data_in(data_in),
        .data_out(data_out)
    );

    task automatic write_mem(input logic [4:0] wr_addr, 
                             input logic [7:0] wr_data,
                             input bit debug = 0);
        begin
            @(negedge clk);
            addr = wr_addr;
            data_in = wr_data;
            read = 0;
            write = 1;
            @(posedge clk)
            write = 0;
            if (debug) 
                $display("WRITE: addr = %0d, data = %0h", wr_addr, wr_data);
        end 
    endtask //automatic

    task automatic read_mem(input logic [4:0] rd_addr,
                            output logic [7:0] rd_data,
                            input bit debug = 0);
        begin
            @(negedge clk)
            addr = rd_addr;
            read = 1;
            write = 0;
            @(posedge clk)
            #1 rd_data = data_out;
            read = 0;
            if (debug) 
                $display("READ: addr = %0d, data = %0h", rd_addr, rd_data);
        end
    endtask //automatic

    task automatic clear_mem(ref int errors);
        logic [7:0] rd_val;
        for (int i = 0; i < 32 ; i++) begin
            write_mem(i, 8'h00);
            read_mem(i, rd_val);
            if (rd_val !== 8'h00) begin
                $display("ERROR @%0d: expected 00, got %0h", i, rd_val);
                errors++;
            end
        end
    endtask //automatic

    task automatic comp_data_addr(ref int errors);
        logic [7:0] rd_val;
        for (int i = 0; i < 32 ; i++) begin
            write_mem(i, i[7:0]);
            read_mem(i, rd_val);
            if (rd_val !== i[7:0]) begin
                $display("ERROR @%0d: expected %0h, got %0h", i, i[7:0], rd_val);
                errors++;
            end
        end
    endtask //automatic

    function void print_status(input int errors);
        if (errors == 0) 
            $display("All Memory Tests Passed");
        else
            $display("Memory Test Failed: %0d ERRORS", errors);
        
    endfunction

    always begin
        #5 clk = ~clk;
    end

    initial begin
        clk = 0;        
        errors = 0;
        rd_data = 8'h00;
        read = 0; write = 0; addr = 0; data_in = 0;
        
        repeat(2) @(posedge clk);
        clear_mem(errors);
        comp_data_addr(errors);
        print_status(errors);
        $finish;
    end

    initial begin
        $dumpfile("mem_test.vcd");
        $dumpvars(0);
    end
    
endmodule