module controller(
    input logic clk,
    input logic rst_,
    input logic zero,
    input logic [2:0] opcode,
    output logic mem_rd,
    output logic load_ir,
    output logic halt,
    output logic inc_pc,
    output logic load_ac,
    output logic load_pc,
    output logic mem_wr
);
    import typedefs::*;
    timeunit 1ns;
    timeprecision 1ps;

    state_t state, next_state;

    always_ff @( posedge clk or negedge rst_ ) begin : State_ctrl
        if (~rst_)
            state <= INST_ADDR;
        else
            state <= next_state;
    end

    always_comb begin : state_transition
        next_state = state;
        unique case (state)
            INST_ADDR:  next_state = INST_FETCH;
            INST_FETCH: next_state = INST_LOAD;
            INST_LOAD:  next_state = IDLE;
            IDLE:       next_state = OP_ADDR;
            OP_ADDR:    next_state = OP_FETCH;
            OP_FETCH:   next_state = ALU_OP;
            ALU_OP:     next_state = STORE;
            STORE:      next_state = INST_ADDR;
            default:    next_state = INST_ADDR;
        endcase
    end

    always_comb begin : state_output
        mem_rd = 0;
        load_ir = 0;
        halt = 0;
        inc_pc = 0;
        load_ac = 0;
        load_pc = 0;
        mem_wr = 0;
        unique case (state)
            INST_FETCH: mem_rd = 1'b1; 
            INST_LOAD, IDLE: begin
                mem_rd = 1'b1;
                load_ir = 1'b1;
            end
            OP_ADDR: halt = (opcode == HLT);
            OP_FETCH: begin
                if (opcode inside{ADD, AND, XOR, LDA}) 
                    mem_rd = 1'b1;
            end
            ALU_OP: begin
                if (opcode inside{ADD, AND, XOR, LDA}) begin
                    mem_rd = 1'b1;
                    load_ac = 1'b1;
                end
                inc_pc = (opcode == SKZ && zero);
                load_pc = (opcode == JMP);
            end
            STORE: begin
                if (opcode inside{ADD, AND, XOR, LDA}) begin
                    mem_rd = 1'b1;
                    load_ac = 1'b1;
                end
                inc_pc = (opcode == JMP);
                load_pc = (opcode == JMP);
                mem_wr = (opcode == STO);
            end
            default: ;
        endcase
    end
endmodule