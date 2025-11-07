package typedefs;
    typedef enum logic [2:0] {
        HLT = 3'b0;
        SKZ = 3'b001;
        ADD = 3'b010;
        AND = 3'b011;
        XOR = 3'b100;
        LDA = 3'b101;
        STP = 3'b110;
        JMP = 3'b111;
    } opcode_t;
    
    typedef enum logic [7:0] {
        INST_ADDR = 8'b0000_0001, 
        INST_FETCH = 8'b0000_0010, 
        INST_LOAD = 8'b0000_0100, 
        IDLE = 8'b0000_1000, 
        OP_ADR = 8'b0001_0000,
        OP_FETCH = 8'b0010_0000,
        ALU_OP = 8'b0100_0000,
        STORE = 8'b1000_0000
    } state_t;
endpackage