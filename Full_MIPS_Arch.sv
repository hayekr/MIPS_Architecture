// Full_MIPS_Arch.sv
// Robert Hayek
// Created November 17, 2021
// A 32-bit MIPS processor with instruction and data memory
//----------------------------------------------------------------//

typedef enum logic [5:0]   {opLW    = 6'b10_0011,
                            opSW    = 6'b10_1011,
                            opRTYPE = 6'b00_0000,
                            opBEQ   = 6'b00_0100,
                            opJ     = 6'b00_0010} opcode;
                            
typedef enum logic [5:0]   {fADD = 6'b10_0000,
                            fSUB = 6'b10_0010,
                            fAND = 6'b10_0100,
                            fOR  = 6'b10_0101,
                            fSLT = 6'b10_1010} functcode;
                            
typedef enum logic [2:0]    {ADD  = 3'b010,
                             SUB  = 3'b110,
                             AND  = 3'b000,
                             OR   = 3'b001,
                             SLT  = 3'b111} ALU_operations;
                                                         
typedef enum logic [8:0]    {RTYPE  = 9'b1_0010_0010,
                             LW     = 9'b0_1111_0000,
                             SW     = 9'b0_1000_1000,
                             BEQ    = 9'b0_0000_0101,
                             J      = 9'b0_0000_0000} control_signals;

module register_file #(parameter N = 5, M = 32)
                     (input logic clk,
                      input logic we3,
                      input logic [N-1:0] a1, a2, a3, 
                      output logic [M-1:0] d1, d2, input logic [M-1:0] d3);

        logic [M-1:0] mem[2**N-1:0];
		
        initial
            begin
              mem[0] = 0;
            end

		always @(posedge clk)
			if (we3) mem[a3] <= d3;
		assign d1 = a1 ? mem[a1] : 0;
		assign d2 = a2 ? mem[a2] : 0;
endmodule

module program_counter (input  logic       clk,
						            input  logic       reset,
						            input  logic [5:0] target_address,
                        output logic [5:0] current_pc,
                        output logic [5:0] next_pc);

	always_ff @(posedge clk)
		if (reset) current_pc <= 6'b0;
		else current_pc <= target_address;

  always_comb
    next_pc = current_pc + 4;
endmodule

module alu #(parameter WIDTH = 32)
            (input  logic [WIDTH-1:0] a, b, 
             input  logic [2:0]       op,
             output logic [WIDTH-1:0] result,
             output logic             zero);
    logic [WIDTH-1:0] d0;
    logic [WIDTH-1:0] d1;
    logic [WIDTH-1:0] d2;
    logic [WIDTH-1:0] d3;
    logic [WIDTH-1:0] bout;

    andN #(WIDTH) andMod(a[WIDTH-1:0], b[WIDTH-1:0], d0[WIDTH-1:0]);
    orN #(WIDTH) orMod(a[WIDTH-1:0], b[WIDTH-1:0], d1[WIDTH-1:0]);
    condinv #(WIDTH) condinvMod(b[WIDTH-1:0], op[2], bout[WIDTH-1:0]);
    adder #(WIDTH) adderMod(a[WIDTH-1:0], bout[WIDTH-1:0], op[2],d2[WIDTH-1:0]);
    assign d3[WIDTH-1:0] = {{(WIDTH-2){1'b0}},d2[WIDTH-1]};
    mux4 #(WIDTH) mux4Mod(d0[WIDTH-1:0], d1[WIDTH-1:0], d2[WIDTH-1:0], d3[WIDTH-1:0], op[1:0], result[WIDTH-1:0]);
    zerodetect #(WIDTH) zeroDetMod(result, zero);
endmodule

module andN #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] a, b,
              output logic [WIDTH-1:0] y);
      assign y = a & b;
endmodule

module orN #(parameter WIDTH = 8)
            (input  logic [WIDTH-1:0] a, b,
             output logic [WIDTH-1:0] y);

  assign y = a | b;
endmodule

module condinv #(parameter WIDTH = 8)
                (input  logic [WIDTH-1:0] a,
                 input  logic             invert,
                 output logic [WIDTH-1:0] y);


always_comb
	if(invert) y = ~a;
	else y = a;

endmodule

module adder #(parameter WIDTH = 8)
              (input  logic [WIDTH-1:0] a, b,
               input  logic             cin,
               output logic [WIDTH-1:0] y);

  assign y = a + b + cin;
endmodule

module mux4 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, d2, d3,
              input  logic [1:0]       s, 
              output logic [WIDTH-1:0] y);

  always_comb
    case (s)
      2'b00: y = d0;
      2'b01: y = d1;
      2'b10: y = d2;
      2'b11: y = d3;
    endcase
endmodule

module mux2 #(parameter WIDTH = 32)
             (input  logic [WIDTH-1:0] d0, d1, 
              input  logic             s, 
              output logic [WIDTH-1:0] y);

  assign y = s ? d1 : d0; 
endmodule

module zerodetect #(parameter WIDTH = 8)
                   (input  logic [WIDTH-1:0] a, 
                    output logic             y);

   logic [WIDTH-1:0] Desired;
   assign Desired = {{(WIDTH-1){1'b0}}};

   always_comb
 	if(a === Desired) y = 1'b1;
	else y = 1'b0;
endmodule  

// Data Memory
module data_memory #(parameter N = 5, M = 8)
                    (input logic clk,
                     input logic re,
                     input logic we,
                     input logic [N-1:0] adr,
                     input logic [4*M-1:0] din,
                     output logic [4*M-1:0] dout);
	logic [M-1:0] mem[2**N-1:0];

	// Initialize the instruction memory
	initial begin
		mem[11] = 8'h00;
    mem[10] = 8'h00;
    mem[9] = 8'h00;
    mem[8] = 8'h0C;
    mem[7] = 8'h00;
    mem[6] = 8'h00;
    mem[5] = 8'h00;
    mem[4] = 8'h03;
    mem[3] = 8'h00;
    mem[2] = 8'h00;
    mem[1] = 8'h00;
    mem[0] = 8'h05;
  end
	always @(posedge clk)
		if(we)
		  {mem[adr+3], mem[adr+2], mem[adr+1], mem[adr]} <= din;
	assign dout = {mem[adr+3], mem[adr+2], mem[adr+1], mem[adr]};
endmodule

module sign_ext (input logic [15:0] a, output logic [31:0] y);
	assign y = {{16{a[15]}}, a[15:0]};
endmodule

module control_unit(input logic  [5:0] op_code, 
                    output logic [8:0] control_sigs);
    always_comb
    	case (op_code)
    		opRTYPE: control_sigs = RTYPE;
    		opLW: control_sigs = LW;
        opSW: control_sigs = SW;
        opBEQ: control_sigs = BEQ;
        opJ: control_sigs = J;
    	endcase                                 
endmodule 

// ALU Control ----------------------------------------
module ALU_control (input logic [1:0] ALUOp, 
                    input logic [5:0] funct,
                    output logic [2:0] ALU_control);
    always_comb
		case (ALUOp)
			2'b00: ALU_control = ADD;
			2'b01: ALU_control = SUB;
			2'b10: case (funct) 
				fADD: ALU_control = ADD;
				fSUB: ALU_control = SUB;
				fAND: ALU_control = AND;
				fOR: ALU_control = OR;
				fSLT: ALU_control = SLT;
        endcase
		endcase
endmodule  

// Target Address ----------------------------------------
module branch_jump_logic(input logic  [31:0]  next_pc,
                         input logic  [31:0]  instruction,
                         input logic  [31:0]  offset_extended,
                         input logic          branch,
                         input logic          zero,
                         output logic [31:0]  target_address
                         );
      logic [5:0] op_code;
      logic [31:0] jump_address, branch_offset, branch_address, branch_seq;
      logic jump, pc_src;

      assign op_code = instruction [31:26];

      always_comb
        begin
          if(op_code == opJ)
            jump = 1;
          else
            jump = 0;
          
          jump_address = {next_pc[31:28], instruction[25:0], 2'b00};
          branch_offset = {offset_extended[29:0], 2'b00};
          branch_address = next_pc + branch_offset;
          pc_src = branch & zero;
        end
      
      mux2 #(32) m1(next_pc, branch_address, pc_src, branch_seq);
      mux2 #(32) m2(branch_seq, jump_address, jump, target_address);
endmodule

// Control Path ----------------------------------------
module control_path(input logic   [31:0]  instruction,
                    input logic   [31:0]  next_pc,
                    input logic   [31:0]  offset_extended,
                    input logic           zero,
                    output logic  [8:0]   control_sigs,
                    output logic  [2:0]   alu_control,
                    output logic  [31:0]  target_address);
      logic [5:0] op_code;
      //logic [8:0] control_sigs;
      logic [1:0] ALUOp;
      logic [5:0] funct;
      //logic [2:0] alu_control;
      logic branch, jump;

      control_unit cu(op_code, control_sigs);
      ALU_control ac(ALUOp, funct, ALU_control);
      branch_jump_logic bjl(branch, jump, zero, instruction, target_address);
endmodule

module instruction_memory #(parameter N = 6, M = 8)
                    (input logic [N-1:0] adr,
                     output logic [4*M-1:0] dout);
        
    logic [M-1:0] mem[2**N-1:0];
    initial
      $readmemh("lab10_instructions.dat", mem);
    
    assign dout = {mem[adr+3], mem[adr+2], mem[adr+1], mem[adr]};                    
     
endmodule 

// Data Path ------------------------------------------
module data_path(input logic          clk,
                 input logic          reset,
                 input logic  [31:0]  instruction,
                 input logic  [31:0]  target_address,
                 input logic  [8:0]   control_sigs,
                 input logic  [2:0]   alu_control,
                 input logic  [31:0]  read_data,
                 output logic [31:0]  next_pc,
                 output logic [31:0]  offset_extended,
                 output logic         zero,
                 output logic [31:0]  current_pc,
                 output logic [31:0]  data_address,
                 output logic [31:0]  write_data,
                 output logic         mem_read, mem_write);

      logic [3:0] readAdr;
      logic [31:0] instruction_output;
      logic [4:0] write_addr;
      logic [31:0] sign_extended;
      logic [31:0] read_data1;
      logic [31:0] read_data2;
      logic [31:0] alu_in2;	
      logic [31:0] alu_output;
      logic [31:0] datamem_read_data;

      program_counter pc(clk, reset, target_address, current_pc, next_pc);

      mux2 #(5) write_address_mux(instruction_output[20:16], instruction_output[15:11], RegDst, write_addr);
      register_file rf(~clk, RegWrite, instruction_output[25:21], instruction_output[20:16], write_addr, read_data1, read_data2, write_data);
      sign_ext se1632(instruction_output[15:0], sign_extended);
      mux2 #(32) read_data_2_mux(read_data2, sign_extended, ALUSrc, alu_in2);
      alu main_alu(read_data1, alu_in2, alu_control, alu_output, Zero);
      data_memory dm(~clk, MemRead, MemWrite, alu_output[4:0], read_data2, datamem_read_data);
      mux2 #(32) dm_read_data_2_mux(alu_output, datamem_read_data, MemtoReg, write_data);
endmodule

// MIPS processor ----------------------------------------
module mips_processor(input logic         clk,
                      input logic         reset,
                      input logic [31:0]  instruction,
                      input logic [31:0]  read_data,
                      output logic [31:0] write_data,
                      output logic [31:0] data_address,
                      output logic [31:0] current_pc,
                      output logic        mem_read, mem_write);
                      
  logic [31:0] target_address, next_pc;
  logic [8:0] control_sigs;
  logic [2:0] alu_control;
  logic [31:0] offset_extended;
  logic zero;
  
  data_path dp (clk, reset, instruction, target_address, control_sigs, alu_control, read_data, next_pc,
                offset_extended, zero, current_pc, data_address, write_data, mem_read, mem_write);
  control_path cp (instruction, next_pc, offset_extended, zero, control_sigs, alu_control, 
                   target_address);             
endmodule

// testbench to test MIPS processor + memories -----------
module testbench_lab10 ();
  logic [31:0] instruction, read_data, write_data, data_address, current_pc;
  logic mem_read, mem_write;
  logic clk, reset;
  
  mips_processor my_mips (clk, reset, instruction, read_data, write_data, 
                          data_address, current_pc, mem_read, mem_write);
                          
  instruction_memory imem (current_pc[5:0], instruction);
  data_memory dmem (~clk, data_address[4:0], mem_read, mem_write, write_data, read_data);
  
  // initialize test
  initial
    begin
      reset <= 1; # 7; reset <= 0;
    end

  // generate clock to sequence tests
  always
    begin
      clk <= 1; # 5; clk <= 0; # 5;
    end

  always@(posedge clk)
    begin
      if(mem_write) begin
        assert(data_address == 8 & write_data == 7) begin
            $display("Simulation of full MIPS Processor for Computer Architecture is successful");
            $display("Value of memory location at address 8 = %h at time %0t",
                    {dmem.mem[11], dmem.mem[10], dmem.mem[9], dmem.mem[8]}, $time);  
        end
        else $error("Simulation failed");
        //$stop;
      end
    end                 
endmodule