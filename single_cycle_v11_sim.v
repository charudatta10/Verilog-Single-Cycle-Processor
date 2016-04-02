// single_cycle.v
// ver 11.0 (simulation)
// VE370 Project #2

// Due: 
// Report & Source code due Nov 27 23:00 through Sakai
// Demonstration is due by 4:00pm, November 27, 2015

// Created by Hua Xing, Junqi Qian, Xinyue Ou on 11/12/15
// Copyright (c) 2015. All rights reserved.

// Version History
// ver 1.0: single cycle highest-level program; module I/O defined
// ver 2.0: added clock-divider and SSD output. SSD outputs PC or reg file content.
// ver 3.0: all module implementation complete. Passed Xilinx synthesis. No error. Tons of warnings.
// ver 4.0: debug complete. FPGA implementation complete.
// ver 5.0: simulation test bench complete
// ver 6.0: improve test bench
// ver 7.0: test bench running time lifted
// ver 8.0: expanded PC width to 7 bits (5 bit + 2 bit offset). I-MEM now supports 2^5 = 32 lines.
// ver 9.0: I-MEM loads 32 lines of instructions
// ver 10.0: modified 9.0 for FPGA demo
// ver 11.0 update the alu control to accomodate andi; this is a version for demostrationmo code
// ver 11.0_sim: modified 10.0 for simulaiton purposes

`timescale 1ns / 1ps

module single_cycle (clkFast, reset, SwitchSelector, switchRun, Cathode, AN, LEDIndicator, reg_read_data_1);
	input clkFast, reset;		// clkFast (5m[6] Hz) feeds clock divider
	input switchRun;			// decide run(1) or check reg file(0)
	input [4:0] SwitchSelector;	// select $0 to $31 for output
	output [6:0] Cathode;		// SSD
	output [3:0] AN;
	output LEDIndicator;		// output clkNormal for user reference
	output [31:0] reg_read_data_1; // moved here for simulation

	// PC signals
	wire [7:0] PC_in, PC_out;
	wire [31:0] PC_original, PC_out_unsign_extended, PC_plus4;
	// I-MEM signals
	wire [31:0] instruction;
	// Register File signals
	wire [4:0] reg_write_addr;
	wire [31:0] reg_write_data, reg_read_data_2; // reg_read_data_1 moved to output for simulation
	// D-MEM signals
	wire [7:0] D_MEM_addr;
	wire [31:0] D_MEM_read_data;
	// control signals
	wire RegDst, Jump, Branch, MemRead, MemtoReg, MemWrite, ALUSrc, RegWrite;
	wire [1:0] ALUOp;
	wire [3:0] ALU_control_out;
	// branch
	wire [31:0] extended_immidiate;
	wire [31:0] shifted_immidiate;
	wire [31:0] Branch_out;
	wire [31:0] Branch_result;
	wire Branch_decided, zero;
	// jump
	wire [27:0] jump_base28;
	wire [31:0] jump_addr;
	// ALU
	wire [31:0] ALU_inB, ALU_out;
	// SSD display & clock slow-down
	wire clkSSD, clkNormal, clkRF, clk;
		// clkFast: 5m Hz
		// clkSSD: 500 Hz for ring counter
		// clkNormal: 1 Hz
    wire  [3:0] tho; // Binary-Coded-Decimal 0-15
	wire  [3:0] hun;
	wire  [3:0] ten;
	wire  [3:0] one;
    wire  [6:0] thossd;
	wire  [6:0] hunssd;
	wire  [6:0] tenssd;
	wire  [6:0] onessd;	
	// multi-purpose I-MEM read_addr_1
	wire [4:0] multi_purpose_read_addr;
	wire multi_purpose_RegWrite;

	// reg to resolve always block technicals
	reg clkRF_reg, clk_reg, multi_purpose_RegWrite_reg;
	reg [4:0] multi_purpose_read_addr_reg;
	reg [3:0] tho_reg, hun_reg, ten_reg, one_reg;

	assign D_MEM_addr = ALU_out[7:0];
	assign PC_in = PC_original[7:0];
	assign PC_out_unsign_extended = {26'b0000_0000_0000_0000_0000_0000, PC_out}; // from 7 bits to 32 bits
	assign jump_addr = {PC_plus4[31:28], jump_base28}; // jump_addr = (PC+4)[31:28] joined with jump_base28[27:0]
	// output processor clock (1 Hz or freeze) to a LED
	assign LEDIndicator = clk;

	Program_Counter Unit1 (.clk(clk), .reset(reset), .PC_in(PC_in), .PC_out(PC_out));
	Instruction_Memory Unit2 (.read_addr(PC_out), .instruction(instruction), .reset(reset));
	Register_File Unit3 (.read_addr_1(multi_purpose_read_addr), .read_addr_2(instruction[20:16]), .write_addr(reg_write_addr), .read_data_1(reg_read_data_1), .read_data_2(reg_read_data_2), .write_data(reg_write_data), .RegWrite(multi_purpose_RegWrite), .clk(clkRF), .reset(reset));
	Data_Memory Unit4 (.addr(D_MEM_addr), .write_data(reg_read_data_2), .read_data(D_MEM_read_data), .clk(clk), .reset(reset), .MemRead(MemRead), .MemWrite(MemWrite));
	Control Unit5 (.OpCode(instruction[31:26]), .RegDst(RegDst), .Jump(Jump), .Branch(Branch), .MemRead(MemRead), .MemtoReg(MemtoReg), .ALUOp(ALUOp), .MemWrite(MemWrite), .ALUSrc(ALUSrc), .RegWrite(RegWrite));
	ALUControl Unit6 (.ALUOp(ALUOp), .funct(instruction[5:0]), .out_to_ALU(ALU_control_out));
	Sign_Extension Unit7 (.sign_in(instruction[15:0]), .sign_out(extended_immidiate));
	Shift_Left_2_Branch Unit8 (.shift_in(extended_immidiate), .shift_out(shifted_immidiate));
	Shift_Left_2_Jump Unit9 (.shift_in(instruction[25:0]), .shift_out(jump_base28));
	Mux_N_bit #(5) Unit10 (.in0(instruction[20:16]), .in1(instruction[15:11]), .mux_out(reg_write_addr), .control(RegDst));
	Mux_N_bit #(32) Unit11 (.in0(reg_read_data_2), .in1(extended_immidiate), .mux_out(ALU_inB), .control(ALUSrc));
	Mux_N_bit #(32) Unit12 (.in0(ALU_out), .in1(D_MEM_read_data), .mux_out(reg_write_data), .control(MemtoReg));
	Mux_N_bit #(32) Unit13 (.in0(PC_plus4), .in1(Branch_out), .mux_out(Branch_result), .control(Branch_decided));
	Mux_N_bit #(32) Unit14 (.in0(Branch_result), .in1(jump_addr), .mux_out(PC_original), .control(Jump));
	ALU Unit15 (.inA(reg_read_data_1), .inB(ALU_inB), .alu_out(ALU_out), .zero(zero), .control(ALU_control_out));
	ALU_add_only Unit16 (.inA(PC_out_unsign_extended), .inB(32'b0100), .add_out(PC_plus4)); // PC + 4
	ALU_add_only Unit17 (.inA(PC_plus4), .inB(shifted_immidiate), .add_out(Branch_out));
	and (Branch_decided, zero, Branch);

	// SSD Display
	divide_by_100k Unit_Clock500HZ (.clock(clkFast), .reset(reset), .clock_out(clkSSD));
	divide_by_500  Unit_Clock1HZ (.clock(clkSSD), .reset(reset), .clock_out(clkNormal));
	Ring_4_counter Unit_Ring_Counter (.clock(clkSSD), .reset(reset), .Q(AN));
	ssd_driver	Unit_SSDTHO (.in_BCD(tho), .out_SSD(thossd));
	ssd_driver	Unit_SSDHUN (.in_BCD(hun), .out_SSD(hunssd));
	ssd_driver	Unit_SSDTEN (.in_BCD(ten), .out_SSD(tenssd));
	ssd_driver	Unit_SSDONE (.in_BCD(one), .out_SSD(onessd));
	choose_chathode Unit_CHOOSE (.tho(thossd), .hun(hunssd), .ten(tenssd), .one(onessd), .AN(AN), .CA(Cathode));

	assign clkRF = clkRF_reg;
	assign clk = clk_reg;
	assign multi_purpose_read_addr = multi_purpose_read_addr_reg;
	assign multi_purpose_RegWrite = multi_purpose_RegWrite_reg;
	assign tho = tho_reg;
	assign hun = hun_reg;
	assign ten = ten_reg;
	assign one = one_reg;

	always @(switchRun or clkSSD) begin
		if (switchRun) begin
			// sys status 1: run single-cycle processor
			clkRF_reg <= clkNormal;	// 1 Hz
			clk_reg <= clkNormal;		// 1 Hz
			multi_purpose_read_addr_reg <= instruction[25:21]; // reg-file-port1 reads from instruction
			// reg-file protection measure; explained in "else"
			multi_purpose_RegWrite_reg <= RegWrite;
			// output PC to SSD, but since PC only has 6 bits
			tho_reg <= PC_out_unsign_extended[15:12];	// always 0
			hun_reg <= PC_out_unsign_extended[11:8];	// always 0
			ten_reg <= PC_out_unsign_extended[7:4];
			one_reg <= PC_out_unsign_extended[3:0];
		end
		else begin
			// sys status 2: pause processor; inspect Reg File content
			clkRF_reg <= clkSSD;	// 500 Hz
			clk_reg <= 1'b0;		// freeze at 0
			multi_purpose_read_addr_reg <= SwitchSelector; // reg-file-port1 reads from SwitchSelector
			// Reg-file is not freezed in time, this protects against RF-data-overwrite
			multi_purpose_RegWrite_reg <= 1'b0;
			// output reg file content to SSD, but only the lower 16 bits (we only have 4 SSD)
			tho_reg <= reg_read_data_1[15:12];
			hun_reg <= reg_read_data_1[11:8];
			ten_reg <= reg_read_data_1[7:4];
			one_reg <= reg_read_data_1[3:0];
		end
	end
endmodule

// rising-edge synchronous program counter
// output range: decimal 0 to 63 (== I-MEM height)
// data I/O width: 64 = 2^6. Actually, 32 = 2^5; 5+2 offset = 7 bits
// async reset: set program counter to 0 asynchronously
module Program_Counter (clk, reset, PC_in, PC_out);
	input clk, reset;
	input [7:0] PC_in;
	output [7:0] PC_out;
	reg [7:0] PC_out;
	always @ (posedge clk or posedge reset)
	begin
		if(reset==1'b1)
			PC_out<=0;
		else
			PC_out<=PC_in;
	end
endmodule

// async read I-MEM
// height: 64, width: 32 bits (as required by TA)
// PC input width: 32 = 2^5 + 2 offset = 7 bits
// instruction output width: 32 bits (== I-MEM width)
// async reset: as specified in document "Project Two Specification (V3)", 
// 		  		first reset all to 0, then hard-code instructions
module Instruction_Memory (read_addr, instruction, reset);
	input reset;
	input [7:0] read_addr;
	output [31:0] instruction;
	reg [31:0] Imemory [63:0];
	integer k;
	// I-MEM in this case is addressed by word, not by byte
	wire [5:0] shifted_read_addr;
	assign shifted_read_addr=read_addr[7:2];
	assign instruction = Imemory[shifted_read_addr];

	always @(posedge reset)
	begin

		for (k=30; k<64; k=k+1) begin// here Ou changes k=0 to k=16
			Imemory[k] = 32'b0;
		end
					
		Imemory[0] = 32'b00100000000010000000000000100000; //addi $t0, $zero, 32 
		Imemory[1] = 32'b00100000000010010000000000110111; //addi $t1, $zero, 55 
		Imemory[2] = 32'b00000001000010011000000000100100; //and $s0, $t0, $t1 
		Imemory[3] = 32'b00000001000010011000000000100101; //or $s0, $t0, $t1 
		Imemory[4] = 32'b10101100000100000000000000000100; //sw $s0, 4($zero) 
		Imemory[5] = 32'b10101100000010000000000000001000; //sw $t0, 8($zero) 
		Imemory[6] = 32'b00000001000010011000100000100000; //add $s1, $t0, $t1 
		Imemory[7] = 32'b00000001000010011001000000100010; //sub $s2, $t0, $t1 
		Imemory[8] = 32'b00010010001100100000000000001001; //beq $s1, $s2, error0 
		Imemory[9] = 32'b10001100000100010000000000000100; //lw $s1, 4($zero) 
		Imemory[10]= 32'b00110010001100100000000001001000; //andi $s2, $s1, 48 
		Imemory[11] =32'b00010010001100100000000000001001; //beq $s1, $s2, error1 
		Imemory[12] =32'b10001100000100110000000000001000; //lw $s3, 8($zero) 
		Imemory[13] =32'b00010010000100110000000000001010; //beq $s0, $s3, error2 
		Imemory[14] =32'b00000010010100011010000000101010; //slt $s4, $s2, $s1 (Last) 
		Imemory[15] =32'b00010010100000000000000000001111; //beq $s4, $0, EXIT 
		Imemory[16] =32'b00000010001000001001000000100000; //add $s2, $s1, $0 
		Imemory[17] =32'b00001000000000000000000000001110; //j Last
		Imemory[18] =32'b00100000000010000000000000000000; //addi $t0, $0, 0(error0) 
		Imemory[19] =32'b00100000000010010000000000000000; //addi $t1, $0, 0 
		Imemory[20] =32'b00001000000000000000000000011111; //j EXIT
		Imemory[21] =32'b00100000000010000000000000000001; //addi $t0, $0, 1(error1) 
		Imemory[22] =32'b00100000000010010000000000000001; //addi $t1, $0, 1 
		Imemory[23] =32'b00001000000000000000000000011111; //j EXIT
		Imemory[24] =32'b00100000000010000000000000000010; //addi $t0, $0, 2(error2) 
		Imemory[25] =32'b00100000000010010000000000000010; //addi $t1, $0, 2 
		Imemory[26] =32'b00001000000000000000000000011111; //j EXIT
		Imemory[27] =32'b00100000000010000000000000000011; //addi $t0, $0, 3(error3) 
		Imemory[28] =32'b00100000000010010000000000000011; //addi $t1, $0, 3 
		Imemory[29] =32'b00001000000000000000000000011111; //j EXIT
			
	end
endmodule

// sync register file (write/read occupy half cycle each)
// height: 32 (from $0 to $ra), width: 32 bits
// write: on rising edge; data width 32 bit; address width 5 bit
// read: on falling edge; data width 32 bit; address width 5 bit
// control: write on rising edge if (RegWrite == 1)
// async reset: set all register content to 0
module Register_File (read_addr_1, read_addr_2, write_addr, read_data_1, read_data_2, write_data, RegWrite, clk, reset);
	input [4:0] read_addr_1, read_addr_2, write_addr;
	input [31:0] write_data;
	input clk, reset, RegWrite;
	output [31:0] read_data_1, read_data_2;

	reg [31:0] Regfile [31:0];
	integer k;
	
	assign read_data_1 = Regfile[read_addr_1];
	assign read_data_2 = Regfile[read_addr_2];

	always @(posedge clk or posedge reset) // Ou combines the block of reset into the block of posedge clk
	begin
		if (reset==1'b1)
		begin
			for (k=0; k<32; k=k+1) 
			begin
				Regfile[k] = 32'b0;
			end
		end 
		
		else if (RegWrite == 1'b1) Regfile[write_addr] = write_data; 
	end
	


endmodule

// rising edge sync-write, async-read D-MEM
// height: 64, width: 32 bits (from document "Project Two Specification (V3)")
// address input: 6 bits (64 == 2^6)
// data input/output: 32 bits
// write: on rising edge, when (MemWrite == 1)
// read: asynchronous, when (MemRead == 1)
module Data_Memory (addr, write_data, read_data, clk, reset, MemRead, MemWrite);
	input [7:0] addr;
	input [31:0] write_data;
	output [31:0] read_data;
	input clk, reset, MemRead, MemWrite;
	reg [31:0] DMemory [63:0];
	integer k;
	wire [5:0] shifted_addr;
	assign shifted_addr=addr[7:2];
	assign read_data = (MemRead) ? DMemory[addr] : 32'bx;

	always @(posedge clk or posedge reset)// Ou modifies reset to posedge
	begin
		if (reset == 1'b1) 
			begin
				for (k=0; k<64; k=k+1) begin
					DMemory[k] = 32'b0;
				end
			end
		else
			if (MemWrite) DMemory[addr] = write_data;
	end
endmodule

// async control signal generation unit based on OpCode
// as specified in Fig 4.22
// attached in email as file "Fig 4_22 Single Cycle Control"
// input: 6 bits OpCode
// output: all 1 bit except ALUOp which is 2-bits wide
module Control (OpCode, RegDst, Jump, Branch, MemRead, MemtoReg, ALUOp, MemWrite, ALUSrc, RegWrite);
	input [5:0] OpCode;
	output RegDst, Jump, Branch, MemRead, MemtoReg, MemWrite, ALUSrc, RegWrite;
	output [1:0] ALUOp;

	assign RegDst=(~OpCode[5])&(~OpCode[4])&(~OpCode[3])&(~OpCode[2])&(~OpCode[1])&(~OpCode[0]);//000000
	assign Jump=(~OpCode[5])&(~OpCode[4])&(~OpCode[3])&(~OpCode[2])&(OpCode[1])&(~OpCode[0]);//000010
	assign Branch=(~OpCode[5])&(~OpCode[4])&(~OpCode[3])&(OpCode[2])&(~OpCode[1])&(~OpCode[0]);//000100
	assign MemRead=(OpCode[5])&(~OpCode[4])&(~OpCode[3])&(~OpCode[2])&(OpCode[1])&(OpCode[0]);//100011
	assign MemtoReg=(OpCode[5])&(~OpCode[4])&(~OpCode[3])&(~OpCode[2])&(OpCode[1])&(OpCode[0]);//100011
	assign MemWrite=(OpCode[5])&(~OpCode[4])&(OpCode[3])&(~OpCode[2])&(OpCode[1])&(OpCode[0]);//101011
	assign ALUSrc=((~OpCode[5])&(~OpCode[4])&(OpCode[3])&(~OpCode[2])&(~OpCode[1])&(~OpCode[0])) | ((~OpCode[5])&(~OpCode[4])&(OpCode[3])&(OpCode[2])&(~OpCode[1])&(~OpCode[0])) | ((OpCode[5])&(~OpCode[4])&(~OpCode[3])&(~OpCode[2])&(OpCode[1])&(OpCode[0])) | (((OpCode[5])&(~OpCode[4])&(OpCode[3])&(~OpCode[2])&(OpCode[1])&(OpCode[0]))); //001000,001100,100011,101011
	assign RegWrite=(~OpCode[5])&(~OpCode[4])&(~OpCode[3])&(~OpCode[2])&(~OpCode[1])&(~OpCode[0]) | ((~OpCode[5])&(~OpCode[4])&(OpCode[3])&(~OpCode[2])&(~OpCode[1])&(~OpCode[0])) | ((~OpCode[5])&(~OpCode[4])&(OpCode[3])&(OpCode[2])&(~OpCode[1])&(~OpCode[0])) | ((OpCode[5])&(~OpCode[4])&(~OpCode[3])&(~OpCode[2])&(OpCode[1])&(OpCode[0]));//000000,001000,001100,100011
	assign ALUOp[1]=((~OpCode[5])&(~OpCode[4])&(~OpCode[3])&(~OpCode[2])&(~OpCode[1])&(~OpCode[0]))|((~OpCode[5])&(~OpCode[4])&(OpCode[3])&(OpCode[2])&(~OpCode[1])&(~OpCode[0]));//000000, 001100(andi)
	assign ALUOp[0]= ((~OpCode[5])&(~OpCode[4])&(~OpCode[3])&(OpCode[2])&(~OpCode[1])&(~OpCode[0]))|((~OpCode[5])&(~OpCode[4])&(OpCode[3])&(OpCode[2])&(~OpCode[1])&(~OpCode[0]));//000100,001100(andi)
endmodule

// async control to generate ALU input signal
// as specified in Fig 4.12
// attached in email as file "Fig 4_12 ALU Control Input"
// input: 2-bit ALUOp control signal and 6-bit funct field from instruction
// output: 4-bit ALU control input
module ALUControl (ALUOp, funct, out_to_ALU);
	input [1:0] ALUOp;
	input [5:0] funct;
	output [3:0] out_to_ALU;

	assign out_to_ALU[3]=0;
	assign out_to_ALU[2]=((~ALUOp[1])&(ALUOp[0])) | ((ALUOp[1])&(~ALUOp[0])&(~funct[3])&(~funct[2])&(funct[1])&(~funct[0])) | ((ALUOp[1])&(~ALUOp[0])&(funct[3])&(~funct[2])&(funct[1])&(~funct[0]));
	assign out_to_ALU[1]=((~ALUOp[1])&(~ALUOp[0]))|((~ALUOp[1])&(ALUOp[0])) | ((ALUOp[1])&(~ALUOp[0])&(~funct[3])&(~funct[2])&(~funct[1])&(~funct[0])) | ((ALUOp[1])&(~ALUOp[0])&(~funct[3])&(~funct[2])&(funct[1])&(~funct[0]))|((ALUOp[1])&(~ALUOp[0])&(funct[3])&(~funct[2])&(funct[1])&(~funct[0]));
	assign out_to_ALU[0]=((ALUOp[1])&(~ALUOp[0])&(~funct[3])&(funct[2])&(~funct[1])&(funct[0]))|((ALUOp[1])&(~ALUOp[0])&(funct[3])&(~funct[2])&(funct[1])&(~funct[0]));	
endmodule

// sign-extend the 16-bit input to the 32_bit output
module Sign_Extension (sign_in, sign_out);
	input [15:0] sign_in;
	output [31:0] sign_out;
	assign sign_out[15:0]=sign_in[15:0];
	assign sign_out[31:16]=sign_in[15]?16'b1111_1111_1111_1111:16'b0;
endmodule

// shift-left-2 for branch instruction
// input width: 32 bits
// output width: 32 bits
// fill the void with 0 after shifting
module Shift_Left_2_Branch (shift_in, shift_out);
	input [31:0] shift_in;
	output [31:0] shift_out;
	assign shift_out[31:0]={shift_in[29:0],2'b00};
endmodule

// shift-left-2 for jump instruction
// input width: 26 bits
// output width: 28 bits
// fill the void with 0 after shifting
// we don't need to shift in this case, becasue the address of the instructions
// are addressed by words
module Shift_Left_2_Jump (shift_in, shift_out);
	input [25:0] shift_in;
	output [27:0] shift_out;
	assign shift_out[27:0]={shift_in[25:0],2'b00};
endmodule

// N-bit 2-to-1 Mux
// input: 2 N-bit input
// output: 1 N-bit output
// control: 1 bit
// possible value of N in single cycle: 5, 6, 32
module Mux_N_bit (in0, in1, mux_out, control);
	parameter N = 32;
	input [N-1:0] in0, in1;
	output [N-1:0] mux_out;
	input control;
	assign mux_out=control?in1:in0;
endmodule

// 32-bit ALU
// data input width: 2 32-bit
// data output width: 1 32-bit and one "zero" output
// control: 4-bit
// zero: output 1 if all bits of data output is 0
// as specified in Fig 4.12
// attached in email as "Fig 4_12 ALU Control Input"
module ALU (inA, inB, alu_out, zero, control);
	input [31:0] inA, inB;
	output [31:0] alu_out;
	output zero;
	reg zero;
	reg [31:0] alu_out;
	input [3:0] control;
	always @ (control or inA or inB)
	begin
		case (control)
		4'b0000:begin zero<=0; alu_out<=inA&inB; end
		4'b0001:begin zero<=0; alu_out<=inA|inB; end
		4'b0010:begin zero<=0; alu_out<=inA+inB; end
		4'b0110:begin if(inA==inB) zero<=1; else zero<=0; alu_out<=inA-inB; end
		4'b0111:begin zero<=0; if(inA-inB>=32'h8000_0000) alu_out<=32'b1; else alu_out<=32'b0; end// how to implement signed number
		default: begin zero<=0; alu_out<=inA; end
		endcase
	end
endmodule

// 32-bit ALU for addition only
// data input width: 2 32-bit
// data output width: 1 32-bit, no "zero" output
// control: no control input, only addition operation implemeneted
// as specified in Fig 4.12
// attached in email as "Fig 4_12 ALU Control Input"
module ALU_add_only (inA, inB, add_out);
	input [31:0] inA, inB;
	output [31:0] add_out;
	assign add_out=inA+inB;
endmodule

module Dff_asy (q, d, clk, rst);
	input d, clk, rst;
	output reg q;
	
	always @ (posedge clk or posedge rst)
		if (rst == 1) q <= 0;
		else q <= d;
endmodule

// The following modules implement SSD display & clock slow-down
module divide_by_500 (clock, reset, clock_out); // modified to divide-by-4 for simulation
	parameter N = 9;
	input 	clock, reset;
	wire		load, asyclock_out;
	wire 		[N-1:0] Dat;
	output 	clock_out;
	reg 		[N-1:0] Q;
	assign	Dat = 9'b000000000;
	assign	load = Q[1] & Q[0]; // modified to load = 3 (DEC) for simulation
	always @ (posedge reset or posedge clock)
	begin
		if (reset == 1'b1) Q <= 9'b000000000;
		else if (load == 1'b1) Q <= Dat;
		else Q <= Q + 1;
	end
	assign	asyclock_out = load;
	Dff_asy Unit_Dff (.q(clock_out), .d(asyclock_out), .clk(clock), .rst(reset));
endmodule

module divide_by_100k (clock, reset, clock_out); // modified to divide-by-4 for simulation
	parameter N = 17;
	input	clock, reset;
	wire	load, asyclock_out;
	wire 	[N-1:0] Dat;
	output 	clock_out;
	reg 	[N-1:0] Q;
	assign	Dat = 0;
	assign	load = Q[1] & Q[0]; // modified to load = 3 (DEC) for simulation
	always @ (posedge reset or posedge clock)
	begin
		if (reset == 1'b1) Q <= 0;
		else if (load == 1'b1) Q <= Dat;
		else Q <= Q + 1;
	end
	assign	asyclock_out = load;
	Dff_asy Unit_Dff (.q(clock_out), .d(asyclock_out), .clk(clock), .rst(reset));
endmodule

module Ring_4_counter(clock, reset, Q);
	input 		clock, reset;
	output reg	[3:0]Q;
	
	always @(posedge clock or posedge reset)
	begin
		if (reset == 1) Q <= 4'b1110;
		else
		begin
			Q[3] <= Q[0];
			Q[2] <= Q[3];
			Q[1] <= Q[2];
			Q[0] <= Q[1];
		end
	end
endmodule

module ssd_driver (in_BCD, out_SSD);
	input [3:0] in_BCD; // input in Binary-Coded Decimal
	output [6:0] out_SSD; // output to Seven-Segment Display
	reg [6:0] out_SSD;
	always @(in_BCD) begin
		case (in_BCD)
		0:out_SSD=7'b0000001;
		1:out_SSD=7'b1001111;
		2:out_SSD=7'b0010010;
		3:out_SSD=7'b0000110;
		4:out_SSD=7'b1001100;
		5:out_SSD=7'b0100100;
		6:out_SSD=7'b0100000;
		7:out_SSD=7'b0001111;
		8:out_SSD=7'b0000000;
		9:out_SSD=7'b0000100;
		10:out_SSD=7'b0001000;
		11:out_SSD=7'b1100000;
		12:out_SSD=7'b0110001;
		13:out_SSD=7'b1000010;
		14:out_SSD=7'b0110000;
		15:out_SSD=7'b0111000;
			default out_SSD = 7'b1111111; // no ssd
		endcase
	end
endmodule

module choose_chathode(tho, hun, ten, one, AN, CA);
	input	[6:0]tho;
	input	[6:0]hun;
	input	[6:0]ten;
	input	[6:0]one;
	input	[3:0]AN;
	output	[6:0]CA;
	assign CA = (AN==4'b1110) ? one : 7'bzzzzzzz,
		   CA =	(AN==4'b1101) ? ten : 7'bzzzzzzz,
		   CA = (AN==4'b1011) ? hun : 7'bzzzzzzz,
		   CA =	(AN==4'b0111) ? tho : 7'bzzzzzzz;
endmodule

`timescale 1ns / 1ps

module test_bench;

	reg clkFast;
	reg reset;
	reg [4:0] SwitchSelector;
	reg switchRun;
	reg clkread;
	
	integer count;


	// Outputs
	wire [31:0]reg_read_data_1;
		
	// Instantiate the Unit Under Test (UUT)
	single_cycle uut (
		.clkFast(clkFast), 
		.reset(reset),
		.SwitchSelector(SwitchSelector),
		.switchRun(switchRun),
		.reg_read_data_1(reg_read_data_1));

	initial begin
		// Initialize Inputs
		count = 0;
		clkFast = 0;
		reset = 1;
		switchRun = 0;
		SwitchSelector = 5'd0;
		clkread = 0;
		#4 reset=0;
		#3000;
		#50 $stop;
	end

	always begin #1 clkFast=~clkFast; end
	always begin #200 clkread = ~clkread; end 
	
	always @(posedge clkread)
	begin
		$display ("Time: %d", count);
	  			SwitchSelector = 5'd16;
	  		#10 $display ("[$s0] = %h", reg_read_data_1);
	  			SwitchSelector = 5'd17;
	  		#10 $display ("[$s1] = %h", reg_read_data_1);
	  			SwitchSelector = 5'd18;
	  		#10 $display ("[$s2] = %h", reg_read_data_1);
				SwitchSelector = 5'd19;
	  		#10 $display ("[$s3] = %h", reg_read_data_1);
	  			SwitchSelector = 5'd20;
	  		#10 $display ("[$s4] = %h", reg_read_data_1);
	  			SwitchSelector = 5'd21;
	  		#10 $display ("[$s5] = %h", reg_read_data_1);
	  			SwitchSelector = 5'd22;
	  		#10 $display ("[$s6] = %h", reg_read_data_1);
	  			SwitchSelector = 5'd23;
	  		#10 $display ("[$s7] = %h", reg_read_data_1);
	  			SwitchSelector = 5'd8;
	  		#10 $display ("[$t0] = %h", reg_read_data_1);
	  			SwitchSelector = 5'd9;
	  		#10 $display ("[$t1] = %h", reg_read_data_1);
	  			SwitchSelector = 5'd10;
	  		#10 $display ("[$t2] = %h", reg_read_data_1);
	  			SwitchSelector = 5'd11;
	  		#10 $display ("[$t3] = %h", reg_read_data_1);
	  			SwitchSelector = 5'd12;
	  		#10 $display ("[$t4] = %h", reg_read_data_1);
	  			SwitchSelector = 5'd13;
	  		#10 $display ("[$t5] = %h", reg_read_data_1);
	  			SwitchSelector = 5'd14;
	  		#10 $display ("[$t6] = %h", reg_read_data_1);
	  			SwitchSelector = 5'd15;
	  		#10 $display ("[$t7] = %h", reg_read_data_1);
	  			SwitchSelector = 5'd24;
	  		#10 $display ("[$t8] = %h", reg_read_data_1);
	  			SwitchSelector = 5'd25;
	  		#10 $display ("[$t9] = %h", reg_read_data_1);
			
			#2 switchRun = 1;
			#32 switchRun = 0;
			count = count + 1;
						
	end

	
endmodule


