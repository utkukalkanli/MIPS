`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: Alper Karadag, Ziya Erkoc
// 
// Create Date: 03.12.2018 19:22:49
// Design Name: 
// Module Name: pipes
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


//module top  (input   logic 	 clk, reset,                        
//	     output logic [31:0] ALUOut, ResultW, instrOut, WriteDataM,
//	     output logic StallD, StallF, 
//         output logic [31:0] PCF);
         
//    logic [31:0] ReadDataW;    

//    // instantiate processor and memories  
//    mips mips (clk, reset, PCF, ALUOut, ResultW, instrOut, WriteDataM, StallD, StallF);  
//   //  imem imem (PCF[5:0], instr);  
//   //  dmem dmem (clk, we, ALUOut, WriteDataM, ReadDataW);

   

//endmodule

// Define pipes that exist in the PipelinedDatapath. 
// The pipe between Writeback (W) and Fetch (F), as well as Fetch (F) and Decode (D) is given to you.
// Create the rest of the pipes where inputs follow the naming conventions in the book.


module PipeFtoD(input logic[31:0] instr, PcPlus4F,
                input logic EN, clk, reset,		// StallD will be connected as this EN
                output logic[31:0] instrD, PcPlus4D);
    
    always_ff @(posedge clk, posedge reset)begin
        if (reset)begin
            instrD <= 0;
            PcPlus4D <= 0;
        end
        else if(EN)
            begin
            instrD <= instr;
            PcPlus4D <= PcPlus4F;
            end
        else begin
            instrD <= instrD;
            PcPlus4D <= PcPlus4D;
        end
    end
endmodule

// Similarly, the pipe between Writeback (W) and Fetch (F) is given as follows.

module PipeWtoF(input logic[31:0] PC,
                input logic EN, clk, reset,		// StallF will be connected as this EN
                output logic[31:0] PCF);
    
    always_ff @(posedge clk, posedge reset)begin
        if (reset)
            PCF <= 0;
        else if(EN)
            begin
            PCF <= PC;
            end
        else 
            PCF <= PCF;
    end
endmodule

// *******************************************************************************
// Below, you are given the argument lists of the modules PipeDtoE, PipeEtoM, PipeMtoW.
// You should implement them by looking at pipelined processor image given to you.   
// Don't forget that these codes are tested but you can always make changes if you want.
// Note that some output logics there for debugging purposes, in other words to trace their values in simulation.
// *******************************************************************************


module PipeDtoE(input logic clr, clk, reset, RegWriteD, MemtoRegD, MemWriteD,
                input logic[2:0] AluControlD,
                input logic AluSrcD, RegDstD, BranchD,
                input logic[31:0] RD1D, RD2D,
                input logic[4:0] RsD, RtD, RdD,
                input logic[31:0] SignImmD,
                input logic[31:0] PCPlus4D,
                    output logic RegWriteE, MemtoRegE, MemWriteE,
                    output logic[2:0] AluControlE,
                    output logic AluSrcE, RegDstE, BranchE,
                    output logic[31:0] RD1E, RD2E,
                    output logic[4:0] RsE, RtE, RdE,
                    output logic[31:0] SignImmE,
                    output logic[31:0] PCPlus4E);

    always_ff @(posedge clk, posedge reset)begin
        // ******************************************************************************
        // YOUR CODE HERE
        // ******************************************************************************
        if (reset)begin
            RegWriteE <= 0;
            MemtoRegE <= 0;
            MemWriteE <= 0;
            AluControlE <= 0;
            AluSrcE <= 0;
            RegDstE <= 0;
            BranchE <= 0;
            RD1E <= 0;
            RD2E <= 0;
            RsE <= 0;
            RtE <= 0;
            RdE <= 0;
            SignImmE <= 0;
            PCPlus4E <= 0;
        end
        else if(clr)
            begin
            RegWriteE <= 0;
            MemtoRegE <= 0;
            MemWriteE <= 0;
            AluControlE <= 0;
            AluSrcE <= 0;
            RegDstE <= 0;
            BranchE <= 0;
            RD1E <= 0;          
            RD2E <= 0;
            RsE <= 0;
            RtE <= 0;
            RdE <= 0;
            SignImmE <= 0;
            PCPlus4E <= 0;
            end
        else begin
            RegWriteE <= RegWriteD;
            MemtoRegE <= MemtoRegD;
            MemWriteE <= MemWriteD;
            AluControlE <= AluControlD;
            AluSrcE <= AluSrcD;
            RegDstE <= RegDstD;
            BranchE <= BranchD;        
            RD1E <= RD1D;
            RD2E <= RD2D;
            RsE <= RsD;
            RtE <= RtD;
            RdE <= RdD;
            SignImmE <= SignImmD;
            PCPlus4E <= PCPlus4D;
        end        
    end
endmodule

module PipeEtoM(input logic clk, reset, RegWriteE, MemtoRegE, MemWriteE, BranchE, Zero,
                input logic[31:0] ALUOut,
                input logic [31:0] WriteDataE,
                input logic[4:0] WriteRegE,
                input logic[31:0] PCBranchE,
                    output logic RegWriteM, MemtoRegM, MemWriteM, BranchM, ZeroM,
                    output logic[31:0] ALUOutM,
                    output logic [31:0] WriteDataM,
                    output logic[4:0] WriteRegM,
                    output logic[31:0] PCBranchM);
    
    always_ff @(posedge clk, posedge reset) begin
        // ******************************************************************************
        // YOUR CODE HERE
        // ******************************************************************************
        if (reset)begin
            RegWriteM <= 0;
            MemtoRegM <= 0;
            MemWriteM <= 0;
            BranchM <= 0;
            ZeroM <= 0;
            ALUOutM <= 0;
            WriteDataM <= 0;
            WriteRegM <= 0;
            PCBranchM <= 0;
        end 
        else begin
            RegWriteM <= RegWriteE;
            MemtoRegM <= MemtoRegE;
            MemWriteM <= MemWriteE;
            BranchM <= BranchE;
            ZeroM <= Zero;
            ALUOutM <= ALUOut;
            WriteDataM <= WriteDataE;
            WriteRegM <= WriteRegE;
            PCBranchM <= PCBranchE;
        end       
    end
endmodule

module PipeMtoW(input logic clk, reset, RegWriteM, MemtoRegM,
                input logic[31:0] ReadDataM, ALUOutM,
                input logic[4:0] WriteRegM,
                    output logic RegWriteW, MemtoRegW,
                    output logic[31:0] ReadDataW, ALUOutW,
                    output logic[4:0] WriteRegW);

		always_ff @(posedge clk, posedge reset) begin
            // ******************************************************************************
		    // YOUR CODE HERE
            // ******************************************************************************
            if(reset) begin
                RegWriteW <= 0;
                MemtoRegW <= 0;
                ReadDataW <= 0;
                ALUOutW <= 0;
                WriteRegW <= 0;
            end
            else begin
                RegWriteW <= RegWriteM;
                MemtoRegW <= MemtoRegM;
                ReadDataW <= ReadDataM;
                ALUOutW <= ALUOutM;
                WriteRegW <= WriteRegM;               
            end
        end
endmodule



// *******************************************************************************
// End of the individual pipe definitions.
// ******************************************************************************

// *******************************************************************************
// Below is the definition of the datapath.
// The signature of the module is given. The datapath will include (not limited to) the following items:
//  (1) Adder that adds 4 to PC
//  (2) Shifter that shifts SignImmE to left by 2
//  (3) Sign extender and Register file
//  (4) PipeFtoD
//  (5) PipeDtoE and ALU
//  (5) Adder for PCBranchM
//  (6) PipeEtoM and Data Memory
//  (7) PipeMtoW
//  (8) Many muxes
//  (9) Hazard unit
//  ...?
// *******************************************************************************

module datapath (input  logic clk, reset,
		         input logic [31:0] PCF,	
		         input logic RegWriteD, MemtoRegD, MemWriteD,
		         input logic [2:0] ALUControlD,
		         input logic AluSrcD, RegDstD, BranchD,
		             output logic PCSrcM, StallD, StallF,
		             output logic[31:0] PCBranchM, PCPlus4F, instrD, ALUOut, ResultW, WriteDataM); 

	// ********************************************************************
	// Here, define the wires (logics) that are needed inside this pipelined datapath module
    // You are given the wires connecting the Hazard Unit.
    // Notice that StallD and StallF are given as output for debugging
	// ********************************************************************

	logic FlushE;
	logic [1:0] ForwardAE, ForwardBE;		
	// Add necessary wires (logics).
	//logic [31:0] PC;
	logic [31:0] instrF;
	logic [31:0] dataResult;
	logic RegWriteE, MemtoRegE, MemWriteE, ALUSrcE, RegDstE, BranchE;
	logic [2:0] ALUControlE;
	logic RegWriteM, MemtoRegM, MemWriteM;
	logic RegWriteW, MemtoRegW;
	logic Zero, ZeroM, BranchM;
	logic [31:0] PCBranch, SignImmsh;
	logic [31:0] RD1D, RD2D;
	logic [31:0] RD1E, RD2E;
	logic [31:0] PCBranchE;
    logic [31:0] SignImmD, SignImmE, WriteDataE, resultMuxF;
    logic [31:0] PCPlus4D, PCPlus4E; 
    logic [31:0] ALUOutM, ALUOutW;
    logic [31:0] ReadDataW, ReadDataM;
    logic [31:0] SrcAE, SrcBE;
    logic [4:0] RsD, RtD, RdD, RsE, RtE, RdE;
    logic [4:0] WriteRegE, WriteRegM, WriteRegW;
	// ********************************************************************
	// Instantiate the required modules below in the order of the datapath flow.
	// ********************************************************************
	
	assign PCSrcM = ZeroM & BranchM; // YOUR CODE HERE
	assign RsD = instrD[25:21]; // YOUR CODE HERE
    assign RtD = instrD[20:16]; // YOUR CODE HERE
    assign RdD = instrD[15:11]; // YOUR CODE HERE
    assign WriteDataE = resultMuxF; // YOUR CODE HERE  it will be defined later
    
	// Below, PipeFtoD and regfile instantiations are given
    // Add other instantiations
    // BE CAREFUL ABOUT THE ORDER OF PARAMETERS!
	// flopr #(32) pcreg(clk, reset, pcnext, PCounter);
	//mux2 pcmux(PCPlus4F, PCBranchM, PCSrcM, PC);
	
    //PipeWtoF wtf(PC, StallF, clk , reset, PCF );
    HazardUnit hzd(RegWriteW, WriteRegW, RegWriteM, WriteRegM, MemtoRegE, RsE, RtE, RsD, RtD, ForwardAE, ForwardBE,
    FlushE, StallD, StallF);
    
	imem imemm(PCF[5:0], instrF);  
	
    adder pcadd1(PCF, 4, PCPlus4F);
	
	PipeFtoD ftd(instrF, PCPlus4F, ~StallD, clk, reset, instrD, PCPlus4D); 
	
	regfile rf (clk, RegWriteW, RsD, RtD,
            WriteRegW, ResultW, RD1D, RD2D);     
	
	signext se(instrD[15:0], SignImmD);

    PipeDtoE dte(FlushE, clk, reset, RegWriteD, MemtoRegD, MemWriteD, ALUControlD, AluSrcD, RegDstD, BranchD, RD1D, RD2D, RsD, RtD, RdD,
	             SignImmD, PCPlus4D, RegWriteE, MemtoRegE, MemWriteE, ALUControlE, ALUSrcE, RegDstE, BranchE, RD1E, RD2E, RsE, RtE, RdE, SignImmE, PCPlus4E);
	
	mux2 #(5) wregmux(RtE, RdE, RegDstE, WriteRegE);
		             	
    mux4 #(32) srcamux(RD1E, ResultW, ALUOutM, 0, ForwardAE, SrcAE);
    
	mux4 #(32) srcbmuxFirst(RD2E, ResultW, ALUOutM, 0, ForwardBE, resultMuxF); //// ???????*
	
	mux2 #(32) srcbmuxSecond(resultMuxF, SignImmE, ALUSrcE, SrcBE);
	
	alu alu(SrcAE, SrcBE, ALUControlE, ALUOut, Zero, reset);

    sl2 immsh(SignImmE, SignImmsh);
    
    adder pcadd2(SignImmsh, PCPlus4E, PCBranchE);
    
	PipeEtoM etm(clk, reset, RegWriteE, MemtoRegE, MemWriteE, BranchE, Zero, ALUOut, WriteDataE, WriteRegE, PCBranchE, RegWriteM, MemtoRegM, 
	             MemWriteM, BranchM, ZeroM, ALUOutM, WriteDataM, WriteRegM, PCBranchM);
	
	dmem datamem(clk, MemWriteM, ALUOutM, WriteDataM, ReadDataM);
	
	// PipeMtoW mtw(clk, reset, RegWriteM, MemtoRegM, ReadDataM, ALUOutM, WriteRegM, RegWriteW, MemtoRegW, ReadDataW, ALUOutW, WriteRegW );
	PipeMtoW mtw(clk, reset, RegWriteM, MemtoRegM, ReadDataM, ALUOutM, WriteRegM, RegWriteW, MemtoRegW, ReadDataW, ALUOutW, WriteRegW );
   
    mux2 #(32) finalmux(ReadDataW, ALUOutW, MemtoRegW, ResultW);                         
	

endmodule



// Hazard Unit with inputs and outputs named
// according to the convention that is followed on the book.

module HazardUnit( input logic RegWriteW,
                input logic [4:0] WriteRegW,
                input logic RegWriteM,
                input logic [4:0] WriteRegM,
                input logic MemtoRegE,
                input logic [4:0] rsE,rtE,
                input logic [4:0] rsD,rtD,
                output logic [1:0] ForwardAE, ForwardBE,
                output logic FlushE,StallD,StallF);
   
    logic lwstall;
    always_comb begin
        // ********************************************************************
        // Here, write equations for the Hazard Logic.
        // If you have troubles, please study pages ~420-430 in your book.
        // ********************************************************************
        if((rsE != 0) & (rsE == WriteRegM) & RegWriteM)begin
             ForwardAE = 10;
        end
        else begin
            if((rsE != 0) & (rsE == WriteRegW) & RegWriteW)begin
                ForwardAE = 01;
            end
            else begin
                ForwardAE = 00;
            end
        end    
        if((rtE != 0) & (rtE == WriteRegM) & RegWriteM)begin
             ForwardBE = 10;
        end
        else begin
            if((rtE != 0) & (rtE == WriteRegW) & RegWriteW)begin
                ForwardBE = 01;
            end
            else begin
                ForwardBE = 00;
            end
        end

    end

         
    assign lwstall = ((rsD == rtD) | (rtD == rtE)) & MemtoRegE;
    assign StallD = lwstall;
    assign StallF = StallD;
    assign FlushE = StallD;
     
endmodule


module mips (input  logic        clk, reset,
             output logic[31:0]  PCF,
             output logic[31:0]  ALUOut, ResultW,
             output logic[31:0]  instrD, WriteDataM,
             output logic StallD, StallF);

    // ********************************************************************
    // You can change the logics below but if you didn't change the signitures of 
    // above modules you will need these.
    // ********************************************************************

    logic MemtoRegD, zero, AluSrcD, RegDstD, RegWriteD, jump, PCSrcM, BranchD, MemWriteD;
    logic [31:0] PCPlus4F, PCm, PCBranchM;
    logic [2:0] ALUControlD;
    //assign instrOut = instr;
   
	// ********************************************************************
	// Below, instantiate a controller and a datapath with their new (if modified) 
	// signatures and corresponding connections.
    // Also, you might want to instantiate PipeWtoF and pcsrcmux here.
    // Note that this is not the only solution.
    // You can do it in your way as long as it works.
	// *******************************************************************
   	mux2 #(32) pcsrcmux(PCPlus4F, PCBranchM, PCSrcM, PCm);
	
	PipeWtoF pwtf(PCm, ~StallF , clk, reset, PCF);
	
    datapath dp(clk, reset, PCF, RegWriteD, MemtoRegD, MemWriteD, ALUControlD, AluSrcD, RegDstD, BranchD, PCSrcM, StallD, StallF, 
                    PCBranchM, PCPlus4F, instrD, ALUOut, ResultW, WriteDataM); 
                    
    controller c(instrD[31:26], instrD[5:0], MemtoRegD, MemWriteD, AluSrcD, RegDstD, RegWriteD, jump, ALUControlD, BranchD); 
     

endmodule


// External instruction memory used by MIPS single-cycle
// processor. It models instruction memory as a stored-program 
// ROM, with address as input, and instruction as output
// Modify it to test your own programs.

module imem ( input logic [5:0] addr, output logic [31:0] instr);

// imem is modeled as a lookup table, a stored-program byte-addressable ROM
	always_comb
	   case ({addr})		   	// word-aligned fetch
//
// 	***************************************************************************
//	Here, you should paste the test cases that are given to you in lab document.
//  You can write your own test cases and try it as well.
//	Below is the program from the single-cycle lab.
//	***************************************************************************
//

8'h00: instr = 32'h20080007;
8'h04: instr = 32'h20090005;
8'h08: instr = 32'h200a0000;
8'h0c: instr = 32'h210b000f;
8'h10: instr = 32'h01095020;
8'h14: instr = 32'h01095025;
8'h18: instr = 32'h01095024;
8'h1c: instr = 32'h01095022;
8'h20: instr = 32'h0109502a;
8'h24: instr = 32'had280002;
8'h28: instr = 32'h8d090000;
8'h2c: instr = 32'h1100fff5;
8'h30: instr = 32'h200a000a;
8'h34: instr = 32'h2009000c;

8'h38: instr = 32'h20080005;
8'h3c: instr = 32'h21090006;
8'h40: instr = 32'h01285020;

//8'h44: instr = 32'h20080005;
//8'h48: instr = 32'h20090006;
//8'h4c: instr = 32'h20040001;
//8'h50: instr = 32'h20050002;
//8'h54: instr = 32'had280000;
//8'h58: instr = 32'h8d090001;
//8'h5c: instr = 32'h01245020;
//8'h60: instr = 32'h01255022;

//8'h64: instr = 32'h20090002;
//8'h68: instr = 32'h10000002;
//8'h6c: instr = 32'h20090005;
//8'h70: instr = 32'h21290006;
//8'h74: instr = 32'h20090008;
//8'h78: instr = 32'h20040000;
//8'h7c: instr = 32'h20050000;
//8'h80: instr = 32'hac090000;
		
			// j 48, so it will loop here
	     default:  instr = {32{1'bx}};	// unknown address
	   endcase
endmodule


// 	***************************************************************************
//	Below are the modules that you shouldn't need to modify at all..
//	***************************************************************************

module controller(input  logic[5:0] op, funct,
                  output logic     memtoreg, memwrite,
                  output logic     alusrc,
                  output logic     regdst, regwrite,
                  output logic     jump,
                  output logic[2:0] alucontrol,
                  output logic branch);

   logic [1:0] aluop;

   maindec md (op, memtoreg, memwrite, branch, alusrc, regdst, regwrite, 
         jump, aluop);

   aludec  ad (funct, aluop, alucontrol);

endmodule

// External data memory used by MIPS single-cycle processor

module dmem (input  logic        clk, we,
             input  logic[31:0]  a, wd,
             output logic[31:0]  rd);

   logic  [31:0] RAM[63:0];
  
   assign rd = RAM[a[31:2]];    // word-aligned  read (for lw)

   always_ff @(posedge clk)
     if (we)
       RAM[a[31:2]] <= wd;      // word-aligned write (for sw)

endmodule

module maindec (input logic[5:0] op, 
	              output logic memtoreg, memwrite, branch,
	              output logic alusrc, regdst, regwrite, jump,
	              output logic[1:0] aluop );
   logic [8:0] controls;

   assign {regwrite, regdst, alusrc, branch, memwrite,
                memtoreg,  aluop, jump} = controls;

  always_comb
    case(op)
      6'b000000: controls <= 9'b110000100; // R-type
      6'b100011: controls <= 9'b101001000; // LW
      6'b101011: controls <= 9'b001010000; // SW
      6'b000100: controls <= 9'b000100010; // BEQ
      6'b001000: controls <= 9'b101000000; // ADDI
      6'b000010: controls <= 9'b000000001; // J
      default:   controls <= 9'bxxxxxxxxx; // illegal op
    endcase
endmodule

module aludec (input    logic[5:0] funct,
               input    logic[1:0] aluop,
               output   logic[2:0] alucontrol);
  always_comb
    case(aluop)
      2'b00: alucontrol  = 3'b010;  // add  (for lw/sw/addi)
      2'b01: alucontrol  = 3'b110;  // sub   (for beq)
      default: case(funct)          // R-TYPE instructions
          6'b100000: alucontrol  = 3'b010; // ADD
          6'b100010: alucontrol  = 3'b110; // SUB
          6'b100100: alucontrol  = 3'b000; // AND
          6'b100101: alucontrol  = 3'b001; // OR
          6'b101010: alucontrol  = 3'b111; // SLT
          default:   alucontrol  = 3'bxxx; // ???
        endcase
    endcase
endmodule

module regfile (input    logic clk, we3, 
                input    logic[4:0]  ra1, ra2, wa3, 
                input    logic[31:0] wd3, 
                output   logic[31:0] rd1, rd2);

  logic [31:0] rf [31:0];

  // three ported register file: read two ports combinationally
  // write third port on rising edge of clock. Register0 hardwired to 0.

  always_ff @(negedge clk)
     if (we3) 
         rf [wa3] <= wd3;	

  assign rd1 = (ra1 != 0) ? rf [ra1] : 0;
  assign rd2 = (ra2 != 0) ? rf[ ra2] : 0;

endmodule

module alu(input  logic [31:0] a, b, 
           input  logic [2:0]  alucont, 
           output logic [31:0] result,
           output logic zero, input logic reset);

    always_comb begin
        case(alucont)
            3'b010: result = a + b;
            3'b110: result = a - b;
            3'b000: result = a & b;
            3'b001: result = a | b;
            3'b111: result = (a < b) ? 1 : 0;
            default: result = {32{1'bx}};
        endcase
        if(reset)
            result = 0;
        end
    
    assign zero = (result == 0) ? 1'b1 : 1'b0;
    
endmodule

module adder (input  logic[31:0] a, b,
              output logic[31:0] y);
     
     assign y = a + b;
endmodule

module sl2 (input  logic[31:0] a,
            output logic[31:0] y);
     
     assign y = {a[29:0], 2'b00}; // shifts left by 2
endmodule

module signext (input  logic[15:0] a,
                output logic[31:0] y);
              
  assign y = {{16{a[15]}}, a};    // sign-extends 16-bit a
endmodule

// parameterized register
module flopr #(parameter WIDTH = 8)
              (input logic clk, reset, 
	       input logic[WIDTH-1:0] d, 
               output logic[WIDTH-1:0] q);

  always_ff@(posedge clk, posedge reset)
    if (reset) q <= 0; 
    else       q <= d;
endmodule


// paramaterized 2-to-1 MUX
module mux2 #(parameter WIDTH = 8)
             (input  logic[WIDTH-1:0] d0, d1,  
              input  logic s, 
              output logic[WIDTH-1:0] y);
  
   assign y = s ? d1 : d0; 
endmodule

// paramaterized 4-to-1 MUX
module mux4 #(parameter WIDTH = 8)
             (input  logic[WIDTH-1:0] d0, d1, d2, d3,  
              input  logic[1:0] s, 
              output logic[WIDTH-1:0] y);
  
   assign y = s[1] ? (s[0] ? d3 : d2) : (s[0] ? d1 : d0); 
endmodule