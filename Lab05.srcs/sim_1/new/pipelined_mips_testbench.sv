`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 04/04/2019 02:15:23 PM
// Design Name: 
// Module Name: mips_testbench
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


module pipelined_mips_testbench();
    
    logic clk,clr;
    logic [31:0] PCF;
    logic [31:0] ALUOut, ResultW, instrD, WriteDataM;
    logic StallD, StallF; 
    // logic memwrite;
    

    mips testpipelinedmips(
    .clk(clk),
    .reset(clr),
    .PCF(PCF),
    .ALUOut(ALUOut),
    .ResultW(ResultW),
    .instrD(instrD),
    .WriteDataM(WriteDataM),
    .StallD(StallD),
    .StallF(StallF)
    );
    
    initial
       begin
       clk = 0;
       clr = 1;
       #1
       clr = 0;
       end
    always
    #20 clk = ~clk;
         
endmodule

