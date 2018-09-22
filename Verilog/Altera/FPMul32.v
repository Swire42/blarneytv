module FPMul32 (
  input wire clock,         // Clock
  input wire [0:0] in_0,    // "go" trigger
  input wire [31:0] in_1,   // Operand A
  input wire [31:0] in_2,   // Operand B
  output wire [0:0] out_0,  // "done" trigger
  output wire [31:0] out_1  // Result
  );

localparam latency = 11;

AlteraFPMult Mult(
  .clock(clock),
  .dataa(in_1),
  .datab(in_2),
  .nan(),
  .overflow(),
  .result(out_1),
  .underflow());

integer i;
reg trigger [latency-1:0];
assign out_0 = trigger[0];
always @(posedge clock) begin
  trigger[latency-1] <= in_0;
  for (i=1; i < latency; i=i+1)
    trigger[i-1] <= trigger[i];
end

endmodule