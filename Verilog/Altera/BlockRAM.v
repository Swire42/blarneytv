// Copyright (C) 1991-2016 Altera Corporation
//
// Your use of Altera Corporation's design tools, logic functions 
// and other software and tools, and its AMPP partner logic 
// functions, and any output files from any of the foregoing 
// (including device programming or simulation files), and any 
// associated documentation or information are expressly subject 
// to the terms and conditions of the Altera Program License 
// Subscription Agreement, Altera MegaCore Function License 
// Agreement, or other applicable license agreement, including, 
// without limitation, that your use is for the sole purpose of 
// programming logic devices manufactured by Altera and sold by 
// Altera or its authorized distributors.  Please refer to the 
// applicable agreement for further details.

// Generated by Quartus.
// With edits from Matthew Naylor, June 2016.

// Single-port block RAM
// =====================

module BlockRAM (
  CLK,     // Clock
  DI,      // Data in
  ADDR,    // Read address
  WE,      // Write enable
  DO       // Data out
  );

  parameter ADDR_WIDTH   = 1;
  parameter DATA_WIDTH   = 1;
  parameter NUM_ELEMS    = 1;
  parameter BE_WIDTH     = 1;
  parameter RD_DURING_WR = "OLD_DATA";     // Or: "DONT_CARE"
  parameter DO_REG       = "UNREGISTERED"; // Or: "CLOCK0"
  parameter INIT_FILE    = "UNUSED";
  parameter DEV_FAMILY   = "Stratix V";

  input  CLK;
  input  [DATA_WIDTH-1:0] DI;
  input  [ADDR_WIDTH-1:0] ADDR;
  input  WE;
  output [DATA_WIDTH-1:0] DO;
`ifndef ALTERA_RESERVED_QIS
// synopsys translate_off
`endif
  tri1 CLK;
  tri0 WE;
`ifndef ALTERA_RESERVED_QIS
// synopsys translate_on
`endif

  altsyncram altsyncram_component (
        .address_a (ADDR),
        .clock0 (CLK),
        .data_a (DI),
        .wren_a (WE),
        .q_a (DO),
        .aclr0 (1'b0),
        .aclr1 (1'b0),
        .address_b (1'b1),
        .addressstall_a (1'b0),
        .addressstall_b (1'b0),
        .byteena_a (1'b1),
        .byteena_b (1'b1),
        .clock1 (1'b1),
        .clocken0 (1'b1),
        .clocken1 (1'b1),
        .clocken2 (1'b1),
        .clocken3 (1'b1),
        .data_b (1'b1),
        .eccstatus (),
        .q_b (),
        .rden_a (1'b1),
        .rden_b (1'b1),
        .wren_b (1'b0));
  defparam
    altsyncram_component.clock_enable_input_a = "BYPASS",
    altsyncram_component.clock_enable_output_a = "BYPASS",
    altsyncram_component.init_file = INIT_FILE,
    altsyncram_component.intended_device_family = DEV_FAMILY,
    altsyncram_component.lpm_hint = "ENABLE_RUNTIME_MOD=NO",
    altsyncram_component.lpm_type = "altsyncram",
    altsyncram_component.numwords_a = 2**ADDR_WIDTH,
    altsyncram_component.operation_mode = "SINGLE_PORT",
    altsyncram_component.outdata_aclr_a = "NONE",
    altsyncram_component.outdata_reg_a = DO_REG,
    altsyncram_component.power_up_uninitialized = "FALSE",
    altsyncram_component.read_during_write_mode_port_a = "NEW_DATA_NO_NBE_READ",
    altsyncram_component.widthad_a = ADDR_WIDTH,
    altsyncram_component.width_a = DATA_WIDTH,
    altsyncram_component.width_byteena_a = 1;

endmodule

// True dual-port block RAM
// ========================

module BlockRAMTrueDual (
  CLK,       // Clock
  DI_A,      // Data in
  ADDR_A,    // Read address
  WE_A,      // Write enable
  DO_A,      // Data out
  DI_B,      // Data in
  ADDR_B,    // Read address
  WE_B,      // Write enable
  DO_B       // Data out
  );

  parameter ADDR_WIDTH   = 1;
  parameter DATA_WIDTH   = 1;
  parameter NUM_ELEMS    = 1;
  parameter RD_DURING_WR = "OLD_DATA";     // Or: "DONT_CARE"
  parameter DO_REG_A     = "UNREGISTERED"; // Or: "CLOCK0"
  parameter DO_REG_B     = "UNREGISTERED"; // Or: "CLOCK0"
  parameter INIT_FILE    = "UNUSED";
  parameter DEV_FAMILY   = "Stratix V";

  input [(DATA_WIDTH-1):0] DI_A, DI_B;
  input [(ADDR_WIDTH-1):0] ADDR_A, ADDR_B;
  input WE_A, WE_B, CLK;
  output reg [(DATA_WIDTH-1):0] DO_A, DO_B;
  reg [DATA_WIDTH-1:0] RAM[2**ADDR_WIDTH-1:0];

  generate
    if (INIT_FILE != "UNUSED") begin
      initial $readmemh(INIT_FILE, RAM);
    end
  endgenerate

    altsyncram altsyncram_component (
        .address_a (ADDR_A),
        .address_b (ADDR_B),
        .byteena_b (1'b1),
        .clock0 (CLK),
        .data_a (DI_A),
        .data_b (DI_B),
        .wren_a (WE_A),
        .wren_b (WE_B),
        .q_a (DO_A),
        .q_b (DO_B),
        .aclr0 (1'b0),
        .aclr1 (1'b0),
        .addressstall_a (1'b0),
        .addressstall_b (1'b0),
        .byteena_a (1'b1),
        .clock1 (1'b1),
        .clocken0 (1'b1),
        .clocken1 (1'b1),
        .clocken2 (1'b1),
        .clocken3 (1'b1),
        .eccstatus (),
        .rden_a (1'b1),
        .rden_b (1'b1));
  defparam
    altsyncram_component.address_reg_b = "CLOCK0",
    altsyncram_component.clock_enable_input_a = "BYPASS",
    altsyncram_component.clock_enable_input_b = "BYPASS",
    altsyncram_component.clock_enable_output_a = "BYPASS",
    altsyncram_component.clock_enable_output_b = "BYPASS",
    altsyncram_component.init_file = INIT_FILE,
    altsyncram_component.init_file_layout = "PORT_A",
    altsyncram_component.indata_reg_b = "CLOCK0",
    altsyncram_component.intended_device_family = DEV_FAMILY,
    altsyncram_component.lpm_type = "altsyncram",
    altsyncram_component.numwords_a = 2**ADDR_WIDTH,
    altsyncram_component.numwords_b = 2**ADDR_WIDTH,
    altsyncram_component.operation_mode = "BIDIR_DUAL_PORT",
    altsyncram_component.outdata_aclr_a = "NONE",
    altsyncram_component.outdata_aclr_b = "NONE",
    altsyncram_component.outdata_reg_a = DO_REG_A,
    altsyncram_component.outdata_reg_b = DO_REG_B,
    altsyncram_component.power_up_uninitialized = "FALSE",
    altsyncram_component.read_during_write_mode_mixed_ports = RD_DURING_WR,
    altsyncram_component.read_during_write_mode_port_a = "NEW_DATA_NO_NBE_READ",
    altsyncram_component.read_during_write_mode_port_b = "NEW_DATA_NO_NBE_READ",
    altsyncram_component.widthad_a = ADDR_WIDTH,
    altsyncram_component.widthad_b = ADDR_WIDTH,
    altsyncram_component.width_a = DATA_WIDTH,
    altsyncram_component.width_b = DATA_WIDTH,
    altsyncram_component.width_byteena_a = 1,
    altsyncram_component.width_byteena_b = 1,
    altsyncram_component.wrcontrol_wraddress_reg_b = "CLOCK0";

endmodule
