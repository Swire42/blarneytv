// (C) 2001-2019 Intel Corporation. All rights reserved.
//
// Your use of Intel Corporation's design tools, logic functions and
// other software and tools, and its AMPP partner logic functions, and
// any output files from any of the foregoing (including device
// programming or simulation files), and any associated documentation
// or information are expressly subject to the terms and conditions of
// the Intel Program License Subscription Agreement, Intel FPGA IP
// License Agreement, or other applicable license agreement,
// including, without limitation, that your use is for the sole
// purpose of programming logic devices manufactured by Intel and sold
// by Intel or its authorized distributors.  Please refer to the
// applicable agreement for further details.

// Generated by Quartus.
// With edits from Matthew Naylor, July 2021.

module BlockRAMQuad (
  clock,     // Clock
  reset,     // Reset

  DI_A,      // Data in
  RD_ADDR_A, // Read address
  WR_ADDR_A, // Write address
  WE_A,      // Write enable
  RE_A,      // Read enable
  DO_A,      // Data out

  RD_ADDR_B, // Read address
  WR_ADDR_B, // Write address
  DI_B,      // Data in
  WE_B,      // Write enable
  RE_B,      // Read enable
  DO_B       // Data out
  );

    parameter ADDR_WIDTH = 1;
    parameter DATA_WIDTH = 1;
    parameter NUM_ELEMS  = 2**ADDR_WIDTH;
    parameter INIT_FILE  = "UNUSED";

    input [(DATA_WIDTH-1):0] DI_A, DI_B;
    input [(ADDR_WIDTH-1):0] RD_ADDR_A, RD_ADDR_B, WR_ADDR_A, WR_ADDR_B;
    input clock, reset, WE_A, WE_B, RE_A, RE_B;
    output [(DATA_WIDTH-1):0] DO_A;
    output [(DATA_WIDTH-1):0] DO_B;

`ifndef ALTERA_RESERVED_QIS
// synopsys translate_off
`endif
    tri1     clock;
    tri1     RE_A;
    tri1     RE_B;
    tri0     WE_A;
    tri0     WE_B;
`ifndef ALTERA_RESERVED_QIS
// synopsys translate_on
`endif

    altera_syncram  altera_syncram_component (
                .address2_a (RD_ADDR_A),
                .address2_b (RD_ADDR_B),
                .address_a (WR_ADDR_A),
                .address_b (WR_ADDR_B),
                .clock0 (clock),
                .data_a (DI_A),
                .data_b (DI_B),
                .rden_a (RE_A),
                .rden_b (RE_B),
                .wren_a (WE_A),
                .wren_b (WE_B),
                .q_a (DO_A),
                .q_b (DO_B),
                .aclr0 (1'b0),
                .aclr1 (1'b0),
                .addressstall_a (1'b0),
                .addressstall_b (1'b0),
                .byteena_a (1'b1),
                .byteena_b (1'b1),
                .clock1 (1'b1),
                .clocken0 (1'b1),
                .clocken1 (1'b1),
                .clocken2 (1'b1),
                .clocken3 (1'b1),
                .eccencbypass (1'b0),
                .eccencparity (8'b0),
                .eccstatus (),
                .sclr (1'b0));
    defparam
        altera_syncram_component.address_aclr_a  = "NONE",
        altera_syncram_component.address_aclr_b  = "NONE",
        altera_syncram_component.address_reg_b  = "CLOCK0",
        altera_syncram_component.clock_enable_input_a  = "BYPASS",
        altera_syncram_component.clock_enable_input_b  = "BYPASS",
        altera_syncram_component.clock_enable_output_a  = "BYPASS",
        altera_syncram_component.clock_enable_output_b  = "BYPASS",
        altera_syncram_component.indata_reg_b  = "CLOCK0",
        altera_syncram_component.init_file = INIT_FILE,
        altera_syncram_component.intended_device_family  = "Stratix 10",
        altera_syncram_component.lpm_type  = "altera_syncram",
        altera_syncram_component.numwords_a  = NUM_ELEMS,
        altera_syncram_component.numwords_b  = NUM_ELEMS,
        altera_syncram_component.operation_mode  = "QUAD_PORT",
        altera_syncram_component.outdata_aclr_a  = "NONE",
        altera_syncram_component.outdata_sclr_a  = "NONE",
        altera_syncram_component.outdata_aclr_b  = "NONE",
        altera_syncram_component.outdata_sclr_b  = "NONE",
        altera_syncram_component.outdata_reg_a  = "UNREGISTERED",
        altera_syncram_component.outdata_reg_b  = "UNREGISTERED",
        altera_syncram_component.power_up_uninitialized  = "FALSE",
        altera_syncram_component.enable_force_to_zero  = "FALSE",
        altera_syncram_component.read_during_write_mode_port_a  = "DONT_CARE",
        altera_syncram_component.read_during_write_mode_port_b  = "DONT_CARE",
        altera_syncram_component.read_during_write_mode_mixed_ports  = "NEW_A_OLD_B",
        altera_syncram_component.widthad_a  = ADDR_WIDTH,
        altera_syncram_component.widthad_b  = ADDR_WIDTH,
        altera_syncram_component.widthad2_a  = ADDR_WIDTH,
        altera_syncram_component.widthad2_b  = ADDR_WIDTH,
        altera_syncram_component.width_a  = DATA_WIDTH,
        altera_syncram_component.width_b  = DATA_WIDTH,
        altera_syncram_component.width_byteena_a  = 1,
        altera_syncram_component.width_byteena_b  = 1;

endmodule