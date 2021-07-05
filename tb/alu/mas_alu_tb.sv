////////////////////////////////////////////////////////////////////////////
//Copyright 2021 Anthony Mui                                              //
//                                                                        //
//Licensed under the Apache License, Version 2.0 (the "License");         //
//you may not use this file except in compliance with the License.        //
//You may obtain a copy of the License at                                 //
//                                                                        //
//    http://www.apache.org/licenses/LICENSE-2.0                          //
//                                                                        //
//Unless required by applicable law or agreed to in writing, software     //
//distributed under the License is distributed on an "AS IS" BASIS,       //
//WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.//
//See the License for the specific language governing permissions and     //
//limitations under the License.                                          //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

`include "mas_architecture_description.svh"
`include "mas_cmd.svh"
`include "mas_test_configuration.sv"
`include "mas_test_class.sv"
`include "mas_alu_tb.cov"

//----------------------------------------------
//  DEBUG CONFIGURATION
//----------------------------------------------

//For initial test environment
//`define MONITOR
//For small test size
//`define VISUAL
//For large test size, results write out to file
`define POSTPROCESS

//----------------------------------------------
//  DEBUG TEST TARGET
//----------------------------------------------

//Broad range test
`define BROAD
//Targeted test
`define TARGETED

module alu_tb;
  logic clk;
  logic rst_n;
  type_mas_alu_cmd mas_alu_cmd_test;
  logic [`MAS_BLEN-1:0] mas_alu_op1_test;
  logic [`MAS_BLEN-1:0] mas_alu_op2_test;
  bit mas_alu_req_test;
  wire mas_alu_ready_test;
  wire [`MAS_BLEN-1:0] mas_alu_res_test;
  event rst_n_ev,req_ev, alu_ready_ev, fsm_ready_ev;
  event test_ready_ev, test_sample_ready_ev;
  event addsub_broadtest_ev,rlshift_broadtest_ev; 
  event addsub_targettest_ev,rlshift_targettest_ev; 
  bit alu_chk_res;
  int error;
  int alu_exp_res;
  `ifdef POSTPROCESS
  int fd_addsub;
  int fd_rlshift;
  string addsub_test_file = "addsub_testfile.txt";
  string rlshift_test_file = "rlshift_testfile.txt";
  `endif

mas_alu_top mtop (.clk(clk),.rst_n(rst_n),
                      .mas_alu_req(mas_alu_req_test),
                      .mas_alu_cmd(mas_alu_cmd_test),
                      .mas_alu_op1(mas_alu_op1_test),
                      .mas_alu_op2(mas_alu_op2_test),
                      .mas_alu_res(mas_alu_res_test),
                      .mas_alu_ready(mas_alu_ready_test));

always #2 clk = ~clk;

//----------------------------------------------
//  Initialize Test/Design
//----------------------------------------------

initial begin
  $display("\nRunning Test for MAS ALU");
	clk = 1'b0;
  rst_n = 1'b0;
  #2
  rst_n = 1'b1;
  mas_alu_req_test = 1'b1;
  -> req_ev; 
end

`ifdef BROAD
`include "mas_add_sub_broadtest.sv"
`include "mas_rl_shift_broadtest.sv"
`endif

`ifdef TARGETED
`include "mas_add_sub_targettest.sv"
`include "mas_rl_shift_targettest.sv"
`endif

//NEXT TEST TRIGGER
always@(posedge clk) begin
  if (mtop.mfsm.mas_alu_fsm_state==MAS_ALU_FSM_OPER) begin
    -> test_ready_ev;
  end
end

//FSM READY TRIGGER
always@(posedge mtop.mfsm.mas_alu_fsm_ready) begin
  -> fsm_ready_ev; 
end


`ifdef MONITOR
initial begin
     $monitor("%0t,%p, CLK:%b, Req:%0b, FSM Ready:%0b, Operate:%0b, \
     \n%p, OP1:%0d, OP2:%0d, RES:%0d, ALU READY:%0b, RESULTS:%0b\n",
     $time,mtop.mfsm.mas_alu_fsm_state,clk,mas_alu_req_test,
     mtop.mdec.mas_alu_fsm_ready,mtop.mfsm.mas_alu_fsm_oper,
     mas_alu_cmd_test,mas_alu_op1_test,mas_alu_op2_test,mas_alu_res_test,
     mtop.mdec.mas_alu_ready,alu_chk_res);
end 
`endif

endmodule
