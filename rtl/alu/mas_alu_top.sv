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

module mas_alu_top (
  input logic clk,
  input logic rst_n,
  input logic mas_alu_req,
  input type_mas_alu_cmd mas_alu_cmd,
  input logic [`MAS_BLEN-1:0] mas_alu_op1,
  input logic [`MAS_BLEN-1:0] mas_alu_op2,
  output logic mas_alu_ready,
  output logic [`MAS_BLEN-1:0] mas_alu_res
);

  wire mas_alu_fsm_oper;
  wire mas_alu_fsm_ready;
  wire mas_alu_inst_ready;

assign mas_alu_ready = mas_alu_fsm_ready;

mas_alu_decoder mdec (.clk(clk),.rst_n(rst_n),
                      .mas_alu_fsm_oper(mas_alu_fsm_oper),
                      .mas_alu_fsm_ready(mas_alu_fsm_ready),
                      .mas_alu_cmd(mas_alu_cmd),
                      .mas_alu_op1(mas_alu_op1),
                      .mas_alu_op2(mas_alu_op2),
                      .mas_alu_res(mas_alu_res),
                      .mas_alu_ready(mas_alu_inst_ready));

mas_alu_fsm mfsm  (.clk(clk),
                  .rst_n(rst_n),
                  .mas_alu_fsm_req(mas_alu_req),
                  .mas_alu_ready(mas_alu_inst_ready),
                  .mas_alu_fsm_oper(mas_alu_fsm_oper),
                  .mas_alu_fsm_ready(mas_alu_fsm_ready));

endmodule
