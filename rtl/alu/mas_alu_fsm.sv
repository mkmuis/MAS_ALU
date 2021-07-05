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

module mas_alu_fsm (
    input logic clk,
    input logic rst_n,
    input logic mas_alu_fsm_req,
    input logic mas_alu_ready,
    output logic mas_alu_fsm_oper,
    output logic mas_alu_fsm_ready
);

type_mas_alu_fsm_state mas_alu_fsm_state;
type_mas_alu_fsm_state mas_alu_fsm_next_state;

always_ff @(posedge clk, negedge rst_n) begin
  if (~rst_n) begin
    mas_alu_fsm_state <= MAS_ALU_FSM_IDLE;
  end else begin
    mas_alu_fsm_state <= mas_alu_fsm_next_state;
  end
end

always_comb begin
  mas_alu_fsm_next_state = MAS_ALU_FSM_IDLE;

  case (mas_alu_fsm_state)
    MAS_ALU_FSM_IDLE : begin
      mas_alu_fsm_oper = 1'b0;
      mas_alu_fsm_ready = 1'b1;
      mas_alu_fsm_next_state = mas_alu_fsm_req ? MAS_ALU_FSM_START: MAS_ALU_FSM_IDLE;
    end
    MAS_ALU_FSM_START : begin
      mas_alu_fsm_oper = 1'b1;
      mas_alu_fsm_ready = 1'b0;
      mas_alu_fsm_next_state = MAS_ALU_FSM_OPER;
    end
    MAS_ALU_FSM_OPER : begin
      mas_alu_fsm_oper = 1'b1;
      mas_alu_fsm_ready = 1'b0;
      mas_alu_fsm_next_state = mas_alu_ready ? MAS_ALU_FSM_IDLE: MAS_ALU_FSM_OPER;
    end
  endcase
end

//Assertion: X Unknown
MAS_ALU_FSM_XCHECK : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown({mas_alu_fsm_state})
    ) else $error("ALU Error: unknown states");

//Assertion: Behavioral
MAS_ALU_FSM_ILL_STATE : assert property (
    @(negedge clk) disable iff (~rst_n)
    $onehot0({ mas_alu_fsm_state}) 
    ) else $error("ALU Error: illegal state");

MAS_ALU_ILL_STATE_JUMP0 : assert property (
    @(negedge clk) disable iff (~rst_n)
    (mas_alu_fsm_state == MAS_ALU_FSM_IDLE) |-> ##[1:2] (mas_alu_fsm_state == MAS_ALU_FSM_START)) else $error("ALU Error: illegal state jump");

MAS_ALU_ILL_STATE_JUMP1 : assert property (
    @(negedge clk) disable iff (~rst_n)
    (mas_alu_fsm_state == MAS_ALU_FSM_START) |-> ##[1:2] (mas_alu_fsm_state == MAS_ALU_FSM_OPER)) else $error("ALU Error: illegal state jump");

MAS_ALU_ILL_STATE_JUMP2 : assert property (
    @(negedge clk) disable iff (~rst_n)
    (mas_alu_fsm_state == MAS_ALU_FSM_OPER) |-> ##[1:2] (mas_alu_fsm_state == MAS_ALU_FSM_IDLE)) else $error("ALU Error: illegal state jump");


endmodule

