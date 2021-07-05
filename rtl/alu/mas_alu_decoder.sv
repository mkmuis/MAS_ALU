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

module mas_alu_decoder (
  input logic clk,
  input logic rst_n,
  input logic mas_alu_fsm_oper,
  input logic mas_alu_fsm_ready,
  input type_mas_alu_cmd mas_alu_cmd,
  input logic [`MAS_BLEN-1:0] mas_alu_op1,
  input logic [`MAS_BLEN-1:0] mas_alu_op2,
  output logic mas_alu_ready,
  output logic [`MAS_BLEN-1:0] mas_alu_res
);

logic mas_alu_oper;
logic [`MAS_BLEN-1:0] mas_alu_op1_dec;
logic [`MAS_BLEN-1:0] mas_alu_op2_dec;
wire mas_alu_ready_add;
wire mas_alu_ready_sub;
wire mas_alu_ready_rshift;
wire mas_alu_ready_lshift;
wire [`MAS_BLEN-1:0] mas_alu_res_add;
wire [`MAS_BLEN-1:0] mas_alu_res_sub;
wire [`MAS_BLEN-1:0] mas_alu_res_rshift;
wire [`MAS_BLEN-1:0] mas_alu_res_lshift;

always_ff @(posedge clk, negedge rst_n) begin
  if (~rst_n) begin
    mas_alu_oper <= 1'b0;
  end else begin
    mas_alu_oper <= mas_alu_fsm_oper;
  end
end

assign mas_alu_op1_dec = mas_alu_fsm_ready ? mas_alu_op1 : mas_alu_op1_dec;
assign mas_alu_op2_dec = mas_alu_fsm_ready ? mas_alu_op2 : mas_alu_op2_dec;

mas_alu_adder madd (.clk(clk),.rst_n(rst_n),.op1(mas_alu_op1_dec),
                    .op2(mas_alu_op2_dec),.res(mas_alu_res_add),
                    .ready(mas_alu_ready_add));
mas_alu_subtractor msub (.clk(clk),.rst_n(rst_n),.op1(mas_alu_op1_dec),
                    .op2(mas_alu_op2_dec),.res(mas_alu_res_sub),
                    .ready(mas_alu_ready_sub));
mas_alu_right_shift mrshift (.clk(clk),.rst_n(rst_n),.op1(mas_alu_op1_dec),
                    .op2(mas_alu_op2_dec),.res(mas_alu_res_rshift),
                    .ready(mas_alu_ready_rshift));
mas_alu_left_shift mlshift (.clk(clk),.rst_n(rst_n),.op1(mas_alu_op1_dec),
                    .op2(mas_alu_op2_dec),.res(mas_alu_res_lshift),
                    .ready(mas_alu_ready_lshift));

always_comb begin
  if (mas_alu_oper) begin
    case (mas_alu_cmd)
      MAS_ALU_CMD_ADD: begin
        mas_alu_res <= mas_alu_res_add;
        mas_alu_ready <= mas_alu_ready_add;
      end
      MAS_ALU_CMD_SUB: begin
        mas_alu_res <= mas_alu_res_sub;
        mas_alu_ready <= mas_alu_ready_sub;
      end
      MAS_ALU_CMD_RIGHT_SHIFT: begin
        mas_alu_res <= mas_alu_res_rshift;
        mas_alu_ready <= mas_alu_ready_rshift;
      end
      MAS_ALU_CMD_LEFT_SHIFT: begin
        mas_alu_res <= mas_alu_res_lshift;
        mas_alu_ready <= mas_alu_ready_lshift;
      end
      default: begin end
    endcase
  end
end

//Assertion: X Unknown
MAS_ALU_DECODER_XCHECK : assert property (
    @(negedge clk) disable iff (~rst_n)
    (mas_alu_oper |=> !$isunknown({mas_alu_cmd}))
    ) else $error("ALU Error: unknown command");

//Assertion: Behavioral
MAS_ALU_DECODER_ILL_OP : assert property (
    @(negedge clk) disable iff (~rst_n)
    (mas_alu_fsm_ready && mas_alu_oper) |=> (mas_alu_ready)) else $error("ALU Error: illegal operation");

endmodule

