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

class AluTest;

  rand type_mas_alu_cmd mas_alu_cmd_test [];
  rand bit [`MAS_BLEN-1:0] mas_alu_op1_test [];
  rand bit [`MAS_BLEN-1:0] mas_alu_op2_test [];
  rand type_mas_operand_range mas_operand_range_test [];
  type_mas_operand_range operand1_range_sel;
  type_mas_operand_range operand2_range_sel;
  longint test_size;
  int error;

constraint op1_size {mas_alu_op1_test.size == test_size;}
constraint op2_size {mas_alu_op2_test.size == mas_alu_op1_test.size;}
constraint cmd_size {mas_alu_cmd_test.size == mas_alu_op1_test.size;}
constraint op_test {mas_operand_range_test.size == mas_alu_op1_test.size;}

function bit[`MAS_BLEN-1:0] op_mid(bit [`MAS_BLEN-1:0] mid);
  op_mid = (mid-1)/2;
endfunction

task automatic res_chk(input int op1, op2, rec_res, type_mas_alu_cmd cmd, output bit chk_res, int exp_res);
    chk_res = 1;
    exp_res = 0;
    case (cmd)
      MAS_ALU_CMD_ADD: begin
        if (rec_res == op1 + op2) chk_res = 1;
        else begin 
          chk_res = 0;
          exp_res = op1 + op2;
        end
      end
      MAS_ALU_CMD_SUB: begin
        if (rec_res == op1 - op2) chk_res = 1;
        else begin 
          chk_res = 0;
          exp_res = op1 - op2;
        end
      end
      MAS_ALU_CMD_RIGHT_SHIFT: begin
        if (rec_res == op1 >> op2) chk_res = 1;
        else begin 
          chk_res = 0;
          exp_res = op1 >> op2;
        end
      end
      MAS_ALU_CMD_LEFT_SHIFT: begin
				if (rec_res == op1 << op2) chk_res = 1;
        else begin 
          chk_res = 0;
          exp_res = op1 << op2;
        end
      end
      default: begin end
    endcase
endtask

endclass:AluTest

class AddSubBroadTest extends AluTest;

constraint op1_range { 
  foreach(mas_alu_op1_test[i]) {
    (operand1_range_sel==LOW_OPERAND_RANGE) -> mas_alu_op1_test[i] < op_mid('h0);
    (operand1_range_sel==HIGH_OPERAND_RANGE) -> mas_alu_op1_test[i] > op_mid('h0);
  }
}

constraint op2_range { 
  foreach(mas_alu_op2_test[i]) {
    (operand2_range_sel==LOW_OPERAND_RANGE) -> mas_alu_op2_test[i] < op_mid('h0);
    (operand2_range_sel==HIGH_OPERAND_RANGE) -> mas_alu_op2_test[i] > op_mid('h0);
  }
}
constraint cmd_range { 
  foreach(mas_alu_cmd_test[i]) {
    mas_alu_cmd_test[i] inside 
{MAS_ALU_CMD_ADD,MAS_ALU_CMD_SUB};
  }
}

endclass:AddSubBroadTest

class RLShiftBroadTest extends AluTest;

constraint op1_range { 
  foreach(mas_alu_op1_test[i]) {
    (operand1_range_sel==LOW_OPERAND_RANGE) -> mas_alu_op1_test[i] < op_mid('h0);
    (operand1_range_sel==HIGH_OPERAND_RANGE) -> mas_alu_op1_test[i] > op_mid('h0);
  }
}

constraint op2_range { 
  foreach(mas_alu_op2_test[i]) { mas_alu_op2_test[i] < 16;}
}

constraint cmd_range { 
  foreach(mas_alu_cmd_test[i]) {
    mas_alu_cmd_test[i] inside 
{MAS_ALU_CMD_RIGHT_SHIFT,MAS_ALU_CMD_LEFT_SHIFT};
  }
}

endclass:RLShiftBroadTest

class AddSubTargetedTest extends AluTest;

constraint op1_range { 
  foreach(mas_alu_op1_test[i]) {
    mas_alu_op1_test[i] inside {`MAS_BLEN'hAAAAAAAA,`MAS_BLEN'h55555555};
  }
}

constraint op2_range { 
  foreach(mas_alu_op2_test[i]) {
    mas_alu_op2_test[i] inside {`MAS_BLEN'hAAAAAAAA,`MAS_BLEN'h55555555};
  }
}
constraint cmd_range { 
  foreach(mas_alu_cmd_test[i]) {
    mas_alu_cmd_test[i] inside 
{MAS_ALU_CMD_ADD,MAS_ALU_CMD_SUB};
  }
}

endclass:AddSubTargetedTest

class RLShiftTargetTest extends AluTest;

constraint op1_range { 
  foreach(mas_alu_op1_test[i]) {
    mas_alu_op1_test[i] inside {`MAS_BLEN'hAAAAAAAA,`MAS_BLEN'h55555555};
  }
}

constraint op2_range { 
  foreach(mas_alu_op2_test[i]) { mas_alu_op2_test[i] < 8;}
}

constraint cmd_range { 
  foreach(mas_alu_cmd_test[i]) {
    mas_alu_cmd_test[i] inside 
{MAS_ALU_CMD_RIGHT_SHIFT,MAS_ALU_CMD_LEFT_SHIFT};
  }
}

endclass:RLShiftTargetTest
