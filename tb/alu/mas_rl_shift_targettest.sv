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

initial begin
  RLShiftTargetTest rlshifttest;
  alu_cov cg_rlshift;
  rlshifttest = new();
  cg_rlshift = new();
  
  wait(addsub_targettest_ev.triggered);
  #2;
  mas_alu_req_test = 1'b1;
  rlshifttest.test_size=`TEST_SIZE;
  rlshifttest.randomize();

  fork
  //Insert Randomized Object into Testbench Variable
  begin 
  wait(mas_alu_req_test);
  foreach(rlshifttest.mas_alu_op1_test[i]) begin
    @(posedge clk) 
    rlshifttest.operand1_range_sel=rlshifttest.mas_operand_range_test[i];
    mas_alu_op1_test=rlshifttest.mas_alu_op1_test[i];
    mas_alu_op2_test=rlshifttest.mas_alu_op2_test[i];
    mas_alu_cmd_test=rlshifttest.mas_alu_cmd_test[i];
    cg_rlshift.sample();
    wait(mtop.mdec.mas_alu_ready);
    wait(fsm_ready_ev.triggered);
  end
  end
  //Functionality check
  begin
  wait(mas_alu_req_test);
  foreach(rlshifttest.mas_alu_op1_test[i]) begin
    @(posedge clk)
    wait(test_ready_ev.triggered);
    rlshifttest.res_chk(mas_alu_op1_test,mas_alu_op2_test,mas_alu_res_test,mas_alu_cmd_test,
    alu_chk_res,alu_exp_res);
    -> test_sample_ready_ev;
  end
  end
  `ifdef VISUAL
    begin
      foreach(rlshifttest.mas_alu_op1_test[i]) begin
        @(posedge clk)
        wait(test_sample_ready_ev.triggered);
        if (alu_chk_res) begin 
          $display("\nSTATE: %p, COMMAND: %p,\nOP1: %0d, OP2: %0d, RESULTS: %0d CORRECT\n"
          ,mtop.mfsm.mas_alu_fsm_state,mas_alu_cmd_test,mas_alu_op1_test,mas_alu_op2_test,
          mas_alu_res_test);
        end
        else begin 
          $display("\nERROR at time %0tns:\nSTATE: %p, COMMAND: %p, \
          \nExpected: %0d, Received: %0d\n",$time,
          mtop.mfsm.mas_alu_fsm_state,mas_alu_cmd_test,mas_alu_res_test,alu_exp_res);
          rlshifttest.error++;
        end
      end
    end
  `endif
  `ifdef POSTPROCESS
    begin
    fd_rlshift = $fopen (rlshift_test_file,"a+"); 
      foreach(rlshifttest.mas_alu_op1_test[i]) begin
        @(posedge clk)
        wait(test_sample_ready_ev.triggered);
        if (alu_chk_res) begin
          $fdisplay(fd_rlshift,"CORRECT,%0t,%p,%p,%0h,%0h,%0h,%0h",$time,mtop.mfsm.mas_alu_fsm_state,
          mas_alu_cmd_test,mas_alu_op1_test,mas_alu_op2_test,mas_alu_res_test,alu_exp_res);
        end
        else begin 
          $fdisplay(fd_rlshift,"ERROR,%0t,%p,%p,%0h,%0h,%0h,%0h",$time,mtop.mfsm.mas_alu_fsm_state,
          mas_alu_cmd_test,mas_alu_op1_test,mas_alu_op2_test,mas_alu_res_test,alu_exp_res);
          rlshifttest.error++;
        end
      end
    $fclose(fd_rlshift);
    end
  `endif
  join
  #4;
  if (rlshifttest.error > 0) begin
    $display("\n--------------------------------------");
    $display(" ALU RIGHT LEFT SHIFT TEST    ");
    $display(" OPERANDS SELECTION: TARGETED");
    $display(" Test Ended, Test FAILED    ");
    $display(" Coverage = %0d%%",cg_rlshift.get_coverage());
    $display(" Summary: %0d/%0d tests failed", rlshifttest.error, rlshifttest.test_size);
    $display("--------------------------------------\n");
  end
  else begin
    $display("\n--------------------------------------");
    $display(" ALU RIGHT LEFT SHIFT TEST    ");
    $display(" OPERANDS SELECTION: TARGETED");
    $display(" Test Ended, Test PASSED   ");
    $display(" Coverage = %0d%%",cg_rlshift.get_coverage());
    $display(" Summary: %0d/%0d tests failed", rlshifttest.error, rlshifttest.test_size);
    $display("--------------------------------------\n");
	end
    $finish;
end 
