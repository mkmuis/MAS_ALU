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
  AddSubTargetedTest addsubtest;
  alu_cov cg_addsub;
  addsubtest = new();
  cg_addsub = new();

  `ifdef BROAD
    wait(rlshift_broadtest_ev.triggered);
    #2;
    mas_alu_req_test = 1'b1;
  `endif

  addsubtest.test_size=`TEST_SIZE;
  addsubtest.randomize();

  fork
  //Insert Randomized Object into Testbench Variable
  begin 
  wait(mas_alu_req_test);
  foreach(addsubtest.mas_alu_op1_test[i]) begin
    @(posedge clk) 
    addsubtest.operand1_range_sel=addsubtest.mas_operand_range_test[i];
    addsubtest.operand2_range_sel=addsubtest.mas_operand_range_test[i];
    mas_alu_op1_test=addsubtest.mas_alu_op1_test[i];
    mas_alu_op2_test=addsubtest.mas_alu_op2_test[i];
    mas_alu_cmd_test=addsubtest.mas_alu_cmd_test[i];
    cg_addsub.sample();
    wait(mtop.mdec.mas_alu_ready);
    wait(fsm_ready_ev.triggered);
  end
  end
  begin
  wait(mas_alu_req_test);
  //Functionality check
  foreach(addsubtest.mas_alu_op1_test[i]) begin
    @(posedge clk)
    wait(test_ready_ev.triggered);
    addsubtest.res_chk(mas_alu_op1_test,mas_alu_op2_test,mas_alu_res_test,mas_alu_cmd_test,
    alu_chk_res,alu_exp_res);
    -> test_sample_ready_ev;
  end
  end
  `ifdef VISUAL
    begin
      foreach(addsubtest.mas_alu_op1_test[i]) begin
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
          addsubtest.error++;
        end
      end
    end
  `endif
  `ifdef POSTPROCESS
    begin
    fd_addsub = $fopen (addsub_test_file,"a+"); 
      foreach(addsubtest.mas_alu_op1_test[i]) begin
        @(posedge clk)
        wait(test_sample_ready_ev.triggered);
        if (alu_chk_res) begin
          $fdisplay(fd_addsub,"CORRECT,%0t,%p,%p,%0h,%0h,%0h,%0h",$time,mtop.mfsm.mas_alu_fsm_state,
          mas_alu_cmd_test,mas_alu_op1_test,mas_alu_op2_test,mas_alu_res_test,alu_exp_res);
        end
        else begin 
          $fdisplay(fd_addsub,"ERROR,%0t,%p,%p,%0h,%0h,%0h,%0h",$time,mtop.mfsm.mas_alu_fsm_state,
          mas_alu_cmd_test,mas_alu_op1_test,mas_alu_op2_test,mas_alu_res_test,alu_exp_res);
          addsubtest.error++;
        end
      end
    $fclose(fd_addsub);
    end
  `endif
  join
  #4;
  if (addsubtest.error > 0) begin
    $display("\n--------------------------------------");
    $display(" ALU ADDITION SUBSTRACTION TEST    ");
    //$display(" OPERAND1 SELECTION: %s",addsubtest.operand1_range_sel);
    //$display(" OPERAND2 SELECTION: %s",addsubtest.operand2_range_sel);
    $display(" Test Ended, Test FAILED    ");
    $display(" Coverage = %0d%%",cg_addsub.get_coverage());
    $display(" Summary: %0d/%0d tests failed", addsubtest.error, addsubtest.test_size);
    $display("--------------------------------------\n");
  end
  else begin
    $display("\n--------------------------------------");
    $display(" ALU ADDITION SUBSTRACTION TEST    ");
    //$display(" OPERAND1 SELECTION: %s",addsubtest.operand1_range_sel);
    //$display(" OPERAND2 SELECTION: %s",addsubtest.operand2_range_sel);
    $display(" Test Ended, Test PASSED   ");
    $display(" Coverage = %0d%%",cg_addsub.get_coverage());
    $display(" Summary: %0d/%0d tests failed", addsubtest.error, addsubtest.test_size);
    $display("--------------------------------------\n");
	end

//Reset ALU
mas_alu_req_test = 1'b0;
->addsub_targettest_ev;
end 
