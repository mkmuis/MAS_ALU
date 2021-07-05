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

module mas_alu_left_shift (
  input clk,
  input rst_n, 
  input  logic [`MAS_BLEN-1:0] op1, op2,
  output logic ready,
  output logic [`MAS_BLEN-1:0] res
);


always_ff @(posedge clk, negedge rst_n) begin
  if (~rst_n) begin
    res <= '0;
    ready <= '0;
  end else begin
    ready <= '1;
    res <= op1 << op2;
  end
end

endmodule

