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

//----------------------------------------------------------------------
// MAS ALU CONFIGURATION
//----------------------------------------------------------------------

// ALU PARAMETERS 
`define MAS_ALU_CMD_WIDTH 3

// ALU FSM
typedef enum logic [1:0] {
   MAS_ALU_FSM_IDLE,
   MAS_ALU_FSM_START,
   MAS_ALU_FSM_OPER
} type_mas_alu_fsm_state;

`define MAS_BLEN 32


