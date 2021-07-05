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
// ALU COMMANDS
//----------------------------------------------------------------------

typedef enum logic [`MAS_ALU_CMD_WIDTH-1:0] {
    MAS_ALU_CMD_ADD,
    MAS_ALU_CMD_SUB,
    MAS_ALU_CMD_RIGHT_SHIFT,
    MAS_ALU_CMD_LEFT_SHIFT
} type_mas_alu_cmd;

