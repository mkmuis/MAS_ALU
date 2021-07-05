# MAS ALU

A simple verification testbench & design written in SystemVerilog for learning purpose.

## Description

The design includes simple addition, subtraction, right shift & left shift function blocks, a decoder block that determines the function to be executed, and fsm to automate the process. The verification testbench covers broad and targeted testing on specific inputs, functionality checks and coverage model.

## Limitation

Although the design is configurable in bit lengths, however, the testbench isn't.

## How to run

At directory MAS_ALU, to do compilation
```
make run_alu
```
to view coverage results
```
make view_res
```

## Author

Anthony Mui : akdemen@gmail.com  
