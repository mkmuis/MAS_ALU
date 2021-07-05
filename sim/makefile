#------------------------------------------------------
# MAS ALU makefile 
#----------------------------------------------------

RTL_PATH := ../rtl
TB_PATH := ../tb
TEST_RESULTS_PATH := ../results
TEST_FILE_PATH := $(TEST_RESULTS_PATH)/test_file
ALU_INC_PATH := $(RTL_PATH)/inc
ALU_PATH := $(RTL_PATH)/alu/
ALU_TB_PATH := $(TB_PATH)/alu
TB_INC_PATH := $(TB_PATH)/inc
ALU_FILES ?= alu.f
ALU_FILE_LIST := $(addprefix $(ALU_PATH),$(shell cat $(ALU_PATH)$(ALU_FILES)))
OPT := -sverilog -R +incdir+$(ALU_INC_PATH) +incdir+$(TB_INC_PATH) +incdir+$(ALU_TB_PATH) +ntb_solver_array_size_warn=20000 

alu:
	cd $(BUILD_PATH); \
	vcs $(OPT) $(ALU_TB_PATH)/mas_alu_tb.sv $(ALU_FILE_LIST) | tee run.log; \
	urg -dir $(BUILD_PATH)/simv.vdb -format both; 

view_report:
	firefox $(BUILD_PATH)/urgReport/tests.html &

  
