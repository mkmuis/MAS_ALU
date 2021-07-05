#------------------------------------------------------
# MAS ALU TOP makefile 
#----------------------------------------------------

#TOP MAKEFILE PARAMETERS
export ROOT_PATH := $(shell pwd)
export SIM_PATH := $(ROOT_PATH)/sim
export BUILD_PATH := $(ROOT_PATH)/build

run_alu: clean_build build_alu

build_alu:
	$(MAKE) -C $(SIM_PATH) alu  

view_res:
	$(MAKE) -C $(SIM_PATH) view_report

clean_build:
	rm -rf $(BUILD_PATH)/*
