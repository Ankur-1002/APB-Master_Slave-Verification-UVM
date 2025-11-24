# ===============================
# Makefile for UVM + VCS
# ===============================
# VCS paths
VCS_HOME = /tools/synopsys/vcs/V-2023.12
UVM_HOME = $(VCS_HOME)/etc/uvm-1.2
# Compilation options
VCS_OPTS = -sverilog -full64 -debug_access+all -timescale=1ns/1ps \
           +incdir+$(UVM_HOME) +define+UVM_NO_DEPRECATED \
           +define+UVM_OBJECT_MUST_HAVE_CONSTRUCTOR
# Source files
SRC = apb_pkg.sv apb_intf.sv  top.sv \
# Default target
all: comp sim
# Compile
comp:
	vcs $(VCS_OPTS) -ntb_opts uvm -l comp.log $(SRC)
# Simulate
sim:
	./simv +UVM_TESTNAME=apb_test +UVM_VERBOSITY=UVM_LOW -l sim.log
# Clean
clean:
	rm -rf simv* csrc* *.log *.key *.vpd *.vcd DVEfiles verdiLog
