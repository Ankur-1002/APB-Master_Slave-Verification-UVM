# ===============================
# Makefile for UVM + VCS
# ===============================
# VCS paths
VCS_HOME = /tools/synopsys/vcs/V-2023.12
UVM_HOME = $(VCS_HOME)/etc/uvm-1.2
FSDB_PATH= /tools/synopsys/verdi/V-2023.12/share/PLI/VCS/linux64

# Compilation options
VCS_OPTS = -sverilog -full64 -kdb -lca -P $(FSDB_PATH)/novas.tab $(FSDB_PATH)/pli.a -debug_access+all -timescale=1ns/1ps  \
           +incdir+$(UVM_HOME)
# Source files
SRC = ./top.sv 
# Default target
all: comp sim
# Compile
comp:
	#vcs $(VCS_OPTS) -ntb_opts uvm -l comp.log $(SRC)
	vcs $(VCS_OPTS) -ntb_opts uvm -cm line+tgl+cond+fsm+branch -l comp.log $(SRC)

# Simulate
sim:
	./simv -a comp.log +ntb_random_seed_automatic -cm_dir ./mem_cov1 +UVM_TESTNAME=n_wr_rd_test +num_tx=2048 +UVM_VERBOSITY=UVM_LOW -ucli -do sim.do
	urg -dir mem_cov1.vdb -format both -report urgReport1
# ./simv -a vcs.log +fsdbfile+wave1.fsdb -cm_dir ./mem_cov1 +ntb_random_seed_automatic +UVM_TESTNAME=test
#	urg -dir mem_cov1.vdb -format both -report urgReport1
	
# Clean
clean:
	rm -rf simv* csrc* *.log *.key *.vpd *.vcd DVEfiles verdiLog

verdi:
	verdi -ssf sim.fsdb -full64

cov_VCS:
	verdi -cov -covdir mem_cov1.vdb
 

#report_VCS:
#	urg -dir mem_cov1.vdb mem_cov2.vdb mem_cov3.vdb mem_cov4.vdb -dbname merged_dir/merged_test -format both -report urgReport
