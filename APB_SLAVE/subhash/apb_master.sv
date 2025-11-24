module apb_master(
	input transfer,  						//to master from processor to initiate the transaction	
	input READ_WRITE,						//signal that says master to read or write from slave
	input apb_wr_addr,						//signal that gives apb write address to slave
	input apb_rd_addr,						//signal that gives apb read address to slave
	output apb_rd_data_out					//the data read from slave
);



endmodule
