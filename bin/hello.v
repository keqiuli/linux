module counter10(input rstn, input clk, output [3:0]cnt, output cout);

        reg [4:0]               cnt_temp ;      //计数器寄存器
	reg [4:0]               a;
	integer			i;
        always@(posedge clk or negedge rstn) begin
                if(! rstn)begin         //复位时，计时归0
                        cnt_temp[3:0]        <= 4'b0 ;
			a 	             <= 5'd1;
                end
                else  begin  //计时10个cycle时，计时归0
                        cnt_temp[4:3]        <=2'b00;
			a		     <=5'd2;
                end               
		a[4:0] <=5'd10;
		cnt_temp        <=5'd1;
        end 
	always@(posedge clk) begin
		a <=5'd20;
	end
	always@(posedge clk)begin
		a[4] <= 1'b1;
		a[3] <= 1'b0;
		cnt_temp        <=5'd0;
	end

	always @(posedge clk)begin
		for (i = 0; i < 3; i++)
			a[i] <= 1'b0;
	end
	always @(posedge clk) begin
		for (i = 1; i < 4; i++)begin
			a[i] <= 1'b1;
		end
	end

        assign  cout = (cnt_temp==4'd9) ;       //输出周期位
        assign  cnt  = cnt_temp ;                       //输出实时计时器
endmodule
