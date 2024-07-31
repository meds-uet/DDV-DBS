package cache_defs;


parameter TAG_LSB = 12;
parameter TAG_MSB = 31;



typedef struct{

logic read;
logic write;

}CPU_Request_type;




typedef struct{

logic [TAG_MSB : TAG_LSB]tag;
logic [7:0]index;
logic [3:0]offset;

}Address_type;




typedef struct {

logic valid_bit;
logic dirty_bit;
logic [19:0]tag;
logic [127:0]data;


}cache_line_type;




endpackage
