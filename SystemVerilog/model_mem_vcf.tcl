# vcf -verdi -f model_mem_vcf.tcl

set_fml_appmode FPV
set_fml_var fml_witness_on true
set_fml_var fml_vacuity_on true
set_fml_var fml_effort high

read_file -format sverilog -sva -top mem_top -vcs {-f file_list}

create_clock clk -period 100
create_rst rst

check_fv
report_fv
