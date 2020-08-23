# jg -fpv model_mem_jg.tcl

analyze -clear

analyze -sv09 -f file_list

elaborate -disable_auto_bbox -top mem_top

clock clk
reset rst

get_design_info

autoprove
# report
