from logic import *

# Figure 1. A Kodkod problem to color strongly connected components
# Power set enumerated, upper and lower out-of-bounds commented out
lang = [
	'A',        
	'B',       
	'C',        
	'D',		
	'Red',      
	'Green',    
	'Blue',     
	'Yellow',   	
	'adj(A,A)', 
	'adj(A,B)',	
	#'adj(A,C)',  
	#'adj(B,A)',  
	#'adj(B,B)',  
	'adj(B,C)',  
	#'adj(C,A)',  
	'adj(C,B)',  
	#'adj(C,C)', 
	'color(A,Red)',  
	'color(A,Green)',
	'color(A,Blue)', 
	'color(A,Yellow)',
	'color(B,Red)',  
	'color(B,Green)',
	'color(B,Blue)', 
	'color(B,Yellow)',
	'color(C,Red)',  
	'color(C,Green)',
	'color(C,Blue)', 
	'color(C,Yellow)'
]
reset("Color SCCs")
for var in lang:
	boolean(var)
#hard(["A", negate("B")], "A_or_!B")
#TODO case study hard/soft constraints
solve()
