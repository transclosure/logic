from logic import *

# Small SAT example from genconstr.py to test API 
lang = [
	'x0',        
	'x1',       
	'x2',        
	'x3'
]
reset("Color SCCs")
for var in lang:
	boolean(var)
hard(['x0', 'x1', 'x2', 'x3'], "(x0 or x1 or x2 or x3)")
hard(['!x0'], "(~x0)")
hard(['!x1'], "(~x1)")
hard(['!x2'], "(~x2)")
hard(['!x3'], "(~x3)")
solve()
