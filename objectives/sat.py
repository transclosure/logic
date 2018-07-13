from gurobiAPI import *

# Small SAT example from genconstr.py
lang = [
	'x0',        
	'x1',       
	'x2',        
	'x3'
]
reset("sat")
for var in lang:
	boolean(var)
hard(['x0', '!x1', 'x2'], "(x0 or ~x1 or x2)")
hard(['x1', '!x2', 'x3'], "(x1 or ~x2 or x3)")
hard(['x2', '!x3', 'x0'], "(x2 or ~x3 or x0)")
hard(['x3', '!x0', 'x1'], "(x3 or ~x0 or x1)")
hard(['!x0', '!x1', 'x2'], "(~x0 or ~x1 or x2)")
hard(['!x1', '!x2', 'x3'], "(~x1 or ~x2 or x3)")
hard(['!x2', '!x3', 'x0'], "(~x2 or ~x3 or x0) ")
hard(['!x3', '!x0', 'x1'], "(~x3 or ~x0 or x1)")
solve()
