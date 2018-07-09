from gurobipy import *

# Syntax
sugarmap = {}

def sugar(n, v):
	global sugarmap
	sugarmap[n] = v

def desugar(lits):
	global sugarmap
	clause = []
	for l in lits:
		clause.append(sugarmap[l]) 
	return or_(clause)

def negate(l):
	return "!"+l

# Semantics
T = None
Tname = None

def reset(n):
	global T, Tname
	T = Model(n)
	Tname = n

def boolean(n): 
	global T, Tname
	b = T.addVar(lb=0.0, ub=1.0, vtype=GRB.BINARY, name=n)
	nb = T.addVar(lb=0.0, ub=1.0, vtype=GRB.BINARY, name=negate(n))
	T.addConstr(b + nb == 1.0)
	sugar(n,b)
	sugar(negate(n), nb)

def hard(clause, n):
	global T, Tname
	# FIXME, add an objective variable
	# LP solver needs that level of indirection, see genconstr.py
	T.addConstr(desugar(clause) == 1.0, n)

def solve():
	global T, Tname
	try:
		# Save problem
		T.write(Tname+".mps")
		T.write(Tname+".lp")
		# Optimize
		T.optimize()
		# SAT
		status = T.getAttr(GRB.Attr.Status)
		if status == GRB.INF_OR_UNBD:
			status = "INFINITE OR UNBOUNDED"
		elif status == GRB.INFEASIBLE:
			status = "INFEASIBLE"
		elif status == GRB.UNBOUNDED:
			status = "UNBOUNDED"
		elif status != GRB.OPTIMAL:
			status = "Optimization was stopped with status "+status
		elif status == GRB.OPTIMAL:
			status = "OPTIMAL"
		else:
			status = "UNKNOWN"
		print("STATUS=", status)
		# MODEL
		objval = T.getAttr(GRB.Attr.ObjVal)
		print("OBJVAL=", objval)
	except GurobiError as e:
		print('Error code ' + str(e.errno) + ": " + str(e))
	except AttributeError:
		print('Encountered an attribute error')
