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

def boolean(n): 
	global T
	b = T.addVar(lb=0.0, ub=1.0, vtype=GRB.BINARY, name=n)
	nb = T.addVar(lb=0.0, ub=1.0, vtype=GRB.BINARY, name=negate(n))
	T.addConstr(b + nb == 1.0)
	sugar(n,b)
	sugar(negate(n), nb)
	return b

def hard(clause, name):
	global T
	name = name.replace(" ", "_")
	c = boolean(name)
	T.addConstr(c == desugar(clause), name)
	T.addConstr(c == 1.0, name)

def reset(n):
	global T, Tname
	T = Model(n)
	Tname = n
	return T

def checksat():
	sat = False
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
		sat = True
	else:
		status = "UNKNOWN"
	print("STATUS:", status)
	return sat

def getmodel():
	print("MODEL:")
	for n in sugarmap.keys():
		print(n, "=", sugarmap[n].x)

def solve():
	global T, Tname, sugarmap
	try:
		T.write(Tname+".mps")
		T.write(Tname+".lp")
		T.optimize()
		if checksat(): getmodel()
	except GurobiError as e:
		print('Error code ' + str(e.errno) + ": " + str(e))
	except AttributeError:
		print('Encountered an attribute error')
