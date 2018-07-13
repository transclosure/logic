from gurobiAPI import *

""" Small UNSAT example """
spec = GurobiSpec("unsat")
spec.addVariable('x0')
spec.addVariable('x1')
spec.addVariable('x2')
spec.addVariable('x3')
spec.addClause(['x0', 'x1', 'x2', 'x3'], "(x0 or x1 or x2 or x3)")
spec.addClause(['!x0'], "(~x0)")
spec.addClause(['!x1'], "(~x1)")
spec.addClause(['!x2'], "(~x2)")
spec.addClause(['!x3'], "(~x3)")
spec.solve()
