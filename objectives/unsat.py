from gurobiAPI import *

""" Small UNSAT example """
spec = GurobiSpec("unsat")
spec.addVariable('x0')
spec.addVariable('x1')
spec.addVariable('x2')
spec.addVariable('x3')
spec.addClause(['x0', 'x1', 'x2', 'x3'])
spec.addClause(['!x0'])
spec.addClause(['!x1'])
spec.addClause(['!x2'])
spec.addClause(['!x3'])
spec.solve()
