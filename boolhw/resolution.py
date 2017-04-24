# Natasha Danas - Resolution Implementation
from sys import stdin
'''
Constants
'''
def UNSAT(): return "unsat"
def SAT(): return "sat"
'''
Runs one resolution step
'''
def resstep(clauses, p):
    pclauses = []
    npclauses = []
    oclauses = []
    for clause in clauses:
        if p in clause:  
            clause.remove(p)   
            pclauses.append(clause)
        elif -p in clause:
            clause.remove(-p)  
            npclauses.append(clause)
        else:               
            oclauses.append(clause)
    for pclause in pclauses:
        for npclause in npclauses:
            oclauses.append(pclause|npclause)
    return oclauses
'''
Runs a resolution loop
'''
def resloop(clauses, variables):
    for p in variables:
        clauses = resstep(clauses, p)
        if set() in clauses:
            return UNSAT()
    return SAT()
'''
Runs the main
'''
def main():
    clauses = []
    variables = set()
    for line in stdin:
        clause = set()
        for word in line.split():
            variable = int(word)
            clause.add(variable)
            variables.add(abs(variable))
        if clause: clauses.append(clause)
    print resloop(clauses, variables)
    return
main()
