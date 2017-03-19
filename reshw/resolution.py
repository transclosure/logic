# Natasha Danas - Resolution Implementation
from sys import stdin
'''
Runs the main
'''
def main():
    clauses = []
    for variables in stdin:
        clause = []
        for variable in variables.split():
            clause.append(int(variable))
        clauses.append(clause)
    print clauses
    return
main()
