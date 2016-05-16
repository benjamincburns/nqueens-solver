#!/usr/bin/env python
# -*- coding: utf-8 -*-

from time import time
from pprint import pprint
from z3 import *
from checker import Checker
import sys


def points(n, x_start = 0, y_start = 0):
    for x in xrange(x_start, n):
        for y in xrange(y_start, n):
            yield x, y

def are_same_row(point1, point2):
    return point1[1] == point2[1]

def are_same_col(point1, point2):
    return point1[0] == point2[0]

def are_diagonal(point1, point2):
    return abs(point2[1] - point1[1]) == abs(point2[0] - point1[0])

def are_colinear(point1, point2, point3):
    rise1 = point3[1] - point2[1]
    rise2 = point2[1] - point1[1]
    run1 = point3[0] - point2[0]
    run2 = point2[0] - point1[0]

    return rise1 * run2 == rise2 * run1

def propositional_nqueens(n):
    """Solves the problem of the nqueens thanks to constraint programming/z3 & a little trick"""

    queens = Function('queens', IntSort(), IntSort(), BoolSort())
    x = Int('x')
    y = Int('y')

    expressions = []
    s = Solver()

    expressions.append(And(x >= 0, x < n))
    expressions.append(And(y >= 0, y < n))

    for val in xrange(n):
        expressions.append(queens(val, y) == True)
        expressions.append(queens(x, val) == True)

    for point1 in points(n):
        for point2 in points(n, point1[0] + 1, point1[1] + 1):
            if are_same_row(point1, point2) or are_same_col(point1, point2) or are_diagonal(point1, point2):
                expressions.append(Implies(queens(point1[0], point1[1]), Not(queens(point2[0], point2[1]))))

            for point3 in points(n, point2[1] + 1, point2[1] + 1):
                if are_colinear(point1, point2, point3):
                    expressions.append(Implies(And(queens(point1[0], point1[1]), queens(point2[0], point2[1])), Not(queens(point3[0], point3[1]))))


    for expression in expressions:
        s.add(expression)

    if s.check() == unsat:
       raise Exception('Unsat.')

    m = s.model()
    #return m

    results = sorted([(a[0].as_long(),a[1].as_long()) for a in m[queens].as_list() if hasattr(a, '__getitem__') and is_true(a[2])])
    return results

def display_solutions(s):
    print '# N = %s' % len(s)
    chessboard = [['0'] * len(s) for i in xrange(len(s))]
    for x,y in s:
        chessboard[x][y] = 'Q'
    for row in chessboard:
        print '# %s' % ' '.join(row)

def main(argc, argv):
    if argc != 2:
        print 'Usage: nqueens <n>'
        return 1

    n = int(argv[1], 10)
    t1 = time()
    try:
        q = propositional_nqueens(n)
    except:
        print('Threw after %f seconds' % (time()-t1))
        raise

    t2 = time()

    
    matrix = [[0] * n for i in xrange(n)]

    for x,y in q:
        matrix[x][y] = 1

    checker = Checker(matrix=matrix)
    if checker.test_all(False) == False:
        checker.print_error_matrix()
    else:
        display_solutions(q)
        print('# calculated in %f seconds' % (t2 - t1))
        print("print '%s'" % n)
        print("print '%s'" % ' '.join(str(column + 1) for row, column in q))

    return 0

if __name__ == '__main__':
    sys.exit(main(len(sys.argv), sys.argv))

