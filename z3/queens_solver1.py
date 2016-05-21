#!/usr/bin/env python
# -*- coding: utf-8 -*-

#
#    nqueens.py - Solve the nqueens problem thanks to recursivity & z3 (constraint programming)
#
#    Modified from original source:
#    https://github.com/0vercl0k/z3-playground/blob/master/nqueens_z3.py
#
#    This program is free software: you can redistribute it and/or modify
#    it under the terms of the GNU General Public License as published by
#    the Free Software Foundation, either version 3 of the License, or
#    (at your option) any later version.
#
#    This program is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#    GNU General Public License for more details.
#
#    You should have received a copy of the GNU General Public License
#    along with this program.  If not, see <http://www.gnu.org/licenses/>.
#


from time import time
#from pprint import pprint
from z3 import *
from checker import Checker
import sys

def good_move(i, j, solutions):
    """Is it an allowed move ?"""

    for i1 in xrange(len(solutions)):
        x,y = solutions[i1]
        # a queen can't be on the same column / line / diag
        if x == i or y == j:
            return False
        if abs(x - i) == abs(y - j):
            return False

        for j1 in xrange(i1+1, len(solutions)):
            x1,y1 = solutions[j1]

            rise1 = x1 - x
            run1 = y1 - y

            rise2 = x - i
            run2 = y - j

            if rise1 * run2 == rise2 * run1:
                return False

    return True

def recurse_nqueens(n, ni, solution_list):
    """A queen can't be placed on the same diag/col/lin of an other"""
    i, j = 0, 0
    while i < n:
        while good_move(i, j, solution_list) == False and j < n:
            j += 1

        if j != n:
            if ni + 1 == n:
                return [(i, j)]

            r = recurse_nqueens(n, ni + 1, solution_list + [(i, j)])
            if r != None:
                return r + [(i, j)]
        else:
            j = 0
        i += 1
    return None

def nqueens(n):
    """Solves the problem of the nqueens thanks to recursivity/backtracking
    and returns the coordinates of the queens"""
    return sorted(recurse_nqueens(n, 0, []))

def abs_z3(a):
    """Get the absolute value of a Z3 variable"""
    return If(a >= 0, a, -a)

def toSMT2(f, status='unknown', name='benchmark', logic=''):
    v = (Ast * 0)()
    if isinstance(f, Solver):
        a = f.assertions()
        if len(a) == 0:
            f = BoolVal(True)
        else:
            f = And(*a)

    Z3_set_ast_print_mode(f.ctx_ref(), Z3_PRINT_SMTLIB2_COMPLIANT)
    return Z3_benchmark_to_smtlib_string(f.ctx_ref(), name, logic, status, '', 0, v, f.as_ast())

def nqueens_constraint_programming_opti(n):
    """Solves the problem of the nqueens thanks to constraint programming/z3 & a little trick"""
    funcs = {}
    row_for_queen = []
    for i in xrange(n):
        name = 'row_for_queen_%d' % i
        row_for_queen.append(Int(name))

    expressions = []
    s = SolverFor('QF_NIA')

    rules = []
    #expressions.append(row_for_queen[-1] > n/2)

    for i in xrange(n):
        # each queen must be in the chessboard's limits
        expressions.append(And(row_for_queen[i] >= 0, row_for_queen[i] < n))

    for i in xrange(n-1):
        for j in xrange(i + 1, n):
            expressions.append(row_for_queen[i] != row_for_queen[j])

    for i in xrange(n - 1):
        for j in xrange(i + 1, n):
            rise = Int('rise_%d_%d' % (j,i))
            expressions.append(rise == row_for_queen[j] - row_for_queen[i])
            expressions.append(abs_z3(rise) != abs(i-j))

    for i in xrange(n - 1):
        for j in xrange(i + 1, n):
            rise1 = Int('rise_%d_%d' % (j,i))
            run1 = j - i

            for k in xrange(j+1, n):

                rise2 = Int('rise_%d_%d' % (k,j))
                run2 = k - j

                expressions.append(run1 * rise2 != run2 * rise1)

    for expression in expressions:
        s.add(expression)


    if s.check() == unsat:
       raise Exception('Unsat.')

    m = s.model()


    rows = [m[Int('row_for_queen_%d' % i)].as_long() for i in xrange(n)]
    cols = range(n)
    model = sorted(zip(rows,cols))
    print model
    return model

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
        q = nqueens_constraint_programming_opti(n)
        #q = nqueens(n)
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

