#!/usr/bin/env python
# -*- coding: utf-8 -*-

from time import time
from pprint import pprint
from z3 import *
from checker import Checker
import sys


def propositional_nqueens(n, print_lines = False, solve_problem = True):

    if solve_problem:
        s = SolverFor('QF_BV')
        queens_by_point = {}
        queens_by_name = {}

    by_rows = [[] for x in xrange(n)]
    by_cols = [[] for x in xrange(n)]

    if print_lines:
        print '(set-logic QF_BV)'
        print ';declarations in the form queen_col_row - if true, queen occupies space on board at col, row'

    for point in points(n):
        name = 'queen_%d_%d' % point

        by_rows[point[1]].append(name)
        by_cols[point[0]].append(name)

        if solve_problem:
            queen = Bool(name)
            queens_by_point[point] = queen
            queens_by_name[name] = queen

        if print_lines:
            print '(declare-const %s Bool)' % name


    if print_lines:
        print
        print ';at least one value in each row must be true'

    for row_of_names in by_rows:
        if print_lines:
            print '(assert (or %s))' % ' '.join(row_of_names)

        if solve_problem:
            s.add(Or(*[queens_by_name[name] for name in row_of_names]))
        
    if print_lines:
        print
        print ';at least one value in each column must be true'

    for col_of_names in by_cols:
        if print_lines:
            print '(assert (or %s))' % ' '.join(col_of_names)

        if solve_problem:
            s.add(Or(*[queens_by_name[name] for name in col_of_names]))

    if print_lines:
        print
        print ';only one value in each row may be true'

    for row in xrange(n):
        for col in xrange(n):
            antecedent_name = by_rows[row][col]
            consequent_names = [by_rows[row][a] for a in xrange(n) if a != col]

            if solve_problem:
                s.add(Implies(queens_by_name[antecedent_name], And(*[Not(queens_by_name[a]) for a in consequent_names])))

            if print_lines:
                print '(assert (=> %s (not (and %s))))' % (antecedent_name, ' '.join('(not %s)' % a for a in consequent_names))

    if print_lines:
        print
        print ';only one value in each column may be true'

    for col in xrange(n):
        for row in xrange(n):
            antecedent_name = by_cols[col][row]
            consequent_names = [by_cols[col][a] for a in xrange(n) if a != row]

            if solve_problem:
                s.add(Implies(queens_by_name[antecedent_name], Not(And(*[queens_by_name[a] for a in consequent_names]))))

            if print_lines:
                print '(assert (=> %s (not (and %s))))' % (antecedent_name, ' '.join(consequent_names))


    if print_lines:
        print
        print '; no two queens may fall on the same diagonal'

    for point1 in points(n):
        for point2 in points(n):
            if point1 == point2:
                continue

            if are_diagonal(point1, point2):
                if solve_problem:
                    s.add(Implies(queens_by_point[point1], Not(queens_by_point[point2])))

                if print_lines:
                    print '(assert (=> %s (not %s)))' % ('queen_%d_%d' % point1, 'queen_%d_%d' % point2)

    if print_lines:
        print
        print '; no three queens may fall on the same line'

    for point in points(n):
        for slope in points(n, 1, 1):

            if slope == (1,1):
                continue

            lines = [ ]
            line = points_along_line(point, slope[0], slope[1], n)

            if len(line) >= 2:
                lines.append(line)

            line = points_along_line(point, -slope[0], slope[1], n)

            if len(line) >= 2:
                lines.append(line)


            if len(lines) == 0:
                continue

            for points1 in lines:
                for point1 in points1:
                    if print_lines:
                        print '(assert (=> (and %s %s) (and %s)))' % ('queen_%d_%d' % point,
                                'queen_%d_%d' % point1,
                                ' '.join('(not queen_%d_%d)' % a for a in points1 if a != point1))
                    if solve_problem:
                        s.add(Implies(And(queens_by_point[point], queens_by_point[point1]), And(*[Not(queens_by_point[a]) for a in points1 if a != point1])))


    if print_lines:
        print '(check-sat)'
        print '(get-model)'

    if solve_problem:
        if s.check() == unsat:
            # dat error checking
            raise Exception('Unsat.')

        m = s.model()


        results = []
        for point in queens_by_point:
            if is_true(m[queens_by_point[point]]):
                results.append(point)

        results.sort()

        return results

def points_along_line(point, rise, run, n):
    points = []
    start_point = point

    #while 0 <= (start_point[0] - run) < n and 0 <= (start_point[1] - rise) < n:
        #start_point = (start_point[0] - run, start_point[1] - rise)
        #points.append(start_point)

    start_point = point
    while 0 <= (start_point[0] + run) < n and 0 <= (start_point[1] + rise) < n:
        start_point = (start_point[0] + run, start_point[1] + rise)
        points.append(start_point)

    return points

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


def display_solutions(s):
    print '# N = %s' % len(s)
    chessboard = [['0'] * len(s) for i in xrange(len(s))]
    for x,y in s:
        chessboard[x][y] = 'Q'
    for row in chessboard:
        print '# %s' % ' '.join(row)

def main(argc, argv):
    if not (1 < argc <= 3):
        print 'Usage: nqueens <n>'
        return 1

    n = int(argv[1], 10)

    if (len(argv) == 3):
        print_lines = True
    else:
        print_lines = False
    t1 = time()
    try:
        q = propositional_nqueens(n, print_lines=print_lines, solve_problem = not print_lines)
    except:
        print('Threw after %f seconds' % (time()-t1))
        raise

    t2 = time()

    if print_lines:
            print('; generated in %f seconds' % (t2 - t1))
    else:
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

