#!/usr/bin/env python
# -*- coding: utf-8 -*-

from time import time
from satispy import Variable, Cnf
from satispy.solver import Minisat, Lingeling
from satispy.io import DimacsCnf
from pprint import pprint
from checker import Checker
import sys

def propositional_nqueens(n):

    rules = 0
    t1 = time()
    exprs = Cnf()
    queens_by_point = {}
    queens_by_name = {}
    points_by_name = {}

    by_rows = [[] for x in xrange(n)]
    by_cols = [[] for x in xrange(n)]

    for point in points(n):
        name = 'queen_%d_%d' % point

        by_rows[point[1]].append(name)
        by_cols[point[0]].append(name)

        queen = Variable(name)
        queens_by_point[point] = queen
        queens_by_name[name] = queen
        points_by_name[name] = point

    for row_of_names in by_rows:
        orexp = Cnf()
        for name in row_of_names:
            orexp = orexp | queens_by_name[name]

        rules += 1
        exprs &= orexp

    for col_of_names in by_cols:
        orexp = Cnf()
        for name in col_of_names:
            orexp |= queens_by_name[name]

        rules += 1
        exprs &= orexp

    for row in xrange(n):
        for col in xrange(n):
            antecedent_name = by_rows[row][col]
            consequent_names = [by_rows[row][a] for a in xrange(n) if a != col]

            # queen_X_Y => (not(queen_X1_Y1) & not(queen_X2_Y2))
            # translates to
            # (not(queen_X_Y) or not(queen_X1_Y1)) and (not(queen_X_Y) or not(queen_X2_Y2))

            #andexpr = Cnf()
            #for name in consequent_names:
                #andexpr &= (-queens_by_name[name])

            #exprs &= (queens_by_name[antecedent_name] >> andexpr)

            for name in consequent_names:
                rules += 1
                exprs &= -queens_by_name[antecedent_name] | -queens_by_name[name]

    for col in xrange(n):
        for row in xrange(n):
            antecedent_name = by_cols[col][row]
            consequent_names = [by_cols[col][a] for a in xrange(n) if a != row]

            # queen_X_Y => (not(queen_X1_Y1) & not(queen_X2_Y2))
            # translates to
            # (not(queen_X_Y) or not(queen_X1_Y1)) and (not(queen_X_Y) or not(queen_X2_Y2))
            #andexpr = Cnf()
            #for name in consequent_names:
                #andexpr &= (-queens_by_name[name])

            #exprs &= (queens_by_name[antecedent_name] >> andexpr)

            for name in consequent_names:
                rules += 1
                exprs &= -queens_by_name[antecedent_name] | -queens_by_name[name]

    for point1 in points(n):
        for point2 in points(n):
            if point1 == point2:
                continue

            if are_diagonal(point1, point2):
                rules += 1
                #exprs &= (queens_by_point[point1] >> (-queens_by_point[point2]))
                exprs &= -queens_by_point[point1] | -queens_by_point[point2]

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
                    #andexpr = Cnf()
                    for point2 in points1:
                        if point2 != point1:
                            #andexpr &= (-queens_by_point[point2])
                            rules += 1
                            exprs &= -queens_by_point[point] | -queens_by_point[point1] | -queens_by_point[point2]

                    #exprs &= ((queens_by_point[point] & queens_by_point[point1]) >> andexpr)
    t2 = time()
    print('# defined %d rules in %f seconds' % (rules, t2 - t1))
    t1 = time()

    with open('/media/rust/%d.cnf' % n, 'w') as f:
        io = DimacsCnf()
        f.write(io.tostring(exprs))

    t2 = time()
    print('# wrote rules in %f seconds' % (t2 - t1))
    t1 = time()
    #return
    s = Minisat()
    #s = Lingeling(command='/home/bburns/projects/nqueens-solver/lingeling-bal-2293bef-151109/lingeling --witness=1 --verbose=1 %s')
    solution = s.solve(exprs)
    t2 = time()
    print('# solved in %f seconds' % (t2 - t1))

    if solution.error:
        raise Exception(solution.error)

    if solution.success:
        results = []

        #for a in solution.varmap:
            #if solution.varmap[a]:
                #results.append(points_by_name[a.name])
        for point in queens_by_point:
            if solution[queens_by_point[point]]:
                results.append(point)

        results.sort()

        return results
    else:
        raise Exception('Unsat.')

def points_along_line(point, rise, run, n):
    points = []
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

