#!/usr/bin/env python
# -*- coding: utf-8 -*-

from time import time
from fractions import gcd
from fractions import Fraction
import sys

epsilon = sys.float_info.epsilon * 5

def clause(f, *args):
    f.write(' '.join(str(a) for a in sorted(args)))
    f.write(' 0\n')

def propositional_nqueens(n):

    rules = 0
    t1 = time()
    queens = []
    queens_by_point = {}
    points_by_name = {}
    ids_by_name = {}
    ids_by_point = {}

    by_rows = [[] for x in xrange(n)]
    by_cols = [[] for x in xrange(n)]

    with open('comments.cnf', 'w') as comments:
        with open('clauses.cnf', 'w') as clauses:
            with open('problem.cnf', 'w') as problem:
                for point in points(n):
                    name = 'queen_%d_%d' % point

                    by_rows[point[1]].append(name)
                    by_cols[point[0]].append(name)

                    queens.append(name)
                    ids_by_name[name] = len(queens)
                    ids_by_point[point] = len(queens)
                    queens_by_point[point] = name
                    points_by_name[name] = point
                    comments.write('c %d %s\n' % (len(queens), name))

                for row_of_names in by_rows:
                    rules += 1
                    clause(clauses, *(ids_by_name[name] for name in row_of_names))

                for col_of_names in by_cols:
                    rules += 1
                    clause(clauses, *(ids_by_name[name] for name in row_of_names))

                for row in xrange(n):
                    for col in xrange(n):
                        antecedent_name = by_rows[row][col]
                        consequent_names = [by_rows[row][a] for a in xrange(n) if a != col]

                        for name in consequent_names:
                            rules += 1
                            clause(clauses, *(-ids_by_name[antecedent_name], -ids_by_name[name]))

                for col in xrange(n):
                    for row in xrange(n):
                        antecedent_name = by_cols[col][row]
                        consequent_names = [by_cols[col][a] for a in xrange(n) if a != row]

                        for name in consequent_names:
                            rules += 1
                            clause(clauses, *(-ids_by_name[antecedent_name], -ids_by_name[name]))

                for point1 in points(n):
                    for point2 in points(n):
                        if point1 == point2:
                            continue

                        if are_diagonal(point1, point2):
                            rules += 1
                            clause(clauses, *(-ids_by_name[queens_by_point[point1]], -ids_by_name[queens_by_point[point2]]))

                for x1 in xrange(n):
                    for x2 in xrange(x1 + 1, n):
                        run = x2 - x1

                        for y1 in xrange(n):
                            for y2 in xrange(n):
                                if y1 == y2:
                                    continue

                                rise = y2 - y1

                                #if point collision or if inspecting diagonal, continue
                                if run == abs(rise):
                                    continue

                                step = run / gcd(rise, run)

                                #for x3 in xrange(x2 + 1, n):
                                for x3 in xrange(x2 + step, n, step):

                                    y3 = y2 + (float(x3 - x2) * rise)/run

                                    iy3 = int(round(y3))

                                    if abs(iy3 - y3) > epsilon:
                                        continue

                                    if n <= iy3 or iy3 < 0:
                                        continue

                                    rules += 1
                                    clause(clauses, -ids_by_point[(x1, y1)], -ids_by_point[(x2, y2)], -ids_by_point[(x3, iy3)])

                problem.write('p cnf %d %d\n' % (len(queens), rules))

    t2 = time()
    print('# defined %d rules in %f seconds' % (rules, t2 - t1))

    return

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


def main(argc, argv):
    if argc != 2:
        print 'Usage: nqueens <n>'
        return 1

    n = int(argv[1], 10)

    propositional_nqueens(n)
    return 0

if __name__ == '__main__':
    sys.exit(main(len(sys.argv), sys.argv))

