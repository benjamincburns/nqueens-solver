#!/usr/bin/env python
# -*- coding: utf-8 -*-

from __future__ import print_function
from colorama import Fore, Back, Style
import sys

class Checker(object):

    def __init__(self, matrix=None, columns=None):
        if not(matrix):
            self._n = len(columns)
            self._matrix = []
            for i in xrange(self._n):
                row = [0] * self._n
                row[columns[i]] = 1
                self._matrix.append(row)
        else:
            self._n = len(matrix)
            self._matrix = matrix

        self._error_matrix = []

        for row in xrange(self._n):
            self._error_matrix.append([])
            for col in xrange(self._n):
                self._error_matrix[row].append([])

    def _set_error_colour(self, color, i, j):
        self._error_matrix[i][j].append(color)

    def _check_row_or_column(self, row, id, is_row = False, verbose = True):
        t = 'row' if is_row else 'column'
        x = sum(row)

        if x < 1:
            if verbose:
                print('No queen in %s %s' % (t, id), file = sys.stderr)
            for j in xrange(self._n):
                if is_row:
                    self._set_error_colour(Back.YELLOW, id - 1, j)
                else:
                    self._set_error_colour(Back.YELLOW, j, id - 1)
            return False

        elif x > 1:
            if verbose:
                print('Too many queens (%s, expected 1) in %s %s' % (x, t, id), file = sys.stderr)

            for j in xrange(self._n):
                if is_row:
                    if self._matrix[id - 1][j] != 0:
                        self._set_error_colour(Back.YELLOW, id - 1, j)
                else:
                    if self._matrix[j][id - 1] != 0:
                        self._set_error_colour(Back.YELLOW, j, id - 1)

            return False

        return True

    def _is_diagonal(self, point1, point2, verbose=True):
        result = abs(point1[0] - point2[0]) == abs(point1[1] - point2[1])

        if result:
            if verbose:
                print('Queen at row %s, col %s forms diagonal with queen at row %s, col %s' % (point1[0], point1[1], point2[0], point2[1]), file=sys.stderr)

            self._set_error_colour(Back.BLUE, point1[0], point1[1])
            self._set_error_colour(Back.BLUE, point2[0], point2[1])
        elif verbose:
            print('Queens at %s,%s and %s,%s are not diagonal' % (point1[0], point1[1], point2[0], point2[1]))

        return result

    def _are_colinear(self, point1, point2, point3, verbose):
        rise1 = float(point3[1] - point2[1])
        rise2 = float(point2[1] - point1[1])

        run1 = float(point3[0] - point2[0])
        run2 = float(point2[0] - point1[0])

        result = (rise1/run1) == (rise2/run2)

        if result:
            if verbose:
                print('Queens at (%s, %s), (%s,%s) and (%s,%s) are colinear' % (point1[0], point1[1], point2[0], point2[1], point3[0], point3[1]), file=sys.stderr)

            self._set_error_colour(Back.RED, point1[0], point1[1])
            self._set_error_colour(Back.RED, point2[0], point2[1])
            self._set_error_colour(Back.RED, point3[0], point3[1])

        return result


    def get_rows(self):
        for row in self._matrix:
            yield row

    def _get_column(self, i):
        for row in self._matrix:
            yield row[i]

    def get_columns(self):
        for i in xrange(self._n):
            yield self._get_column(i)

    def test_rows(self, verbose=True):
        rows_good = True
        for row, id in zip(self._matrix, xrange(1, self._n+1)):
            rows_good = self._check_row_or_column(row, id, True, verbose) and rows_good

        if verbose:
            if rows_good:
                print('Rows good.')
            else:
                print('Rows error.', file = sys.stderr)
        return rows_good

    def test_columns(self, verbose=True):
        cols_good = True
        for column, id in zip(self.get_columns(), xrange(1, self._n+1)):
            cols_good = self._check_row_or_column(column, id, True, verbose) and cols_good

        if verbose:
            if cols_good:
                print('Columns good.')
            else:
                print('Columns error.', file = sys.stderr)
        return cols_good

    def test_diagonals(self, verbose=True):
        diagonals_good = True

        for i in xrange(self._n-1):
            try:
                column_i = self._matrix[i].index(1)
            except:
                continue

            for j in xrange(i+1, self._n):

                try:
                    column_j = self._matrix[j].index(1)
                except:
                    continue
                diagonals_good = not self._is_diagonal((i, column_i), (j, column_j), verbose) and diagonals_good

        if verbose:
            if diagonals_good:
                print('Diagonals good.')
            else:
                print('Diagonals error.', file = sys.stderr)
        return diagonals_good

    def test_colinearity(self, verbose=True):
        colinearity_good = True
        for i in xrange(self._n):
            try:
                column_i = self._matrix[i].index(1)
            except:
                continue
            for j in xrange(i+1, self._n):
                try:
                    column_j = self._matrix[j].index(1)
                except:
                    continue
                for k in xrange(j+1, self._n):
                    try:
                        column_k = self._matrix[k].index(1)
                    except:
                        continue
                    colinearity_good = not self._are_colinear((i, column_i), (j, column_j), (k, column_k), verbose) and colinearity_good

        if verbose:
            if colinearity_good:
                print('Colinearity good.')
            else:
                print('Colinearity error.', file = sys.stderr)

        return colinearity_good

    def test_all(self, verbose=True):
        row_result = self.test_rows(verbose)
        col_result = self.test_columns(verbose)
        diag_result = self.test_diagonals(verbose)
        colinearity_result = self.test_colinearity(verbose)

        return row_result and col_result and diag_result and colinearity_result

    def _get_coloured_row(self, i):
        for j in xrange(self._n):
            val = ''
            colours = self._error_matrix[i][j]
            for color in colours:
                val += color

            yield val + str(self._matrix[i][j]) + (Style.RESET_ALL if colours else '')

    def print_error_matrix(self):
        for i in xrange(self._n):
            print('%s' % ' '.join(self._get_coloured_row(i)))

if __name__ == '__main__':
    if len(sys.argv) == 1:
        print('usage: %s n [columns]' % sys.argv[0], file=sys.stderr)

    n = int(sys.argv[1], 10)
    columns = map(int, sys.argv[2:])

    if len(columns) != n:
        print('Expected %s columns, got %s' % (n, len(columns)), file=sys.stderr)

    checker = Checker(columns=[a-1 for a in columns])
    checker.test_all(False)
    checker.print_error_matrix();

