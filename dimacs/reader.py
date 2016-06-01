import sys
from checker import Checker

def reader(problem_filename, solution_filename):
    point_map = {}

    solution = []

    with open(problem_filename, 'r') as f:
        for line in f:
            atoms = line.strip().split(' ')
            if atoms[0] == 'c' and len(atoms) == 3 and atoms[2].startswith('queen_'):
                queen_parts = atoms[2].split('_')[1:]
                point = (int(queen_parts[0]), int(queen_parts[1]))
                point_map[point] = atoms[1]
                point_map[atoms[1]] = point
            else:
                break

    with open(solution_filename, 'r') as f:
        for line in f:
            atoms = line.strip().split(' ')
            if atoms[0] == 'v':
                ids = atoms[1:]
                for i in ids:
                    if int(i) > 0:
                        solution.append(point_map[i])
    return sorted(solution)

def display_solutions(s):
    print '# N = %s' % len(s)
    chessboard = [['0'] * len(s) for i in xrange(len(s))]
    for x,y in s:
        chessboard[x][y] = 'Q'
    for row in chessboard:
        print '# %s' % ' '.join(row)

def main(argc, argv):

    n = int(argv[1])
    q = reader(argv[2], argv[3])

    matrix = [[0] * n for i in xrange(n)]

    for x,y in q:
        matrix[x][y] = 1

    checker = Checker(matrix=matrix)
    if checker.test_all(False) == False:
        checker.print_error_matrix()
    else:
        display_solutions(q)
        print("print '%s'" % n)
        print("print '%s'" % ' '.join(str(column + 1) for row, column in q))

    return 0

if __name__ == '__main__':
    sys.exit(main(len(sys.argv), sys.argv))
