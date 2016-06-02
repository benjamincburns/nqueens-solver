#include <stdlib.h>
#include <stdio.h>
#include <float.h>

void write_comments(const unsigned int n);
void write_problem(const unsigned int n, const unsigned int clauses);
unsigned int write_row_col_constraints(FILE* f, const unsigned int n);
unsigned int write_diagonal_constraints(FILE* f, const unsigned int n);
unsigned int write_collinear_constraints(FILE* f, const unsigned int n);

unsigned int point_to_id(const unsigned int n, const unsigned int x, const unsigned int y);
unsigned int gcd(unsigned int u, unsigned int v);

long double epsilon = LDBL_EPSILON * 5;

int main(int argc, char** argv) {

    if (argc != 2) {
        printf("Usage: dimacs_nqueens n");
        return 0;
    }

    unsigned int n = atoi(argv[1]);
    unsigned int rule_count = 0;

    write_comments(n);
    FILE* clauses = fopen("clauses.cnf", "w");
    rule_count += write_row_col_constraints(clauses, n);
    rule_count += write_diagonal_constraints(clauses, n);
    rule_count += write_collinear_constraints(clauses, n);
    fclose(clauses);

    write_problem(n, rule_count);
}

void write_comments(const unsigned int n) {
    unsigned int id = 0;
    FILE* comments = fopen("comments.cnf", "w");

    for (unsigned int i = 0; i < n; i++) {
        for (unsigned int j = 0; j < n; j++) {
            fprintf(comments, "c %u queen_%u_%u\n", ++id, i, j);
        }
    }

    fclose(comments);
}

unsigned int write_row_col_constraints(FILE* f, const unsigned int n) {
    unsigned int rule_count = 0;

    // at least one queen per row must be true
    for (unsigned int i = 0; i < n; i++) {
        for (unsigned int j = 0; j < n; j++) {
            fprintf(f, "%u ", point_to_id(n, i, j));
        }
        fprintf(f, "0\n");
        ++rule_count;
    }

    // at least one queen per column must be true
    for (unsigned int i = 0; i < n; i++) {
        for (unsigned int j = 0; j < n; j++) {
            fprintf(f, "%u ", point_to_id(n, j, i));
        }
        fprintf(f, "0\n");
        ++rule_count;
    }

    // only one queen per row may be true
    for (unsigned int y = 0; y < n; y++) {
        for (unsigned int x1 = 0; x1 < n; x1++) {
            for (unsigned int x2 = x1 + 1; x2 < n; x2++) {
                fprintf(f, "-%u -%u 0\n", point_to_id(n, x1, y), point_to_id(n, x2, y));
                ++rule_count;
            }
        }
    }

    // only one queen per column may be true
    for (unsigned int x = 0; x < n; x++) {
        for (unsigned int y1 = 0; y1 < n; y1++) {
            for (unsigned int y2 = y1 + 1; y2 < n; y2++) {
                fprintf(f, "-%u -%u 0\n", point_to_id(n, x, y1), point_to_id(n, x, y2));
                ++rule_count;
            }
        }
    }

    return rule_count;
}

unsigned int write_diagonal_constraints(FILE* f, const unsigned int n) {
    unsigned int rule_count = 0;

    for (unsigned int x1 = 0; x1 < n; x1++) {
        for (unsigned int x2 = x1 + 1; x2 < n; x2++) {

            unsigned int run = x2 - x1;

            for (unsigned int y1 = 0; y1 < n; y1++) {

                unsigned int y2 = y1 + run;

                if (y2 < n) {
                    fprintf(f, "-%u -%u 0\n", point_to_id(n,x1, y1), point_to_id(n, x2, y2));
                    ++rule_count;
                }

                y2 = y1 - run;
                if (y2 < n) {
                    fprintf(f, "-%u -%u 0\n", point_to_id(n,x1, y1), point_to_id(n, x2, y2));
                    ++rule_count;
                }
            }
        }
    }

    return rule_count;
}

unsigned int write_collinear_constraints(FILE* f, const unsigned int n) {
    int rule_count = 0;

    // 6,14 10,6 13,0
    for (int x1 = 0; x1 < n; x1++) {
        for (int x2 = x1 + 1; x2 < n; x2++) {

            int run = x2 - x1; //4

            for (int y1 = 0; y1 < n; y1++) {
                for (int y2 = 0; y2 < n; y2++) {
                    if (y1 == y2) {
                        continue;
                    }

                    int rise = y2 - y1; // -8

                    if (run == rise || run == -rise) {
                        continue;
                    }

                    unsigned int positive_rise = rise < 0 ? -rise : rise; // 8

                    unsigned int gcd_val = gcd(positive_rise, (unsigned int)run); //4
                    unsigned int step = run / gcd_val; //1

                    // rise: 13, run: 2, gcd: 1, step: 2
                    //printf("rise: %d, run: %d, gcd: %d, step: %d\n", positive_rise, run, gcd_val, step);

                    for (int x3 = x2 + step, i = 1; x3 < n; x3 += step, ++i) {
                        long double y3 = y2 + ((long double)(x3 - x2) * rise) / run; // 10 + ((13 - 10) * -8) / 4
                        unsigned int iy3 = (unsigned int) y3;

                        if (y3 - iy3 >= 0.5) {
                            iy3++;
                        }

                        long double diff = iy3 - y3;
                        if (diff < 0) {
                            diff = -diff;
                        }

                        if (diff > epsilon || n <= iy3 || iy3 < 0) {
                            continue;
                        }

                        fprintf(f, "-%u -%u -%u 0\n", point_to_id(n,x1, y1), point_to_id(n, x2, y2), point_to_id(n, x3, iy3));
                        ++rule_count;
                    }
                }
            }
        }
    }

    return rule_count;
}

void write_problem(const unsigned int n, const unsigned int clauses) {
    FILE* problem = fopen("problem.cnf", "w");

    fprintf(problem, "p cnf %u %u\n", n * n, clauses);

    fclose(problem);
}

unsigned int point_to_id(const unsigned int n, const unsigned int x, const unsigned int y) {
    return y * n + x + 1;
}

// stolen from https://en.wikipedia.org/wiki/Binary_GCD_algorithm#Iterative_version_in_C
unsigned int gcd(unsigned int u, unsigned int v) {
    int shift;

    /* GCD(0,v) == v; GCD(u,0) == u, GCD(0,0) == 0 */
    if (u == 0) return v;
    if (v == 0) return u;

    /* Let shift := lg K, where K is the greatest power of 2
     *         dividing both u and v. */
    for (shift = 0; ((u | v) & 1) == 0; ++shift) {
        u >>= 1;
        v >>= 1;
    }

    while ((u & 1) == 0) {
        u >>= 1;
    }

    /* From here on, u is always odd. */
    do {
        /* remove all factors of 2 in v -- they are not common */
        /*   note: v is not zero, so while will terminate */
        while ((v & 1) == 0) {  /* Loop X */
            v >>= 1;
        }

        /* Now u and v are both odd. Swap if necessary so u <= v,
         *           then set v = v - u (which is even). For bignums, the
         *                     swapping is just pointer movement, and the subtraction
         *                               can be done in-place. */
        if (u > v) {
            unsigned int t = v; v = u; u = t;
        }  // Swap u and v.

        v = v - u;                       // Here v >= u.
    } while (v != 0);

    /* restore common factors of 2 */
    return u << shift;
}

