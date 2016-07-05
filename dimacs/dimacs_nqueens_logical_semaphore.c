#include <stdlib.h>
#include <stdio.h>
#include <float.h>

void write_comments(const unsigned int n);
void write_problem(const unsigned int n, unsigned int vars, const unsigned int clauses);

unsigned int write_row_col_constraints(FILE* f, const unsigned int n, unsigned int* last_var);
unsigned int write_diagonal_constraints(FILE* f, const unsigned int n, unsigned int* last_var);
unsigned int write_collinear_constraints(FILE* f, const unsigned int n, unsigned int* last_var);
unsigned int handle_semaphore_from_point(FILE* f, const unsigned int n, int rise, int run, int x1, int y1, unsigned int* last_var);

unsigned int write_mutex_clause(FILE* f, unsigned int var_a, unsigned int var_b, unsigned int* last_var);
unsigned int write_semaphore_clause(FILE* f, unsigned int last_queen_id, unsigned int curr_queen_id, unsigned int* last_shadow_id, unsigned int *last_collector_id, unsigned int* last_var);
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

    unsigned int last_var = point_to_id(n, n-1, n-1);

    write_comments(n);
    FILE* clauses = fopen("clauses.cnf", "w");
    rule_count += write_row_col_constraints(clauses, n, &last_var);
    rule_count += write_diagonal_constraints(clauses, n, &last_var);
    rule_count += write_collinear_constraints(clauses, n, &last_var);

    fclose(clauses);

    write_problem(n, last_var, rule_count);
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

unsigned int write_row_col_constraints(FILE* f, const unsigned int n, unsigned int* last_var) {
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
        for (unsigned int x = 0; x < n; x++) {
            unsigned int var_a = point_to_id(n, x, y);
            unsigned int var_b = ((x < n - 1) ? point_to_id(n, x + 1, y) : 0);
            rule_count += write_mutex_clause(f, var_a, var_b, last_var);
        }
    }

    // only one queen per column may be true
    for (unsigned int x = 0; x < n; x++) {
        for (unsigned int y = 0; y < n; y++) {

            unsigned int var_a = point_to_id(n, x, y);
            unsigned int var_b = ((y < n - 1) ? point_to_id(n, x, y + 1) : 0);

            rule_count += write_mutex_clause(f, var_a, var_b, last_var);
        }
    }

    return rule_count;
}

unsigned int write_diagonal_constraints(FILE* f, const unsigned int n, unsigned int* last_var) {
    unsigned int rule_count = 0;

    // positive slope diagonals
    for (unsigned int x = 0; x < n - 1; x++) {
        for (unsigned int y = 0; y < ((x == 0) ? n : 1); y++) {

            // positive length examples:
            // 1 0 0 0     0 1 0 0     0 0 1 0
            // 0 1 0 0     0 0 1 0     0 0 0 1
            // 0 0 1 0     0 0 0 1     0 0 0 0
            // 0 0 0 1     0 0 0 0     0 0 0 0
            // 0, 0 => n   1, 0 => 3   2, 0 => 2
            unsigned int diagonal_length = n - (x + y);

            if (diagonal_length < 2) {
                continue;
            }

            // for each diagonal with positive slope
            for (unsigned int step = 0; step < diagonal_length; step++) {
                // x1, y1 are coordinate of item along diagonal
                unsigned int x1 = x + step;
                unsigned int y1 = y + step;

                unsigned int var_a = point_to_id(n, x1, y1);
                unsigned int var_b = ((x1 < n - 1 && y1 < n - 1) ?  point_to_id(n, x1 + 1, y1 + 1) : 0);
                rule_count += write_mutex_clause(f, var_a, var_b, last_var);
            }
        }

    }

    for (unsigned int x = 0; x < n - 1; x++) {
        for (unsigned int y = ((x == 0) ? 1 : n - 1); y < n; y++) {

            // negative length examples
            // 0 0 0 1     0 0 1 0     0 0 0 0     0 0 0 0
            // 0 0 1 0     0 1 0 0     0 0 0 1     0 0 0 0
            // 0 1 0 0     1 0 0 0     0 0 1 0     0 0 0 1
            // 1 0 0 0     0 0 0 0     0 1 0 0     0 0 1 0
            // 0, 3 => 4   0, 2 => 3   1, 3 => 3   2, 3 = > 2
            unsigned int diagonal_length = (x == 0) ? y + 1 : n - x;

            if (diagonal_length < 2) {
                continue;
            }

            for (unsigned int step = 0; step < diagonal_length; step++) {
                unsigned int x1 = x + step;
                unsigned int y1 = y - step;

                unsigned int var_a = point_to_id(n, x1, y1);
                unsigned int var_b = ((x1 < n - 1 && y1 > 0) ?  point_to_id(n, x1 + 1, y1 - 1) : 0);
                rule_count += write_mutex_clause(f, var_a, var_b, last_var);
            }
        }
    }

    return rule_count;
}

unsigned int write_collinear_constraints(FILE* f, const unsigned int n, unsigned int* last_var) {
    int rule_count = 0;

    // for each slope
    for (int rise = 1; rise <= (n + 1)/2; rise++) {
        for (int run = 1; run <= (n + 1)/2; run++) {
            //printf("%d/%d\n", rise, run);
            if (rise == run || gcd(rise, run) != 1) {
                //printf("continuing due to equality or reducible fraction\n");
                continue;
            }

            // for each point
            for (int x1 = 0; x1 < n; x1++) {
                for (int y1 = 0; y1 < n; y1++) {
                    rule_count += handle_semaphore_from_point(f, n, rise, run, x1, y1, last_var);
                    rule_count += handle_semaphore_from_point(f, n, 0 - rise, run, x1, y1, last_var);
                }
            }
        }
    }

    return rule_count;
}

unsigned int  handle_semaphore_from_point(FILE* f, const unsigned int n, int rise, int run, int x1, int y1, unsigned int* last_var) {
    unsigned int rule_count = 0;

    // only write out rules from the start of the line
    // subtracting rise from y or run from x should be less than zero
    // when we're at the start of the line
    int reverseXStep = x1 - run;
    int reverseYStep = y1 - rise;
    if (reverseXStep >= 0 && reverseXStep < n && reverseYStep >= 0 && reverseYStep < n) {
        //printf ("continuing because %d,%d is not at the start of a line\n", x1, y1);
        return 0;
    }

    // only write out rules for lines with 3 or more points
    int doubleForwardXStep = x1 + run * 2;
    int doubleForwardYStep = y1 + rise * 2;
    if (doubleForwardXStep < 0 || doubleForwardXStep >= n || doubleForwardYStep < 0 || doubleForwardYStep >= n) {
        //printf ("continuing because line at %d,%d does not have more than three points.\n", x1, y1);
        return 0;
    }

    unsigned int last_queen_id = 0; 
    unsigned int curr_queen_id = point_to_id(n, x1, y1);
    unsigned int last_shadow_id = 0;
    unsigned int last_collector_id = 0;
    rule_count += write_semaphore_clause(f, last_queen_id, curr_queen_id, &last_shadow_id, &last_collector_id, last_var);


    //printf ("%d/%d\n", rise, run);
    //printf ("%d,%d  ", x1, y1);

    int x2 = x1 + run;
    int y2 = y1 + rise;

    while (x2 >= 0 && x2 < n && y2 >= 0 && y2 < n) {
        last_queen_id = curr_queen_id;
        //printf ("%d,%d  ", x2, y2);
        curr_queen_id = point_to_id(n, x2, y2);
        rule_count += write_semaphore_clause(f, last_queen_id, curr_queen_id, &last_shadow_id, &last_collector_id, last_var);
        x2 += run;
        y2 += rise;
    }

    //printf("\n");

    return rule_count;
}

void write_problem(const unsigned int n, unsigned int vars, const unsigned int clauses) {
    FILE* problem = fopen("problem.cnf", "w");

    fprintf(problem, "p cnf %u %u\n", vars, clauses);

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

unsigned int write_mutex_clause(FILE* f, unsigned int var_a, unsigned int var_b, unsigned int* last_var) {
    unsigned int rule_count = 0;
    unsigned int shadow_a = ++(*last_var);

    // var_a --> shadow_a
    fprintf(f, "-%u %u 0\n", var_a, shadow_a);
    ++rule_count;

    if (var_b != 0) {
        // shadow_a --|--> b
        fprintf(f, "-%u -%u 0\n", shadow_a, var_b);
        ++rule_count;

        unsigned int shadow_b = shadow_a + 1;

        // shadow_a --> shadow_b
        fprintf(f, "-%u %u 0\n", shadow_a, shadow_b);
        ++rule_count;
    }

    return rule_count;
}

unsigned int write_semaphore_clause(FILE* f, unsigned int last_queen_id, unsigned int curr_queen_id, unsigned int* last_shadow_id, unsigned int *last_collector_id, unsigned int* last_var) {

    unsigned int rule_count = 0;

    unsigned int curr_shadow_id = ++(*last_var);
    unsigned int curr_collector_id = 0;

    fprintf(f, "-%u %u 0\n", curr_queen_id, curr_shadow_id);
    ++rule_count;
    if (last_queen_id > 0) {
        curr_collector_id = ++(*last_var);

        fprintf(f, "-%u %u 0\n", *last_shadow_id, curr_shadow_id);
        ++rule_count;

        fprintf(f, "-%u -%u %u 0\n", *last_shadow_id, curr_queen_id, curr_collector_id);
        ++rule_count;

        if (*last_collector_id != 0) {
            fprintf(f, "-%u %u 0\n", *last_collector_id, curr_collector_id);
            ++rule_count;

            fprintf(f, "-%u -%u 0\n", *last_collector_id, curr_queen_id);
            ++rule_count;
        }
    }

    *last_shadow_id = curr_shadow_id;
    *last_collector_id = curr_collector_id;

    return rule_count;
}

