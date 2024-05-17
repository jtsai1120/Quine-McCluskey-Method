#include <iostream>
#include <string>
#include <vector>
using namespace std;

struct QmSolution {
    int numVar;
    vector<string> primes;
    vector<vector<string> > minimumSops;
};

int count_ones(int n) {
    int count = 0;
    while(n) {
        count += n & 1;
        n >>= 1;
    }
    return count;
}

QmSolution *solveQm(int numVar, vector<int> minterms, vector<int> dontcares, bool verbose) {
    QmSolution *sol = new QmSolution;
    sol->numVar = numVar;

    if (verbose) {
        // print the process of QM method (every column)
    }

    if (verbose) {
        // print the prime implicant chart of final result
    }

    return sol;
}