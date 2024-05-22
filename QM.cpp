#include <iostream>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <algorithm>
using namespace std;

int _numVar;

string gen_bin_str(int n) { // dec to bin to string
    if (n == 0) return string(_numVar, '0');
    
    string s;
    while (n > 0) {
        s = (n % 2 == 0)? '0' + s : '1' + s;
        n /= 2; 
    }

    s.insert(0, 8 - s.length(), '0');

    return s;
}

class Term {
public:
    Term(int m, bool is_dc) {
        minterms.push_back(m);
        is_dontcare = is_dc;
        is_checked = 0;
        is_duplicated = 0;
        bin_str = gen_bin_str(m);
    }
    Term(vector<int> ms, string s) {
        minterms.insert(minterms.end(), ms.begin(), ms.end());
        bin_str = s;
        is_dontcare = 0;
        is_checked = 0;
        is_duplicated = 0;
    }

    vector<int> minterms;
    string bin_str;
    bool is_checked;
    bool is_dontcare;
    bool is_duplicated;
};

int count_bin_ones(int n) {
    int cnt = 0;
    while(n) {
        cnt += n & 1;
        n >>= 1;
    }
    return cnt;
}

int diff_one_bit(Term *a, Term *b) {
    int cnt = 0;
    int diff_bit;
    for (int i = 0; i < _numVar; i++) {
        if (a->bin_str[i] != b->bin_str[i]) {
            diff_bit = i;
            if (cnt++) return -1;
        }
    }
    return diff_bit;
}

void print_column(int column_num, map<int, vector<Term*>> column) {
    cout << "=====================\nColumn " << column_num << " \n=====================\n";

    for (auto group : column) {
        for (auto term : group.second) {

            if (term->is_dontcare) cout << "d ";
            else if (term->is_duplicated) cout << "x ";
            else if (term->is_checked) cout << "v ";
            else cout << "  ";

            cout << term->bin_str << ": ";

            int m_size = int(term->minterms.size());
            for (int i = 0; i < m_size - 1; i++) {
                cout << term->minterms[i] << ", ";
            } cout << term->minterms[m_size - 1] << endl;
        }
        cout << "---------------------\n";
    }

    cout << endl;
};

string gen_literal(string bin_str) {
    const string alphabet = "abcdefghij";
    string s;
    for (int i = 0; i < _numVar; i++) {
        if (bin_str[i] == '0') {
            s += alphabet[i];
            s += "\'";
        }
        else if (bin_str[i] == '1') s += alphabet[i];
    }
    return s;
}

struct QmSolution {
    int numVar;
    vector<string> primes;
    vector<vector<string>> minimumSops;
};

QmSolution *solveQm(int numVar, vector<int> minterms, vector<int> dontcares, bool verbose) {
    
    _numVar = numVar;
    vector<string> primes;
    vector<vector<string>> minimumSops;

    // grouping by counting 1's number
    int column_num = 1;
    map<int, vector<Term*>> column;
    set<int> groups;
    map<int, bool> is_minterm;

    for (const auto i : minterms) {
        is_minterm[i] = 1;
        int cnt = count_bin_ones(i);
        groups.insert(cnt);
        column[cnt].push_back(new Term(i, false));
    }

    for (const auto i : dontcares) {
        int cnt = count_bin_ones(i);
        groups.insert(cnt);
        column[cnt].push_back(new Term(i, true));
    }

    bool out_flag = 0;
    map<int, vector<Term*>> next_column;
    set<int> next_groups;
    vector<Term*> primes_term;

    while(!out_flag) {

        out_flag = 1;
        
        for (const auto group : column) {
            int group_num = group.first;
            if (group_num == *groups.rbegin()) break;
            if (!groups.count(group_num + 1)) continue;

            set<set<int>> avoid_duplicate;

            for (const auto term1 : column[group_num]) {
                for (const auto term2 : column[group_num+1]) {
                    int db = diff_one_bit(term1, term2);
                    if (db != -1) {
                        // cout << term1->bin_str << " " << term2->bin_str << " " << db << endl;
                        out_flag = 0;

                        term1->is_checked = 1;
                        term2->is_checked = 1;

                        string new_bin_str = term1->bin_str;
                        new_bin_str[db] = '-';

                        vector<int> new_minterms = term1->minterms;
                        new_minterms.insert(new_minterms.end(), term2->minterms.begin(), term2->minterms.end());
                        set<int> to_check(new_minterms.begin(), new_minterms.end());

                        if (!avoid_duplicate.count(to_check)) {
                            avoid_duplicate.insert(to_check);
                            next_column[group_num].push_back(new Term(new_minterms, new_bin_str));
                            next_groups.insert(group_num);
                        } else {
                            Term *ptr = new Term(new_minterms, new_bin_str);
                            ptr->is_duplicated = 1;
                            next_column[group_num].push_back(ptr);
                        }
                    }
                }
            } 
        }

        if (verbose) print_column(column_num, column);
        column_num++;

        for (const auto group : column) {
            for (const auto term : group.second) {
                if (!term->is_checked) {
                    primes.push_back(gen_literal(term->bin_str));
                    primes_term.push_back(term);
                }
            }
        }

        column = next_column;
        groups = next_groups;
        next_column.clear();
        next_groups.clear();
    }

    map<int, vector<Term*>> cmt; // covered_minterm_term : records terms which cover specific minterm
    map<int, bool> mc; // minterm_covered : minterm which has been covered

    for (auto term : primes_term) {
        for (auto m : term->minterms) {
            if (is_minterm[m]) {
                cmt[m].push_back(term);
                mc[m] = 0;
            }
        }
    }

    vector<Term*> essentials;

    for (auto m : cmt) {
        if (m.second.size() == 1) { // is Essential
            essentials.push_back(m.second[0]);
        }
    }

    for (auto e : essentials) {
        for (auto m : e->minterms) 
            mc[m] = 1;
    }

    for (auto m : mc) { // 對剩下的做 Patrick's Method
        if (m.second == false) {
            
        }
    }


    if (verbose) {
        // print the prime implicant chart of final result
    }

    QmSolution *sol = new QmSolution;
    sol->numVar = numVar;
    sol->primes = primes;
    sol->minimumSops = minimumSops;
    return sol;
}

int main() {
    int numVar = 8;
    vector<int> minterms = {0, 1, 2, 5, 6, 7, 8, 9, 10, 14};
    vector<int> dontcares = {};
    bool verbose = true;

    QmSolution *sol = solveQm(numVar, minterms, dontcares, verbose);
    cout << "Primes: " << endl;
    for (auto i : sol->primes) cout << i << endl;
    cout << endl << "minimumSops: " << endl;
    for (auto i : sol->minimumSops) { 
        for (auto j : i)
            cout << j << " + ";
        cout << endl;
    }
}