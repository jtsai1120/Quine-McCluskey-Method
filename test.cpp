#include <iostream>
#include <iomanip>
#include <string>
#include <sstream>
#include <vector>
#include <map>
#include <set>
#include <algorithm>
#include <cassert>
#include <climits>
using namespace std;

int _numVar;

string gen_bin_str(int n) { // dec to bin to string
    if (n == 0) return string(_numVar, '0');
    
    string s;
    while (n > 0) {
        s = (n % 2 == 0)? '0' + s : '1' + s;
        n /= 2; 
    }

    s.insert(0, _numVar - s.length(), '0');

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
    Term(vector<int> ms, string s, bool is_dc) {
        minterms.insert(minterms.end(), ms.begin(), ms.end());
        bin_str = s;
        is_dontcare = is_dc;
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
        else if (bin_str[i] == '1') {
            s += alphabet[i];
            //s += " ";
        }
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
    set<vector<string>> minimumSops_set;

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
                            next_column[group_num].push_back(new Term(new_minterms, new_bin_str, term1->is_dontcare&&term2->is_dontcare));
                            next_groups.insert(group_num);
                        } else {
                            Term *ptr = new Term(new_minterms, new_bin_str, term1->is_dontcare&&term2->is_dontcare);
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
                if (!term->is_checked && !term->is_duplicated && !term->is_dontcare) {
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

    for (auto term : primes_term) {
        for (auto m : term->minterms) {
            if (is_minterm[m]) {
                cmt[m].push_back(term);
            }
        }
    }

    if (verbose) {
        cout << "=====================\nPrime Implicant Chart\n=====================\n";
        cout << "                     |";
        for (auto m : cmt) cout << setw(4) << m.first << "|";
        cout << "\n --------------------+";
        for (auto m : cmt) cout << "----+";
        cout << endl;
        
        for (auto term : primes_term) {
            string tmp_str = gen_literal(term->bin_str); 
            cout << tmp_str;
            int tmp_size = int(tmp_str.size());
            while (tmp_size++ < 21) cout << " ";
            cout << "|";
            for (auto m : cmt) {
                cout << "   ";
                if (count(m.second.begin(), m.second.end(), term)) cout << "x|";
                else cout << " |";
            }
            cout << endl;
        }
        cout << " --------------------+";
        for (auto m : cmt) cout << "----+";
        cout << endl << endl;
    }
    
    // Patrick's Method
    vector<set<set<Term*>>> pm;
    for (auto m : cmt) {
        set<set<Term*>> tmp_sum;
        for (auto term : cmt[m.first])
            tmp_sum.insert({term});
        pm.push_back(tmp_sum);
    }

    // Merge Patrick's Method POS
    for (int i = int(pm.size()) - 1; i > 0; i--) {
        set<set<Term*>> new_sop;
        set<Term*> new_term;
        for (auto front : pm[i-1]) {
            for (auto back : pm[i]) {
                new_term.insert(front.begin(), front.end());
                new_term.insert(back.begin(), back.end());
                new_sop.insert(new_term);
                new_term.clear();
            }
        }
        pm.pop_back();
        pm[i-1] = new_sop;
    }
    
    // Find minimum set size
    int min_set_size = INT_MAX;
    for (auto i : pm[0]) min_set_size = min(min_set_size, int(i.size()));

    for (set<Term*> i : pm[0]) {
        if (int(i.size()) == min_set_size) {
            vector<string> tmp_s;
            for (Term* t : i) tmp_s.push_back(gen_literal(t->bin_str));
            minimumSops_set.insert(tmp_s);
        }
    }

    vector<vector<string>> minimumSops(minimumSops_set.begin(), minimumSops_set.end());
    
    QmSolution *sol = new QmSolution;
    sol->numVar = numVar;
    sol->primes = primes;
    sol->minimumSops = minimumSops;
    return sol;
}

int main() {
    
    int numVar;
    cin >> numVar;
    cin.ignore();

    vector<int> minterms;
    string tmp_s;
    getline(cin, tmp_s);
    istringstream iss1(tmp_s);
    int tmp_i;
    while(iss1 >> tmp_i) minterms.push_back(tmp_i);
    for (auto i : minterms) cout << i << ", ";
    cout << endl;

    vector<int> dontcares;
    getline(cin, tmp_s);
    istringstream iss2(tmp_s);
    while(iss2 >> tmp_i) dontcares.push_back(tmp_i);
    for (auto i : dontcares) cout << i << ", ";
    cout << endl;
    
    bool verbose = true;

    QmSolution *sol = solveQm(numVar, minterms, dontcares, verbose);
    
    cout << "Primes: " << endl;
    for (auto i : sol->primes) cout << i << endl;
    cout << endl << "minimumSops: " << endl;
    for (auto i : sol->minimumSops) { 
        for (int j = 0; j < int(i.size()) - 1; j++)
            cout << i[j] << " + ";
        cout << i[int(i.size() - 1)] << endl;
    }
    cout << endl;
}
