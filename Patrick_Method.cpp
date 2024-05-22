#include <iostream>
#include <vector>
#include <algorithm>
#include <set>
#include <string>
#include <sstream>
using namespace std;

int main() {
    int product_num;
    cin >> product_num;
    cin.ignore();
    vector<vector<set<int>>> pm;

    for (int i = 0; i < product_num; i++) {
        string tmp_s;
        getline(cin, tmp_s);
        istringstream iss(tmp_s);
        int tmp;
        vector<set<int>> row;
        while(iss>>tmp) row.push_back({tmp});
        pm.push_back(row);
        //cout << "end one" << endl;
    }

    for (int i = int(pm.size())-1; i > 0; i--) {
        vector<set<int>> new_front_row;
        set<int> new_term;
        for (auto front : pm[i-1]) {
            for (auto back : pm[i]) {
                new_term.insert(front.begin(), front.end());
                new_term.insert(back.begin(), back.end());
                new_front_row.push_back(new_term);
                new_term.clear();
            }
        }
        pm.pop_back();
        pm[i-1] = new_front_row;
    }

    for (auto i : pm[0]) {
        for (auto j : i) 
            cout << j;
        cout << " ";
    }
}