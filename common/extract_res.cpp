#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <map>
#include <vector>
#include <iterator>
#include <algorithm>

using namespace std;
map<string, string> numNameMap;
vector<string> RAND;
vector<string> KEY_IND;
vector<string> KEY_SENSITIVE;
vector<string> HD_SENSITIVE;
void ReadAndFillMap(string f_name, string keyword)
{
    ifstream fin(f_name);
    string s, s1, s2;
    while(fin >> s)
    {
        if(!s.compare(keyword))
        {
            fin >> s1;
            fin >> s2;
            numNameMap.insert(pair<string, string>(s1, s2));
        }
    }
    fin.close();
}

bool hasEnding (string const fullString, string const ending) {
    if (fullString.length() >= ending.length()) {
        return (0 == fullString.compare (fullString.length() - ending.length(), ending.length(), ending));
     } else {
        return false;
     }
}

/** read type inference result from z3 **/
void ReadResult(string f_name, string toCheck)
{
    ifstream fin(f_name);
    string s, toCheck_C, toCheck_CC;
    toCheck_C = toCheck + ")";
    toCheck_CC = toCheck + "))";
    unsigned tmp = 0;
    while(getline(fin, s))
    {
        if((!s.compare("unsat")) || (!s.compare("sat")))
        {   
            tmp++;
            continue;
        }
        istringstream iss(s);
        vector<string> tokens;
        copy(istream_iterator<string>(iss), istream_iterator<string>(), back_inserter(tokens));
        iss.str("");
        iss.clear();
        // test
        for(vector<string>::iterator it = tokens.begin(); it != tokens.end(); it++)
        {
        //    cout << *it << endl;
        }
        if((find(tokens.begin(), tokens.end(), toCheck_C) != tokens.end()) || (find(tokens.begin(), tokens.end(), toCheck_CC) != tokens.end())) 
        {
            string inter_var = numNameMap[toCheck];
            /* only focus on the type of intermediate vars instead of the input */
            if(hasEnding(inter_var, ".addr"))
                continue;
            switch(tmp){
                case 1: KEY_IND.push_back(inter_var);
                          break;
                case 2: KEY_SENSITIVE.push_back(inter_var);
                          break;
                case 3: RAND.push_back(inter_var);
                          break;
                case 4: HD_SENSITIVE.push_back(inter_var);
                        break;
            }
        }
    }
    fin.close();
}

void writeType(string f_name)
{
    ofstream in;
    in.open(f_name, ios::ate);
    string type_s;
    vector<string> type;
    type_s = "RAND";
    type = RAND;
    for(vector<string>::iterator it = type.begin(); it != type.end(); ++it)
    {
        in << type_s << ' ' << *it << "\n";
    }
    type_s = "KEY_IND";
    type = KEY_IND;
    for(vector<string>::iterator it = type.begin(); it != type.end(); ++it)
    {
        in << type_s << ' ' << *it << "\n";
    }
    type_s = "KEY_SENSITIVE";
    type = KEY_SENSITIVE;
    for(vector<string>::iterator it = type.begin(); it != type.end(); ++it)
    {
        in << type_s << ' ' << *it << "\n";
    }
    type_s = "HD_SENSITIVE";
    type = HD_SENSITIVE;
    for(vector<string>::iterator it = type.begin(); it != type.end(); ++it)
    {
        in << type_s << ' ' << *it << "\n";
    }
    in.close();
}

int main(int argc, char *argv[])
{
    if(argc < 4)
        cout << "please specify the smt file and inference result file!" << endl;
    //string smt_file = "compute.smt2";
    //string res_file = "res.txt";
    //argv[0] we assume it's the program name
    string smt_file = argv[1];
    string res_file = argv[2];
    string keyword = ";(alloca";
    /** the output file for the backend **/
    //string output_file = "output.txt";
    string output_file = argv[3];
    ReadAndFillMap(smt_file, keyword);
    /** test **/
    map<string, string>::iterator it;
    for(it = numNameMap.begin(); it != numNameMap.end(); ++it)
    {
        cout << it->first << " => " << it->second << "\n";
        ReadResult(res_file, it->first);
    }
    writeType(output_file);
    return 0;
}
