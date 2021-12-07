#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <map>
#include <vector>
#include <iterator>
#include <algorithm>

using namespace std;
typedef tuple<string, string> hd_pair;
vector<hd_pair> hd_sensitive_2;
vector<string> hd_sensitive;


string getIndex(string f_name, string check)
{
    ifstream fin(f_name);
    string s, index;
    while(fin >> s)
    {
        if(!s.compare("SIMPLE"))
            break;
        unsigned len = s.size();
        string tmp = s.substr(5, len-6);
        if(!tmp.compare(check))
        {
            fin >> s;
            index = s.substr(5, -1);
            break;
        }
    }
    return index;
}

//extract the HD sensitive keyword
void readResult(string f_name)
{
    ifstream fin(f_name);
    string s;
    string toCheck = "HD_SENSITIVE";
    string toCheck2 = "HD_SENSITIVE_2";
    while(getline(fin, s))
    {
        istringstream iss(s);
        vector<string> tokens;
        copy(istream_iterator<string>(iss), istream_iterator<string>(), back_inserter(tokens));
        iss.str("");
        iss.clear();
        if(find(tokens.begin(), tokens.end(), toCheck) != tokens.end())
        {
            vector<string>::iterator it1, it2;
            it1 = find(tokens.begin(), tokens.end(), toCheck);
            ++it1;
            //test
            cout << *it1 << endl;
            hd_sensitive.push_back(*it1);
        }else if(find(tokens.begin(), tokens.end(), toCheck2) != tokens.end())
        {
            vector<string>::iterator it1, it2;
            it1 = find(tokens.begin(), tokens.end(), toCheck2);
            ++it1;
            it2 = it1;
            ++it2;
            hd_sensitive_2.push_back(make_tuple((*it1), (*it2)));
        }else
            continue;
    }
    fin.close();
}

//write the var name and ID (HD_sensitive) to the output file
void readMemWrite(string f_name, string w_name)
{
    ifstream fin(f_name);
    ofstream in;
    in.open(w_name, ios::ate);
    string s, tmp, index;
    string end_s = "SIMPLE";
    vector<string> type_vector;
    while(fin >> s)
    {
        if(!s.compare(end_s))
            break;
        unsigned len = s.size();
        tmp = s.substr(5, len-6);
        // handling HD_SENSITIVE
        if((find(hd_sensitive.begin(), hd_sensitive.end(), tmp) != hd_sensitive.end()) && (!s.substr(0, 2).compare("ST")))
        {
            fin >> s;
            index = s.substr(5, -1);
            in << "HD_SENSITIVE" << ' ' << tmp << ' ' << index << "\n";
        }
    }
    fin.close();
    in.close();
}

//write the var ID (HD_sensitive) to the output file
void readMemWrite2(string f_name, string w_name)
{
    ifstream fin(f_name);
    ofstream in;
    in.open(w_name, ios::app);
    string tmp;
    string end_s = "SIMPLE";
    for(vector<hd_pair>::iterator it = hd_sensitive_2.begin(); it != hd_sensitive_2.end(); it++)
    {
        string pair_s1 = get<0>(*it);
        string pair_s2 = get<1>(*it);
        string index_s1 = getIndex(f_name, pair_s1);
        string index_s2 = getIndex(f_name, pair_s2);
        in << index_s1 << ' ' << index_s2 << "\n";
    }
    fin.close();
    in.close();
}


int main(int argc, char *argv[])
{
    if(argc < 4)
        cout << "pls specify the output file, memOriginal file and write file!" << endl;
    //argv[1]: output.txt
    readResult(argv[1]);
    //argv[2]: memOriginal.log argv[3]: forBackend.txt
    readMemWrite(argv[2], argv[3]);
    readMemWrite2(argv[2], argv[3]);
    return 0;
}

