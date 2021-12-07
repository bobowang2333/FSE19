#include <iostream>
#include <fstream>
#include <sstream>
#include <map>
#include <vector>
#include <iterator>
#include <algorithm>
#include <tuple>
#include <string>

using namespace std;
map<string, string> vreg_preg;
vector<string> file_line;
void readBEGIN(string f_name)
{
    ifstream fin(f_name);
    string s;
    bool begin_flag = false;
    bool end_flag = false;
    while(getline(fin, s))
    {
        istringstream iss(s);
        vector<string> tokens;
        copy(istream_iterator<string>(iss), istream_iterator<string>(), back_inserter(tokens));
        iss.str("");
        iss.clear();
        if((begin_flag) && (!end_flag))
        {
            if(find(tokens.begin(), tokens.end(), "->") != tokens.end())
            {
                vector<string>::iterator it, it_before, it_after;
                it = find(tokens.begin(), tokens.end(), "->");
                it_before = it;
                it_after = it;
                --it_before;
                ++it_after;
                unsigned b = (*it_before).size();
                unsigned a = (*it_after).size();
                vreg_preg.insert(pair<string, string>(((*it_before).substr(1, -1)), ((*it_after).substr(0, a-1))));
            }
        }
        if(end_flag)
        {
            fin.close();
            break;
        }
        if(!s.compare("BEGIN"))
            begin_flag = true;
        if(!s.compare("END"))
            end_flag = true;
    }
}

string getShortName(string nameWithDef)
{
    string delimiter = "<";
    string token = nameWithDef.substr(0, nameWithDef.find(delimiter));
    return token;
}

// remove the form of LD1[] or ST[] but still with %
string removeSL(string nameWithSL)
{
    unsigned len = nameWithSL.size();
    return nameWithSL.substr(4, len-5);
    
}

bool checkStr (string s, string toCheck)
{
    istringstream iss(s);
    vector<string> tokens;
    copy(istream_iterator<string>(iss), istream_iterator<string>(), back_inserter(tokens));
    iss.str("");
    iss.clear();
    if(find(tokens.begin(), tokens.end(), toCheck) != tokens.end())
        return true;
    else 
        return false;
}

vector<string> lineToVector(string s)
{
    istringstream iss(s);
    vector<string> tokens;
    copy(istream_iterator<string>(iss), istream_iterator<string>(), back_inserter(tokens));
    iss.str("");
    iss.clear();
    return tokens;
}

void checkXor(string f_read_name, string f_write_name)
{
    ifstream fin(f_read_name);
    ofstream fout;
    fout.open(f_write_name);
    string s;
    bool end_flag = false;
    bool xor_flag = false; // indicate if it's the second consistent XOR
    tuple<string, string> xor_first_pair;
    while(getline(fin, s))
    {
        file_line.push_back(s);
        vector<string> tokens = lineToVector(s);
        if(end_flag)
        {
            vector<string>::iterator s_it = find(file_line.begin(), file_line.end(), s);
            string last_s = *(--s_it);
            xor_flag = checkStr(last_s, "XOR");
            // first XOR statement
            if(checkStr(s, "XOR") && (!xor_flag))
            {
                //test
                cout << "come into the first xor" << "\n";
                string left = getShortName(tokens[0]);
                string right1 = tokens[3];
                string right2 = tokens[4];
                vector<string>::iterator it = file_line.end();
                --it; //current xor line
                --it; // one operand in the right side
                vector<string> beforeXOR1 = lineToVector(*it);
                --it; // another operand in the right side
                vector<string> beforeXOR2 = lineToVector(*it);
                string addr1, addr2;
                if(!getShortName(beforeXOR1[0]).compare(right1))
                {
                    addr1 = removeSL(beforeXOR1[3]); //right1's address
                    addr2 = removeSL(beforeXOR2[3]); //right2's address
                }else{
                    addr1 = removeSL(beforeXOR2[3]); //right1's address
                    addr2 = removeSL(beforeXOR1[3]); //right2's address
                }
                // left result share the register with the right operand 1 else not
                // share(2) means the share info only contains two elements
                string share_form1;
                if(!left.compare(right1))
                {
                    share_form1 = "share(2) " + addr1 + ' ' + addr2; 
                    xor_first_pair = make_tuple(addr1, addr2);
                }else{
                    share_form1 = "share(2) " + addr2 + ' ' + addr1;
                    xor_first_pair = make_tuple(addr2, addr1);
                }
                cout << share_form1 << "\n";
                fout << share_form1;
                fout << "\n";
            }
            // last line is also a "XOR"
            if(checkStr(s, "XOR") && (xor_flag))
            {
                //test
                cout << "come into the second xor" << "\n";
                string left = getShortName(tokens[0]);
                //test
                cout << left << endl;
                string right1 = tokens[3];
                string right2 = tokens[4];
                //test
                cout << right1 << ' ' << right2 << endl;
                string toCompare;
                //share: left and right1
                if(!left.compare(right1))
                    toCompare = right2;
                else
                    toCompare = right1;
                vector<string>::iterator it = s_it; //current line
                vector<string> beforeXOR1 = lineToVector(*(it));
                //test
                cout << *it << endl;
                // find the element's loading address
                // out iteration condition: "MOV" and string match
                while(!((!getShortName(beforeXOR1[0]).compare(toCompare)) && (checkStr((*it), "MOV"))))
                {
                    cout << "find the corresponding it" << "\n";
                    --it;
                    //test
                    cout << *it << endl;
                    beforeXOR1 = lineToVector(*it);
                }
                string addr3 = removeSL(beforeXOR1[3]);
                string share_form2;
                share_form2 = "share(3) " + addr3 + ' ' + get<0>(xor_first_pair) + ' ' + get<1>(xor_first_pair);
                cout << share_form2 << "\n";
                fout << share_form2;
                fout << "\n";
            }
        }
        if(!s.compare("END"))
            end_flag = true;
    }
    fin.close();
    fout.close();
}

int main(void)
{
    string read = "memOperand.log";
    string write = "shareVariable.txt";
    checkXor(read, write);
    return 0;
}
