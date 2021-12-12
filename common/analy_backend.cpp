#include <iostream>
#include <fstream>
#include <sstream>
#include <map>
#include <vector>
#include <iterator>
#include <algorithm>
#include <string>

using namespace std;
map<string, string> vreg_preg;
map<string, string> var_vreg;
vector<string> var;
vector<string> vreg;
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
                /* [%vreg0 -> %EDI] need to transfer [%vreg0 to %vreg0 and transfer %EDI] to %EDI */
                vreg_preg.insert(pair<string, string>(((*it_before).substr(1, -1)), ((*it_after).substr(0, a-1))));
            }
        }
        if(end_flag)
        {
            vector<string>::iterator it_var, it_vreg;
            it_var = tokens.begin();
            it_vreg = ++tokens.begin();
            unsigned v_s = (*it_var).size();
            if(!(*it_var).compare("Deleting"))
                break;
            else
            {
                var.push_back((*it_var).substr(4, v_s-5));
                vreg.push_back((*it_vreg));
                //var_vreg.insert(pair<string, string>(((*it_var).substr(4, v_s-5)), *it_vreg));
            }
        }
        /* based on the mark "BEGIN" and "END", assign different flags to them */
        if(!s.compare("BEGIN"))
            begin_flag = true;
        if(!s.compare("END"))
            end_flag = true;
    }
}

/* given a vreg, output all the corresponding variable names in string vector */
vector<int> find_multiple (vector<string> vreg, string tofind)
{
    vector<string>::iterator i = find(vreg.begin(), vreg.end(), tofind);
    vector<int> result;
    while(i != vreg.end())
    {
        result.push_back((i - vreg.begin()));
        i = find(i+1, vreg.end(), tofind);
    }
    return result;
}

bool comp(int i, int j)
{
    return (i < j);
}

vector<string> convert(vector<int> index)
{
    sort(index.begin(), index.end(), comp);
    vector<string> res;
    for(vector<int>::iterator it = index.begin(); it != index.end(); it++)
    {
        std::string tmp = var[*it];
        vector<int>::iterator it_after = it;
        it_after++;
        if((it_after != index.end()) && (!(var[*it_after]).compare(tmp)))
            continue;
        // remove the same variable name in the "var" array adjacently
        //if(find(res.begin(), res.end(), tmp) != res.end())
          //  continue;
        else
            res.push_back(tmp);
    }
    return res;
}

int main(int argc, char *argv[])
{
    if(argc < 3)
        cout << "please input the backend file and name of the output!" << endl;
    //string f_name = "memOperand.log";
    string f_name = argv[1];
    readBEGIN(f_name);
    map<string, string>::iterator iter1, iter2;
    vector<int> res1, res2;
    vector<string> var_outFile;
    vector<string> checked;
    //ofstream output_file("share_variable.txt");
    ofstream output_file(argv[2]);
    
   for(iter1 = vreg_preg.begin(); iter1 != vreg_preg.end(); iter1++)
    {
        string vreg1 = iter1->first;
        string preg1 = iter1->second;

        if(find(checked.begin(), checked.end(), preg1) != checked.end())
            continue;
        else{
            iter2 = iter1;
            ++iter2;
            res1 = find_multiple(vreg, vreg1);
            checked.push_back(preg1);
            cout << "checked: " << preg1 << endl;
            for( ; iter2 != vreg_preg.end(); iter2++)
            {
                if(!preg1.compare(iter2->second))
                {   
                string vreg2 = iter2->first;
                res2 = find_multiple(vreg, vreg2);
                res1.insert(res1.end(), res2.begin(), res2.end());
                continue;
                }
            }
            vector<string> order_Var;
            order_Var = convert(res1);
            ostream_iterator<string> output_iterator(output_file, " ");
            copy(order_Var.begin(), order_Var.end(), output_iterator);
            output_file << "\n";
        }
    }
   output_file.close();
    return 0;
}
