#include <string.h>
#include <vector>
#include <map>
#include <cstdlib>
#include <string>
#include <map>
#include <iostream>

using namespace std;
/**
* Class Cloz to hold the variables and methods for any clause.
**/
class Cloz {
    public :
    // number of literals in the clause
	int nLit;
    // stores the literals in a clause
	vector<string> vecLit;
	Cloz (vector<string> v){
		this->vecLit = v;
		nLit = this->vecLit.size();	
	}
	/**
	* Method to print the clause
	**/
	void printCloz(){
		int i=0;
		for(i=0;i<nLit;i++){
			cout << vecLit[i] << " ";
		}
		cout << endl;
	}
	/**
	*  Method to evaluate the clause
	**/
	bool evalCloz(map<int,bool> vars){
		int i=0;
		bool res = false;
		for(i=0;i<nLit;i++){
			int x = atoi(vecLit[i].c_str());
			if(x==0){
				continue;
			}
			bool temp = false;
			if(x>0){
			  temp = vars[x];
				
			}
			else{
				//x is negative
				temp = !vars[x*(-1)];
				
			}
			res = res || temp;
				if(res == true){
					return res;
				}
		}
		return res;
	} 
	
};
