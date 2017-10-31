#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <string.h>
#include <cstdlib>
//#include "Solver.h"
#include "DPLL.h"

using namespace std;
/**
* Split method to split a string based on a delimiter
**/
vector<string> split(string str,string sep){
    char* cstr=const_cast<char*>(str.c_str());
    char* current;
    vector<string> arr;
    current=strtok(cstr,sep.c_str());
    while(current!=NULL){
        arr.push_back(current);
        current=strtok(NULL,sep.c_str());
    }
    
    return arr;
}

/**
* Parses the file and reads the clauses line by line and runs the SAT Solver
**/
int main(){
	string filePath = "C:\\study\\4th quarter\\cse 291 E\\petite\\sat-benchmarks-master\\petite\\total-order-alt-19.cnf";
	ifstream infile(filePath.c_str());
    string line;
    int nvar = 0;
    int ncloz = 0;
    string type;
    vector<Cloz*> vecClozes;
	int countCloz = 0;  
  while (getline(infile, line))
{
    if(line[0]=='c' || line[0] == 'C'){
    	continue;
	}
	else if(line[0]=='p' || line[0]=='P'){
	vector<string> first = split(line, " ");
	type = first[1];
	nvar = atoi(first[2].c_str());
	ncloz = atoi(first[3].c_str());
	}
	else {
	countCloz++;
	vector<string> cloz = split(line, " ");
	int i=0;
	Cloz* cl = new Cloz(cloz);
	vecClozes.push_back(cl);		
	}

    //Debug : cout << line << "\n";
}

if(countCloz < ncloz){
	cout << "Missing number of lines in the file. \n ";
	infile.close();
    exit(-1);
}
if(type != "cnf" && type != "CNF"){
	cout << type << " not implemented \n ";
	infile.close();
    exit(-1);
}

infile.close();
//Solver* solver = new Solver(vecClozes,nvar);
//solver -> solveRandom();

DPLLSolver* solver = new DPLLSolver(vecClozes,nvar);
solver->solveDPLL(); 


 
//Debug : cout << nvar << " variables and " << ncloz << " clauses " << endl; 

}

