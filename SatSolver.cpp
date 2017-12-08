#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <string.h>
#include <cstdlib>
//#include "Solver.h"
//#include "DPLL.h"
#include "CDCL.h"
#include <csignal>

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

CDCLSolver* solver;
/**
* Parses the file and reads the clauses line by line and runs the SAT Solver
* C:\\study\\4th quarter\\cse 291 E\\petite\\sat-benchmarks-master\\done\\
* C:\\study\\4th quarter\\sat solver\\resource\\dimacs3.sat
* C:\\study\\4th quarter\\cse 291 E\\petite\\sat-benchmarks-master\\done\\total-order-alt-19.cnf
* C:\\Users\\tanej\\Downloads\\CBS_k3_n100_m403_b30\\CBS_k3_n100_m403_b30_0.cnf
* cd C:\study\4th quarter\sat solver;  SatSolver.exe "C:\\study\\4th quarter\\cse 291 E\\petite\\sat-benchmarks-master\\done\\total-order-alt-2.cnf"
**/

sig_atomic_t sigflag = 0;
int verbose = 0;	
void sighandler(int s)
{     
      std::cerr << "Unknown " << ".\n"; // this is undefined behaviour
      if(verbose){
	     solver->printStack();
	  }
	  exit(1);
      sigflag = 1; // something like that
}

int main(int argc, char *argv[]){
	string filePath = "C:\\study\\4th quarter\\sat solver\\resource\\dimacs3.sat";
	int timeout = 300;
	
	if(argc == 1){
		cout << "Please provide input file name \n";
		cout << "Correct order - SatSolver.exe filePath Timeout Verbose \n";
		cout << " Ex: SatSolver.exe \"C:\\filename.sat\" or SatSolver.exe \"C:\\filename.sat\" 300 or SatSolver.exe \"C:\\filename.sat\" 300 0" << endl;
		exit(1);
	}
	if(argc == 2){
	  filePath = argv[1];	
	}
	if(argc == 3){
		filePath = argv[1];
		timeout = atoi(argv[2]);
	}
	if(argc == 4){
		filePath = argv[1];
		timeout = atoi(argv[2]);
		verbose = atoi(argv[3]);
	}
	//cout << "argc is " <<  argc <<endl;
	//cout << "File path is " << filePath<<endl;
	//cout << "Time out is " << timeout<<endl;
	//cout << " Verbose is " << verbose <<endl;
	std::signal(SIGINT, sighandler);  
	
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

   // cout << line << "\n";
}

if(countCloz < ncloz){
	cout << "Missing number of lines in the file. \n ";
	infile.close();
    exit(-1);
}
if(type != "cnf" && type != "CNF"){
	cout << type << " not provided  \n ";
	infile.close();
    exit(-1);
    
}

infile.close();
//Solver* solver = new Solver(vecClozes,nvar);
//solver -> solveRandom();

//DPLLSolver* solver = new DPLLSolver(vecClozes,nvar);
//solver->solveDPLL(); 

solver = new CDCLSolver(vecClozes,nvar,timeout,verbose!=0);
solver->solveCDCL();

 
//Debug : cout << nvar << " variables and " << ncloz << " clauses " << endl; 

}

