#include <iostream>
#include <map>
#include <vector>
#include <cmath>
#include <queue>
#include <stack>
#include "Cloz.h"
#include <set>
#include <ctime>
#include <algorithm>


class DPLLSolver {
	public :
		//number of clauses
		int nCloz;
		// number of total variables = $nvar
		int nVars;
		//vector of clauses - from the file
		vector<Cloz*> vecCloz;
		// the assignment of variables to be evaluated on. 
		map<int,bool> assignment;
		//vector of special clauses
		vector<Cloz*> gamma;
		//vector of cluases that holds the latest clauses in consideration
		vector<Cloz*> currForm;
		// decision stack
		stack<int> delStack;
		//map for easy backtrack in every decision. So this is decision to vector of literals that get propagated after making decision.
		map<int, vector<int> > decVec;
	    //stack for backtrack
		stack<int> decList;
	    
		
		 
	//Constructor to initialize variables.	 
	DPLLSolver(vector<Cloz*> vecCl, int numVars){
		this -> vecCloz = vecCl;
		nCloz = vecCl.size();
		nVars = numVars;
		singleton();
		pureLiterals();
        //Debug
     /*   cout << "Singleton clauses in gamma\n";
        for(int i=0;i<gamma.size();i++){
        	Cloz* cloz = gamma[i];
			cloz->printCloz(); 
		}
		cout<< "Singleton ended" << endl;
		cout<< "PureLiteral Clauses Not in following" << endl;
		for(int i=0;i<currForm.size();i++){
        	Cloz* cloz = currForm[i]; 
        	cloz->printCloz();
		}
		cout << "pureLiteralNonClauses ended" << endl;
	*/	
	}
	
	/*
	* Finds the pureliteral clauses and assigns the corresponding literals to 1 (eliminate clauses) .
	*/
	void pureLiterals(){
	  // map to store the literal and its last occured polarity
	  map<int, bool> m ;
	  //vector to store literals that are not pure
      vector<int> notPure;
       
	  for(int i=0;i<vecCloz.size();i++){
	     Cloz* cloz = vecCloz[i];
	     for(int j=0;j<cloz->nLit -1 ; j++){
	     	int lit = atoi((cloz->vecLit[j]).c_str()); 
	     //	cout << "Current Lit is " << lit << endl;
	     	if(lit > 0){
	     		  if(m.count(lit)>0){
	     		  	bool temp = m[lit];
	     		  	if(temp == false){
					   	notPure.push_back(lit);
				     }
				   }
				   else{
				   	  //insert in the map
				   	  m[lit] = true;
				   }
			 }
			 else{
			 	if(m.count(-1*lit)>0){
	     		  	bool temp = m[-1*lit];
	     		  	if(temp){
	     		  		notPure.push_back(-1*lit);
					   }
				   }
				   else{
				   	  //insert in the map
				   	  m[-1*lit] = false;
				   }
			 	
			 }
		 }
	  }
	  //Debug
	  /*
	  cout << "Not Pure lits" << endl;
	  for(int i=0;i<notPure.size();i++){
	  	cout << notPure[i] << "\n";
	  }
	  cout<< "Not Pure Ends\n";*/
	  //Debug end
	  //Print Not Pure
	  set<int> s(notPure.begin(), notPure.end());
	  //Make changes in the assignment 
	  for(int k=0;k<nVars;k++){
	  	if(!s.count(k+1)){
	  //		cout << k+1 << "th literal is being assigned  " << m[k+1] << endl;
	  		assignment[k+1] = m[k+1];
		  }
	  }
	  // remove clauses for pure literal
	  
	  vector<Cloz*> pureCloz;
	//  cout << "CurrFOrm size is " << currForm.size();
	  for(int l =0 ; l< currForm.size(); l++){
	  	Cloz* cloz = currForm[l];
	   //  cout << "Current Cloz " << endl;
	   // cloz->printCloz();
	  	bool checkLit = false;
	  	for(int m=0;m<cloz->nLit -1 ; m++){
	  		int lit = atoi((cloz->vecLit[m]).c_str());
	  	//	cout << "current lit is " << lit << endl;
	  		if(lit<0)
            { 
              lit = -1*lit;
			  }
			if(!s.count(lit)){
		//		cout << "pushing to pure cloz" << endl;
				pureCloz.push_back(cloz);
			}
		  }
	  
	  }
	   /* cout << "Pure Lit clauses in gamma";
        for(int i=0;i<pureCloz.size();i++){
        	Cloz* cloz = pureCloz[i];
			cloz->printCloz(); 
		}
		cout<< "Pure lit clauses ended" << endl;
	  */
	  set<Cloz*> pureSet(pureCloz.begin(), pureCloz.end());
	  
	  vector<Cloz*> remainCloz;
	  for(int n = 0 ; n< currForm.size(); n++)
	  {
	  	Cloz* cloz = currForm[n];
	  	if(!pureSet.count(cloz)){
		    remainCloz.push_back(cloz);
		  }
	  }
	  
	  //Update CurrForm
	  currForm = remainCloz;
	  
	}
	
	/* 
	*  Also finds singleton clauses and eliminates them (which have a single literal)
	*/
	void singleton(){
			
			//Singleton Clause below;
		for(int i=0;i<vecCloz.size();i++){	
		    Cloz* cloz = vecCloz[i];
			if(cloz->nLit == 2){
			/*	int lit = atoi((cloz->vecLit[0]).c_str());
				if(lit < 0){
					assignment[-1*lit] = 0;
				}
				else{
					assignment[lit] = 1;
				}*/
				if(find(gamma.begin(), gamma.end(),cloz)==gamma.end())
			       gamma.push_back(cloz);
			}
			else{		
			   currForm.push_back(cloz);
	     	}
		}
	
		
	}
	/*
	* Finds all clauses that have literal . And adds to gamma
	*/
	void addClauseToGamma(int literal){
	//	cout << "Adding gamma(" << literal <<") to gamma\n"; 
		for(int i=0;i<currForm.size();i++){
			Cloz* cloz = currForm[i];
			for(int j=0;j< (cloz->nLit)-1;j++){
				int tLit = atoi((cloz->vecLit[j]).c_str());
				if(literal == tLit || literal*-1 == tLit){
					if(find(gamma.begin(), gamma.end(),cloz)==gamma.end())
					   gamma.push_back(cloz);
	//				cout <<"Pushing cloz t0 gamma " ;
	//				cloz->printCloz();
				}
			}
		}
		return ;
	}
	/*
	* Checks if the clause is unit and returns the literal if it is unassigned. 
	*  otherwise returns 0;
	*/
	int isUnitClause(Cloz* cloz){
	//	cout << " ckecking if follow is unit clause " << endl;
	//	cloz->printCloz();
		
		int x = 0;
		// count is number of un-assigned variables
		int count = 0;
		int retLit = 0;
		
		bool litAssigned = true;
		for(int i=0;i<cloz->nLit - 1; i++){
			int lit = atoi((cloz->vecLit[i]).c_str());
			if(lit<0){
				lit = -1*lit;
			}
			if(assignment.count(lit)==0){
				litAssigned = false;
			  break;
			}
		}
		if(litAssigned){
			bool evalRes = cloz->evalCloz(assignment);
			if(!evalRes){
				//CONFLICT
				assignment[-1] = true;
	//			cout << "Conflict created in " << endl;
	//			cloz->printCloz();
				//gamma.clear();
			}
		}
		bool sum = false;
		for(int i=0;i<cloz->nLit - 1; i++){
			int lit = atoi((cloz->vecLit[i]).c_str());
		//	cout << "literal in the above clause is " << lit << "  \n";
			if(lit==0){
				continue;
			}
			if(lit<0){
			  	if(assignment.count(-1*lit)>0){
			  	    sum |= !assignment[-1*lit];
			  	  }
				  else{
				  	retLit = lit;
				  	count++;
			      }
			}
			else
			{
				if(assignment.count(lit)>0){
			  		sum |= assignment[lit];
			  	}
				  else{
				  	retLit = lit;
				  	count++;
			      }
			}
			
		}
		if(count==1 && !sum){
			return retLit;
		}
	
	//	cout << "Res x = " << x ;
		return x;
	}
	
	/* finds unit clauses from gamma. 
	*/
	Cloz* pickCloz(){
		Cloz* retCloz = NULL;
		vector<Cloz*> gam;
	//	cout << "PickCloz iterating over\n"; 
		for(int i=0;i<gamma.size();i++){
			// return Cloz if unit and remove from gamma as well
			if(assignment.count(-1)){
				//there is a conflict
				retCloz = new Cloz(true);
				return retCloz;
			}
		//	cout << "current cloz in consideration is ";
	//		gamma[i] -> printCloz();
			int res = isUnitClause(gamma[i]);
	//		cout << "Is Unit Clause " << res << endl;
			if(res!=0){
				//remove this cloz from gamma
				retCloz = gamma[i];
			 	gamma.erase(remove(gamma.begin(), gamma.end(), retCloz), gamma.end()); 
				return retCloz;
			}
		}
		
		return retCloz;
	}
	/* unitPropagation
	*/
	void unitPropagate(){
	//	cout << "Inside unitPropagate" << endl;
		while(true){
		//	cout << "Current Gamma \n";
			//see gamma
		//	for(int i=0;i<gamma.size();i++){
		//		gamma[i] -> printCloz();
		//	}
			//see assignment
		//	cout << "Current Assignment \n" ; 
		//	printAssign();
			
			Cloz* unitCloz = pickCloz();
			if(unitCloz == NULL){
				return;
			}
			else if(unitCloz->isConflict){
		//	cout << " Conflict Clause is " << endl;
				//unitCloz->printCloz();
				assignment[-1] = true; // redundant
				return;
			}
			else{
		//		cout << "Picked Clause \n" ;
		//		unitCloz -> printCloz(); 
				// Find the literal in the unit clause and make assignment 
				for(int i=0;i<unitCloz->nLit - 1; i++){
					int lit = atoi((unitCloz->vecLit[i]).c_str());
					if(lit==0){
						continue;
					}
					int mapKey = lit;
					if(lit<0){
						mapKey = -1*lit;
						
					}
					if(assignment.count(mapKey)==0){
		//				cout << "Assigning value for lit " << lit <<endl;
						assignment[mapKey] = lit < 0 ? false : true;
					/*	cout << "decList size is "<< decList.size() << endl;
						cout << "decList empty ? " << decList.empty()<<endl;
						if(!decList.empty())
						   cout << "Top of decList has " << decList.top() <<endl;
						decList.push(mapKey);*/
					    if(!delStack.empty()) {
					    int top = delStack.top();
		//			    cout << "Adding lit " << mapKey << " for top on Stack " << top << endl;
		//			    cout << "DecVec has top" << decVec.count(top) << endl;
		//			    if(decVec.count(top))
		//			      cout << "Size of vector decVec[top]" << decVec[top].size() <<endl;	
						decVec[top].push_back(mapKey);
					}
					else{
					//	cout << "Stack is empty ,\n"; 
					}
					
						addClauseToGamma(lit);
					}
				}
			}
		}
	}
		
	/*
	* Makes decision, adds to stack and 
	*/	
	void makeDecision(){
		
		int lit = 0;
	
		for(int i=0;i<nVars;i++){
			if(assignment.count(i+1)==0){
				//make decision
				assignment[i+1] = 1;
				lit = i+1;
				break;
			}
		}
	//	cout << "Making decision for " << lit << endl;
		delStack.push(lit);
		//decList.push(lit);
		addClauseToGamma(lit);
	}
	/*Checks if all literals have been assigned*/
	bool allAssigned(){
		for(int i=0;i<nVars;i++){
			if(assignment.count(i+1)==0){
         	     return false;
			 }
	    }
		return true; 
	}
	
	void backtrack(){
		//remove conflict
		if(assignment.count(-1)>0){
			assignment.erase(assignment.find(-1));
		}
		int lit = delStack.top();
		delStack.pop();
	//	cout << "Backtracking flipping bit for lit " << lit << endl;
		assignment[lit] = !assignment[lit];
		
		
		//Delete all assignments made after making decision
	
	/*	while(decList.top()!=lit){
			int elem = decList.top();
	 	if(assignment.count(elem)){
	 		assignment.erase(assignment.find(elem));
		 }
			cout << " removing lit " << elem << " from assignment" << endl;
			decList.pop();
		}
		decList.pop();
		cout << "Size of decList after backtrack is " <<decList.size() <<endl; 
	  */  
	   
	    for(int i=0;decVec[lit].size();i++){
	    	int elem = decVec[lit][i];
	    	if(elem == 0){
			  break;	
			}
			if(assignment.count(elem))
	    	  assignment.erase(assignment.find(elem));
	//		cout << " removing lit " << elem << " from assignment" << endl;
			
		}
	//	cout << "All removed \n";
		decVec.erase(decVec.find(lit));
	//	cout << "removed " << lit << " from decVec\n" ; 
//		cout << "decvec has lit" << lit << "  " << decVec.count(lit) << endl;
	

	}
	
	/**
	* Method to print the assignment that generated the SAT . 
	**/
	void printAssign(){
		int n = assignment.size();
		int i;
		for(map<int,bool> :: const_iterator it = assignment.begin(); it!=assignment.end(); ++it){
			cout << it->first << " " << it->second << endl;
		}	
	}
		
	void solveDPLL(){
	//	cout << "Inside solveDPLL" << endl;
		time_t start ;
		time_t end;
		start = time(NULL) ;
		end = time(NULL);
		while (end - start < 30){
			end = time(NULL);
			unitPropagate();
			if(assignment.count(-1)==0){
				//there is no conflict
				if(allAssigned()){
				//	printAssign();
					cout << "SAT";
					return;
				}
				else{
					//Need to Make decision
					makeDecision();
				}
			}
			else{
				//there is conflict
				if(delStack.empty()){
					cout << "UNSAT";
					return;
				}
				 else{
					backtrack();
				}
			}
		}
		cout << "TIMEOUT \n"; 
	}
		
};
