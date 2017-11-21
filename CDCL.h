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
#include "Graph.h"
#include <sstream>

class CDCLSolver {
	public :
		//number of clauses
		int nCloz;
		// number of total variables = $nvar
		int nVars;
		//vector of clauses - from the file
		vector<Cloz*> vecCloz;
		// the assignment of variables to be evaluated on. 
		map<int,bool> assignment;
		//the assignment decision level
		map<int,int> assignLevel;
		map<int,Node*> litToNode;
		//vector of special clauses
		vector<Cloz*> gamma;
		//vector of cluases that holds the latest clauses in consideration
		vector<Cloz*> currForm;
		//current decision level
		int d;
		// Implication Graph
		Graph* G;
		//Learned CLoz
		Cloz* learnedCloz;
		//Decision to Backtrack to
		int decToBacktrack;
		// Conflict Node reference for easy access
		Node* globConflict;
		// decision stack that stores literal and decision level
		stack<Node*> delStack;
		//map for easy backtrack in every decision. So this is decision to vector of literals that get propagated after making decision.
		map<Node*, vector<Node*> > decVec;
	    //stack for backtrack
		stack<int> decList;
	    
		
		 
	//Constructor to initialize variables.	 
	CDCLSolver(vector<Cloz*> vecCl, int numVars){
		this -> vecCloz = vecCl;
		nCloz = vecCl.size();
		nVars = numVars;
		singleton();
		pureLiterals();
		d = 0;
		decToBacktrack = 0;
		//G = new Graph(NULL,NULL);
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
	//	cout << "Inside unitcloz";
		int x = 0;
		// count is number of un-assigned variables
		int count = 0;
		int retLit = 0;
		// Assume all literals are assigned in the cloz and set it to false if find any literal not assigned.
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
	//	cout << "\nCheckpoint 1\n";
		/* 
		* If all literals are assigned. Then either the cloz evaluates to true or false. If false then we have a conflict and we put -1 as lit in assignment .
		* If true then this is not a unitCloz and we return 0
		*/ 
		if(litAssigned){
			bool evalRes = cloz->evalCloz(assignment);
			if(!evalRes){
				cout << "Found conflict \n";
				//CONFLICT
				assignment[-1] = true;
				assignLevel[-1] = d;
				//Add the conflict node to the graph
				vector<Node*> vecNode;
			    for(int i=0;i<cloz->nLit - 1; i++){
			    		int lit = atoi((cloz->vecLit[i]).c_str());
					if(lit==0){
						continue;
					}
					int mapKey = lit;
					if(lit<0){
						mapKey = -1*lit;
						
					}
					
					  Node* tempNode = litToNode[mapKey];
					  vecNode.push_back(tempNode);
					
				}
				
				Node* conflict = new Node(d,-1,true);
				
				conflict->adjacentFrom = vecNode;
				globConflict = conflict;
				
				litToNode[-1] = conflict;
				return 0;
				//gamma.clear();
			}
			else{
				return 0;
			}
		}
		//At this point there is atleast one unassigned literal in the cloz. For each literal unassigned , we increase the count. We also update the literal we wish to return in retLit
		//It is also possible that there is exactly one unassigned literal but it would not matter because already assigned literal can make it true. Hence we keep sum which evaluates
		// the cloz on whatever assigned literals.
		bool sum = false;
		for(int i=0;i<cloz->nLit - 1; i++){
			int lit = atoi((cloz->vecLit[i]).c_str());
	
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
		//Now if the count is exactly one and the rest of the sum evaluates to false, we have found our unit literal. 
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

            // returns the literal if gamma[i] is a unitcloz . returns 0 otherwise.
			int res = isUnitClause(gamma[i]);

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
	void unitPropagateCDCL(){
		//cout << "Inside unitPropagate" << endl;
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
				int maxDecisionLevel = 0; 
				int unassignedLit = 0;
				vector<Node*> vecNode;
				for(int i=0;i<unitCloz->nLit - 1; i++){
					int lit = atoi((unitCloz->vecLit[i]).c_str());
					if(lit==0){
						continue;
					}
					int mapKey = lit;
					if(lit<0){
						mapKey = -1*lit;
						
					}
					if(assignment.count(mapKey)>0){
					  int tempD = assignLevel[mapKey];
					  if(tempD > maxDecisionLevel){
					  	maxDecisionLevel = tempD;
					  }
					  Node* tempNode = litToNode[mapKey];
					  
					  vecNode.push_back(tempNode);
					  
					}
					else{
		//				cout << "Assigning value for lit " << lit <<endl;
						unassignedLit = mapKey;
						assignment[mapKey] = lit < 0 ? false : true;
					
	                    Node* mapKeyNode = new Node(d,mapKey,assignment[mapKey]);
						litToNode[mapKey] = mapKeyNode;
					    if(!delStack.empty()) {
					        Node* topNode = delStack.top();
					        decVec[topNode].push_back(mapKeyNode);
					     }
					else{
					//	cout << "Stack is empty ,\n"; 
					} 
					
						addClauseToGamma(lit);
					}
				}
				//Make sure unassignedLit and maxDeicisionbLevel are well formed
				assignLevel[unassignedLit] = maxDecisionLevel;
			    Node* tempNode = litToNode[unassignedLit];
			    tempNode->adjacentFrom = vecNode;
			    // For each node in vecNode , we also have to assign adjacentTo
			    for(int i=0;i<vecNode.size();i++){
			    	Node* node = vecNode[i];
                    (node->adjacentTo).push_back(tempNode);
				}
			}
		}
	}
		
	/*
	* Makes decision, adds to stack and 
	*/	
	void makeDecision(){
		//increment the decision level
		
		d++;
		cout << "Making decision at level " << d << endl;
		int lit = 0;
	
		for(int i=0;i<nVars;i++){
			if(assignment.count(i+1)==0){
				//make decision
				assignment[i+1] = 1;
				assignLevel[i+1] = d;
				lit = i+1;
				break;
			}
		}
	//	cout << "Making decision for " << lit << endl;
	       
	    Node* node = new Node(d,lit,1);
	    litToNode[lit] = node;
		delStack.push(node);
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
		Node* litNode = delStack.top();
		int lit = litNode->lit;
		delStack.pop();
		
	    // ToDO : remove litToNode[lit] nodes from graph
	    // delete assignments from data structures. also remove corresponding stacks and revert to second highest decision level and next step should be to make decisions based on learned cloz.
	    // removeNodes having decision level greater than secondhighest decision level.
		
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
	   
	    /*for(int i=0;decVec[lit].size();i++){
	    	int elem = decVec[lit][i];
	    	if(elem == 0){
			  break;	
			}
			if(assignment.count(elem))
	    	  assignment.erase(assignment.find(elem));
	//		cout << " removing lit " << elem << " from assignment" << endl;
			
		}*/
		
	//	cout << "All removed \n";
		//decVec.erase(decVec.find(lit));
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
	/*
	* Updates the learned clause global variable. Also finds second highest decision level. 
	*/
	void learnClause(queue<Node*> q){
		//cout << "learn cloz \n"; 
		set<Node*> setQ;
		set<Node*>::iterator it;
		Node* cur;
		while(!q.empty()){
			cur = q.front();
			q.pop();
			setQ.insert(cur);
		}
		//cout << "check 1 \n";
	   	int count = 0;
	   	vector<string> vecLiterals;
	   	int cLevel = globConflict->dLevel;
	   	int maxSecond = -1;
		for (it=setQ.begin(); it!=setQ.end(); ++it){
          //  cout << "check 2 \n";
			cur = *it;
		    int lit = cur->lit;
		    bool assigned = cur->assigned;
		    int dLevel = cur->dLevel;
		    // Checks dLevel only when it is not the max level at conflict. Finds the maximum among the remaining. 
		    if(dLevel!=cLevel){
		    	if(maxSecond> dLevel){
		    		maxSecond = dLevel;
				}
			}
		    
		    if(assigned){
		    	lit = -1*lit;
		    	 std::stringstream ss; 
                 ss << lit;
                 std::string str = ss.str();
		       vecLiterals.push_back(str);
			   }	
			else{
			    std::stringstream ss; 
                ss << lit;
                std::string str = ss.str();
		       	
			   vecLiterals.push_back(str);
			}
		}
		
		decToBacktrack = maxSecond;
		learnedCloz = new Cloz(vecLiterals);
	}
	
	/*
	*  Iterates over queue and checks if the cLevel is exactly once.
	*/
	bool isUniqueImp(queue<Node*> q , int cLevel){
		//cout << "IsUnique Impl \n";
		int count = 0;
		set<Node*> setQ;
		set<Node*>::iterator it;
		Node* cur;
		//cout << "Queue size is " << q.size() <<endl;
		while(q.size() != 0){
		//	cout << "check 1 \n";
			cur = q.front();
          //  cout << "Cur val is " << cur->lit <<endl;
		//	 cout << "setQ size " << setQ.size(); 
			setQ.insert(cur);
		//	cout << "inserted in setQ \n"; 
			 q.pop();
	      //  cout << " popped \n";
		}
		//cout << "check 2 \n";
		//int secondHighestDec = 0;
		for (it=setQ.begin(); it!=setQ.end(); ++it)
        {
          // 	cout << "check 3 \n";
		    int tempD = (*it)->dLevel;
		  //  if(tempD != cLevel){
		  //  	if(tempD > secondHighestDec){
		  //  		secondHighestDec = tempD;
	//			}
		//	}
			if(tempD == cLevel){
				count++;
			}
           	 
	    }
		if(count == 1){
	//		decToBacktrack = secondHighestDec;
			return true;
		}
		return false;
	}
	/*
	* Gets a queue and performs BFS and checks for unique implication point
	*/
	void analyzeAndLearn(){
		//cout << "Analyze and learn\n";
		queue<Node*> q;
		Node* cur ;
		q.push(globConflict);
		int decConflict = globConflict->dLevel;
		//cout << "check 1 \n";
		while(true){
		//	cout << "check 2 \n";
			if(q.empty()){
				break;
			}
			else{
			 cur = q.front();
			  q.pop();
			}
		  // cout << "check 3 \n";	
		  vector<Node*> adjNodes = cur->adjacentFrom;
		  for(int i=0;i<adjNodes.size();i++){
			   q.push(adjNodes[i]);
		  }
		  
		  queue<Node*> tempQU = q;
		  queue<Node*> tempQD = q;
		  //iterate over this cut and check for unique implication point
		  
		  if(isUniqueImp(tempQU ,decConflict)){
		  	//Found the cut . So learn the clause and break
		  	learnClause(tempQD);
		  	cout << "Decision Level is " << d <<endl;
		  	learnedCloz->printCloz();
		  	cout << "Decision level to backtrack to " << decToBacktrack << endl;
		  	return;
		  }
          //cout << "check 5 \n";
		}
		
		
		//cout << "can reach end \n";
	}
		
	void solveCDCL(){
	//	cout << "Inside solveDPLL" << endl;
		time_t start ;
		time_t end;
		start = time(NULL) ;
		end = time(NULL);
		while (end - start < 30){
			end = time(NULL);
			unitPropagateCDCL();
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
				analyzeAndLearn();
				break;
				/*
				if(decToBacktrack < 0){
					cout << "UNSAT";
					return;
				}
				 else{
				 	currForm.push_back(learnedCloz);
					backtrack();
				}*/
			}
		}
		//cout << "TIMEOUT \n"; 
	}
		
};
