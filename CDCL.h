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
//#include <windows.h> 


class CDCLSolver {
	public :
		//number of clauses
		int nCloz;
		// number of total variables = $nvar
		int nVars;
		//vector of clauses - from the file
		vector<Cloz*> vecCloz;
		// the assignment of variables to be evaluated on
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
		//timeout parameter
		int timeout;
		//verbose
		bool verbose;
	    
		
		 
	//Constructor to initialize variables.	 
	CDCLSolver(vector<Cloz*> vecCl, int numVars, int time, bool verb){
		this -> vecCloz = vecCl;
		nCloz = vecCl.size();
		nVars = numVars;
		singleton();
		pureLiterals();
		d = 0;
		decToBacktrack = 0;
		learnedCloz = NULL;
		timeout = time;
		verbose = verb;
		
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
	//	cout << "IUC : Inside unitcloz \n";
		int x = 0;
		// count is number of un-assigned variables
		int count = 0;
		int retLit = 0;
		// Assume all literals are assigned in the cloz and set it to false if find any literal not assigned.
		bool litAssigned = true;
	//	cloz->printCloz();
	//	cout << "IUC : isConflict var ? " << cloz->isConflict << endl;
		for(int i=0;i<cloz->nLit - 1; i++){
			int lit = atoi((cloz->vecLit[i]).c_str());
	//		cout << "IUC: For checking if all elements assigned ? Checking lit  " << lit << "\n";
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
	//			cout << "Found conflict \n";
				//CONFLICT
	//			cout << "Conflict cloz at level "<< d << " is \n" ;
	//			cloz->printCloz();
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
		//cout << "Unit: Inside unitPropagate" << endl;
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
	//			cout << " Unit : Picked Clause \n" ;
		//		unitCloz -> printCloz(); 
				// Find the literal in the unit clause and make assignment
				int maxDecisionLevel = 0; 
				int unassignedLit = 0;
				vector<Node*> vecNode;
	//			cout << " Unit : Iterating over literals of unitcloz \n";
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
	//				   cout << " Unit : lit " << mapKey << " is assigned to " << assignment[mapKey] << " at decision level " << assignLevel[mapKey] << endl; 
					  int tempD = assignLevel[mapKey];
					  if(tempD > maxDecisionLevel){
					  	maxDecisionLevel = tempD;
					  }
	//				  cout << "Unit : getting the above lit " << mapKey << " and its node value from litToNode \n";
					  Node* tempNode = litToNode[mapKey];
	//				  cout << " Unit : the node value is NULL ? " << (tempNode == NULL) << endl;
					  vecNode.push_back(tempNode);
					  
					}
					else{
	//					cout << " Unit : The  " << lit << " is unassigned" <<endl;
						unassignedLit = mapKey;
						assignment[mapKey] = lit < 0 ? false : true;
	//				 cout << "Unit : assigning " << mapKey << " " << assignment[mapKey] << endl;
	                    Node* mapKeyNode = new Node(d,mapKey,assignment[mapKey]);
						litToNode[mapKey] = mapKeyNode;
	//					cout << " Unit : created a new node for this unassigned lit " << mapKey <<" and put in litToNode\n";
	//					cout << " Unit : Need to put the current unassigned node in decVec[topNode] and hence check if delStack is empty ? " << (delStack.empty()) << endl;
					    if(!delStack.empty()) {
					        Node* topNode = delStack.top();
	//				        cout << "Unit : topNode lit on delStack is " << topNode->lit <<" and topNode level for decVec is" << topNode->dLevel << endl; 
					        decVec[topNode].push_back(mapKeyNode);
	//				        cout << " Unit : Pushed the unassigned node on decVec[topNode] \n";
					     }
					else{
	//				    	cout << "Unit : Stack is empty and hence can't assign the decVec[topNode] . This is for lit " << mapKey<< " \n"; 
					} 
					
						addClauseToGamma(lit);
	//					cout << "Unit : Added clause to gamma for lit " << lit << " \n" ; 
					}
				}
				//Make sure unassignedLit and maxDeicisionbLevel are well formed
				assignLevel[unassignedLit] = maxDecisionLevel;
	//			cout << "Unit : assignLevel of lit " << unassignedLit << " is " << maxDecisionLevel << endl;
				//debug
				//cout << "unit level : lit " << unassignedLit << " at level " << maxDecisionLevel << endl; 
			    Node* tempNode = litToNode[unassignedLit];
			    tempNode->adjacentFrom = vecNode;
	//		    cout << "Unit : unassigned lit " << tempNode->lit << " is adjacentFrom " << vecNode.size() << " nodes \n";
			    // For each node in vecNode , we also have to assign adjacentTo
	//		    cout << "Unit : Checking adjacentTo behavior \n";
			    for(int i=0;i<vecNode.size();i++){
			    	Node* node = vecNode[i];
	//		    	cout << "Unit : current node is " << node->lit << " and the size of adjacenTo before adding is " << (node->adjacentTo).size() << endl;
                    (node->adjacentTo).push_back(tempNode);
                    //Debug code in this block below -- 
                    vector<Node*> adjTo = node->adjacentTo;
    //                cout << "Unit : current node " << node->lit << " has the following nodes in adjacentTo after adding unassgined to it. \n"; 
				//	for(int i=0;i<adjTo.size();i++){
    //                	cout << "Unit: adj[i] is " << adjTo[i]->lit << endl;
				//	}
				}
				//cout << "Unit : Unit Prop ends for decision level " << d;
			}
		}
		//cout << "Unit : prop ends\n"; 
	}
		
		
	void makeDecisionFB(){
		d++;
		//cout << "MD : Inside md\n";
	//	cout << "MD: Iterating over currForm \n";
	    bool noAssign = true; 
		for(int i=currForm.size()-1;i>=0;i--){
			
			Cloz* cloz = currForm[i];
		//	cloz->printCloz();
			for(int j=0;j<cloz->nLit-1;j++){
			//	printAssign();
			//	cloz->printCloz();
				int lit_t = atoi((cloz->vecLit[j]).c_str());
				int mapKey = lit_t;
		     	if(lit_t<0){
	    	      	mapKey = -1*lit_t;
				}
				if(assignment.count(mapKey)==0){
					//Make assignment accordingly. 
					assignment[mapKey] = lit_t<0?false:true;
					assignLevel[mapKey] = d;
					noAssign = false;
          //  	    cout << "MD : Assigning " << mapKey << " = " << assignment[mapKey] << " at level " << d << endl;
					Node* node = new Node(d,mapKey,(bool)assignment[mapKey]);
	                //cout << "MD : Node stored has lit " << node->lit << " And value assigned to it is " << (bool)(node->assigned )<< endl;
	                litToNode[mapKey] = node;
		            delStack.push(node);
		            //cout << "MD : pushed node on litToNode and delStack \n";
		            vector<Node*> temp;
		            decVec[node] = temp;
		            //cout << "MD : Also added an empty vector<node> in decVec[node]\n";
             		addClauseToGamma(mapKey);
					 return;	
				}else{
					bool val = assignment[mapKey];
					if((lit_t<0 && !val) || (lit_t>0 && val)){
						break;
					}
					
				}
				
			}
			
		}
		if(noAssign){
			//If no decision has been made but still some variables are unassigned . 
			if(!allAssigned()){
				
				 // Find the literal that is not assigned
	        //cout << "MD : Making decision normally"  << endl;
		    for(int i=0;i<nVars;i++){
			    if(assignment.count(i+1)==0){
				//make decision
				   assignment[i+1] = 1;
				   assignLevel[i+1] = d;
				  // cout << "MD : Assign lit " << i+1 << " = " << assignment[i+1] << " at level " << d <<endl;
					    
				   Node* node = new Node(d,i+1,(bool)assignment[i+1]);
	                //cout << "MD : Node stored has lit " << node->lit << " And value assigned to it is " << (bool)(node->assigned )<< endl;
	                litToNode[i+1] = node;
		            delStack.push(node);
		            //cout << "MD : pushed node on litToNode and delStack \n";
		            vector<Node*> temp;
		            decVec[node] = temp;
		            //cout << "MD : Also added an empty vector<node> in decVec[node]\n";
             		addClauseToGamma(i+1);
				   
				   break;
			    }
		    }
		
				
				
				
			}
		}
		//cout << "MD: Exit Make Decision \n";
	}	
		
	/*
	* Makes decision, adds to stack and 
	*/	
	void makeDecision(){
		//increment the decision level
	//	printAssign();
		d++;
		//cout << "MD : Making decision at level " << d << endl;
		int lit = 0;
	    //Make Decision based on learned cloz 
	    //cout << (learnedCloz == NULL) << endl;
	    bool assignedBasedOnLC = false;
	    if(learnedCloz != NULL){
	    	//cout << "MD : making decision from learned clause" << endl;
	    	for(int i=0;i<learnedCloz->nLit-1; i++){
					int lit_t = atoi((learnedCloz->vecLit[i]).c_str());
	    	         int mapKey = lit_t;
					 if(lit_t<0){
	    	         	mapKey = -1*lit_t;
					 }
					 if(assignment.count(mapKey)==0){
					 	//cout << "MD : lit " << mapKey << " is not assigned in learned cloz. \n";
					 	assignment[mapKey] = lit_t<0?false:true;
					 	assignLevel[mapKey] = d;
					 	cout << "MD : Making assignment for lit " << mapKey << " = " << assignment[mapKey] << " at level " << d <<endl;
					    //lit = lit_t;
					    assignedBasedOnLC = true;
					    lit = mapKey;
						break;
					 }
	            }
		
		
		}
	    else{
		
	    // Find the literal that is not assigned
	     cout << "MD : Making decision since no learnedCloz"  << endl;
		    for(int i=0;i<nVars;i++){
			    if(assignment.count(i+1)==0){
				//make decision
				   assignment[i+1] = 1;
				   assignLevel[i+1] = d;
				   cout << "MD : Assign lit " << i+1 << " = " << assignment[i+1] << " at level " << d <<endl;
					    
				   lit = i+1;
				   break;
			    }
		    }
		
	    }   
	    // if all the literals in leranedCloz are assigned , we will make learnedCloz as NULL so that next time while making decision decision is made in order 
	    if(learnedCloz!=NULL){
		cout << "MD : learnedCloz is not null. So here we check if all the literals in it have been assigned . \n";
		int countOfUnLit = 0;
		cout << "MD : Learned cloz is \n";
	//	learnedCloz->printCloz();
	    for(int i=0;i<learnedCloz->nLit-1; i++){
					int lit_t = atoi((learnedCloz->vecLit[i]).c_str());
					cout << "MD: Processing current lit of Learned Cloz " << lit_t << endl;
					if(lit_t ==0){
						continue;
					}
	    	         int mapKey = lit_t;
					 if(lit_t<0){
	    	         	mapKey = -1*lit_t;
					 }
					 if(assignment.count(mapKey)==0){
					    countOfUnLit++;
					 }
				}
		if(countOfUnLit==0){
			//ALL assigned in learned Cloz ;
			//delete learnedCloz;
			learnedCloz = NULL;
		//	cout << "MD: All literals have been assigned in learned cloz and therefor delted learnedCloz node and assigned it NULL\n";
		//	cout << "MD: All literals have been assigned in learned cloz and therefore before we intialize a node we must find the right lit\n";
			
			
			// Find the literal that is not assigned
			if(!assignedBasedOnLC){
			
			
	     cout << "MD : Making decision normally since all lits in learnedCloz assigned"  << endl;
		    for(int i=0;i<nVars;i++){
			    if(assignment.count(i+1)==0){
				//make decision
				   assignment[i+1] = true;
				   assignLevel[i+1] = d;
				   cout << "MD : Assigning lit " << i+1 << " = " << assignment[i+1] << " assignlevel is " << d <<endl;
					    
				   lit = i+1;
				   break;
			      }
		       }
		    }
		}
		
       }
	    // Create the node for the current decision made and update litToNode Mapping and also update our decision stack .    
	  //  cout << " MD: Finally creating node for lit " << lit << " This should not be zero. It should be assigned to value  "<< assignment[lit]<< "\n"; 
	    Node* node = new Node(d,lit,(bool)assignment[lit]);
	    cout << "MD : Node stored has lit " << node->lit << " And value assigned to it is " << (bool)(node->assigned )<< endl;
	    litToNode[lit] = node;
		delStack.push(node);
		cout << "MD : pushed node on litToNode and delStack \n";
		vector<Node*> temp;
		decVec[node] = temp;
		cout << "MD : Also added an empty vector<node> in decVec[node]\n";
		//decList.push(lit);
		addClauseToGamma(lit);
		
    	cout << "MD : Added Clause to Gamma . Make Decision over" << endl;
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
	
	void delGraphWithBFS(Node* node){
		queue<Node*> q;
		Node* cur ;
		q.push(node);
		set<Node*> setQ;
		//decision level of conflict
		while(!q.empty()){
			
			 cur = q.front();
			 q.pop();
			 setQ.insert(cur);
			 for(int i=0; i < (cur->adjacentTo).size();i++){
			 	q.push((cur->adjacentTo)[i]);
			 	
			 //	((cur->adjacentFrom)[i]->adjacentTo).erase(std::remove(((cur->adjacentFrom)[i]->adjacentTo).begin(), ((cur->adjacentFrom)[i]->adjacentTo).end(), cur), ((cur->adjacentFrom)[i]->adjacentTo).end());
			 }
			 
		    // delete cur;
			// cur = NULL;	
		}
		set<Node*>::iterator it;
			for (it=setQ.begin(); it!=setQ.end(); ++it)
        {
        
		    delete (*it);
	    }
		
		
		
	}
	
	void traverseDFS(Node* node){
		if(node == NULL){
			return;
		}
		cout << " Node lit is -> " << node->lit << endl;
		vector<Node*> vec = node->adjacentTo;
		for(int i=0;i<vec.size();i++){
			traverseDFS(vec[i]);
		}
	}
	
	
	void delGraphAt(Node* node){
		if(node == NULL){
           
			return;
		}
		//cout << "Del : calling del on lit " << node->lit << endl;
		if(assignment.count(node->lit))
		assignment.erase(assignment.find(node->lit));
		//vector<Node*> tVec = node->adjacentTo;
		//cout << "Del : Deleting vector of size " << (node->adjacentTo).size() << "\n";
		//for(int i=0;i<tVec.size();i++){
		//	delGraphAt(tVec[i]);
		//}
		
		//for(int i=0;i<(node->adjacentTo).size();i++){
		//	cout << (node->adjacentTo)[i]->lit <<"\n";
			
		//}
		for(int i=0;i<(node->adjacentTo).size();i++){
			delGraphAt((node->adjacentTo)[i]);
			
		}
		//cout << "Del : About time to delete node lit " << node->lit  << endl;
		//remove every reference of node from its adjacent from . 
		//vector<Node*> adjFrom = node->adjacentFrom;
		//for(int i=0;i<adjFrom.size();i++){
			
		//	(adjFrom[i]->adjacentTo).erase(std::remove((adjFrom[i]->adjacentTo).begin(), (adjFrom[i]->adjacentTo).end(), node), (adjFrom[i]->adjacentTo).end());
			//().erase((adjFrom[i]->adjacentTo).find(node));
		//	cout << "Del: removed node " << node->lit << " from " << adjFrom[i]->lit << endl;
		//}
        for(int i=0;i<(node->adjacentFrom).size();i++){
			
			((node->adjacentFrom)[i]->adjacentTo).erase(std::remove(((node->adjacentFrom)[i]->adjacentTo).begin(), ((node->adjacentFrom)[i]->adjacentTo).end(), node), ((node->adjacentFrom)[i]->adjacentTo).end());
			//().erase((adjFrom[i]->adjacentTo).find(node));
		//	cout << "Del: removed node " << node->lit << " from " << (node->adjacentFrom)[i]->lit << endl;
		}
        
		delete node;
		node = NULL;
		
		//cout << "Del: deleted node . Exit delGraph " << endl;
		
	}
	
	/*Backtrack procedure*/
	void backtrack(){
		
		//remove conflict
	//	cout << "BT: Backtracking check if conflict is there assignment.count(-1)  "<<assignment.count(-1) << " remove if true \n";
		if(assignment.count(-1)>0){
			assignment.erase(assignment.find(-1));
			litToNode.erase(litToNode.find(-1));
			
		}
	
		//cout << "BT: is delStack empty ? " << delStack.empty() << " if not empty run while loop (pop each element until decToBacktrack comes) \n";
		while(true){
			
			if(delStack.empty()){
				d--;
				break;
			}
		//cout << "Inside loop \n";
			//get top node 
		Node* litNode = delStack.top();
	//	cout << "BT : Got the top node from stack having lit " << litNode->lit << " \n";
		// remove all nodes from decVec for litNode .
		int curLevel = litNode->dLevel; 
	//	cout << "BT : Current Node on top has level " << curLevel << endl;
	
		
	//	cout << "BT : DecVec check for the current lit "<<litNode->lit<< " .  decVec has litNode ?" << decVec.count(litNode) << endl;
		if(decVec.count(litNode))
		 {
		 	 for(int i=0;i<decVec[litNode].size();i++){
		 	 	int lit = (decVec[litNode])[i]->lit;
		 	 	assignment.erase(assignment.find(lit));
	//	 	 	cout << "BT: deleting assignment based on DecVec for " << lit << endl;
			  }
		     decVec.erase(decVec.find(litNode));
	//	     cout << "BT: deleting the current lit " << litNode->lit << " from decVec \n";
	    }
		int lit = litNode->lit;
		
	//	cout << "BT : litToNode has lit" << lit << "? " << litToNode.count(lit) << endl;
		//remove from litToNode
		litToNode.erase(litToNode.find(lit));
	//	cout << "BT : Removed from litToNode \n";
	//	cout << "BT : assignLevel has lit" << lit << "? " << assignLevel.count(lit) << endl;
		//remove from assignLevel 
		assignLevel.erase(assignLevel.find(lit));
	//	cout << "BT : Removed from assignLevel \n";
		assignment.erase(assignment.find(lit));
	//	cout << "BT: Remove from assignment \n";
		
		
		//traverseDFS(litNode);
		//delGraphAt(litNode);
	 	//delGraphWithBFS(litNode);
		if (lit < 0){
			lit = -1*lit;
		}
		//cout << " Current lit is " << lit << endl;
		
		delStack.pop();
	    d--;
	//	cout << "BT : removed lit "<< lit << " from delStack and decremented decision level to " << d  << " curLevel is " << curLevel  << " dectobacktrack " << decToBacktrack << " \n";
			
		if(curLevel == decToBacktrack){
	//		cout << " current Level " <<  curLevel << "is equal to decToBacktrack . While loop must end now. \n";
		   break;	
		}
		
	}
		
			//delete globConflict;
		globConflict = NULL;
	//    cout << "BT: Made globConflict NULL. Did not delete. Assumption. will be deleted later in delGraph \n";
		
	    // ToDO : remove litToNode[lit] nodes from graph
	    // delete assignments from data structures. also remove corresponding stacks and revert to second highest decision level and next step should be to make decisions based on learned cloz.
	    // removeNodes having decision level greater than secondhighest decision level.
		
		//Delete all assignments made after making decision
	
    //cout << "BT: Should also update gamma accordingly. Best is to choose all clauses having assigned literals in assignment" << endl;
    gamma.clear();
    map<int, bool>::iterator it;
    for ( it = assignment.begin(); it != assignment.end(); it++ )
    {
        int key = it->first;  // string (key)
          if(key!=-1){
      //    	cout << "BT : Adding Clause to gamma for lit " << key << endl;
             addClauseToGamma(key);      	
		  }      
     }
    
	//cout << "BT: Exit Backtrack \n";

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
	
	void printStack(){
		cout << "Printing stack of size " << delStack.size() << endl;
		while(!delStack.empty()){
			Node* top = delStack.top();
			cout << top->lit << endl;
			delStack.pop();
		}
		exit(1);
	}
	
	/*
	* Updates the learned clause global variable. Also finds second highest decision level. 
	*/
	void learnClause(queue<Node*> q){
	//	cout << "LC: learn cloz \n"; 
		set<Node*> setQ;
		set<Node*>::iterator it;
		Node* cur;
	//	cout << "LC : Size of queue to learn clause from " << q.size() << endl;
		while(!q.empty()){
			cur = q.front();
	//		cout << " LC : Before inserting in it . current lit is " << cur->lit << " and assigned value is " << cur->assigned << endl;
			q.pop();
			setQ.insert(cur);
		}
	//	cout << "LC: inserted all queue elements to set . size of set is " <<setQ.size()<< "\n";
	   	int count = 0;
	   	vector<string> vecLiterals;
	   	int cLevel = globConflict->dLevel;
	//   	cout << "LC: Conflict at level " << cLevel << endl;
	   	int maxSecond = -1;
	   	int setSize = setQ.size();
		for (it=setQ.begin(); it!=setQ.end(); ++it){
          //  cout << "check 2 \n";
			cur = *it;
		    int lit = cur->lit;
		    bool assigned = cur->assigned;
		    int dLevel = cur->dLevel;
		    //cout << "LC: Set iter -- Current lit " << lit << " is at level " << dLevel <<  " and assigned to " << assigned << endl;
		    // Checks dLevel only when it is not the max level at conflict. Finds the maximum among the remaining. 
		    if(dLevel!=cLevel){
		    	if(maxSecond < dLevel){
		    		maxSecond = dLevel;
				}
				count++;
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
		std::string charEnd = "0";
		vecLiterals.push_back(charEnd);
		// either count == 0 or setSize == 1
		if(count == 0){
			int tDLevel = cur->dLevel;
			if(tDLevel == 0){
				decToBacktrack = -1;
			}
			else
		        decToBacktrack = 0;
		}
		else
		    decToBacktrack = maxSecond;
		learnedCloz = new Cloz(vecLiterals);
	//	cout <<"LC : Exit LC with size of learned literals " << vecLiterals.size() << endl;
	}
	
	/*
	*  Iterates over queue and checks if the cLevel is exactly once. cLevel is conflict level. Checks if the decision level of conflict is excatly once in the queue elements level
	*/
	bool isUniqueImp(queue<Node*> q , int cLevel){
	//	cout << "IUI : IsUnique Impl \n";
		int count = 0;
		set<Node*> setQ;
		set<Node*>::iterator it;
		Node* cur;
	//	cout << "IUI : Queue size is " << q.size() <<endl;
		while(q.size() != 0){
		//	cout << "check 1 \n";
			cur = q.front();
    //        cout << "IUI : Cur lit is " << (cur->lit) << " And is assigned value " << (cur->assigned) <<endl;
		//	 cout << "setQ size " << setQ.size(); 
			setQ.insert(cur);
		//	cout << "inserted in setQ \n"; 
			 q.pop();
	      //  cout << " popped \n";
		}
	//	cout << "IUI : Inserted all elements to the set having size " << setQ.size() << endl; 
		//cout << "check 2 \n";
		//int secondHighestDec = 0;
		for (it=setQ.begin(); it!=setQ.end(); ++it)
        {
          // 	cout << "check 3 \n";
		    int tempD = (*it)->dLevel;
		  	if(tempD == cLevel){
				count++;
			}
    //       	 cout << "IUI : Set current element is " << (*it)->lit << " and has value " << (*it)->assigned << endl;
	    }
	//    cout << "IUI : iterated over all elements to check the count of nodes at conflict level " << cLevel << " and count is " << count << endl;
		if(count == 1){ // count == setQ.size() ||
	//		decToBacktrack = secondHighestDec;
	//       cout << "IUI : Exit Found IUI . \n";
			return true;
		}
		//Verify this below - 
	//	if(count == setQ.size()){
			//All nodes in q are at same level . 
	//		decToBacktrack = 0;
	//		return true;
	//	}
	//	cout << "IUI : Exit Not Found IUI \n";
		return false;
	}
	bool allAtSameLevel(queue<Node*> q){
		set<Node*> setQ;
		set<Node*>::iterator it;
		Node* cur;
		while(!q.empty()){
			cur = q.front();
			q.pop();
			setQ.insert(cur);
		}
		int count =0;
		int index = 0;
		int prevLevel = -1;
		for (it=setQ.begin(); it!=setQ.end(); ++it){
          	cur = *it;
          	
		    int level = cur->dLevel;
	     	if(prevLevel==-1){
			    prevLevel = level;
			    count++;
		   }
		   else{
	            if(prevLevel == level){
	               count++;	
				}		   	
     	    }
			index++;
		}
		if(count==index){
			if(prevLevel == 0){
				decToBacktrack =-1;
			}
			else
			    decToBacktrack =0;
			    
			return true;
		}
		return false;
	}
	/*
	* Gets a queue and performs BFS and checks for unique implication point
	*/
	void analyzeAndLearn(){
	//	cout << "ALA : Analyze and learn\n";
		queue<Node*> q;
		Node* cur ;
		// We add conflict node to our queue. We can be sure that globConflict is not NULL because we only enter here if there is a conflict. And if there is a conflict we get a reference of the conflict in globConflict . Line number 280 in isUnitCloz 
		q.push(globConflict);
	//	cout << "ALA : pushed conflict Node " << globConflict->lit << " in the queue\n";
		//decision level of conflict
		int decConflict = globConflict->dLevel;
	//	cout << "ALA : conflict is at decision level " << decConflict << endl;
		//If the conflict occurs at level zero , it results from singleton and pure literals. So simly return with decToBacktrack =-1
		if(decConflict == 0){
			decToBacktrack =-1;
			return;
		}
		set<Node*> bigSet;
		bigSet.insert(globConflict);
		while(true){
		//	cout << "check 2 \n";
			if(q.empty()){
	//			cout << " ALA: Big queue is empty \n";
				break;
			}
			else{
			 cur = q.front();
			 q.pop();
	//		 cout << " ALA: Popped front. Front of Big queue is " << cur->lit << "Ans is assigned value " << cur->assigned <<endl;
			 // if the current node is a vertex node , then pop it and push to fron tback.  
			 if((cur->adjacentFrom).size() == 0){
	//		 	  cout << "ALA: it is a vertex element" << cur->lit << " So pushing back on the Big queue \n"; 
			 	  
			      q.push(cur);
			  }
			}
		  // cout << "check 3 \n";
		  //get Adjacent nodes to the current Node which have an edge from them to the current node. 	
	//	  cout << "ALA : Size of the current node's adjacentFrom (isVertex ? )" << (cur->adjacentFrom).size() << endl;
		  vector<Node*> adjNodes = cur->adjacentFrom;
		  for(int i=0;i<adjNodes.size();i++){
		  	  if(bigSet.count(adjNodes[i])){
		  	  	continue;
				}
			   q.push(adjNodes[i]);
			   bigSet.insert(adjNodes[i]);
	//		   cout << "ALA pushing " << (adjNodes[i])->lit << " on the front of Big queue \n";
		  }
		  //Temporary references/snapshots of the queue that are used in isUniueImplication and learningCloz from the cut.  
		  queue<Node*> tempQU = q;
		  queue<Node*> tempQD = q;
		  queue<Node*> tempQq = q;
		  //check if all the elements in the queue are vertex node, then break from the loop
		  //if(allVertex(tempQq)){
		  //	break;
		 // }
		 
		  //iterate over this cut and check for unique implication point
		  //Each iteration represents a cut. So we must check the unique implication point at every iteration and break/return when we find one. 
		  if(isUniqueImp(tempQU ,decConflict)){
		  	//Found the cut . So learn the clause and break
		  	learnClause(tempQD);
		  	//cout << "ALA : Decision Level is " << d <<endl;
		  	//printAssign();
		  	//learnedCloz->printCloz();
		  	//cout << "ALA: Decision level to backtrack to " << decToBacktrack << endl;
		  	return;
		  }
		  
		  //if(allAtSameLevel(tempQq)){
		  //      break;	
		 // }
          //cout << "check 5 \n";
		}
	//	cout << "ALA : Exit ALA \n";
		
		//cout << "can reach end \n";
	}
	
/*BOOL CtrlHandler( DWORD fdwCtrlType ) 
{ 
  switch( fdwCtrlType ) 
  { 
    // Handle the CTRL-C signal. 
    case CTRL_C_EVENT: 
      printf( "Ctrl-C event\n\n" );
      Beep( 750, 300 ); 
      return( TRUE );

    // CTRL-CLOSE: confirm that the user wants to exit. 
    case CTRL_CLOSE_EVENT: 
      Beep( 600, 200 ); 
      cout <<  "Ctrl-Close event\n\n" ;
      return( TRUE ); 

    // Pass other signals to the next handler. 
    case CTRL_BREAK_EVENT: 
      Beep( 900, 200 ); 
      printf( "Ctrl-Break event\n\n" );
      return FALSE; 

    case CTRL_LOGOFF_EVENT: 
      Beep( 1000, 200 ); 
      printf( "Ctrl-Logoff event\n\n" );
      return FALSE; 

    case CTRL_SHUTDOWN_EVENT: 
      Beep( 750, 500 ); 
      printf( "Ctrl-Shutdown event\n\n" );
      return FALSE; 

    default: 
      return FALSE; 
  } 
} 
*/
	
    
	void solveCDCL(){
	//	cout << "Inside solveCDCL" << endl;
	//    printAssign();
	  /*if( !SetConsoleCtrlHandler( (PHANDLER_ROUTINE) &CtrlHandler, TRUE ) ){
	  	  cout << "Could not set control handler \n";
	  }
	  else{
	  	cout << " Control Handle Set. \n";
	  }*/
        
		time_t start ;
		time_t end;
		start = time(NULL) ;
		end = time(NULL);
		while (end - start < timeout){
			end = time(NULL);
			unitPropagateCDCL();
			if(assignment.count(-1)==0){
				//there is no conflict
				if(allAssigned()){
					
					cout << "SAT\n";
					if(verbose){
					  printAssign();	
					}
					return;
				}
				else{
					//Need to Make decision
					
					makeDecisionFB();
				}
			}
			else{
				//there is conflict
				analyzeAndLearn();
				
				if(decToBacktrack < 0){
					cout << "UNSAT\n";
					if(verbose){
						if(learnedCloz == NULL){
							cout << "No learned Cloz. Conflict detected at Preprocessing \n";
						}
						else
					        learnedCloz->printCloz();	
					}
					
					return;
				}
				 else{
				 	currForm.push_back(learnedCloz);
					backtrack();
				}
			}
		}
		cout << "UNKNOWN : TO \n";
		if(verbose){
			printStack();
		} 
	}
		
};
