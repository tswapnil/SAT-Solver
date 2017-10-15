#include <map>
#include "Cloz.h"
#include <time.h>
#include <ctime>
#include <iostream>
#include <vector>
#include <cmath>
#include <queue>
#include <stack>
/**
* This class stores the variable and its boolean value. Variables can be from 1 to $nvar .
**/
class node {
	public :
		// Bool value for variable var
		bool val;
		// stores info for variable / literal var
		int var;
		//left and right pointers in the state space
		node* left;
		node* right;
		node(int variable,bool value){
			var = variable;
			val = value;
			left = NULL;
			right = NULL;
		}
		node(int variable,bool value,node* l, node* r){
			var = variable;
			val = value;
			left = l;
			right = r;
		}
		node* getLeft(){
			return left;
		}
		node* getRight(){
			return right;
		}
		bool getVal(){
			return val;
		}
		int getVar(){
			return var;
		}
};
/**
* This class has the methods for solving the cnf expression. It also holds member variables for evaluation
**/
class Solver {
	public :
		//number of clauses
		int nCloz;
		// number of total variables = $nvar
		int nVars;
		//vector of clauses 
		vector<Cloz*> vecCloz;
		// the assignment of variables to be evaluated on. 
		map<int,bool> assignment;
		//Root of the state space 
		node* root;
		// Stack for DFS that stores the nodes in the dfs paths from root to leaves
		stack<node*> stackN; 
		// flag to check if all the possible assignments have been explored in the state space
		bool allExplored;
		// vector to hold all previously explored different assignments.
		vector<map<int,bool> > prevAssigns;
	
	//Constructor to initialize vector of clauses and $nvar		
	Solver (vector<Cloz*> vecCl, int numVars){
		this -> vecCloz = vecCl;
		nCloz = vecCl.size();
		nVars = numVars;
		root = new node(0,false);
		//Done when exploring state space from a tree
		//setupTree(root);
		//initializeStack(root);
		srand (time(NULL));
		allExplored = false;
		      //Debug : cout << "N var is " << nVars << endl;
		      //Debug : cout <<"Stack size at t0 is " << stackN.size() << endl;
	}
	/**
	*  This method compares two assignments and returns true if they both are the same
	**/
	bool map_compare (map<int,bool> const &lhs, map<int,bool> const &rhs) {
        return lhs.size() == rhs.size() && equal(lhs.begin(), lhs.end(), rhs.begin());
    }
    /**
    * This method generates next Random assignment 
    **/
    void getNextAssignmentRandom(){
		int i;
		int r;
		map<int,bool> assign ;
		r = ( rand() % nVars + 1) ;
		assignment[r] = !assignment[r];
		return ;
	}
	/**
	* Attempts to find the solution by exploring random assignments
	**/
	void solveRandom (){
		time_t start ;
		time_t end;
		int prevSize ;
		int i;
		bool rotate = false;
		int totalPossibleAssignments = pow(2,nVars);
		start = time(NULL) ;
		int counter = 0;
		while(end - start < 10){
			 end = time(NULL);
			 rotate = false;
			 getNextAssignmentRandom();
			 //check to see UNSAT 
			 prevSize = prevAssigns.size();
			 if(prevSize == totalPossibleAssignments){
			 	cout << "Number of explored Assignments " << prevAssigns.size() << endl;
			 	double ratio = (double)prevAssigns.size()/totalPossibleAssignments;
				cout << "Ratio " << ratio <<endl;
			 	cout << "UNSAT \n";
			 	return;
			 }
			for(i=0;i<prevSize;i++){
				
				if(map_compare(prevAssigns[i], assignment)){
					rotate = true;
					break;
				}
			}
				
			if(rotate){
				continue;
			}
			else{
				if(evalExpr()){
					//Debug : printAssign();
					cout << "Number of explored Assignments " << prevAssigns.size() << endl;
					double ratio = (double)prevAssigns.size()/totalPossibleAssignments;
				    cout << "Ratio " << ratio <<endl;
					cout << "SAT \n";
					return;
				}
				
				prevAssigns.push_back(assignment);
			}
			counter++;
		 }
		
		int x = prevAssigns.size();
		cout << "Number of explored Assignments " << x << endl;
		double ratio = (double)x/totalPossibleAssignments;
		cout << "Ratio " << ratio <<endl;
		cout << "UNKNOWN \n";
	    return;
	}
	
	/** 
	* Initialize stack with assignment to zero of all the variables. This is done by traversing the tree left from root to leaf.
	**/
	void initializeStack(node * root){
		node* iter = root;
		while(iter != NULL && iter != NULL){
			stackN.push(iter);
	    	   //Debug : cout << "stack iter var has " <<iter -> var << endl;
			(this->assignment)[iter->var] = iter->val;
			iter = iter -> left;
		}
	}
	
	/**
	* This is used to set up the tree so that all the nodes are populated and the links between the nodes are established. 
	* This is done by level order traversal using queue . At each level all the nodes have the same variable. 
	**/
	void setupTree(node * root){
		queue<node*> q;
		q.push(root); 
		while(!q.empty()){
			node* temp = q.front();
			       //Debug : cout << "Creating " <<temp->getVar() <<endl;
			int tVar = temp->getVar();
			node* tLeft = new node(tVar+1,false);
			node* tRight = new node(tVar+1,true);
			if(tVar < nVars){
		      temp->left = tLeft;
			  temp->right= tRight;
			  q.push(tLeft);
			  q.push(tRight); 
			}		
			q.pop();
		}
	}
	/**
	* This method modifies the assignment map by exploring the next possible assignment in the state space. 
	* This is done by keeping a stack of a path traversed last from root to leaf. Next assignment is generated in the DFS order. 
	**/
	void getNextAssign(){	
		if(stackN.empty()){
			//Nothing to do if the stack is empty
			return ;
		}
		else{
	     	node* temp = stackN.top();
	     	stackN.pop();
			node* parent = stackN.top();
			
			if(parent->left == temp){
				// Case when there is a right node to explore for the parent.
				node* r = parent->right;
				stackN.push(r);
				assignment[r->var] = r->val;
			}
			else{
				// Case when the current node is the right node hence must backtrack;
				bool condition = (parent->right == temp);
				while(condition){
				        //Debug : cout << "Temp Var is " << temp -> var << endl;
			        temp = stackN.top();
			        stackN.pop();
			      	if(stackN.empty()){
						//All assignments explored
						allExplored = true;
						return;
					}
			      parent = stackN.top();
                  condition = (parent->right == temp);			
				}
				node * iter = parent -> right;
				while(iter != NULL){
					stackN.push(iter);
					//Debug : cout << "iter var is " << iter -> var << endl;
					assignment[iter->var]=iter->val;
					iter = iter ->left;
				}
				
			}
			
		}
		
	}
	/**
	* This method evaluates the cnf expression with the assignment and returns the result.
	**/
	bool evalExpr (){
		int i=0;
		bool res = true;
		
		for(i=0;i<nCloz;i++){
			    //Debug : vecCloz[i]->printCloz();
		    bool temp = vecCloz[i] -> evalCloz((this->assignment));
		    res = res && temp;
		}
		        //Debug : cout << "Result of expr evaluated to " << res << endl;
		return res;
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
	/**
	*  Method that keeps track of time . If time exceeds 10 seconds it prints the number of explored states so far .
	* Also prints SAT or UNSAT if the assignment is found or can not be found in the given limited time.
	**/
	void solve(){
		time_t start ;
		time_t end;
        int totalPossibleAssignments = pow(2,nVars);
	    start = time(NULL) ;
	    int count = 0;
	    if(evalExpr()){
	    	        printAssign();
					cout << "SAT \n";
					return;
		}
		while(end - start < 10){
			end = time(NULL);
			getNextAssign();
			//Debug : printAssign();
			count++;
			if(allExplored){
				cout << "UNSAT" <<endl;
				cout << "Explored Assignments " << count <<endl;
				cout << "Total Assignments possible " << totalPossibleAssignments << endl;
				double ratio = (double)count/totalPossibleAssignments;
				cout << "Ratio " << ratio <<endl;
				return;
			}
	        if(evalExpr()){
	        	    printAssign();
					cout << "SAT \n";
					return;
				}
				
		 }
	    cout << "Unknown" << endl;
	    cout << "Explored Assignments " << count <<endl;
		cout << "Total Assignments possible " << totalPossibleAssignments << endl;
		double ratio = (double)count/totalPossibleAssignments;
		cout << "Ratio " << ratio <<endl;
	    return;
	}		
};
