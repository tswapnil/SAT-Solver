#include <iostream>
//#include "Cloz.h"

class Node{
	public:
		//decision level
		int dLevel;
		// the literal it stores
		int lit;
		// bool assigned to the literal
		bool assigned;
		// adjacent nodes in the graph to the current nodes. Nodes this node points to. 
		vector<Node*> adjacentTo;
		// adjacent nodes that point to this node.
		vector<Node*> adjacentFrom; 
		
		Node(int level, int literal, bool assignment){
			dLevel = level;
			lit = literal;
			assignment = assigned;
		}
		
	
};
class Edge{
	public :
		// starting node
		Node* u;
		// end node
		Node* v;
		//Cloz this edge stores
		Cloz* c;
		Edge(Node* start, Node* end, Cloz* h){
			u = start;
			v = end;
			c = h;
		}
};
class Graph{

	public :
	//edges
	vector<Edge*> edges;	
	//nodes
	vector<Node*> nodes;
	Graph(vector<Edge*> edgeVec, vector<Node*> nodeVec){
	  edges = edgeVec;
	  nodes = nodeVec;
	}
};
