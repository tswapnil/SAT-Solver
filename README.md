"# sat-solver-tswapnil" 
------- CDCL Solver -- 
Compatibility : Windows 

Format of the command to run --
SatSolver.exe FILEPATH [TIMEOUT] [Verbose]

FILEPATH is a string 
TIMEOUT AND VERBOSE are type int
VERBOSE = {0,1} 

Typical Command to run Solver -- 
SatSolver.exe "C:\\filename.sat"  or 
SatSolver.exe "C:\\filename.sat" 300  or 
SatSolver.exe "C:\\filename.sat" 300 0

When verbose = 1 . 
Case SAT : Assignments are printed in the format x,y  where x is the lit and y is assignment (delta(x))
Case UNSAT : Prints the learned cloz as in the dimacs format . 
Case UNKNOWN : results when either time out or user cancels (Ctrl + C). Prints the current decision stack (delStack)

In order to generate SatSolver.exe , compile CDCL.h, SatSolver.cpp, Cloz.h , Graph.h .



---- Conflict Analysis ----
SatSolver.cpp has the main() method to run the SAT Solver. 
CDCL.h has the complete implementation of conflict Analysis.
The code stops at the first conflict. or returns SAT if without any conflict it finds an assignment. 
compile SatSolver.cpp, CDCL.h , and Cloz.h .

Specify the file path in the string filePath and run SatSolver.cpp
The results of petite benchmarks are mentioned in the file DPLLResults.txt (./resource/CDCLResults.txt)


----DPLL Below -------------------------
SatSolver.cpp has the main() method to run the SAT Solver. 
DPLL.h has the complete implementation of DPLL algo. 
compile SatSolver.cpp, DPLL.h , and Cloz.h .

Specify the file path in the string filePath and run SatSolver.cpp
The results of petite benchmarks are mentioned in the file DPLLResults.txt (./resource/DPLLResults.txt)


--------Random assignment below --------
SatSolver.cpp has the main() method to run the SAT Solver. 
In order to specify a file path , please add the file path in the SatSolver.cpp file to the string filePath. 
Compile Solver.h , Cloz.h and SatSolver.cpp and run SatSolver.cpp.

Solver.h has the "Solver" class and solveRandom() function that generates a random assignment and evaluates it. 
Cloz.h has "Cloz" class that has the utility functions and variables for clauses.   
