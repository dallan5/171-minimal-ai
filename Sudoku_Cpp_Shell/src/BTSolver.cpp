#include"BTSolver.hpp"
#include <climits>
using namespace std;


// =====================================================================
// Constructors
// =====================================================================

BTSolver::BTSolver ( SudokuBoard input, Trail* _trail,  string val_sh, string var_sh, string cc )
: sudokuGrid( input.get_p(), input.get_q(), input.get_board() ), network( input )
{
	valHeuristics = val_sh;
	varHeuristics = var_sh; 
	cChecks =  cc;

	trail = _trail;
}

// =====================================================================
// Consistency Checks
// =====================================================================

// Basic consistency check, no propagation done
bool BTSolver::assignmentsCheck ( void )
{
	for ( Constraint c : network.getConstraints() )
		if ( ! c.isConsistent() )
			return false;

	return true;
}

// =================================================================
// Arc Consistency
// =================================================================
bool BTSolver::arcConsistency ( void )
{
    vector<Variable*> toAssign;
    vector<Constraint*> RMC = network.getModifiedConstraints();
    for (int i = 0; i < RMC.size(); ++i)
    {
        vector<Variable*> LV = RMC[i]->vars;
        for (int j = 0; j < LV.size(); ++j)
        {
            if(LV[j]->isAssigned())
            {
                vector<Variable*> Neighbors = network.getNeighborsOfVariable(LV[j]);
                int assignedValue = LV[j]->getAssignment();
                for (int k = 0; k < Neighbors.size(); ++k)
                {
                    Domain D = Neighbors[k]->getDomain();
                    if(D.contains(assignedValue))
                    {
                        if (D.size() == 1)
                            return false;
                        if (D.size() == 2)
                            toAssign.push_back(Neighbors[k]);
                        trail->push(Neighbors[k]);
                        Neighbors[k]->removeValueFromDomain(assignedValue);
                    }
                }
            }
        }
    }
    if (!toAssign.empty())
    {
        for (int i = 0; i < toAssign.size(); ++i)
        {
            Domain D = toAssign[i]->getDomain();
            vector<int> assign = D.getValues();
            trail->push(toAssign[i]);
            toAssign[i]->assignValue(assign[0]);
        }
        return arcConsistency();
    }
    return network.isConsistent();
}

/**
 * Part 1 TODO: Implement the Forward Checking Heuristic
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all MODIFIED variables, mapped to their MODIFIED domain. 
 * 		   The bool is true if assignment is consistent, false otherwise.
 */
pair<unordered_map<Variable*,Domain>,bool> BTSolver::forwardChecking ( void )
{
    unordered_map<Variable*,Domain> modified;

    // Loop through all the constrints.
    for (Constraint* constraint : network.getModifiedConstraints())
    {
        // Get all variables in each constraint
        for (Variable* variable : constraint->vars)
        {
            // if the variable is already assigned, then skip it and move to next.
            if (!variable->isAssigned()) continue;

            //get the current variable assignment to make sure we don't use the same for assignment
            int assignmentValue = variable->getAssignment();

            // Loop over all neightbours of the variables in the constraints,
            // if the assignment is the current variable assignment then skip it.
            for (Variable* neighbour : network.getNeighborsOfVariable(variable))
            {
                if (neighbour->isAssigned()) continue;

                Domain neighbourDomain = neighbour->getDomain();
                if (!neighbourDomain.contains(assignmentValue)) continue;

                if (neighbourDomain.size() == 1)
                    return {modified, false};

                // Only push + store original domain once per neighbour
                if (modified.find(neighbour) == modified.end())
                    trail->push(neighbour);

                neighbour->removeValueFromDomain(assignmentValue);

                modified[neighbour] = neighbour->getDomain();
            }
        }
    }

    return {modified, true};
}


/**
 * Part 2 TODO: Implement both of Norvig's Heuristics
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * (2) If a constraint has only one possible place for a value
 *     then put the value there.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all variables that were assigned during 
 *         the whole NorvigCheck propagation, and mapped to the values that they were assigned. 
 *         The bool is true if assignment is consistent, false otherwise.
 */
pair<unordered_map<Variable*,int>,bool> BTSolver::norvigCheck ( void )
{
    unordered_map<Variable*, int> assignedVariables;
    bool boardChanged = true;
    // get N squares on board
    int N = sudokuGrid.get_p() * sudokuGrid.get_q();

    while (boardChanged)
    {
        boardChanged = false;
        
        //rule 1, find contraint with only 1 variaible available
        for (Variable* var : network.getVariables())
        {
            //if var is already assigned, then prune neightbours to reduce domain
            if (var->isAssigned())
            {
                int value = var->getAssignment();
                for (Variable* neighbour : network.getNeighborsOfVariable(var))
                {
                    if (!neighbour->isAssigned() && neighbour->getDomain().contains(value))
                    {
                        trail->push(neighbour);
                        neighbour->removeValueFromDomain(value);
                        boardChanged = true; // A domain shrank, which might trigger new singles

                        if (neighbour->getDomain().size() == 0) {
                            return {assignedVariables, false};
                        }
                    }
                }
            }
            // check domain is 1. then assign that value. This is biggest constrain.
            else if (var->getDomain().size() == 1)
            {
                // get only variable available
                int value = var->getDomain().getValues()[0];

                // track it and assign it
                trail->push(var);
                var->assignValue(value);
                assignedVariables[var] = value;
                boardChanged = true;

                // prune the value from all neighbour
                for (Variable* neighbour : network.getNeighborsOfVariable(var))
                {
                    if (!neighbour->isAssigned() && neighbour->getDomain().contains(value))
                    {
                        trail->push(neighbour);
                        neighbour->removeValueFromDomain(value);

                        if (neighbour->getDomain().size() == 0) {
                            return {assignedVariables, false};
                        }
                    }
                }
            }
        }
        
        // rule 1, find hidden singles
        for (Constraint* constraint : network.getModifiedConstraints())
        {
            for (int value = 1; value <= N; value ++)
            {
                int possibleCount = 0;
                Variable* targetVariable = nullptr;
                bool alreadyAssignedInContraint = false;

                // scan the constrint for this value
                for (Variable* var : constraint->vars)
                {
                    if (var->isAssigned() && var->getAssignment() == value) {
                        alreadyAssignedInContraint = true;
                        break;
                    }
                    if (!var->isAssigned() && var->getDomain().contains(value)) {
                        possibleCount++;
                        targetVariable = var;
                    }
                }
                
                // check waht we gound and move on to the next value
                if (alreadyAssignedInContraint) {
                    continue;
                }

                if (possibleCount == 0) {
                    return {assignedVariables, false};
                }
                else if (possibleCount == 1 && targetVariable != nullptr)
                {
                    // this is a hidden single found
                    // but check it's not already processed
                    if (assignedVariables.find(targetVariable) == assignedVariables.end())
                    {
                        trail->push(targetVariable);
                        targetVariable->assignValue(value);
                        assignedVariables[targetVariable] = value;
                        boardChanged = true;

                        // prune the new assignment from all neighbours
                        for (Variable* neightbour : network.getNeighborsOfVariable(targetVariable))
                        {
                            if (!neightbour->isAssigned() && neightbour->getDomain().contains(value))
                            {
                                trail->push(neightbour);
                                neightbour->removeValueFromDomain(value);

                                if (neightbour->getDomain().size() == 0) {
                                    return {assignedVariables, false};
                                }
                            }
                        }
                    }
                }
           }
        }
    }
    return {assignedVariables, true};
}
/**
 * Optional TODO: Implement your own advanced Constraint Propagation
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
bool BTSolver::getTournCC ( void )
{
	return false;
}

// =====================================================================
// Variable Selectors
// =====================================================================

// Basic variable selector, returns first unassigned variable
Variable* BTSolver::getfirstUnassignedVariable ( void )
{
	for ( Variable* v : network.getVariables() )
		if ( !(v->isAssigned()) )
			return v;

	// Everything is assigned
	return nullptr;
}

/**
 * Part 1 TODO: Implement the Minimum Remaining Value Heuristic
 *
 * Return: The unassigned variable with the smallest domain
 */
Variable* BTSolver::getMRV ( void )
{
    vector<Variable*> allCells = network.getVariables();

    Variable* chosenCell = nullptr;
    int minDomainSize = INT_MAX;

    for (Variable* cell : allCells)
    {
        if (!cell->isAssigned())
        {
            int currentDomainSize = cell->getDomain().size();

            if (currentDomainSize < minDomainSize)
            {
                minDomainSize = currentDomainSize;
                chosenCell = cell;
            }
        }
    }

    return chosenCell;
}

/**
 * Part 2 TODO: Implement the Minimum Remaining Value Heuristic
 *                with Degree Heuristic as a Tie Breaker
 *
 * Return: The unassigned variable with the smallest domain and affecting the most unassigned neighbors.
 * 		   If there are multiple variables that have the same smallest domain with the same number 
 * 		   of unassigned neighbors, add them to the vector of Variables.
 *         If there is only one variable, return the vector of size 1 containing that variable.
 */
vector<Variable*> BTSolver::MRVwithTieBreaker ( void )
{
    vector<Variable*> variables = network.getVariables();

    int minDomain = INT_MAX;
    int maxDegree = -1;
    vector<Variable*> best;

    for (Variable* v : variables)
    {
        if (!v->isAssigned())
        {
            int domainSize = v->getDomain().size();

            int degree = 0;
            for (Variable* n : network.getNeighborsOfVariable(v))
                if (!n->isAssigned())
                    degree++;

            if (domainSize < minDomain)
            {
                minDomain = domainSize;
                maxDegree = degree;
                best.clear();
                best.push_back(v);
            }
            else if (domainSize == minDomain)
            {
                if (degree > maxDegree)
                {
                    maxDegree = degree;
                    best.clear();
                    best.push_back(v);
                }
                else if (degree == maxDegree)
                {
                    best.push_back(v);
                }
            }
        }
    }
    // add empty null so the best variable selector won't crash when retriving first element
    if (best.empty())
    {
        best.push_back(nullptr);
    }

    return best;
}

/**
 * Optional TODO: Implement your own advanced Variable Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
Variable* BTSolver::getTournVar ( void )
{
	return nullptr;
}

// =====================================================================
// Value Selectors
// =====================================================================

// Default Value Ordering
vector<int> BTSolver::getValuesInOrder ( Variable* v )
{
	vector<int> values = v->getDomain().getValues();
	sort( values.begin(), values.end() );
	return values;
}

/**
 * Part 1 TODO: Implement the Least Constraining Value Heuristic
 *
 * The Least constraining value is the one that will knock the least
 * values out of it's neighbors domain.
 *
 * Return: A list of v's domain sorted by the LCV heuristic
 *         The LCV is first and the MCV is last
 */
vector<int> BTSolver::getValuesLCVOrder ( Variable* v )
{
	//we need to loop over our domain values. Then loop over each neighbour. Check how many prunes are necessary
    vector<int> values = v->getDomain().getValues();
    auto neighbours = network.getNeighborsOfVariable(v);

    vector<pair<int,int>> scorePairs; // {pruneCount, value}

    for (int val : values)
    {
        int count = 0;
        for (Variable* n : neighbours)
        {
            if (!n->isAssigned() && n->getDomain().contains(val))
                count++;
        }

        scorePairs.push_back({count, val});
    }

    sort(scorePairs.begin(), scorePairs.end()); // sorts by pruneCount ascending

    vector<int> orderedOut;
    for (auto& scorePair : scorePairs)
        orderedOut.push_back(scorePair.second);

    return orderedOut;
}

/**
 * Optional TODO: Implement your own advanced Value Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
vector<int> BTSolver::getTournVal ( Variable* v )
{
	return vector<int>();
}

// =====================================================================
// Engine Functions
// =====================================================================

int BTSolver::solve ( float time_left)
{
	if (time_left <= 60.0)
		return -1;
	double elapsed_time = 0.0;
    clock_t begin_clock = clock();

	if ( hasSolution )
		return 0;

	// Variable Selection
	Variable* v = selectNextVariable();

	if ( v == nullptr )
	{
		for ( Variable* var : network.getVariables() )
		{
			// If all variables haven't been assigned
			if ( ! ( var->isAssigned() ) )
			{
				return 0;
			}
		}

		// Success
		hasSolution = true;
		return 0;
	}

	// Attempt to assign a value
	for ( int i : getNextValues( v ) )
	{
		// Store place in trail and push variable's state on trail
		trail->placeTrailMarker();
		trail->push( v );

		// Assign the value
		v->assignValue( i );

		// Propagate constraints, check consistency, recurse
		if ( checkConsistency() ) {
			clock_t end_clock = clock();
			elapsed_time += (float)(end_clock - begin_clock)/ CLOCKS_PER_SEC;
			double new_start_time = time_left - elapsed_time;
			int check_status = solve(new_start_time);
			if(check_status == -1) {
			    return -1;
			}
			
		}

		// If this assignment succeeded, return
		if ( hasSolution )
			return 0;

		// Otherwise backtrack
		trail->undo();
	}
	return 0;
}

bool BTSolver::checkConsistency ( void )
{
	if ( cChecks == "forwardChecking" )
		return forwardChecking().second;

	if ( cChecks == "norvigCheck" )
		return norvigCheck().second;

	if ( cChecks == "tournCC" )
		return getTournCC();

	return assignmentsCheck();
}

Variable* BTSolver::selectNextVariable ( void )
{
	if ( varHeuristics == "MinimumRemainingValue" )
		return getMRV();

	if ( varHeuristics == "MRVwithTieBreaker" )
		return MRVwithTieBreaker()[0];

	if ( varHeuristics == "tournVar" )
		return getTournVar();

	return getfirstUnassignedVariable();
}

vector<int> BTSolver::getNextValues ( Variable* v )
{
	if ( valHeuristics == "LeastConstrainingValue" )
		return getValuesLCVOrder( v );

	if ( valHeuristics == "tournVal" )
		return getTournVal( v );

	return getValuesInOrder( v );
}

bool BTSolver::haveSolution ( void )
{
	return hasSolution;
}

SudokuBoard BTSolver::getSolution ( void )
{
	return network.toSudokuBoard ( sudokuGrid.get_p(), sudokuGrid.get_q() );
}

ConstraintNetwork BTSolver::getNetwork ( void )
{
	return network;
}
