# CSP Assignment
# Original code by Håkon Måløy
# Updated by Xavier Sánchez Díaz

import copy
from itertools import product as prod


class Solver:
    def __init__(self):
        # self.variables is a list of the variable names in the CSP
        self.variables = []

        # self.domains is a dictionary of domains (lists)
        self.domains = {}

        # self.constraints[i][j] is a list of legal value pairs for
        # the variable pair (i, j)
        self.constraints = {}

        self.numCalls = 0
        self.numFailures = 0

    # -------------------------------------- Method -------------------------------------------------

    def add_variable(self, name: str, domain: list):
        """Add a new variable to the CSP.

        Parameters
        ----------
        name : str
            The name of the variable to add
        domain : list
            A list of the legal values for the variable
        """
        self.variables.append(name)
        self.domains[name] = list(domain)
        self.constraints[name] = {}

    # -------------------------------------- Method -------------------------------------------------

    @staticmethod
    def get_all_possible_pairs(a: list, b: list) -> list[tuple]:
        """Get a list of all possible pairs (as tuples) of the values in
        lists 'a' and 'b', where the first component comes from list
        'a' and the second component comes from list 'b'.

        Parameters
        ----------
        a : list
            First list of values
        b : list
            Second list of values

        Returns
        -------
        list[tuple]
            List of tuples in the form (a, b)
        """
        return prod(a, b)

    # -------------------------------------- Method -------------------------------------------------

    def get_all_arcs(self) -> list[tuple]:
        """Get a list of all arcs/constraints that have been defined in
        the CSP.

        Returns
        -------
        list[tuple]
            A list of tuples in the form (i, j), which represent a
            constraint between variable `i` and `j`
        """
        return [(i, j) for i in self.constraints for j in self.constraints[i]]

    # -------------------------------------- Method -------------------------------------------------

    def get_all_neighboring_arcs(self, var: str) -> list[tuple]:
        """Get a list of all arcs/constraints going to/from variable 'var'.

        Parameters
        ----------
        var : str
            Name of the variable

        Returns
        -------
        list[tuple]
            A list of all arcs/constraints in which `var` is involved
        """
        return [(i, var) for i in self.constraints[var]]

    # -------------------------------------- Method -------------------------------------------------

    def add_constraint_one_way(self, i: str, j: str,
                               filter_function: callable):
        """Add a new constraint between variables 'i' and 'j'. Legal
        values are specified by supplying a function 'filter_function',
        that should return True for legal value pairs, and False for
        illegal value pairs.

        NB! This method only adds the constraint one way, from i -> j.
        You must ensure to call the function the other way around, in
        order to add the constraint from j -> i, as all constraints
        are supposed to be two-way connections!

        Parameters
        ----------
        i : str
            Name of the first variable
        j : str
            Name of the second variable
        filter_function : callable
            A callable (function name) that needs to return a boolean.
            This will filter value pairs which pass the condition and
            keep away those that don't pass your filter.
        """
        if j not in self.constraints[i]:
            # First, get a list of all possible pairs of values
            # between variables i and j
            self.constraints[i][j] = self.get_all_possible_pairs(
                self.domains[i], self.domains[j])

        # Next, filter this list of value pairs through the function
        # 'filter_function', so that only the legal value pairs remain
        self.constraints[i][j] = (
            list(filter(lambda value_pair: filter_function(*value_pair), self.constraints[i][j])))

    # -------------------------------------- Method -------------------------------------------------

    def add_all_different_constraint(self, var_list: list):
        """Add an Alldiff constraint between all the variables in the
        list provided.

        Parameters
        ----------
        var_list : list
            A list of variable names
        """
        for (i, j) in self.get_all_possible_pairs(var_list, var_list):
            if i != j:
                self.add_constraint_one_way(i, j, lambda x, y: x != y)

    # -------------------------------------- Method -------------------------------------------------

    def backtracking_search(self):
        """This functions starts the CSP solver and returns the found
        solution.
        """
        # Make a so-called "deep copy" of the dictionary containing the
        # domains of the CSP variables. The deep copy is required to
        # ensure that any changes made to 'assignment' does not have any
        # side effects elsewhere.
        assignment = copy.deepcopy(self.domains)

        # Run AC-3 on all constraints in the CSP, to weed out all the
        # values that are not arc-consistent to begin with
        self.ac3_inference(assignment, self.get_all_arcs())

        # Call backtrack with the partial assignment 'assignment'
        return self.backtrack(assignment)

    # -------------------------------------- Method -------------------------------------------------

    def backtrack(self, assignment: dict):
        """The function 'Backtrack' from the pseudocode in the
        textbook.

        The function is called recursively, with a partial assignment of
        values 'assignment'. 'assignment' is a dictionary that contains
        a list of all legal values for the variables that have *not* yet
        been decided, and a list of only a single value for the
        variables that *have* been decided.

        When all the variables in 'assignment' have lists of length
        one, i.e. when all variables have been assigned a value, the
        function should return 'assignment'. Otherwise, the search
        should continue. When the function 'inference' is called to run
        the AC-3 algorithm, the lists of legal values in 'assignment'
        should get reduced as AC-3 discovers illegal values.

        IMPORTANT: For every iteration of the for-loop in the
        pseudocode, you need to make a deep copy of 'assignment' into a
        new variable before changing it. Every iteration of the for-loop
        should have a clean slate and not see any traces of the old
        assignments and inferences that took place in previous
        iterations of the loop.
        """
        self.numCalls += 1
        if self.hasCompletedThe(assignment):
            return assignment
        Xi = self.selectUnassignedVariableFrom(assignment)
        for Di in assignment[Xi]:
            if self.isConsistent(Xi, Di, assignment):
                assignmentCopy = copy.deepcopy(assignment)
                assignmentCopy[Xi] = [Di]  # a new version where the solution for X1 is Di
                if self.ac3_inference(assignmentCopy, copy.deepcopy(self.get_all_arcs())):
                    result = self.backtrack(assignmentCopy)
                    if result is not None:
                        return result
        self.numFailures += 1
        return None

    # -------------------------------------- Method -------------------------------------------------

    def ac3_inference(self, assignment: dict, queue: list[tuple]) -> bool:
        """The function 'AC-3' from the pseudocode in the textbook.
        'assignment' is the current partial assignment, that contains
        the lists of legal values for each undecided variable. 'queue'
        is the initial queue of arcs that should be visited.
        """
        while len(queue) > 0:
            Xi, Xj = queue.pop()
            if self.revised(assignment, Xi, Xj):
                if len(assignment[Xi]) == 0:
                    return False
                Xi_neighbors = list(self.get_all_neighboring_arcs(Xi))
                for neighbor_arc in Xi_neighbors:
                    if Xj not in neighbor_arc:  # All neighbors but Xj
                        queue.append(neighbor_arc)
        return True

    # -------------------------------------- Method -------------------------------------------------

    def revised(self, assignment: dict, Xi: str, Xj: str):
        """The function 'Revise' from the pseudocode in the textbook.
        'assignment' is the current partial assignment, that contains
        the lists of legal values for each undecided variable. 'i' and
        'j' specifies the arc that should be visited. If a value is
        found in variable i's domain that doesn't satisfy the constraint
        between Xi and Xj, the value should be deleted from i's list of
        legal values in 'assignment'.

        Constraint-based pruning
        """
        revised = False
        constraints_Xi_Xj = self.constraints[Xi][Xj]
        notSatisfyingValues = []
        Di = list(assignment[Xi])
        Dj = list(assignment[Xj])

        for x_in_Di in Di:
            satisfies = False
            for y_in_Dj in Dj:
                if (x_in_Di, y_in_Dj) in constraints_Xi_Xj:
                    satisfies = True
            if not satisfies:
                notSatisfyingValues.append(x_in_Di)
                revised = True

        # removes all the not satisfying x from Di
        for x in notSatisfyingValues:
            Di.remove(x)
        assignment[Xi] = Di
        return revised

    # -------------------------------------- Method -------------------------------------------------

    @staticmethod
    def selectUnassignedVariableFrom(assignment: dict[str, list]) -> str:
        """The function 'Select-Unassigned-Variable' from the pseudocode
        in the textbook. Should return the name of one of the variables
        in 'assignment' that have not yet been decided, i.e. whose list
        of legal values has a length greater than one.

        Return:
            The first variable holding a list of possible values (domain) greater than one.
        """
        for Xi, Domain in assignment.items():
            if len(Domain) > 1:
                return Xi

    # -------------------------------------- Method -------------------------------------------------

    @staticmethod
    def isConsistent(Xi, Di, assignment) -> bool:
        # TODO add more intelligence in future versions?
        return True

    # -------------------------------------- Method -------------------------------------------------

    @staticmethod
    def hasCompletedThe(assignment: dict) -> bool:
        """
        Verifies whether the assignment is complete i.e. each variable has only one value associated to it.
        :param assignment: a dictionary of variable and domain.
        :return: True if all variable have one - and only one - solution. False if otherwise.
        """
        for Xi, Di in assignment.items():
            if len(Di) != 1:
                return False
        return True


# -------------------------------------- class CSP end ----------------------------------------------------------------
def create_map_coloring_csp():
    """Instantiate a CSP representing the map coloring problem from the
    textbook. This can be useful for testing your CSP solver as you
    develop your code.
    """
    csp = Solver()
    states = ['WA', 'NT', 'Q', 'NSW', 'V', 'SA', 'T']
    edges = {'SA': ['WA', 'NT', 'Q', 'NSW', 'V'],
             'NT': ['WA', 'Q'], 'NSW': ['Q', 'V']}
    colors = ['red', 'green', 'blue']
    for state in states:
        csp.add_variable(state, colors)
    for state, other_states in edges.items():
        for other_state in other_states:
            csp.add_constraint_one_way(state, other_state, lambda i, j: i != j)
            csp.add_constraint_one_way(other_state, state, lambda i, j: i != j)
    return csp


# -------------------------------------- function -----------------------------------------------------------------
def create_sudoku_csp(filename: str) -> Solver:
    """Instantiate a CSP representing the Sudoku board found in the text
    file named 'filename' in the current directory.

    Parameters
    ----------
    filename : str
        Filename of the Sudoku board to solve

    Returns
    -------
    Solver
        A Solver instance
    """
    solver = Solver()
    board = list(map(lambda x: x.strip(), open(filename, 'r')))

    for row in range(9):
        for col in range(9):
            if board[row][col] == '0':
                solver.add_variable('%d-%d' % (row, col), list(map(str,
                                                                   range(1, 10))))
            else:
                solver.add_variable('%d-%d' % (row, col), [board[row][col]])

    for row in range(9):
        solver.add_all_different_constraint(['%d-%d' % (row, col)
                                             for col in range(9)])
    for col in range(9):
        solver.add_all_different_constraint(['%d-%d' % (row, col)
                                             for row in range(9)])
    for box_row in range(3):
        for box_col in range(3):
            cells = []
            for row in range(box_row * 3, (box_row + 1) * 3):
                for col in range(box_col * 3, (box_col + 1) * 3):
                    cells.append('%d-%d' % (row, col))
            solver.add_all_different_constraint(cells)

    return solver


# -------------------------------------- function -----------------------------------------------------------------

def print_sudoku_solution(solution):
    """Convert the representation of a Sudoku solution as returned from
    the method CSP.backtracking_search(), into a human-readable
    representation.
    """
    for row in range(9):
        for col in range(9):
            print(solution['%d-%d' % (row, col)][0], end=" "),
            if col == 2 or col == 5:
                print('|', end=" "),
        print("")
        if row == 2 or row == 5:
            print('------+-------+------')
