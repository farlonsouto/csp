if __name__ == "__main__":
    print("Entry point. Not expect to run as a module.")

from Solver import *

solver = create_sudoku_csp("easy.txt")
solver.backtracking_search()
