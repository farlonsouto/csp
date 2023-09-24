if __name__ == "__main__":
    print("Entry point. Not expect to run as a module.")

from Solver import *


solver = create_map_coloring_csp()
map_solution = solver.backtracking_search()
print(map_solution)
