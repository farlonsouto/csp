if __name__ == "__main__":
    print("Entry point. Not expect to run as a module.")

from Solver import *
import time

solver = create_map_coloring_csp()
solution = solver.backtracking_search()
print(solution)

fileNames = ["easy.txt", "medium.txt", "hard.txt", "veryhard.txt"]
for sudokuInput in fileNames:
    solver = create_sudoku_csp(sudokuInput)
    start = time.time()
    print_sudoku_solution(solver.backtracking_search())
    end = time.time()
    print("File name {}. Backtracking calls: {}. Failures: {}. Time {} seconds"
          .format(sudokuInput, solver.numCalls, solver.numFailures, end - start))
