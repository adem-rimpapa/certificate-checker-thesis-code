"""
This script contains functions to convert linear programs into the MPS format.
"""

import os
import random


def dense_mat_to_mps(name, mat, rhs, bounds):
    """
    Takes a list of lists representing a matrix and a list containing the 
    right-hand sides of equations with the type of equation as input and prints 
    the LP in MPS format. (TODO proper comment)
    """
    
    m = len(mat) # number of equations
    n = len(mat[0]) # number of variables
    
    print('NAME'.ljust(10), end='')
    print(name)
    print('ROWS')
    print(' N  obj')
    
    for i in range(m):
        print(' {}  e{}'.format(rhs[i][1], i + 1))
    
    print('COLUMNS')
    
    for j in range(n):
        # print('    xx        obj                  0')
       
        print(4 * ' ', end = '')
        print(('x{}'.format(j)).ljust(10), end = '')
        print('obj'.ljust(21), end = '')
        print('0', end = '')
        print()
        
        for i in range(m):
            print(4 * ' ', end = '')
            print(('x{}'.format(j)).ljust(10), end = '')
            print(('e{}'.format(i + 1)).ljust(4), end = '')
            print(('{}'.format(mat[i][j])).rjust(18), end = '')
            print()
    
    print('RHS')
    
    for i in range(m):
        print(4 * ' ', end = '')
        print('rhs'.ljust(10), end = '')
        print(('e{}'.format(i + 1)).ljust(4), end = '')
        print(('{}'.format(rhs[i][0])).rjust(18), end = '')
        print()
        
    print('BOUNDS')
        
    for j in range(n):
        print(' LO bnd'.ljust(14), end='')
        print(('x{}'.format(j)).ljust(4), end = '')
        print(('{}'.format(bounds[j][0])).rjust(18), end = '')
        print()
        
    for j in range(n):
        print(' UP bnd'.ljust(14), end='')
        print(('x{}'.format(j)).ljust(4), end = '')
        print(('{}'.format(bounds[j][1])).rjust(18), end = '')
        print()
        
    print('ENDATA')

        
                
def dense_mat_to_mps_file(name, filename, mat, rhs, bounds):
    """
    Takes a list of lists representing a matrix and a list containing the 
    right-hand sides of equations with the type of equation as input and writes 
    the LP to a file in MPS format.
    """
    
    with open(filename, 'w') as f:
        m = len(mat) # number of equations
        n = len(mat[0]) # number of variables
        
        f.write('NAME'.ljust(10))
        f.write(name + '\n')
        f.write('ROWS\n')
        # f.write(' N  obj\n')
        
        for i in range(m):
            f.write(' {}  e{}\n'.format(rhs[i][1], i + 1))
        
        f.write('COLUMNS\n')
        
        for j in range(n):
            # print('    xx        obj                  0')
        
            """
            f.write(4 * ' ')
            f.write(('x{}'.format(j)).ljust(10))
            f.write('obj'.ljust(21))
            f.write('0')
            f.write('\n')
            """
            
            for i in range(m):
                f.write(4 * ' ')
                f.write(('x{}'.format(j)).ljust(10))
                f.write(('e{}'.format(i + 1)).ljust(4))
                f.write(('{}'.format(mat[i][j])).rjust(18))
                f.write('\n')
        
        f.write('RHS\n')
        
        for i in range(m):
            f.write(4 * ' ')
            f.write('rhs'.ljust(10))
            f.write(('e{}'.format(i + 1)).ljust(4))
            f.write(('{}'.format(rhs[i][0])).rjust(18))
            f.write('\n')
            
        f.write('BOUNDS\n')
            
        for j in range(n):
            f.write(' LO bnd'.ljust(14))
            f.write(('x{}'.format(j)).ljust(4))
            f.write(('{}'.format(bounds[j][0])).rjust(18))
            f.write('\n')
            
        for j in range(n):
            f.write(' UP bnd'.ljust(14))
            f.write(('x{}'.format(j)).ljust(4))
            f.write(('{}'.format(bounds[j][1])).rjust(18))
            f.write('\n')
            
        f.write('ENDATA\n')                        
                                
                                                
# Examples 

"""
name = 'new_example_1'

mat = [ \
    [3, -1, -2], \
    [1, -2, 1], \
    [2, 1, 1]]
    
rhs = [(1, 'L'), (-1, 'G'), (5, 'G')]

bounds = [(1, 3), (0, 2), (1, 4)]
    
# rhs = [(1, 'L'), (1, 'G'), (1, 'E')]                 
    
dense_mat_to_mps(name, mat, rhs, bounds)
print()
"""

"""
name = 'new_example_2'

mat = [ \
    [1, -1, 0.5, 2], \
    [1, -1, 0.5, 2]]
    
rhs = [(2, 'G'), (1, 'L')]

bounds = [(1, 4), (0, 2), (0, 3), (-1, 2)]                    
    
dense_mat_to_mps(name, mat, rhs, bounds)
"""


def parse_dimacs_file(filename):
    
    n = 0 # number of vertices
    m = 0 # number of edges/variables
    # idx = 1
    sources = {} # maps source node to amount of flow
    targets = {} # maps target node to amount of flow
    bounds = []
    coefficient_rows = []
    
    # The variables of the LP are set to be x0 to x(m - 1)
    # Accordingly, bounds and coefficient_rows both are indexed from 0 to m - 1 
    
    with open(filename) as f:
        lines = f.readlines()
    
        for line in lines:
            head = line[:1]
            tail = line[2:]
            
            if (head == 'c'):
                continue
            elif (head == 'p'):
                tokens = tail.split()
                n = int(tokens[1])
                m = int(tokens[2])
                
            elif (head == 'n'):
                tokens = tail.split()
                int_tokens = list(map(int, tokens))
                
                if int_tokens[1] > 0:
                    sources[int_tokens[0]] = int_tokens[1]
                else:
                    targets[int_tokens[0]] = int_tokens[1]
                
            elif (head == 'a'):
                tokens = tail.split()
                int_tokens = list(map(int, tokens))
                # print(int_tokens)
                
                # This implicitly lets coefficient_rows and bounds be indexed
                # from 0 to m - 1
                
                coefficient_rows.append((int_tokens[0], int_tokens[1]))
                bounds.append((int_tokens[2], int_tokens[3]))
    
    return(n, m, sources, targets, coefficient_rows, bounds)
    
    

def perturb_upper_bounds(bounds, max_diff):
    return [(lower, (max(lower, upper + round(random.uniform(-max_diff, max_diff), 3)))) \
        for (lower, upper) in bounds]   

 
    
def dimacs_file_to_mps_file(in_file, out_file, perturb_bounds=False, max_diff=0):
    (n, m, sources, targets, coefficient_rows, bounds) = parse_dimacs_file(in_file)
    
    if (perturb_bounds):
        bounds = perturb_upper_bounds(bounds, max_diff)
    
    with open(out_file, 'w') as f:
        f.write('NAME'.ljust(10))
        f.write('mps_file\n') # TODO replace
        f.write('ROWS\n')
        f.write(' N  obj\n')
        
        for v in range(1, n + 1):
            if (not v in targets):
                f.write(' E  e{}\n'.format(v))
            
        f.write('COLUMNS\n')
        
            
        for j in range(m):      
            """  
            f.write(4 * ' ')
            f.write(('x{}'.format(j)).ljust(10))
            f.write('obj'.ljust(21))
            f.write('0\n')
            """
            
            # !!! TODO is this correct? !!
            # Description in CLRS actually seems to have coefficient signs switched
            # for vertices which are not the source, but since the rhs is 0 in these
            # cases it shouldn't make a difference
            
            (row1, row2) = coefficient_rows[j]
            
            if (not row1 in targets):
                f.write(4 * ' ')
                f.write(('x{}'.format(j)).ljust(10))
                f.write(('e{}'.format(row1)).ljust(4))
                f.write(('{}\n'.format(1)).rjust(18))
            
            if (not row2 in targets):
                f.write(4 * ' ')
                f.write(('x{}'.format(j)).ljust(10))
                f.write(('e{}'.format(row2)).ljust(4))
                f.write(('{}\n'.format(-1)).rjust(18))
                
            
        f.write('RHS\n')
    
        for v in range(1, n + 1):
            if (v in sources):
                f.write(4 * ' ')
                f.write('rhs'.ljust(10))
                f.write(('e{}'.format(v)).ljust(4))
                f.write(('{}\n'.format(sources[v])).rjust(18))
            elif (not v in targets):
                f.write(4 * ' ')
                f.write('rhs'.ljust(10))
                f.write(('e{}'.format(v)).ljust(4))
                f.write(('{}\n'.format(0)).rjust(18))
            
        f.write('BOUNDS\n')
            
        for j in range(m):
            f.write(' LO bnd'.ljust(14))
            f.write(('x{}'.format(j)).ljust(4))
            f.write(('{}\n'.format(bounds[j][0])).rjust(18))
            
            f.write(' UP bnd'.ljust(14))
            f.write(('x{}'.format(j)).ljust(4))
            f.write(('{}\n'.format(bounds[j][1])).rjust(18))
            
        f.write('ENDATA\n')


"""
print(parse_dimacs_file('dimacs_example.txt'))

dimacs_file_to_mps_file('dimacs_example.txt', 'dimacs_example.mps')

dimacs_file_to_mps_file('gte_bad.20', 'gte_bad_20.mps')

dimacs_file_to_mps_file('big1.net', 'big1_net.mps')
"""


# Converting entries in gte_dataset
"""
print("Converting entries in gte_dataset:\n")

gte_dir = "../Datasets/gte_dataset"
gte_mps_dir = "../Datasets/gte_dataset_mps"

for f in os.listdir(gte_dir):
    if f.startswith("gte"):
        in_file = os.path.join(gte_dir, f)
        print("Converting {} to MPS".format(in_file))

        # Extract the filename
        filename_idx = in_file.rfind("/")
        filename = in_file[filename_idx + 1:]

        # Create the new filename
        dot_idx = filename.rfind(".")
        new_filename = "{}_{}.mps".format(filename[:dot_idx], filename[dot_idx + 1:])
        
        out_file = "{}/{}".format(gte_mps_dir, new_filename)
        print("Output file: {}".format(out_file))
        
        # Perform the conversion to MPS
        dimacs_file_to_mps_file(in_file, out_file)
        
        print()
"""



"""
# Converting entries in gte_dataset, adding random perturbations of at most 10000
random.seed(0)

print("Converting entries in gte_dataset and adding perturbations:\n")

gte_mod4_mps_dir = "../Datasets/gte_mod4_dataset_mps"

for f in os.listdir(gte_dir):
    if f.startswith("gte"):
        in_file = os.path.join(gte_dir, f)
        print("Converting {} to MPS and adding perturbations".format(in_file))

        # Extract the filename
        filename_idx = in_file.rfind("/")
        filename = in_file[filename_idx + 1:]

        # Create the new filename
        dot_idx = filename.rfind(".")
        new_filename = "{}_{}.mps".format(filename[:dot_idx], filename[dot_idx + 1:])
        
        out_file = "{}/{}".format(gte_mod4_mps_dir, new_filename)
        print("Output file: {}".format(out_file))
        
        # Perform the conversion to MPS with perturbation of at most 1000
        dimacs_file_to_mps_file(in_file, out_file, True, 10000)
        
        print()
"""

# --------
from infeasible_lp_generator import generate_random_infeasible

random.seed(0)

"""
print("Putting entries into infeasible1 dataset:\n")

infeasible1_mps_dir = "../Datasets/infeasible1_dataset_mps"

m = 30 # number of equations
n = 20 # number of variables
max_coeff = 10
max_bound_diff = 10

num_examples = 20

for i in range(1, num_examples + 1):
    (name, mat, rhs, bounds) = generate_random_infeasible(m, n, max_coeff, max_bound_diff)
    
    filename = "infeasible{}.mps".format(i)
    filepath = os.path.join(infeasible1_mps_dir, filename)
    print(filepath)
    dense_mat_to_mps_file(name, filepath, mat, rhs, bounds)
"""

print("Putting entries into infeasible2 dataset:\n")

infeasible2_mps_dir = "../Datasets/infeasible2_dataset_mps"

m = 20 # number of equations
n = 20 # number of variables
max_coeff = 10
max_bound_diff = 10

num_examples = 20

for i in range(1, num_examples + 1):
    (name, mat, rhs, bounds) = generate_random_infeasible(m, n, max_coeff, max_bound_diff)
    
    filename = "infeasible2_{}.mps".format(i)
    filepath = os.path.join(infeasible2_mps_dir, filename)
    print(filepath)
    dense_mat_to_mps_file(name, filepath, mat, rhs, bounds)
