import random


def generate_random_infeasible(m, n, max_coeff, max_bound_diff):
    # m x n matrix
    mat = [[None for j in range(n)] for i in range(m)]
    
    # rhs (size m)
    rhs = [None for i in range(m)]
    
    # bounds (size n)
    bounds = [None for j in range(n)]
    
    for i in range(m):
        
        if (i == m - 1): # last row
            # coefficients of last row are copied
            for j in range(n):
                mat[i][j] = mat[i - 1][j]
                
            # Right-hand side of last row, adding or subtracting 1 to ensure infeasibility 
            r = rhs[i - 1][0]
            eqtype = rhs[i - 1][1]
            
            if (eqtype == 'L' or eqtype == 'E'):
                rhs[i] = (r + 1, 'G')
            else:
                rhs[i] = (r - 1, 'L')
            
        
        else:
            for j in range(n):
                mat[i][j] = random.randint(-max_coeff, max_coeff)
                
            eqtype = random.choice(['L', 'G', 'E'])
            rhs[i] = (random.randint(-max_coeff, max_coeff), eqtype)
        
    for j in range(n):
        
        # old code
        # -----
        # l = random.randint(-max_coeff, max_coeff)
        # u = l + random.randint(0, max_bound_diff)
        # -----
        
        # new code
        # -----
        l = 0
        u = random.randint(0, max_bound_diff)
        # -----
        
        bounds[j] = (l, u)
        
    return("name", mat, rhs, bounds)
        
        
random.seed(0)

# Example

"""
m = 4 # number of equations
n = 3 # number of variables
max_coeff = 10
max_bound_diff = 10

(name, mat, rhs, bounds) = generate_random_infeasible(m, n, max_coeff, max_bound_diff)
"""


