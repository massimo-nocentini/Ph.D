

import matplotlib.pyplot as plt
import matplotlib.patches as patches

import math

from sympy import *

def colour_matrix(matrix, colors={0:'blue', 1:'orange'}):

    fig3 = plt.figure()
    ax3 = fig3.add_subplot(111, aspect='equal')

    radius = .6
    rows = matrix.rows
    coordinates = {}

    for r in range(rows):
        for c in range(r+1):
            coordinates[(r,c)] = (-r/2+c, -r)
            #coordinates.append((c, -r))

    for (mr,mc), co in coordinates.items():
        c, r = co
        #color = "orange" if c > -(-1)/2 else "blue"
        color = colors[matrix[mr, mc]]
        #a = .4 if r > -rows/2 else 1
        circle = patches.Circle(co, radius, facecolor=color, alpha=1, fill=True) 
                                #joinstyle='miter',fill=False,hatch='*')
        #if c is -3: circle.set_visible(False)
        ax3.add_patch(circle)

    ax3.set_xlim(-((rows+2*radius)/2),(rows+2*radius)/2)
    ax3.set_ylim(-rows,1)
    #ax3.set_autoscale_on(True)
    ax3.set_axis_off()
    return fig3
    
    #fig3.savefig('circles.svg', dpi=600)#, bbox_inches='tight')

def triangle_copy(source, target, point):
    pr, pc = point
    for r in range(source.rows):
        for c in range(r+1):
            target[pr + r, pc + c] = source[r,c]
            
def mirror_triangle(principal_cluster, point, mirror_segment):
    r, c = point
    for m in mirror_segment:
        for s in range(1, m+1):
            principal_cluster[r+(m-s), c-s] = principal_cluster[r+m, c+s]
            
def fill_odd_coeffs(principal_cluster, row, cols):
    principal_cluster[row, :cols] = ones(1, cols)    

def build_modular_catalan(principal_cluster, modulo=Integer(2)):
    d = Dummy()
    eq = Eq(modulo**d, principal_cluster.rows)
    sols = solve(eq, d)
    assert len(sols) is 1
    alpha = sols[0]
    
    end_of_principal_cluster = modulo**alpha
    next_alpha = modulo**(alpha + 1)
    next_pc = zeros(next_alpha, next_alpha)

    triangle_copy(principal_cluster, next_pc, (0,0))
    triangle_copy(principal_cluster, next_pc, 
                    (end_of_principal_cluster,end_of_principal_cluster))
    mirror_triangle(next_pc, (end_of_principal_cluster, end_of_principal_cluster-1), 
                    range(end_of_principal_cluster-1))
    fill_odd_coeffs(next_pc, next_alpha-1, end_of_principal_cluster)

    return next_pc
