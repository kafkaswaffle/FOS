"""
diffdiff
==================

"""


#############################################################################
#  Copyright (C) 2020                                                       #
#                Maximilian Jaroschek (maximilian@mjaroschek.com),          #
#                                                                           #
#  Distributed under the terms of the GNU General Public License (GPL)      #
#  either version 2, or (at your option) any later version                  #
#                                                                           #
#  http://www.gnu.org/licenses/                                             #
#############################################################################

from .config import *
from .tools import __parent_info,matrix_valuation
from .differential import _rational_solutions_diff,_polynomial_solutions_diff,_desingularize_diff

from ore_algebra.generalized_series import GeneralizedSeriesMonoid

from sage.matrix.constructor import matrix

def are_equivalent(M1,M2,systype=None):
    if systype==None: systype=systype_fallback()

    (M,MS,_,_,_,_)=__parent_info(M1)
    sols=rational_solutions(MS.one().tensor_product(M1)-M2.transpose().tensor_product(MS.one()),systype=systype)[0]
    if len(sols)>0:
        return True
    return False

def desingularize(M,l=None,systype=None):
    r"""
    Desingularize M completely or at a given pole.


    """
    if systype==None: systype=systype_fallback()

    if systype in systype_s:
        return _desingularize_shift(M,l)
    elif systype in systype_d:
        return _desingularize_diff(M,l)
    else: raise ValueError(systype_error_string)


def polynomial_solutions(M,rhs=None,logarithms=False,systype=None):
    r"""
    Computes a basis of the space of all polynomial solutions of a
    (non-)homogeneous system of difference or differential equations.

    Input:
        - M ... a matrix defining a first order system.
        - rhs ... (optional) the right hand side of the system of equations.
        - systype ... (optional) a string specifying whether the system is a
          system of differential or difference equations. Can be either 'shift'
          or 'diff'. The defualt value is set in the global variable
          'global_systype'.

    Output:
        - sols: A list of solutions of the homogeneous system of equations.
        - special: A solution of the inhomogeneous system of equations.

    """
    (_,_,_,_,K,var)=__parent_info(M)
    if systype==None: systype=systype_fallback()
    if systype in systype_d:
        if logarithms:
            basesols=_polynomial_solutions_diff(M,rhs)[0]
            logsols=[[i] for i in basesols]
            D=matrix([[var**(-min(1+matrix_valuation(M.rows()[i], var),0)) if i==j else 0 for i in range(M.nrows())] for j in range(M.nrows())])
            for i in logsols:
                #TODO: Vorzeichenfehler?
                newsol=_polynomial_solutions_diff(M,-D*i[-1]/var)[1]
                while newsol!=None:
                    i.append(newsol)
                    newsol=_polynomial_solutions_diff(M,-D*i[-1]/var)[1]
            mon=GeneralizedSeriesMonoid(K,var,'continuous')
            log=mon.tail_ring().gens()[0]
            for i in range(len(logsols)):
                deg=len(logsols[i])
                logsols[i]=sum([logsols[i][j]*log**(deg-j-1) for j in range(deg)])
            return basesols+logsols
        else:
            return _polynomial_solutions_diff(M,rhs)
    elif systype in systype_s:
        if logarithms:
            raise NotImplementedError
        else:
            return _polynomial_solutions_shift(M,rhs)
    else:
        raise ValueError(systype_error_string)
    

def rational_solutions(M,rhs=None,systype=None):
    if systype==None: systype=systype_fallback()

    if systype in systype_d:
        return _rational_solutions_diff(M,rhs)
    elif systype in systype_s:
        return _rational_solutions_shift(M,rhs)
    else: raise ValueError(systype_error_string)


