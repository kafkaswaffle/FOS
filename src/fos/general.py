"""
general
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

from .tools import __parent_info,matrix_valuation,padic_expansion,__lift
from .config import *

from sage.modules.free_module_element import vector
from sage.matrix.constructor import matrix
from sage.structure.element import Matrix
from sage.matrix.special import companion_matrix,block_matrix
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.semirings.non_negative_integer_semiring import NN
from functools import reduce
from sage.calculus.functional import diff

def _bounded_polynomial_solutions(M,degbound,N=None,systype=None):

    (M,_,F,R,K,var)=__parent_info(M)

    if N==None:
        N=VectorSpace(F,M.ncols()).zero()
    if isinstance(N,Matrix):
        if N.ncols()>1:
            raise ValueError("N has to be a vector")
        N=VectorSpace(F,M.ncols())(N.columns()[0])

    if systype==None: systype=systype_fallback()

    op=operator(M,systype=systype)

    # Case: Degree bound is zero:
    if degbound<=0:
        return ([],None)
    
    # Set up the equations and clear denominators
    eqs=block_matrix(1,degbound,[op(var**i) for i in range(degbound-1,-1,-1)])
    den=N.denominator().lcm(eqs.denominator())
    N=den*N

    eqs=block_matrix(1,2,[den*eqs,matrix(-N).transpose()])
    eqs=eqs.parent().change_ring(R)(eqs)
    sol=[]
    special=None

    size=M.ncols()
    EQSdeg=max(sum([[R(i).degree() for i in j] for j in eqs],[]))+1
    eqs2=[[0 for j in range(eqs.ncols())] for i in range(eqs.nrows()*EQSdeg)]

    for i in range(eqs.nrows()*EQSdeg):
        (row,coeff)=NN(i).quo_rem(EQSdeg)
        for j in range(eqs.ncols()):
            eqs2[i][j]=eqs[row][j][coeff]

    sol=matrix(eqs2).right_kernel().basis()
    polysol=[]

    # Compute the solutions as vectors with entries in Q, compress them to
    # vectors with polynomial entries
    for i in sol:
        v=i[:-1]
        l=[0 for j in range(M.ncols())]
        for j in range(M.ncols()):
            for h in range(degbound):
                l[j]=l[j]+var**(degbound-h-1)*v[h*M.ncols()+j]

        # If the last entry is non-zero, and not all other entries are zero, it
        # is a solution to the inhomogeneous system
        if reduce((lambda x,y:y==0 and x),v,True): continue
        if i[-1]!=0:
            if special!=None:
                polysol.append(special-vector(l)/i[-1])
            else:
                special=vector(l)/i[-1]
        else:
            polysol.append(vector(l))
    return (polysol,special)


#TODO: Change to deterministic algorithm
def _cyclic_vector(M,d,j,k,addDiag,systype=None):
    r"""
    Computes a cyclic vector for a given first order system.

    Input:
        - M ... a matrix defining a first order system.
        - d ... the min. degree of the components of the output vector.
        - j ... the min. number of components of the output vector that could
          potentially be non-zero.
        - k ... the number of tries to find a cyclic vector. If k=0, then a
          MonteCarloExcpetion is raised.
        - addDiag ... A modifier that specifies if the output transformation
          should be of the form (a) or (b). See the specification of the output
          for more information.
        - systype ... (optional) a string specifying whether the system is a
          system of differential or difference equations. Can be either 'shift'
          or 'diff'. The defualt value is set in the global variable
          'global_systype'.

    Output:
        - c ... a cyclic vector for the given system.
        - T ... a matrix with columns T_i such that:
            (a) if addDiag is False, T_i is the vector \partial^i*c, where
                \partial is the pseudo-linear map associated to the input system
            (b) if addDiag is true, then T_0 is c, and T_i (i>1)
                is the vector \partial^i*c + T_{i-1}

   Algorithm:
        - naive

    """
    if systype==None: systype=systype_fallback()

    (M,MS,_,R,_,var)=__parent_info(M)

    while k>0:
        v=vector([R.random_element(d) if i <j else R.zero() for i in range(M.nrows())])
        A=[v]
        op=operator(M,systype=systype)
        for i in range(1,M.nrows()):
            if addDiag:
                A.append(op(A[-1])+A[-1])
            else:
                A.append(op(A[-1]))
        A=MS(A)
        if A.rank()==A.nrows():
            return (v,A.transpose())
        else:
            if j==M.nrows():
                d=d+1
            j=(j+1)%(M.nrows()+1)
            k=k-1
    raise MonteCarloException("Could not find a cyclic vector.")


def adjoint(M,systype=None):
    if systype==None: systype=systype_fallback()

    if systype in systype_d:
        return M.transpose()
    elif systype in systype_s:
        var=M.parent().base_ring().gens()[0]
        return M.subs({var:var-1}).transpose()
    else: raise ValueError(systype_error_string)


def annihilating_system(r,systype=None):
    r"""
    Computes an annihilating first order system for a rational function.

    Input:
        - r ... A rational function in one variable.
        - systype ... (optional) a string specifying whether the system is a
          system of differential or difference equations. Can be either 'shift'
          or 'diff'. The defualt value is set in the global variable
          'global_systype'.

    Output:
        - A matrix of differential or difference type whose associtated pseudo
          linear operator annihilates r.

    EXAMPLES:

        sage: L.<x>=PolynomialRing(QQ)
        sage: d=randint(1,100)
        sage: n=randint(1,100)
        sage: p=L.random_element(d,n)
        sage: Md=annihilating_system(p,systype='d')
        sage: Ms=annihilating_system(p,systype='s')
        sage: operator(Md,systype='d')(p)==0
        True
        sage: operator(Ms,systype='s')(p)==0
        True
        sage: p=L.zero()
        sage: Md=annihilating_system(p,systype='d')
        sage: Ms=annihilating_system(p,systype='s')
        sage: operator(Md,systype='d')(p)==0
        True
        sage: operator(Ms,systype='s')(p)==0
        True

    Algorithm:
        - naive
    """
    if systype==None: systype=systype_fallback()

    var=r.parent().gens()[0]
    if r==0: return matrix([[r.parent().one()]])
    if systype in systype_s:
        return matrix([[r.subs({var:var+1})/r]])
    elif systype in systype_d:
        return matrix([[diff(r,var)/r]])
    else: raise ValueError(systype_error_string)


# TODO: k for difference
def apply_transformation(M,T,k=0,systype=None):
    r"""
    Applies a basis transformation to a first order system given by
    x^k*D(Y)=M*Y, where D is the differential or the shift operator.

    Input:
        - T ... a matrix defining a basis transformation.
        - M ... a matrix defining a first order system.
        - k ... (optional) a non-negative integer. Default is 0.
        - systype ... (optional) a string specifying whether the system is a
          system of differential or difference equations. Can be either 'shift'
          or 'diff'. The defualt value is set in the global variable
          'global_systype'.

    Output:
        - The defining matrix of the transformed system.

    EXAMPLES:
        sage: L.<x>=PolynomialRing(QQ)
        sage: MS=MatrixSpace(L,2)
        sage: M=MS([[2*x,x+1],[3,0]])
        sage: T=shearing_transformation(MS,2)
        sage: apply_transformation(M,T,'d')
        [(2*x^2 - 1)/x         x + 1]
        [            3          -1/x]
        sage: apply_transformation(M,T,'s')
        [2*x^2/(x + 1)             x]
        [  3*x/(x + 1)             0]
        sage: apply_transformation(M,MS.one(),'d')==M
        True
        sage: apply_transformation(M,MS.one(),'s')==M
        True

    Algorithm:
        - naive

    """
    if systype==None: systype=systype_fallback()
    var=M.parent().base_ring().gens()[0]
    
    if systype in systype_s:
        if k==0:
            return T.inverse().subs({var:var+1})*M*T
        return T.inverse().subs({var:var+1})*(M*T-T.subs({var:var+1})+T)
    elif systype in systype_as:
        return T.inverse().substitute({var:var-1})*M*T
    elif systype in systype_d:
        return T.inverse()*(M*T-var**k*T.parent()(diff(T)))
    elif systype in systype_ad:
        return T.inverse()*(M*T+var**k*T.parent()(diff(T)))
    else: raise ValueError(systype_error_string)


def companion_form(M,systype=None):
    r"""
    Brings a first order system into a companion form

    Input:
        - M ... a matrix defining a first order system.
        - systype ... (optional) a string specifying whether the system is a
          system of differential or difference equations. Can be either 'shift'
          or 'diff'. The defualt value is set in the global variable
          'global_systype'.

    Output:
        - T ... a transformation that transform M into the output matrix MT
        - MT ... a matrix in companion form equivalent to M.

    EXAMPLES:
        sage: L.<x>=PolynomialRing(QQ)
        sage: MS=MatrixSpace(L,3)
        sage: M=MS.random_element(2)
        sage: CM=companion_form(M,'d')
        sage: CM[1].rows()[0]==vector([L.zero(),L.one(),L.zero()])
        True
        sage: CM[1].rows()[1]==vector([L.zero(),L.zero(),L.one()])
        True
        sage: apply_transformation(M,CM[0],'d')==CM[1]
        True
        sage: CM=companion_form(M,'s')
        sage: CM[1].rows()[0]==vector([L.zero(),L.one(),L.zero()])
        True
        sage: CM[1].rows()[1]==vector([L.zero(),L.zero(),L.one()])
        True
        sage: apply_transformation(M,CM[0],'s')==CM[1]
        True
        sage: M=matrix([L.one()])
        sage: CM=companion_form(M,'d')
        sage: CM[1]==M
        True
        sage: apply_transformation(M,CM[0],'d')==CM[1]
        True
        sage: CM=companion_form(M,'s')
        sage: CM[1]==M
        True
        sage: apply_transformation(M,CM[0],'s')==CM[1]
        True

    Algorithm:
        - cyclic vector method
    """
    if systype==None: systype=systype_fallback()

    if systype in systype_s:
        addDiag=True
        sysad=systype_as[0]
    else:
        addDiag=False
        sysad=systype_ad[0]
    dM=adjoint(M,systype)
    T=cyclic_vector(dM,addDiag,systype=sysad)[1].transpose().inverse()
    return (T,apply_transformation(M,T,systype=systype))


def cyclic_vector(M,addDiag=False,systype=None):
    r"""
    Computes a cyclic vector for a given first order system. Acts as a wrapper
    for _cyclic_vector(M,systype,d,j,k).

    Input:
        - M ... a matrix defining a first order system.
        - addDiag ... (optional)A modifier that specifies if the output transformation
          should be of the form (a) or (b). See the specification of the output
          for more information.
        - systype ... (optional) a string specifying whether the system is a
          system of differential or difference equations. Can be either 'shift'
          or 'diff'. The defualt value is set in the global variable
          'global_systype'.

    Output:
        - c ... a cyclic vector for the given system.
        - T ... a matrix with columns T_i such that:
            (a) if addDiag is False, T_i is the vector \partial^i*c, where
                \partial is the pseudo-linear map associated to the input system
            (b) if addDiag is true, then T_0 is c, and T_i (i>1)
                is the vector \partial^i*c + T_{i-1}

    Algorithm:
        - see _cyclic_vector
    """
    return _cyclic_vector(M,0,0,20,addDiag,systype)


#TODO: Difference version
def indicial_matrix(M,p,systype=None):
    if systype==None: systype=systype_fallback()
    
    (M,MS,F,R,_,var)=__parent_info(M)

    if systype in systype_d:
        D=matrix([[var**(-min(1+matrix_valuation(M.rows()[i], p),0)) if i==j else 0 for i in range(M.nrows())] for j in range(M.nrows())])
        A=(p/diff(p,var)*D*M)
    elif systype in systype_s:
        #TODO: THis is just tested at infinity, so for indicial_matrix(M(-1/x),x)
        if p!=var:
            raise NotImplementedError
        A=1/var*(M-MS.one())
        D=matrix([[var**(-min(matrix_valuation(A.rows()[i], p),0)) if i==j else 0 for i in range(A.nrows())] for j in range(A.nrows())])
        A=D*A
    else:
        raise ValueError(systype_error_string)
    
    A0=padic_expansion(A,p,1)
    D0=padic_expansion(D,p,1)
    A0=__lift(A0[1][0]) if A0[0]==0 else A.parent().zero()
    D0=__lift(D0[1][0]) if D0[0]==0 else D.parent().zero()
    R2=PolynomialRing(R,[repr(var)+'0'])
    var2=R2.gens()[0]
    MS=A0.parent().change_ring(R2)
    A0=MS(A0)
    D0=MS(D0)
    var2=R2.gens()[0]
    return A0-var2*D0

#TODO: Shift system
def infinity_to_zero(M,systype=None):
    r"""
    Performs the substitution x->1/x to move the point at infinity to zero.

    Input:
        - M ... a matrix defining a first order system.
        - systype ... (optional) a string specifying whether the system is a
          system of differential or difference equations. Can be either 'shift'
          or 'diff'. The defualt value is set in the global variable
          'global_systype'.

    """
    if systype==None: systype=systype_fallback()

    if systype in systype_d:
        var=M.parent().base_ring().gens()[0]
        return -1/var**2*M.subs({var:1/var})
    elif systype in systype_s:
        raise NotImplementedError
    else: raise ValueError(systype_error_string)


def is_valid_system(M,checkRank=True):
    r"""
    Checks if a sage object defines a first order system that admits the
    necessary properties for the algorithms provided in the FOS package.

    Input:
        - M ... a sage object.
        - checkRank ... (optional) if 'true', a check is performed if M is
          non-singular.

    Output:

        - b ... a Boolean value. 'True' if the input object is a (non-singular)
          square matrix with entries in (the fraction field of) a polynomial
          ring over a field of characteristic zero. 'False' otherwise
        - msg ... if b is 'False' msg contains a reasoning on why the matrix is
          not valid

    """
    MS=M.parent()
    if not isinstance(MS,MatrixSpace):
        return (False, "Parent of input system must be a matrix space.")
    if not M.is_square():
        return (False, "Input matrix has to be square.")
    R=MS.base_ring()
    if R.is_field(): R=R.base()
    if not isinstance(R, PolynomialRing_general):
        return (False, "Ground ring must be a polynomial ring or a rational function field.")
    if not len(R.gens())==1:
        return (False, "Ground ring must be univariate.")
    K=R.base()
    if not QQ<=K:
        return (False, "Constant field has to be an extension of the rational numbers.")
    if checkRank:
        if not M.rank()==M.nrows():
            return (False, "Input matrix has to be non-singular.")
    return (True,"")


# TODO: k for difference
def operator(M,k=0,systype=None):
    if systype==None: systype=systype_fallback()
    var=M.parent().base_ring().gens()[0]
    if systype in systype_s:
        return lambda x: (M*x -x.subs({var:var+1})).subs({var:var-1})
    elif systype in systype_as:
        return lambda x: (M*x -x.subs({var:var-1})).subs({var:var+1})
    elif systype in systype_d:
        return lambda x: M*x - var**k*diff(x,var)
    elif systype in systype_ad:
        return lambda x: M*x + var**k*diff(x,var)
    else: raise ValueError(systype_error_string)



def ramification(M,r,systype=None):
    if systype==None: systype=systype_fallback()

    if systype in systype_d:
        (_,_,_,_,var)
        return r*M.subs({var:var**r})
    elif systype in systype_s:
        raise NotImplementedError
    else: raise ValueError(systype_error_string)


def rational_form(M,systype=None):
    raise NotImplementedError
    # if systype==None: systype=systype_fallback()

    # (M,MS,F,R,K,var)=__parent_info(M)
    # val=-matrix_valuation(M,var)

    # # Bring the leading matrix of M in rational form
    # M0=__cast_to_base(__lift(lcmatrix(M,var)))
    # M0=M0.rational_form(format='bottom')
    # # TODO: This is a workaround used because rational_form does not return the
    # # transformation.
    # T=MS.zero()
    # transformations=__solve_sylvester_rat(M0,-M0,M0.parent().zero())[0]
    # while det(T)==0:
    #     T=MS(sum([K.random_element()*i for i in transformations]))
    # M=apply_transformation(M,T,systype=systype)
    
    # # TODO: Start here
    # (Tb,M)=_block_decomposition(M,M0,2)
    # return M

    
    # block=0
    # divs=M0r.subdivisions()
    # M.subdivide(divs)
    # (i,j)=(divs[0][-1],divs[1][-1])
    # n=M.nrows()-i
    # #Lemma 2.
    # for k in range(i,M.nrows()-1):
    #     Tb=shearing_transformation(M.parent(),1,start=n+k-1,p=M[k][k+1]**(-1))
    #     M=apply_transformation(M,Tb,systype)
    #     Tb=[[1 if s==r else 0 for s in range(M.nrows())] for r in range(M.nrows())]
    #     for l in range(M.ncols()):
    #         if l!=k+1:
    #             Tb[k+1][l]=-M[k][l]
    #     Tb=matrix(Tb)
    #     M=apply_transformation(M,Tb,systype)
    # return M
    # for k in range(M.ncols()-1,i,-1):
    #         for l in range(i):
    #             Tb=[[1 if s==r else 0 for s in range(M.nrows())] for r in range(M.nrows())]
    #             Tb[l][k-1]=M[l][k]
    #             Tb=matrix(Tb)
    #             M=apply_transformation(M,Tb,systype)
    # #Lemma 3
    # U=M.submatrix(M.nrows()-n,0,n,M.ncols()-n)
    # V=M.submatrix(0,M.ncols()-n,M.nrows()-n,M.ncols()-n)
    # print M
    # if U!=0:
    #     m=-matrix_valuation(U,x)
    #     Tb=shearing_transformation(M.parent(),n,start=M.nrows()-n+1,p=var**(val-m))
    #     M=apply_transformation(M,Tb,systype)
    #     return M


def shearing_transformation(MS,length,start=1,p=None):
    r"""
    Constructs a diagonal matrix of the form diag(1,...,1,p,...,p,1...,1) where
    p is a polynomial.

    Input:
        - MS ... a MatrixSpace over a univariate polynomial ring.
        - length ... the number of entries in the diagonal that equal p.
        - start ... (optional) the index of the first diagonal entry equal to
          p. First position has index 1, which is also the default value.
        - p ... (optional) a univariate polynomial. If not specified, p is set
          to the first generator of the ground ring of MS.

    EXAMPLES:
        sage: L.<x>=PolynomialRing(QQ)
        sage: MS=MatrixSpace(L,3)
        sage: shearing_transformation(MS,2,2,x-1)
        [    1     0     0]
        [    0 x - 1     0]
        [    0     0 x - 1]
        sage: shearing_transformation(MS,0,2,x-1)
        [1 0 0]
        [0 1 0]
        [0 0 1]

    """
    start=start-1
    length=length-1
    if p==None:
        p=MS.base_ring().gens()[0]
    return MS([[0 if i!=j else (p if (i>=start and i-start<=length) else 1) for j in range(MS.nrows())] for i in range(MS.nrows())])


def to_first_order_system(p):
    r"""
    Compute a first order system corresponding to an Ore operator.

    Input:
        - p ... an Ore operator.

    Output:
        - The transposed companion matrix of p.
    """
    return companion_matrix(p.monic()).transpose()


# TODO: Zürcher.
def to_scalar_operator(M,systype=None):
    r"""
    Computes a scalar operator corresponding to a given first order system.

    Input:

        - M ... a matrix defining a first order system.
        - systype ... (optional) a string specifying whether the system is a
          system of differential or difference equations. Can be either 'shift'
          or 'diff'. The defualt value is set in the global variable
          'global_systype'. Alternatively, it can be either a shift or a
          differential Ore algebra.

    Output:

        - An Ore operator whose transposed companion matrix is equivalent to the
          input matrix.
        - The transformation used to bring the system into companion form.

    """
    if systype==None: systype=systype_fallback()

    if isinstance(systype,str):
        from ore_algebra import OreAlgebra
        R=M.parent().base_ring()
        if systype in systype_d:
            pre='D'
        elif systype in systype_s:
            pre='S'
        else:
            raise ValueError(systype_error_string)
        var=pre+repr(R.gens()[0])
        ore=OreAlgebra(R,var)
    else:
        ore=systype

    K=M.parent().base_ring()
    if ore.is_D()==K.gens()[0] or ore.is_S()==K.gens()[0]:
        (T,dM)=companion_form(M,systype)
        l=dM.rows()[-1]
        D=ore.gen()
        return (sum([l[i]*D**i for i in range(len(l))])-D**len(l),T)
    else: raise ValueError("Ore Algebra has to be differential or shift.")



class MonteCarloException(Exception):
    r"""
    An error class indicating that a monte carlo algorithm was not able to
    return a valid result.

    """
    def __init__(self, message):
        super(MonteCarloException, self).__init__(message)

