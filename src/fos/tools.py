"""
tools
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

from sage.structure.element import Matrix
from sage.modules.free_module_element import FreeModuleElement
from sage.rings.infinity import Infinity
from sage.matrix.constructor import matrix
from sage.matrix.matrix_space import MatrixSpace

def __bit_count(M):
    r"""
    Estimates the bit size of a first order system.

    Input:
        - M ... a matrix defining a first order system.

    Output:
        - An estimate of the bit size of M.

    Algorithm:
        - Counting bit sizes of all number coefficients.

    """
    total=0
    (M,_,_,R,_,_)=__parent_info(M)
    for i in M.rows():
        for j in i:
            # Get bit size of numerator
            for k in R(j.numerator()).coefficients():
                total=total+ceil(log(abs(k.numerator()),2))
                if abs(k.denominator())!=1:
                    total=total+ceil(log(abs(k.denominator()),2))
            # Get bit size of denominator
            for k in R(j.denominator()).coefficients():
                if k!=1:
                    total=total+ceil(log(abs(k.numerator()),2))
                    if abs(k.denominator())!=1:
                        total=total+ceil(log(abs(k.denominator()),2))
    return total


def __bit_count_op(p):
    r"""
    Estimates the bit size of an Ore operator.

    Input:
        - p ... an Ore operator.

    Output:
        - An estimate of the bit size of p.

    Algorithm:
        - Counting bit sizes of all number coefficients.

    """
    total=0
    p=p.numerator()
    R=p.parent().base_ring()
    if R.is_field(): R=R.base()
    for i in p.coefficients():
        for j in R(i).coefficients():
            # Get bit size of numerator
            total=total+ceil(log(abs(j.numerator()),2))
            # Get bit size of denominator
            if abs(j.denominator())!=1:
                total=total+ceil(log(abs(j.denominator()),2))
    return total


#TODO: Add a parementer to reduce to block diagonal form. Use this in exponential_part
#TODO: Obsolete?
def __column_reduced_form(M,k):
    r"""
    Performs column reduction on the last k columns of a polynomial
    matrix. Column reduction is a similarity transformation such that the
    specific columns in the transformed matrix span the same space as the
    columns in the original matrix, but they contain the maximal possible number
    of zero columns which all have higher indicies than the non-zero columns.

    Input:
        - M ... a matrix with polynomial entries.
        - k ... a non-negative integer less than or equal to the number of
          columns in M.

    Output:
        - A matrix similar to M whose last #cols-k columns are column reduced.

    Algorithm:
        - naive via smith form computation
    """
    B=M.submatrix(0,k,M.nrows(),M.ncols()-k)
    T=B.smith_form()[2]
    c=[]
    for i in range(M.nrows()):
        if i<k:
            c.append([1 if i==j else 0 for j in range(M.ncols())])
        else:
            row=T.rows()[i-k]
            c.append([(1 if i==j else 0) if j<k else row[j-k] for j in range(M.ncols())])
    return M.parent()(c)


def __cast_to_base(M):
    r"""
    Changes the parent of a matrix or vector whose parent allows entries from a
    polynomial ring or its fraction field, but all entries actually live in the
    base ring. The new parent of M will be a matrix/vector space over the base
    ring.

    Input:
        - A matrix or vector with entries in the base ring of the entries'
          parent.
    
    Output:
        - The same matrix or vector as was given as input, but the parent is
          changed to a matrix/vector space over the base ring of the original
          entries' parent.

    Algorithm:
        - None.

    """
    if isinstance(M,Matrix):
        base=M.parent().base_ring().base_ring()
        return matrix([[base(j) for j in i] for i in M.rows()])
    elif isinstance(M,FreeModuleElement):
        base=M.parent().base_ring().base_ring()
        return vector([QQ(i) for i in M])
    else:
        base=M.parent().base_ring()
        return base(M)
    

def __lift(M):
    r"""
    Lifts all entries of a matrix or vector from a quotient ring to the ambient
    ring.

    Input:
        - M ... a matrix or vector with entries in a quotient ring.

    Output:
        - A matrix/vector whose entries are the entries of M lifted to the
          ambient ring of their parent ring.

    Algorithm:
        - None.

    EXAMPLES:
        sage: L.<x>=PolynomialRing(QQ)
        sage: I=L.ideal(x^2+1)
        sage: F=L.quotient(I)
        sage: M=matrix([[F(x),F(1)],[F(x+1),F(0)]])
        sage: __lift(M).parent().base_ring()==L
        True
        sage: M=vector([F(0),F(0)])
        sage: __lift(M).parent().base_ring()==L
        True

    """
    if isinstance(M,Matrix):
        return matrix([[i.lift() for i in j] for j in M])
    elif isinstance(M,FreeModuleElement):
        return vector([i.lift() for i in M])
    else:
        return M.lift()


def __mod(M,p):
    r"""
    Reduces all entries of a matrix or vector modulo an irreducible polynomial.

    Input:
        - M ... a matrix or vector with rational function entries.
        - p ... an irreducible polynomial.

    Output:
        - A matrix whose entries are the entries of M modulo p.

    Algorithm:
        - Division with remainder and modular inverses.

    EXAMPLES:
        sage: L.<x>=PolynomialRing(QQ)
        sage: p=x^2+1
        sage: M=matrix([[x^3,0],[x^2+2*x+1,p*x]])
        sage: Mmod=__mod(M,p)
        sage: Mmod
        [ -xbar      0]
        [2*xbar      0]
        sage: reduce(lambda x,y: (x and y ), sum([[M[i][j]%p==Mmod[i][j] for j in range(M.ncols())] for i in range(M.nrows())],[]))
        True

    """

    R=p.parent()
    if R.is_field():
        R=R.base()
        p=R(p)
    R=p.parent().quotient(p)
    if isinstance(M,Matrix):
        MS=M.parent().change_ring(R)
        return MS([[((j.numerator()%p)*(R(j.denominator())**(-1)).lift())%p for j in i] for i in M])
    elif isinstance(M,FreeModuleElement):
        MS=M.parent().change_ring(R)
        return MS([((i.numerator()%p)*(R(i.denominator())**(-1)).lift())%p for i in M])
    else:
        return R(((M.numerator()%p)*(R(M.denominator())**(-1)).lift())%p)


def __parent_info(M,adjust=True):
    r"""
    Extracts the relevant information about the space a matrix lives in.

    Input: 
        - M ... a matrix with entries in a rational function field in one
          variable.

    Output:
        - The same matrix as M, but its entries are now elements of the fraction
          field of their original parent (if the original parent is not already
          a field)
        - The MatrixSpace object M lives in.
        - The rational function field the entries of M live in.
        - The unpolynomial ring that forms the rational function field.
        - The ground ring/field of the polynomial ring.
        - The variable in the polynomial ring.

    Algorithm:
        - None.

    """
    MS=M.parent()
    F=MS.base_ring()
    if F.is_field():
        R=F.base()
    else:
        R=F
        F=R.fraction_field()
        MS=MS.change_ring(F)
    var=R.gens()[0]
    return (MS(M),MS,F,R,R.base_ring(),var)


# Algorithm: Bartels, Stewart
# TODO: Doesn't work with Matlab example at
# https://www.mathworks.com/help/matlab/ref/sylvester.html
# TODO: Obsolete?
def __solve_sylvester(A,B,C):
    A=A.parent().change_ring(CDF)(A)
    B=B.parent().change_ring(CDF)(B)
    n=A.nrows()
    m=B.nrows()
    (U,R)=A.schur()
    (V,S)=B.schur()
    Rs=conjugate(R).transpose()
    Y=[]
    for i in range(n):
        v=[]
        Y.append(v)
        for j in range(m):
            v.append(
                (C[i][j]-sum([Rs[i][k]*Y[k][j] for k in range(i)]) - sum([S[k][j]*Y[i][k] for k in range(j)]))/(Rs[i][i]+S[j][j])
            )
    Y=matrix(Y)
    return U*Y*conjugate(V).transpose()

def __solve_sylvester_rat(A,B,C):
    r"""
    Computes, if possible, a solution in X for the Sylvester equation A*X+X*B=C,
    without extending the underlying base field.

    Input:
        - A ... A matrix of size N x M.
        - B ... A matrix of size M x K.
        - C ... A matrix of size N x K.

    Output:
        - A generating set of the kernel of the map AX+XB.
        - A solution of AX+XB=C

    Algorithm:
        - Linear system solving.

    """
    
    # Compute matrix of the map AX+XB
    MS=MatrixSpace(A.parent().base(),A.ncols(),B.nrows())
    e=MS.basis()
    h=lambda x: A*x+x*B
    l=[h(i).list() for i in e]
    # Add -C as a column to get solutions for the inhomogenuous system
    l.append((-C).list())
    S=matrix(l).transpose()
    null=[]
    special=None
    ncols=B.ncols()
    nrows=A.nrows()
    # Solve the system and translate solutions back into matrices. Distinguish
    # between solutions of the inhomogenuous and the homogenuous equation
    for i in S.right_kernel().basis():
        if i[-1]!=0:
            l=i*i[-1]**(-1)
            M=[]
            for j in range(nrows):
                M.append([])
                for k in range(ncols):
                    M[j].append(l[j*ncols+k])
            if special==None:
                special=matrix(M)
            else:
                null.append(matrix(M)-special)
        else:
            l=i
            M=[]
            for j in range(nrows):
                M.append([])
                for k in range(ncols):
                    M[j].append(l[j*ncols+k])
            null.append(matrix(M))
    return (null,special)


def matrix_valuation(M,p):
    r"""
    Computes the order of an irreducible polynomial in a matrix or vector.

    Input:
        - M ... a matrix or vector with rational function entries.
        - p ... an irreducible polynomial.

    Output:
        - The minimum of all orders of p in the entries of M.

    Algorithm:
        - Built-in .valuation method.

    EXAMPLES:
        sage: L.<x>=PolynomialRing(QQ)
        sage: matrix_valuation(matrix([1/x,1/x^2,x^3]),x)
        -2
        sage: matrix_valuation(matrix([L.zero()]),x)
        +Infinity

    """
    if isinstance(M,Matrix):
        return min([min([i.valuation(p) for i in j]) for j in M])
    elif isinstance(M,FreeModuleElement):
        return min([i.valuation(p) for i in M])
    else:
        return M.valuation(p)


def SN_decomposition(M):
    r"""
    Decomposes a matrix M two blocks, one non-singular and the other one
    nilpotent.

    Input:
        - M ... a square matrix with entries in a field

    Output: 
        - A transformation such that T^(-1)*M*T=B, where B is similar to M and
          has the block structure as described above.
        - The non-singular block of B, where B is as above. None if M is
          nilpotent.
        - The nilpotent block of B, where B is as above. None if M is
          non-singular.

    Algorithm:
        - Computing the kernel and column space basis of M^n, where n is the
          order of M.

    """
    # Compute column space basis of M^n.
    Mn=M**M.nrows()
    basis=Mn.column_space().basis()
    n=len(basis)
    # Case: M is not nilpotent and not non-singular.
    if n>0 and n<Mn.nrows():
        # Compute the kernel of M^n and construct transformation.
        T=matrix(basis + Mn.right_kernel().basis()).transpose()
        M=T.inverse()*M*T
        M.subdivide((n,n))
        return (T,M.subdivision(0,0),M.subdivision(1,1))
    # Case: M is non-singular
    if n>0:
        return (M.parent().one(),M,None)
    # Case: M is nilpotent.
    return (M.parent().one(),None,M)


def eigenvalue_splitting_rat(M):
    r"""
    Transforms a matrix M into block diagonal form, where the eigenvalues of a
    block are the roots of an irreducible factor of the characteristic polynomial
    of M.

    Input:
        - M ... a square matrix with entries in a field

    Output: 
        - A transformation such that T^(-1)*M*T=B, where B is as below.
        - A matrix B similar to M with the block structure as described above.

    Algorithm:
        - Computing kernels and column space bases of the matrices f(M), where f
          are (powers of) irreducible factors of the characteristic polynomial
          of M.

    """
    F=M.parent()
    c=M.charpoly()
    # Compute the factors of the characteristic polynomial
    c=[i for i in c.factor() if c.parent()(i[0]).degree()>0]
    # Case: There is more than one non-trivial factor
    if len(c)>1:
        # Compute the column space of f^m(M), where f is an irred. factor of the
        # charpoly with multiplicity m.
        (f,m)=c[-1]
        Mf=(f**m)(M)
        basis=Mf.column_space().basis()
        n=len(basis)
        # Case: f^m(M) is not zero.
        if n>0:
            # Compute the right kernel of f^m(M) and assemble the
            # transformation to get a block corresponding to f^m.
            T=matrix(basis + Mf.right_kernel().basis()).transpose()
            M=T.inverse()*M*T
            M.subdivide(n,n)
            # Split the block not corresponding to f^m.
            (Tb,Mb)=eigenvalue_splitting_rat(M.subdivision(0,0))
            # Combine the two transformations.
            Tb=block_matrix(T.parent().base_ring(),2,2,[[Tb,0],[matrix([[0 for j in range(Tb.ncols())] for i in range(M.nrows()-Tb.nrows())]),1]])
            T=T*Tb
            M=block_matrix(M.parent().base(),2,2,[[Mb,0],[0,M.subdivision(1,1)]])
        # Case: f^m(M) is zero. There is nothing to do.
        return (T,M)
    # Case: The characteristic polynomial is irreducible. There is nothing to do.
    return (M.parent().one(),M)


def is_nilpotent(M):
    r"""
    Tests if a square matrix is nilpotent.

    Input:
        - M ... a square matrix.

    Output:
        - True if M is nilpotent, False otherwise.

    Algorithm:
        - See if the characteristic polynomial of M is x^k for some k.

    EXAMPLES:
        sage: is_nilpotent(matrix([[5,-3,2],[15,-9,6],[10,-6,4]]))
        True
        sage: is_nilpotent(matrix([[1,2,3],[4,5,6],[7,8,9]]))
        False
    """
    p=M.charpoly()
    return len(p.monomials())==1 and p[0]==0


def lcmatrix(M,p):
    r"""
    Computes the leading coefficient matrix in the p-adic expansion of a given
    matrix at an irreducible polynomial p.

    Input:
        - M ... a matrix with rational function coefficients.
        - p ... an irreducible polynomial.

    Output:
        - A matrix M0 with entries in the quotient field of the polynomial ring
          p lives in modulo p, such that M=p^v*(M0 + O(p)), where v is the order
          of M at p.

    Algorithm:
        - See padic_expansion(M,p,k).

    """
    return padic_expansion(M,p,1)[1][0]


#TODO: Slow?
def padic_expansion(M,p,k):
    r"""
    Computes the p-adic expansion up to some specified order of a matrix at an
    irreducible polynomial p.

    Input:
        - M ... a matrix with rational function coefficients.
        - p ... an irreducible polynomial.
        - k ... a bound for the order up to which the expansion is computed.

    Output:
        - The order v of M at p
        - A list of matrices M0,M1,...,Mk with entries in the quotient field of
          the polynomial ring p lives in modulo p, such that M=p^v*(M0 + M1*p +
          ... +Mk*p^(k-1) + O(p^k)), where v is as above.

    Algorithm:
        - Division with remainder.

    """
    val=matrix_valuation(M,p)
    if val==Infinity:
        return (val,[__mod(M,p)])
    A=M*p**(-val)
    l=[0 for i in range(k)]
    for i in range(k):
        A0=__mod(A,p)
        l[i]=A0
        if i<k: A=(A-__lift(A0))/p
    return (val,l)

#TODO: Slow
def factorial_expansion(M,k):
    (_,_,_,_,_,var)=__parent_info(M)
    p=var
    val=matrix_valuation(M,Infinity)
    if val==Infinity:
        return (val,[__mod(M,p)])
    A=M*p**val
    l=[0 for i in range(k)]
    for i in range(k):
        Ai=A.subs({var:1/var})
        A0=__mod(Ai,p)
        l[i]=A0
        if i<k:
            A=(A-__lift(A0))*p
            A=A.subs({var:var-1})
    return (-val,l)


def __column_reduce(M,k):
    r"""
    Given a matrix M and a positive integer k, reduces as many of the last k
    columns of M to zero as possible and puts them as the last columns of the
    resulting matrix. 

    Input:
        - M ... a matrix with entries in a field.
        - k ... a posiive integer less than or equal to the number of columns of
          M.

    Output:
        - A similarity transformation T, bringing M into the form described
          above.
        - The number of zero columns obtained.

    Algorithm:
        - T is obtained from a basis of  M.right_kernel().

    """
    # # Compute the right kernel of M
    P=[i for i in M.submatrix(0,0,M.nrows(),M.ncols()).right_kernel().basis()]
    n=M.ncols()-k
    # Initialize T
    T=[[1 if i==j else 0 for j in range(M.ncols())] for i in range(n)]
    T=T+[[] for i in range(k)]
    switch=[]
    nulldim=0
    # Look for columns that can be reduced to zero.
    for i in range(k):
        found=None
        for j in P:
            # Case: We found a column. Adjust T accordingly.
            if j[-i-1]!=0:
                found=j
                T[-i-1]=(j/j[-i-1])
                break
        if found:
            # When we found a column, we mark it for putting it at the end.
            nulldim=nulldim+1
            P.remove(found)
            switch.append(-i-1)
        else:
            T[-i-1]=([1 if j==M.ncols()-i-1 else 0 for j in range(M.ncols())])
    T=matrix(T)
    # Swap the zero columns to the end.
    for i in range(len(switch)):
        T=T.with_swapped_rows(T.nrows()+switch[i],T.nrows()-1-i)
    return (T.transpose(),nulldim)


def find_transformation(M1,M2,k=10,r=3):
    r"""
    Computes the similarity transformation for two similar matrices, that
    transforms the first matrix into the second.

    Input:
        - M1 ... a square matrix with entries in a field.
        - M2 ... a square matrix with entries in a field.
        - k ... (optional) the number of tries to find a transformation. Default
          value is 10.
        - r ... (optional) used as a bound to obtain random rational
          numbers. Default is 3.

    Output:
        - A transformation T such that T^(-1)*M1*T == M2, or 'None' if no such
          transformation exists.

    Algorithm:
        - Compute a basis of the solution space of M1*X-X*M"==0. Take a random
          linear combinations of elements in the solution space basis.

    """
    l=__solve_sylvester_rat(M1,-M2,M1.parent().zero())[1]
    for i in range(k):
        T=sum([QQ.random_element(3)*i for i in l])
        if det(T)!=0:
            return T
    return None
