"""
differential
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

from .tools import __parent_info,matrix_valuation, padic_expansion, lcmatrix, __column_reduce, __lift, __solve_sylvester_rat,__mod,__cast_to_base,is_nilpotent,SN_decomposition
from .config import *
from .general import indicial_matrix, shearing_transformation, apply_transformation, infinity_to_zero, _bounded_polynomial_solutions, to_scalar_operator
from .difference import dispersion
from .generalized_series_space import GeneralizedSeriesRing

from sage.modules.free_module import VectorSpace
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from functools import reduce
from sage.rings.rational_field import QQ
from sage.rings.semirings.non_negative_integer_semiring import NN
from sage.rings.infinity import Infinity
from sage.structure.element import Matrix
from sage.matrix.special import block_matrix,diagonal_matrix
from sage.matrix.constructor import matrix
from sage.functions.other import ceil
from sage.categories.pushout import pushout

def _block_decomposition(M,M0,k):
    r"""
    For a differential system given by a matrix M, decomposes the all matrices
    in the truncated series expansion of M around 0 into the same block
    structure as given by its leading matrix M0. The valuation of M at the
    origin has to be less than or equal to 2.

    Input:
        - M ... a matrix defining a first order differential system. The
          valuation of M at x has to be less than or equal to 2.
        - M0 ... the leading coefficient matrix of M, i.e. M=(1/x^q)*(M0+
          x*M1+x^2*M2+...), where q is the valuation of M at x. This has to be
          in block diagonal form, where the blocks are explicitly specified as a
          subdivison of M0.
        - k ... a bound for the truncation. The first k matrices in the
          expansion M=(1/x^q)*(M0+ x*M1+x^2*M2+... x^k*Mk + \dots) will have a
          block structure corresponding to the block structure of M0.

    Output:
        - A gauge transformation T such that the first k matrices in the series
          expansion if T[M] around x have the required block diagonal structure.
        - The first k matrices in the series expansion of T[M] around 0.

    Algorithm:
        - Wasow '65, Section 11.

        """

    # Initialization. Bring the system into the form x*d/dx Y = xM*Y
    (M,MS,F,_,_,var)=__parent_info(M)
    (q,Ms)=padic_expansion(M,var,k)
    # addQ=False
    # if q>=0:
    #     addQ=True
    #     M=1/var*M
    #     q=q-1

    # Determine the number of blocks in M0. If there is only one, then there is
    # nothing to do
    nblocks=len(M0.subdivisions()[0])+1
    if nblocks==1:
        return (MS.one(),M)
    Ms=[__lift(i) for i in Ms]
    q=-q
    Bs=[M0]
    Ts=[M0.parent().one()]

    # Construct the transformation and the result after the transformation block
    # by block for increasing order. This is done by Ansatz.
    for i in range(1,k):
        Bblocks=[0 for j in range(nblocks)]
        Tblocks=[0 for j in range(nblocks)]
        if i<q:
            H=-Ms[i] + sum([Ts[j]*Bs[i-j] - Ms[i-j]*Ts[j] for j in range(1,i)])
        else:
            H=-Ms[i] + (i-q)*Ts[i-q] + sum([Ts[j]*Bs[i-j] - Ms[i-j]*Ts[j] for j in range(1,i)])
        H.subdivide(M0.subdivisions())
        for j in range(nblocks):
            Bblocks[j]=-H.subdivision(j,j)
            Tblocks[j]=__solve_sylvester_rat(M0.subdivision(j,j),-M0.subdivision(nblocks-j-1,nblocks-j-1),H.subdivision(j,nblocks-j-1))[1]
        B=block_matrix(F,nblocks,nblocks,[[Bblocks[j] if h==j else 0 for h in range(nblocks)] for j in range(nblocks)])
        T=block_matrix(F,nblocks,nblocks,[[Tblocks[j] if nblocks-h-1==j else 0 for h in range(nblocks)] for j in range(nblocks)])
        Bs.append(B)
        Ts.append(T)
    B=sum([Bs[i]*var**(i-q) for i in range(len(Bs))])
    B.subdivide(M0.subdivisions())
    #return (sum([Ts[i]*var**i for i in range(len(Ts))]),addQ*var*B)
    return (sum([Ts[i]*var**i for i in range(len(Ts))]),B)


def _desingularize_diff(M,l=None):
    r"""
    Desingularizes a differential system at given irreducible poles. If no poles
    are specified, then all possible apparent singularities are removed.

    Input:
        - M ... a matrix defining a first order differential system.
        - l ... (optinal) a list of irreducible polynomials or a single
          irreducible polynomial. If not specified, l is set to the list of all
          irreducible factors of the denominator of M.

    Output:
        - A transformation such that T[M]=B, where B is as below.
        - A matrix B defining a differential system equivalent to M,
          desingularized at the poles in l (or all poles if l is None).

    Algorithm:
        - Barkatou, Maddah, ISSAC'15.

    """
    if l!=None and not isinstance(l,list):
        l=[l]
    else:
        l=[i[0] for i in M.denominator().factor() if i[0].degree()>0]

    (M,MS,F,R,K,var)=__parent_info(M)
    systype=systype_d[0]
    T=MS.one()

    for p in l:
        # Perform Moser reduction
        (Tb,M,r)=moser_reduction(M,p)

        # Case: Moser rank >1
        if r>1:
            continue
        T=T*Tb

        # Compute rational residue matrix and its integer eigenvalues
        Mr=residue_matrix(M,p)
        c=Mr.charpoly(repr(var)+"0")
        var2=c.parent().gens()[0]
        R=PolynomialRing(PolynomialRing(K,[repr(var2)]),[repr(var)])
        R2=PolynomialRing(K,[repr(var2),repr(var)])
        c=R(R2(c.numerator()))
        g=reduce(lambda u,v:u.gcd(v),c.coefficients())
        ev=[i for i in g.roots(QQ) if i[0].denominator()==1 and i[0]>=0]

        # If the Eigenvalues are not all non-negative integers...
        if g==1 or sum([i[1] for i in ev])!=g.degree():
            continue

        # While there are nonzero eigenvalues
        while Mr!=Mr.parent().zero():
            # Compute SN decomposition
            (Tb,A,N)=SN_decomposition(Mr)
            M=apply_transformation(M,Tb,systype=systype)
            T=T*Tb
            # Case: non-singular block
            if A==None:
                # Apply shearing. If N is daigonal matrix, this will
                # desingularize M. If not, then M is not desingularizable
                Tb=shearing_transformation(MS,M.nrows(),p=p**NN(N[0][0]))
                M=apply_transformation(M,Tb,systype=systype)
                T=T*Tb
                break
            # Case: There is a nilpotent part
            elif N!=None:
                # Create shearing for non-singular part and add a block for the
                # nilpotent part
                Tb=block_matrix(F,2,2,[[shearing_transformation(A.parent(),A.nrows(),p=p),0],[0,N.parent().one()]])
            # Case: There is no nilpotent part
            else:
                # Create shearing for non-singular part
                Tb=shearing_transformation(A.parent(),A.nrows(),p=p)
            M=apply_transformation(M,Tb,systype=systype)
            T=T*Tb
            Mr=residue_matrix(M,p)

    return (T,M)


def _moser_reduction(M,p,T=None):
    r"""
    Performs the rational version of Moser reduction of a differential system at
    a pole p. Called by moser_reduction(M,p).

    Input:
        - M ... a matrix defining a first order differential system.
        - p ... an irreducible polynomial.
        - T ... a non-singular matrix used as a transformation to obtain M from
          another differential system.

    Output:
        - A transformation such that T[M]=B, where B is as below.
        - A matrix B defining a differential system equivalent to M with minimal
          Moser rank at p. In particular, B will have minimal Poincare rank at
          p.

    Algorithm:
        - Barkatou, ISSAC'95.

    """
    #Helper function to find an appropriate left kernel vector
    def __left_kernel_vector(G,r):
        v=None
        i=0
        b=G.left_kernel().basis()
        if len(b)==0:
            return (None,None)
        while not v:
            vt=b[i]
            if reduce(lambda x,y:x or y, [j!=0 for j in vt[r:]]): v=b[i]
            i=i+1
        v=v.parent().ambient_vector_space().change_ring(M.parent().base_ring())([i.lift() for i in v])
        T=copy(M.parent().one())
        if v[-1]==0:
            for i in range(r,len(v)-1):
                if v[i]!=0:
                    T=T.with_swapped_rows(i,len(v)-1)
                    break
        v=T*v
        #Normalize last entry.
        if v[-1]!=1:
            v=1/v[-1]*v
        return (T,v)

    (M,MS,F,R,K,var)=__parent_info(M)
    systype=systype_d[0]
    mr=moser_rank(M,p)
    if T==None:
        T=M.parent().one()

    while True:
        # If moser rank is <= 1, then there is nothing to do
        if mr<=1: return (T,M)
        #Test if leading coefficient matrix is in column reduced form. If not, apply transformation.
        A=padic_expansion(M,p,2)[1]
        r=A[0].rank()
        (A11,A12,A21,A22)=(A[0].submatrix(0,0,r,r),A[0].submatrix(0,r,nrows=r),A[0].submatrix(r,0,ncols=r),A[0].submatrix(r,r))
        (B12,B22)=(A[1].submatrix(0,r,nrows=r),A[1].submatrix(r,r))
        R2=PolynomialRing(A11.parent().base_ring(),[repr(var)+'0'])
        var2=R2.gens()[0]
        
        if not (A12==A12.parent().zero() and A22==A22.parent().zero()):
            Tb=__lift(A[0].smith_form()[2])
            M=apply_transformation(M,Tb,systype=systype)
            T=T*Tb
            continue

        G=block_matrix(2,2,[A11,B12,A21,B22+var2*B22.parent().one()])
        if G.determinant()!=0:
            return (T,M)

        # See if Proposition 1 applies
        if block_matrix(1,2,[A11,B12]).rank()<r:
            Tb=shearing_transformation(M.parent(),r,1,p)
            Mb=apply_transformation(M,Tb,systype=systype)
            if moser_rank(Mb,p)<mr: return (T*Tb,Mb)
            return (T,M)
        else:
            # Construct G and determine h
            R2=PolynomialRing(A11.parent().base_ring(),[repr(var)+'0'])
            var2=R2.gens()[0]
            G=block_matrix(2,2,[A11,B12,A21,B22+var2*B22.parent().one()])
            h=1
            while (G[-h][-h]==var2 and G.columns()[-h][-h:][1:]==0 and G.rows()[-h][:-h]==0):
                h=h+1
            h=h-1

            # See if Proposition 2 applies
            if (G.submatrix(0,0,r,M.nrows()-r-h).rank()<r):
                Tb=shearing_transformation(M.parent(),r,p=p)*shearing_transformation(M.parent(),h,M.nrows()-h+1,p=p)
                Mb=apply_transformation(M,Tb,systype=systype)
                if moser_rank(Mb,p)<mr: return (T*Tb,Mb)
                return (T,M)
            else:
                if h>0 and G.submatrix(0,0,r,M.nrows()-h).rank()<r:
                    Gh = G.submatrix(0,0,G.nrows()-h,M.nrows()-h)
                    (Tb,v)=__left_kernel_vector(Gh)
                    if Tb==None:
                        return (T,M)
                    v=vector([v[i] if i<len(v) else 0 for i in range(G.nrows())])
                    Tc=copy(M.parent().one())
                    Tc.set_block(0,0,Tb)
                    Tb=Tc
                    Tl=matrix([[1 if j==i else 0 for j in range(M.nrows())] if i!=G.nrows()-h-1 else v for i in range(M.nrows())])
                    Tb=(Tl*Tl.parent()(Tb).inverse()).inverse()
                    M=apply_transformation(M,Tb,systype=systype)
                    T=T*Tb
                    continue

                # Apply construction from Proposition 3 Find left kernel vector
                # with last entry non-zero. Swap rows if necessary.
                G0=block_matrix(2,2,[A11,B12,A21,B22])
                (Tb,nullrows)=__column_reduce(G0.submatrix(0,0,G.nrows()-h,G.nrows()-h).transpose(),G.nrows()-h-r)
                Tb=__lift(Tb)
                if G0.nrows() > Tb.nrows():
                    Tb=block_matrix(F,2,2,[[Tb,0],[matrix([[0 for j in range(Tb.ncols())] for i in range(M.nrows()-Tb.nrows())]),1]])
                else:
                    Tb=MS(Tb)
                Tb=Tb.transpose().inverse()
                M=apply_transformation(M,Tb,systype=systype)
                T=T*Tb


def _polynomial_solutions_diff(M,N=None):
    r"""
    Computes all polynomial solutions of the pseudo linear system of
    differential type with matrix M and right hand side N.

    Input:
        - M ... a matrix defining a first order differential system.
        - N ... (optional) a vector whose length is equal to the number of
          columns in M with rational function entries.

    Output:
        - A basis for the solutions of the homogeneous pseudo linear system of
          differential type defined by M with polyomial entries.
        - One solution for the inhomogeneous pseudo linear system of
          differential type defined by M and N with polynomial entries.

    Algorithm:
        - Barkatou, JSC'99, with straightforward improvements.

    """
    
    (M,_,F,R,K,var)=__parent_info(M)
    systype=systype_d[0]

    # Set right hand side to zero if it is set to None
    if N==None:
        N=VectorSpace(F,M.ncols()).zero()
    if isinstance(N,Matrix):
        if N.ncols()>1:
            raise ValueError("N has to be a vector")
        N=VectorSpace(F,M.ncols())(N.columns()[0])
    # Compute the indicial polynomial
    ip=indicial_matrix(infinity_to_zero(M,systype).transpose(),var,systype=systype).determinant()
    ip=ip.parent().change_ring(K)(ip)
    
    # Case: indicial polynomial is zero. The system has to be made simple
    if ip==0:
        # Perform super reduction
        # TODO: I don't know what I am doing here
        MR=super_reduction(infinity_to_zero(M,systype=systype),var)
        T=infinity_to_zero(MR[0])
        #Ti=Ti*var**(matrix_valuation(Ti,var))
        Ti=T.inverse()
        M=apply_transformation(M,T,systype=systype)
        #M=infinity_to_zero(MR[1]).transpose()

        # Compute polynomial solutions of transformed system
        (sol,special)=_polynomial_solutions_diff(M,Ti*N)
        sol=[T*i for i in sol]
        if special!=None:
            special=T*special
        return (sol,special)

    # Compute the degree bound
    ip=ip.parent().change_ring(K)(ip)
    l=[-i[0] for i in ip.roots(QQ) if i[0].denominator()==1 and i[0]<=0]

    #TODO Not sure if the max degree in N is correct here
    if l==[]:
        #degbound=max([R(i).degree() for i in N])+1
        degbound=max([i.numerator().degree()-i.denominator().degree() for i in N])+1
    else:
        #degbound=max(max(l),max([R(i).degree() for i in N]))+1
        #TODO: Why +2 and not +1?
        degbound=max(max(l),max([i.numerator().degree()-i.denominator().degree() for i in N]))+2

    degbound=degbound
    return _bounded_polynomial_solutions(M,degbound,N,systype)
    # # op=operator(M,systype=systype)
    # # N=den*N

    # # # Case: Degree bound is zero:
    # # if degbound<=0:
    # #     return ([],None)
    
    # # # Set up the equations and clear denominators
    # # eqs=block_matrix(1,degbound,[op(var**i) for i in range(degbound-1,-1,-1)])
    # # eqs=block_matrix(1,2,[den*eqs,matrix(-N).transpose()])
    # # eqs=eqs.parent().change_ring(R)(eqs)
    # # sol=[]
    # # special=None

    # # size=M.ncols()
    # # EQSdeg=max(sum([[R(i).degree() for i in j] for j in eqs],[]))+1
    # # eqs2=[[0 for j in range(eqs.ncols())] for i in range(eqs.nrows()*EQSdeg)]

    # # for i in range(eqs.nrows()*EQSdeg):
    # #     (row,coeff)=NN(i).quo_rem(EQSdeg)
    # #     for j in range(eqs.ncols()):
    # #         eqs2[i][j]=eqs[row][j][coeff]

    # # sol=matrix(eqs2).right_kernel().basis()
    # # polysol=[]

    # # # Compute the solutions as vectors with entries in Q, compress them to
    # # # vectors with polynomial entries
    # # for i in sol:
    # #     v=i[:-1]
    # #     l=[0 for j in range(M.ncols())]
    # #     for j in range(M.ncols()):
    # #         for h in range(degbound):
    # #             l[j]=l[j]+var**(degbound-h-1)*v[h*M.ncols()+j]

    # #     # If the last entry is non-zero, and not all other entries are zero, it
    # #     # is a solution to the inhomogeneous system
    # #     if reduce((lambda x,y:y==0 and x),v,True): continue
    # #     if i[-1]!=0:
    # #         if special!=None:
    # #             polysol.append(special-vector(l)/i[-1])
    # #         else:
    # #             special=vector(l)/i[-1]
    # #     else:
    # #         polysol.append(vector(l))
    # # return (polysol,special)

def _rational_solutions_diff(M,B=None):
    r"""
    Computes all rational solutions of the pseudo linear system of differential
    type with matrix M and right hand side N.

    Input:
        - M ... a matrix defining a first order differential system.
        - N ... a vector whose length is equal to the number of columns in M
          with rational function entries.

    Output:
        - A basis for the solutions of the homogeneous pseudo linear system of
          differential type defined by M with rational function entries.
        - One solution for the inhomogeneous pseudo linear system of
          differential type defined by M and N with rational function entries.

    Algorithm:
        - Barkatou, JSC'99, with straightforward improvements.

    """
    
    (M,MS,F,R,K,var)=__parent_info(M)
    systype=systype_d[0]

    # Set right hand side to zero if it is set to None
    if B==None:
        B=VectorSpace(F,M.ncols()).zero()

    R2=PolynomialRing(R.base_ring(),[repr(var)+'0'])

    # get the irreducible factors in the denominator of M and B
    denom_M=M.denominator()
    denom_factors=[i[0] for i in denom_M.factor()]
    denom_B=B.denominator()
    denom_B=denom_B/denom_B.gcd(denom_M)

    # Reduce the multiplicty of the factors in the denominator of B by 1
    denom_B=denom_B.gcd(denom_B.derivative())

    # Compute exponent bound for each factor in denom_M
    # Stupid casting because of coercion system
    R2=PolynomialRing(PolynomialRing(K,[repr(var)+"0"]),[repr(var)])
    R3=PolynomialRing(K,[repr(var)+"0",repr(var)])
    exps=[0 for i in denom_factors]

    for i in range(len(denom_factors)):
        ip=R2(R3(indicial_matrix(M.transpose(),denom_factors[i],systype=systype).determinant()))
        hp=0

        if ip==0:
            (Tb,Mb)=super_reduction(M,denom_factors[i])
            hp=matrix_valuation(Tb.determinant(),denom_factors[i])
            ip=R2(R3(indicial_matrix(Mb.transpose(),denom_factors[i],systype=systype).determinant()))

        g=reduce(lambda u,v:u.gcd(v),ip.coefficients())
        roots=[j[0] for j in g.roots(QQ) if j[0].denominator()==1]
        if roots==[]:
            exps[i]=-1+hp-matrix_valuation(B,denom_factors[i])
            if exps[i]==-Infinity:
                return ([],None)
        else:
            exps[i]=-min(1-hp+matrix_valuation(B,denom_factors[i]),min(roots))
            if exps[i]==-Infinity:
                return ([],None)
    denom = reduce(lambda a,b:a*b,[denom_factors[i]**exps[i] for i in range(len(denom_factors))])*denom_B
    #INVESTIGATE: denom bound way to high for certain systems. eg
    # q1=1/x
    # q2=1/(x+1)
    # q3=1/(x+2)
    # Q1=q1*Dx-diff(q1)
    # Q2=q2*Dx-diff(q2)
    # Q=Q1.lclm(Q2)
    # Maybe it is because it is desingularizable?
    # Also not simple at infinity after multiplying by denom
    T=shearing_transformation(MS,M.nrows(),p=1/denom)
    M=apply_transformation(M,T,systype=systype)
    B=T.inverse()*B
    (sol,special)=_polynomial_solutions_diff(M,B)
    if special!=None:
        return [[i/denom for i in sol], special/denom]
    return [[i/denom for i in sol], None]


def _super_reduction(M,p,k):
    r"""
    Reduce the i-th generalizations of the Moser rank of M at p, as described by
    Hilali, Wazner '87, and Barkatou JCAMDI'04. This is method requires the
    input system to be already reduced for all i<k. If this is not the case, one
    should call super_reduction(M,p,k).

    Input:
        - M ... a matrix defining a first order differential system, reduced for
          every i<k.
        - p ... an irreducible polynomial.
        - k ... (optional) specifies which rank should be minimized. By default,
          k will be set to the negative valuation of M at p.

    Output:
        - a transformation T such that T[M]=B, where B is as below.
        - a matrix B equivalent to M with minimal k-th generalized Moser rank at
          p. In particular. if k is equal to the negative valuation of M, B will
          be super reduced.

    Algorithm:
        - Barkatou JCAMDI'04

    """

    def __left_kernel_vector(G,r):
        v=None
        i=0
        b=G.left_kernel().basis()

        if len(b)==0:
            return (None,None)
        while not v:
            vt=b[i]
            if reduce(lambda x,y:x or y, [j!=0 for j in vt[r:]]): v=b[i]
            i=i+1
        v=v.parent().ambient_vector_space().change_ring(M.parent().base_ring())([i.lift() for i in v])
        T=M.parent().one()
        if v[-1]==0:
            for i in range(len(v)-1,-1,-1):
                if v[i]!=0:
                    T=copy(T).with_swapped_rows(i,len(v)-1)
                    break
        v=T*v
        # Normalize last entry.
        if v[-1]!=1:
            v=1/v[-1]*v
        return (T,v)

    (M,MS,F,R,K,var)=__parent_info(M)
    systype=systype_d[0]
    (val,M0)=padic_expansion(M,p,1)
    M0=M0[0]

    # Case: k is too small, or greater than the negative valuation, or the roots
    # of p are regular singular (or ordinary) points: there is nothing to do
    if k<1 or k>=-val or val>=-1:
        return (M.parent().one(),M)

    # Order columns of M, get number of rows of order j for each j<k.
    (T,M,kRank,n,vals)=k_rank(M,p,k,True)

    # if val+k>vals[-1]:
    #     return (T,M)

    # Construct N such that A=p^(-val)*N*diag(I,pI,p^2*I,...)
    N=[]
    s=0
    pval=p**(-val)
    start=0
    for i in range(len(n)):
        if n[i]!=0:
            N=N+[M.columns()[start+j]*pval*p**(-s) for j in range(n[i])]
            start=start+n[i]
        s=s+1
    N=MS(N).transpose()

    # Construct G
    G0=lcmatrix(N,p)
    R2=PolynomialRing(K,[repr(var)+'0'])
    F2=PolynomialRing(R2.fraction_field(),[repr(var)])
    F2=F2.quotient(F2(p))
    MS2=MS.change_ring(F2)
    var2=R2.gens()[0]
    h=sum(n[:-1])
    h0=h-n[-2]
    
    G=MS2(G0)+shearing_transformation(MS2,n[-1],h+1,var2+1)-MS2.one()
    # Case G0 is non-singular:
    if G.determinant()!=0:
        return (T,M)
    # # Case: The first h columns of G are lin. dep.
    S=G0.submatrix(0,0,G.nrows(),h)
    r=S.rank()
    if r<h:
        # Bring the first h coluns of M to the same rank, and recombine them zo
        # zero columns
        (Tb,nullrows)=__column_reduce(S,h)
        Tb=__lift(Tb)
        P1=Tb.submatrix(0,h0,h0,Tb.nrows()-h0)
        P2=Tb.submatrix(h0,h0,Tb.ncols()-h0,Tb.nrows()-h0)
        h1=Tb.ncols()-P1.ncols()
        d=P2.determinant()
        P1=P1.with_rescaled_col(P1.ncols()-1,1/d)
        P2=P2.with_rescaled_col(P2.ncols()-1,1/d)
        P1=matrix([[(p**(vals[h-1]-vals[i]) if i<h else 1) if i==j else 0 for j in range(P1.nrows())] for i in range(h1)])*P1
        I1=matrix([[1 if i==j else 0 for j in range(h1)] for i in range(h1)])
        I2=matrix([[1 if i==j else 0 for j in range(M.nrows()-h)] for i in range(M.nrows()-h)])
        Tb=block_matrix(F,3,3,[[I1,P1,0],[0,P2,0],[0,0,I2]])
        M=apply_transformation(M,Tb,systype=systype)
        (Tc,M)=_super_reduction(M,p,k)
        return (T*Tb*Tc,M)

    #Case: The first h rows of G are lin. dep.
    #TODO: The +n[-1] is new. Test it
    S=G0.submatrix(0,0,h,h+n[-1])
    r=S.rank()
    if r<h:
        # Get zero rows and then multiply the columns corresponding to order vals[h-1] by p
        (Tb,nullrows)=__column_reduce(S.transpose(),n[-2])
        Tb=__lift(Tb)
        if Tb.ncols()!=M.ncols():
            Tb=block_matrix(F,2,2,[[Tb,0],[matrix([[0 for j in range(Tb.ncols())] for i in range(M.nrows()-Tb.nrows())]),1]])
        Tb=Tb.transpose().inverse()
        M=apply_transformation(M,Tb,systype=systype)
        #TODO: Test if TB works correctly here.
        T=T*Tb
        Tb=matrix([[(p**(vals[h-1]-vals[i]+1) if i<h and i>=h-nullrows else 1) if i==j else 0 for j in range(M.nrows())] for i in range(M.nrows())])
        M=apply_transformation(M,Tb,systype=systype)
        (Tc,M)=_super_reduction(M,p,k)
        return (T*Tb*Tc,M)
    else:
        # Determine block structure of G
        q=1
        while (G[-q][-q]==var2 and G.columns()[-q][-q:][1:]==0 and G.rows()[-q][:-q]==0):
            q=q+1
        q=q-1
        # If G doesn't have the appropriate block structure, tranform M such
        # that G can be decomposed.

        if q==0 or G0.submatrix(0,0,h,G.ncols()-q).rank()>=h:
            (Tb,nullrows)=__column_reduce(G0.submatrix(0,0,G0.nrows()-q,G0.nrows()-q).transpose(),G.nrows()-q-r)
            Tb=__lift(Tb)
            if G0.nrows() > Tb.nrows():
                Tb=block_matrix(F,2,2,[[Tb,0],[matrix([[0 for j in range(Tb.ncols())] for i in range(M.nrows()-Tb.nrows())]),1]])
            else:
                Tb=MS(Tb)
            Tb=Tb.transpose().inverse()
            M=apply_transformation(M,Tb,systype=systype)
            (Tc,M)=_super_reduction(M,p,k)
            return (T*Tb*Tc,M)
        else:
            # Construct shearing transformation
            Tb=MS([[0 if i!=j else p**(0 if ((i+1)>h and i+1<=M.nrows()-q) else 1) for i in range(M.nrows())] for j in range(M.nrows())])
            M=apply_transformation(M,Tb,systype=systype)
            (Tc,M)=_super_reduction(M,p,k)
            return (T*Tb*Tc,M)


def exponential_part_diff(M):
    def block_diagonalize(M,truncation):
        # Decompose A into two blocks (up to order given by truncation), one
        # non-singular and one nilpotent
        var=M.parent().base_ring().gens()[0]
        M0=__cast_to_base(__lift(lcmatrix(M,var)))
        M0n=M0**M0.nrows()
        basis=M0n.column_space().basis()
        n=len(basis)
        if n>0 and n<M0n.nrows():
            T=matrix(basis + M0n.right_kernel().basis()).transpose()
            M=apply_transformation(M,T,systype=systype)
            M0=__cast_to_base(__lift(lcmatrix(M,var)))
            M0.subdivide((n,n))
            (Tb,M)=_block_decomposition(M,M0,truncation)
            return (M.subdivision(0,0),M.subdivision(1,1))
        if n>0:
            return (M,[])
        return ([],M)

    systype=systype_d[0]
    (M,MS,F,R,K,var)=__parent_info(M)

    # Perform Moser reduction to get real Poincare rank
    M=moser_reduction(M,var)[1]

    q=-matrix_valuation(M,var)

    # Case: regular singular or ordinary point
    if q<=1:
        #F=GeneralizedSeriesRing(M.parent().base_ring().base().base(),var,5)
        return [(F(0),1)]

    # Case: Scalar equation
    if M.nrows()==1:
        #F=GeneralizedSeriesRing(M.parent().base_ring().base().base(),var,5)
        l=map(lambda x:(x._ContinuousGeneralizedSeries__exp(),x.ramification()),to_scalar_operator(M,systype)[0].generalized_series_solutions())
        l=map(lambda x:((x[0]-x[0].constant_coefficient()).subs({var:1/var}),x[1]),l)
        return [*l]
        #return map(lambda x:F(x.exponential_part()),to_scalar_operator(M,systype)[0].generalized_series_solutions())


    # Truncate M to the relevant terms in its series expansion
    truncation=M.nrows()*q-1
    M=padic_expansion(M,var,truncation)
    M=sum([__lift(M[1][i])*var**(i-q) for i in range(len(M[1]))])

    M0=__cast_to_base(__lift(lcmatrix(M,var)))
    # Compute Katz invariant k=l/m, corresponding reduced Newton polynomial, and
    # u,v such that ul+vm = 1
    if is_nilpotent(M0):
        (k,Pk)=katz_invariant(M,ramify=True)
        l=k.numerator()
        m=k.denominator()
        # if m==1:
        #     u=0
        #     v=1
        # else:
        #     u=l.inverse_mod(m)
        #     v=(1-u*l)/m
        M=M.subs({var:var**m})*m*var**(m-1)
        ramification=m
        M=moser_reduction(M,var)[1]
        M0=__cast_to_base(__lift(lcmatrix(M,var)))
        q=-matrix_valuation(M,var)
    else:
        ramification=1
    Pk=M0.charpoly()
    if not sum([i[1] for i in Pk.factor()])==Pk.degree():
        SF=Pk.splitting_field(repr(var)+'_1')
        MS2=M0.parent().change_ring(SF)
        R2=R.change_ring(SF)
    else:
        SF=K
        MS2=M0.parent()
        R2=R
    M0=MS2(M0)
    evs=list(dict.fromkeys(M0.eigenvalues()))
    expN=[]
    F=GeneralizedSeriesRing(SF,var,5)
    Mon=F.get_monoid()
    for i in evs:
        M2=(M-(SF(i)/var**(q))*M.parent().one())
        (A,N)=block_diagonalize(M2,truncation)
        # ex=Mon(1)
        # ex._ContinuousGeneralizedSeries__exp=(-i)*var**q
        # expN=expN+[i*F(ex) for i in exponential_part_diff(N)]
        #expN=expN+[(-i/((q-1)*var**(q-1)))+j.get_summands()[0]._ContinuousGeneralizedSeries__exp() for j in exponential_part_diff(N)]
        expN=expN+[((-i/((q-1)*var**(q-1)))+j[0],j[1]*ramification) for j in exponential_part_diff(N)]
    return expN
    # Ramify x<-c*x^m, where c is a new variable
    # Rbase=R.change_ring(PolynomialRing(R.base_ring(),[repr(var)+"0"]).fraction_field())
    # Rmult=R.extend_variables(repr(var)+"0")
    # MSbase=MS.change_ring(Rbase.fraction_field())
    # var1=Rmult.gens()[1]
    # M=MSbase(M.subs({var:var1*Rmult(var)**m})**m*var**(m-1))

    # # Decompose M into blocks
    # (A,N)=block_diagonalize(M,truncation)

    # expN=[]
    # expA=[]
    # # If there is a nilpotent block
    # if N!=[]:
    #     N=N.parent().change_ring(Rmult.fraction_field())(N)
    #     N=N.subs({var1:1})
    #     N=N.parent().change_ring(F)(N)
    #     # TODO: Use of k correct here?
    #     expN=exponential_part_diff(N)
    #     #expN=[ContinuousGeneralizedSeries(i.parent(),1,-1/m*x,m)*i for i in exponential_part_diff(N)]
    # if A!=[]:
    #     if not sum([i[0].degree()*i[1] for i in Pk.factor()])==Pk.degree():
    #         SF=Pk.splitting_field(repr(var)+'_1')
    #         R=R.change_ring(SF)
    #         Rmult=Rmult.change_ring(SF)
    #     else:
    #         SF=K
    #     A=A.parent().change_ring(Rmult.fraction_field())(A)

    #     roots=[i[0].coefficients()[0] for i in R(Pk).factor() if i[0].degree()>0]
    #     F=GeneralizedSeriesRing(SF,var,5)
    #     Mon=F.get_monoid()
    #     for r in roots:
    #         B=A.subs({Rmult(var1):r**u})
    #         B=B.parent().change_ring(R.fraction_field())(B)
    #         B=moser_reduction(B,var)[1]
    #         # TODO: I use q here instead of l/m. is this correct?
    #         B=(var*B-m*r**v*B.parent().one()/var**l)/var
    #         print B
    #         #B=B-m*r**v*B.parent().one()/var**(l)
    #         (A2,N2)=block_diagonalize(B,truncation)

    #         if N2!=[]:
    #             ex=Mon(1)
    #             ex._ContinuousGeneralizedSeries__exp=(m*r**v)*var**l
    #             expA=expA+[i*F(ex) for i in exponential_part_diff(N2)]
    #     #expA=diagonal_matrix(expA)
    # print expN
    # return diagonal_matrix(sum([expN,expA],[]))

def exponential_part(M):
    l=exponential_part_diff(M)
    var=l[-1][0].parent().gens()[0]
    Fs=[i[0].parent().base().base_ring() for i in l]
    #Todo: Too much work just for getting all variables together.
    F=reduce(pushout,Fs)
    G=GeneralizedSeriesRing(F,var,5)
    m=G.get_monoid()
    exps=[]
    for (s,r) in l:
        monoms=[(s.numerator().list()[i]*var**(s.denominator().degree()-i),r) for i in range(len(s.numerator().list()))]
        # TODO: This i just do because of a bug in GeneralizedSeriesMonoid, where m(1,x^d,ramification=r) does not work if r divides d
        for i in range(len(monoms)):
            mon=monoms[i]
            r=mon[1]
            mon=mon[0]
            if mon.parent().is_field():
                mon=mon.parent().base()(mon)
            d=mon.degree()
            if d%r==0:
                ex=d/r
                newmon=mon/var**(d)*var**(ex)
                monoms[i]=(newmon,1)
        exps.append(G(reduce(lambda a,b:a*b,map(lambda x: m(1,x[0]*1/x[1]*x[0].numerator().degree(),ramification=x[1]), monoms))))
    return diagonal_matrix(exps)

def fundamental_solution_regular_diff(M,prec=5):
    r"""
    Computes a fundamental system of soltuions with generalized series entries
    of a first order differential system around zero up to a given order,
    provided zero is an ordinary or regular singular point.

    Input:
        - M ... a matrix defining a first order differential system with
          valuation -1 or higher at x.
        - prec ... (optional) a bound for the order up to which the series
          entries in the fundamental system are computed. Default value is 5.

    Output:
        - A matrix with entries whose entries are sums of elements of the form

                `\exp(\int_0^x \frac{p(t^{-1/r})}t dt)*q(x^{1/r},\log(x))`

          where

            * `r` is a positive integer (the object's "ramification")
            * `p` is in `K[x]` (the object's "exponential part")
            * `q` is in `K[[x]][y]` with `x\nmid q` unless `q` is zero (the
              object's "tail")
            * `K` is the base ring.

          For more details see the GeneralizedSeriesMonoid class in the
          ore_algebra package.

          The columns of the matrix form a basis of the solution space of M
          around 0.
          If 0 is not a singularity of M, then the entries will live in the same
          parent as the entries of M.

    Algorithm:
        - Wasow '65, Chapter 2.

    """
    # Computes a solution of the form P*x^A, where P is a power series.
    (M,MS,F,R,K,var)=__parent_info(M)
    systype=systype_d[0]
    prec=prec+1
    MSbase=MS.change_ring(K)
    one=MSbase.one()
    zero=MSbase.zero()
    (q,Ms)=padic_expansion(M,var,prec)
    
    # Case: Irregular singular point.
    if q<-1:
        raise ValueError("0 is not a regular singularity or an ordinary point in M")
    
    # Case: Ordinary point. Solve coefficient-wise
    if q>-1:
        Ms=[Ms[0].parent().zero() for i in range(q)] + Ms
        sol=[MS.zero() for i in range(prec)]
        sol[0]=MS.one()
        for i in range(1,prec):
            sol[i]=1/QQ(i)*sum([__lift(Ms[i-j-1])*sol[j] for j in range(i)])
        return (MS.one(),sum([var**i*sol[i] for i in range(prec)]))

    M=var*M
    q=q+1
    Ms=[zero for i in range(q)] + [*map(lambda x: MSbase(__lift(x)),Ms)]

    # Compute the dispersion
    M0=Ms[0]
    cP=M0.charpoly()
    disp=dispersion(cP,cP)

    # Case: Eigenvalues in integer distance. Shift them together. And compute
    # solutions of new system.
    if disp!=0:
        # Bring leading coeff matrix in block form
        p=shift_minimal_part(M0.charpoly())
        Mf=p(M0)
        basis=Mf.column_space().basis()
        T=matrix(basis + Mf.right_kernel().basis()).transpose()
        # Shearing transformation to shift eigenvalues by one,
        T=T*shearing_transformation(MS,M.nrows()-len(basis),len(basis)+1,var**disp)
        M=apply_transformation(M,T,1)
        M=M/var
        (Tb,M,_)=moser_reduction(M,var)
        T=T*Tb
        (Tb,sol)=fundamental_solution_regular_diff(M,prec)
        return (T*Tb,T*sol)

    # Construct T coefficientwise such that the transformed system is just the
    # leading coefficient matrix of M
    Ts=[MS.one()]
    for i in range(1,prec):
        Ts.append(MS(__solve_sylvester_rat(M0-i*one,-M0,-sum([Ms[i-j]*Ts[j] for
                                                              j in range(i)]))[1]))
    power=var
    T=Ts[0]
    for i in Ts[1:]:
        T=T+i*power
        power=power*var

    # Compute the solutions of the system with constant coefficients
    sol=__matrix_exponential(MS.change_ring(K)(M0),var,prec)
    return (T,T*sol)


def __matrix_exponential(M,base=None,prec=5):
    r"""
    Computes base^M, where base is an indeterminate and M a square matrix. The
    entries of the result will be sums of generalized series (see description of
    fundamental_solution_regular_diff for more details).

    Input:
        - M ... a square matrix with entries in a number field.
        - base ... an indeterminate in a polynomial ring.
        - prec ... (optional) a bound for the order up to which the generalized
          series entries are computed.

    Output:
        - The matrix base^M.

    Algorithm:
        - Jordan decomposition.
    """
    (M,MS,F,_,_,_)=__parent_info(M,False)
    if not base:
        b=PolynomialRing(F,'e').gens()[0]
    else:
        b=base
    Fs=M.charpoly().splitting_field('a')
    if Fs.defining_polynomial().degree()>1:
        a=Fs.gens()[0]
        F2=GeneralizedSeriesRing(Fs,b,prec)
    else:
        F2=GeneralizedSeriesRing(F,b,prec)
    mon=F2.get_monoid()
    log=F2.tail_ring().gens()[0]
    (M,T)=M.jordan_form(base_ring=Fs,transformation=True)
    MS=MS.change_ring(F2)
    ex=matrix([[(F2(mon(1,M[i][j]))) if i==j else 0 for j in range(M.ncols())] for i in range(M.nrows())])
    if base:
        MN=matrix([[F2(mon(log))*F2(mon(M[i][j])) if i!=j else 0 for j in range(M.ncols())] for i in range(M.nrows())])
    else:
        MN=matrix([[F2(mon(M[i][j])) if i!=j else 0 for j in range(M.ncols())] for i in range(M.nrows())])
    return MS(T)*ex*__matrix_exponential_nilpotent(MN)*MS(T.inverse())


def __matrix_exponential_nilpotent(M):
    r"""
    Computes the exponential of a nilpotent matrix. The entries of the result
    will be sums of generalized series (see description of
    fundamental_solution_regular_diff for more details).

    Input:
        - M ... a nilpotent square matrix with entries in a number field.

    Output:
        - The matrix e^M.

    Algorithm:
        - Explicit series computation.

    """
    sol=M.parent().one()
    factorial=QQ.one()
    Mn=M.parent().one()
    for i in range(1,M.nrows()+1):
        Mn=Mn*M
        factorial=factorial*i
        sol=sol + 1/factorial*Mn
    return sol


def fundamental_solution_scalar_diff(M):
    R=M.parent().base_ring()
    var='D'+repr(R.gens()[0])
    ore=OreAlgebra(R,var)
    var=ore.gens()[0]
    return (var-M[0][0]).generalized_series_solutions()


#TODO: Trick to shift poles to reduce at infinity and not affect other poles
def is_fuchsian(M):
    r"""
    Determines if a differential system is Fuchsian, i.e. with only regular
    singular or ordinary poimts.

    Input:
        - M ... a matrix defining a first order differential system.

    Output:
        - A boolean value b. True if M is Fuchsian, False otherwise.
        - If b==True:
            - A transformation such that T[M]=B, where B is as below.
            - A matrix B defining a differential system equivalent to M,
              such that the Moser rank at each finite pole is minimal.
        - If b==False:
            - An irreducible polynomial defining a pole of M with Poincare
              rank >1.
            - The Moser rank of M at p.

    Algorithm:
        - Moser reduction at every pole of M and at the point at infinity.

    """
    p=M.parent().base_ring()(M.denominator())
    T=M.parent().one()
    for i in p.factor():
        if i[0].degree()>=1:
            (Tb,M,r)=moser_reduction(M,i[0])
            if r>1:
                return (False,(i[0],r))
            T=T*Tb
    (_,_,r)=moser_reduction(infinity_to_zero(M),M.parent().base_ring().gens()[0])
    if r>1:
        return (False, (Infinity,r))
    return (True,(T,M))


def k_rank(M,p,k,details=False):
    r"""
    Computes the generalization of the Moser rank to the first k matrices
    M0,..,Mk in the series expansion of a differential system M, as described by
    Hilali, Wazner '87, and Barkatou JCAMDI'04.

    Input:
        - M ... a matrix defining a first order differential system.
        - p ... an irreducible polynomial.
        - k ... a positive integer.
        - details ... (optional) if set to True, more details will be given in
          the output. See output specification. Default is False.

    Output:
        - If details==False:
            - The kth rank of M at p.
        - If details==True:
            - A transformation such that T[M]=B, where B is as below.
            - A matrix B defining a differential system equivalent to M,
              such that the columns of B are of increasing valuation in p.
            - A list of length k. The ith entry is the number of columns with
              valuation val+i, where val is the valuation of M at p.
            - A list of integers. The ith entry is the valuation of the ith
              column (counting from zero) of B.

    Algorithm:
        - Naive.

    """
    (M,MS,_,_,_,_)=__parent_info(M)
    T=MS.one()
    systype=systype_d[0]
    
    val=matrix_valuation(M,p)
    if val>=0:
        if details:
            return (T,M,1,[],[])
        else:
            return 1
    n=[[] for i in range(k+1)]
    vals=[0 for i in range(M.ncols())]
    currentval=0
    for i in range(M.ncols()):
        currentval=matrix_valuation(M.columns()[i],p)
        deltaval=currentval-val
        if deltaval<k:
            n[deltaval]=n[deltaval]+[(i,currentval)]
        if deltaval>=k:
            n[k]=n[k]+[(i,currentval)]

    l=sum(n,[])
    vals=[i[1] for i in l]
    l=[i[0] for i in l]
    T=MS([[1 if i==l[j] else 0 for j in range(M.nrows())] for i in range(M.nrows())])
    M=apply_transformation(M,T,systype=systype)
    n=[len(i) for i in n]
    if details:
        return (T,M,-val-1+sum([QQ(n[i])/QQ(M.nrows()**(i+1)) for i in range(k)]),n,vals)
    else:
        return -val-1+sum([QQ(n[i])/QQ(M.nrows()**(i+1)) for i in range(k)])


def katz_invariant(M,ramify=False):
    r"""
    Computes the Katz invariant k and the kth Newton polynomial of a
    differential system.

    Input:
        - M ... a matrix defining a first order differential system.
        - ramify ... (optional) if set to True, The substitution x->x^1/d is
          performed in the Newton polynomial, where d is the denominator of the
          Katz invariant. Default is False.

    Output:
        - The Katz invariant k of M.
        - The kth Newton polynomial of M if k>0, 0 otherwise.

    Algorithm:
        - Barkatou AAECC'97.

    """
    (M,_,_,R,K,var)=__parent_info(M)

    # Interpret system as x*d/dx Y = MY
    M=var*M

    # Make M irreducible
    (_,M,_)=moser_reduction(M,var)

    q=-matrix_valuation(M,var)

    # Case 1: Ordinary point or regular singular point.
    if q<=0:
        return (K(0),R.zero())

    n=QQ(M.nrows())
    r=QQ(lcmatrix(M,var).rank())
    f=1
    m=1

    # If the rank of the lc is too small, we need a ramification
    if q<=n-r and q<=r+1:
        m=ceil(n/(q-1+r/n))
        M=m*M.subs({var:var**m})
        (_,M,_)=moser_reduction(M,var)
        f=1/m

    # Compute the characteristic polynomial of M and expand its coefficients
    cp=M.charpoly(repr(var)+'0')
    cp=cp/cp.leading_coefficient()
    cp=[padic_expansion(i,var,1) for i in cp]

    # Construct k and p
    k2=max([cp[i][0]/(i-n) for i in range(len(cp)-1)])
    k=k2*f
    if ramify: d=k.denominator()
    else: d=1
    p=0
    val=0
    for i in range(len(cp)):
        if k2*(n-i)==-cp[i][0]:
            if p==0: val=i
            p=p+(m**(i-val))*__lift(cp[i][1][0])*var**(NN((i-val)/d))
    return (k,p.monic())


def moser_rank(M,p):
    r"""
    Computes the Moser rank of a differential system at an irreducible pole..

    Input:
        - M ... a matrix defining a first order differential system.
        - p ... an irreducible polynomial.

    Output:
        - The Moser rank of M at p.

    Algorithm:
        - Naive.

    """
    if M==0:
        # Correct?
        return Infinity
    val=matrix_valuation(M,p)
    A=__mod(M*p**(-val),p)
    return abs(val)-1+QQ(A.rank())/A.nrows()


def moser_reduction(M,p):
    r"""
    Reduces the Moser rank of a differential system at an irreducible pole to
    its minimum.

    Input:
        - M ... a matrix defining a first order differential system.
        - p ... an irreducible polynomial.

    Output:
        - A transformation such that T[M]=B, where B is as below.
        - A matrix B defining a differential system equivalent to M with minimal
          Moser rank at p. In particular, B will have minimal Poincare rank at
          p.

    Algorithm:
        - Barkatou ISSAC '95.

    """
    T=M.parent().one()
    r=moser_rank(M,p)
    shift=False
    var=M.parent().base_ring().gens()[0]
    while r>1:
        M_old=M
        T_old=T
        (T,M)=_moser_reduction(M,p,T)
        r_new=moser_rank(M,p)
        if r==r_new:
            M=M_old
            T=T_old
            break
        r=r_new
    return (T,M,r)


def residue_matrix(M,p):
    r"""
    Computes the rational residue matrix of a differential system as defined in
    Barkatou, Maddah ISSAC'15.

    Input:
        - M ... a matrix defining a first order differential system.
        - p ... an irreducible polynomial.

    Output:
        - The rational residue matrix of M at p.

    Algorithm:
        - Barkatou, Maddah ISSAC'15.

    """
    LC=padic_expansion(M,p,1)
    if LC[0]>=0:
        return M.parent().zero()
    return __lift(LC[1][0]/p.derivative())


def super_reduction(M,p,k=None):
    r"""
    Reduce the i-th generalizations of the Moser rank of M at p, as described by
    Hilali, Wazner '87, and Barkatou JCAMDI'04.

    Input:
        - M ... a matrix defining a first order differential system.
        - p ... an irreducible polynomial.
        - k ... (optional) specifies which rank should be minimized. By default,
          k will be set to the negative valuation of M at p.

    Output:
        - a transformation T such that T[M]=B, where B is as below.
        - a differential system B equivalent to M with minimal k-th generalized
          Moser rank at p. In particular. if k is equal to the negative
          valuation of M, B will be super reduced.

    Algorithm:
        - Barkatou JCAMDI'04

    """

    val=-matrix_valuation(M,p)-1
    if k==None:
        k=val
    else:
        k=min(k,val)
    T=M.parent().one()
    i=1
    while i<=k:
        (Tb,M)=_super_reduction(M,p,i)
        i=i+1
        T=T*Tb
    return (T,M)
