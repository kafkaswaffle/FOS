"""
difference
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
from .tools import padic_expansion,__lift
from .general import shearing_transformation, apply_transformation

from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ
from sage.rings.infinity import Infinity
from copy import copy

def _desingularize_shift(M,l=None):
    r"""
    Desingularizes a difference system at given poles. If no poles are
    specified, then all possible apparent singularities are removed.

    Input:
        - M ... a matrix defining a first order system.
        - l ... (optional) a list of irreducible polynomials or a single
          irreducible polynomial. If not specified, l is set to the list of all
          irreducible factors of the denominator of M.

    Output:
        - A difference system equivalent to M, desingularized at the poles in l
          (or all poles if l is None).

    Algorithm:
        - Barkatou, Jaroschek, ISSAC'18.

    """
    if l!=None:
        if not isinstance(l,list):
            l=[[l]]
        else:
            l=[[i] for i in l]
    else:
        #TODO: Problem: Factorization first will split orbits
        l=_shift_minimal_orbits(M.denominator())#sum([_shift_minimal_orbits(i[0]) for i in M.denominator().factor() if i[0].degree()>0],[])
    S=M.parent().one()
    var=M.parent().base_ring().gens()[0]
    d=M.denominator()
    for l2 in l:
        for q in l2:
            valcount=0
            oldVal=None
            while True:
                (v,RA)=padic_expansion(M,q,1)
                if oldVal==None:
                    oldVal=v
                RA=RA[0]
                if(v>=0): break
                r=RA.rank()
                T = M.parent().one()
                disp=dispersion(M.determinant().numerator(),q)
                if (disp==-Infinity): break
                A=copy(M)
                i=0
                d=d/q
                A=A*d
                qs=q
                br=False
                while True:
                    (v2,RA) = padic_expansion(A,qs,1)
                    RA=RA[0]
                    (RA,_,Ti)=RA.smith_form()
                    r2=RA.rank()
                    if v2>=0 or r2<r:
                        (S,M)=(S*T,A/d)
                        if v2>=0:
                            valcount=valcount-1
                        break
                    Ti = __lift(Ti)
                    T2i = shearing_transformation(A.parent(),r2,p=qs)
                    T = T*Ti*T2i
                    print(Ti)
                    print(T2i)
                    A=apply_transformation(A,Ti*T2i,systype=systype_s[0])
                    qs=qs.parent()(qs.subs({var:var+1}))
                    i=i+1
                    if i>disp:
                        br=True
                        break
                if br: break
            if valcount>oldVal:
                break
    return (S,M)


def _is_shift_minimal(p,q):
    r"""
    Returns true if q is a shift-minimal factor of p, i.e. if there exists no
    strictly positive integer k such that q(x-k) divides p.

    Input:
        - p ... a univariate polynomial.
        - q ... a univariate polynomial with the same parent as q.

    Output:
        - True if q is a shift-minimal factor of p, False otherwise.

    EXAMPLES:
        sage: L.<x>=PolynomialRing(QQ)
        sage: p=x*(x+1)
        sage: _is_shift_minimal(p,x)
        False
        sage: _is_shift_minimal(p,x+1)
        True
        sage: _is_shift_minimal(p,x+1/2)
        False
        sage: _is_shift_minimal(p,0)
        False
        sage: _is_shift_minimal(0,x)
        False

    Algorithm:
        - naive
    """
    if q==0 or p==0: return False
    x=q.variables()[0]
    R=PolynomialRing(q.parent().base_ring(),[repr(x)+'0'])
    L=PolynomialRing(q.parent().base_ring(),[repr(x)+'0',repr(x)])
    y=L.gens()[0]
    x=L(x)
    p=L(p)
    q=L(q)
    return p%q==0 and len([i[0] for i in R(q.subs({x:x+y}).resultant(p,x)).roots(QQ) if
             i[0].denominator()==1 and i[0]>=1])==0


def _polynomial_solutions_shift(M,N=None):
    
    (M,_,F,R,K,var)=__parent_info(M)
    systype=systype_s[0]

    # Set right hand side to zero if it is set to None
    if N==None:
        N=VectorSpace(F,M.ncols()).zero()
    if isinstance(N,sage.structure.element.Matrix):
        if N.ncols()>1:
            raise ValueError("N has to be a vector")
        N=VectorSpace(F,M.ncols())(N.columns()[0])

    # Compute the indicial polynomial
    #TODO. Not sure if M.subs({var:-1/var}) is correct, but works with current implementation of indicial_polynomial for shifts
    ip=det(indicial_matrix(M.subs({var:-1/var}).transpose(),var,systype=systype))

    # Case: indicial polynomial is zero. The system has to be made simple
    if ip==0:
        return NotImplementedError

    ip=ip.parent().change_ring(K)(ip)
    l=[-i[0] for i in ip.roots(QQ) if i[0].denominator()==1 and i[0]<=0]

    if l==[]:
        #degbound=max([R(i).degree() for i in N])+1
        degbound=max([i.numerator().degree()-i.denominator().degree() for i in N])+1
    else:
        #degbound=max(max(l),max([R(i).degree() for i in N]))+1
        degbound=max(max(l),max([i.numerator().degree()-i.denominator().degree() for i in N]))+1

    return _bounded_polynomial_solutions(M,degbound,N,systype)


def _rational_solutions_shift(M,B=None):
    raise NotImplementedError


def _shift_minimal_orbits(p):
    r"""
    #TODO: Rewrite description
    Returns a polynomial that contains all shift-minimal factors of p.

    Input:
        - p ... a univariate polynomial.

    Output:
        - A polynomial that's a product of all shift minimal factors of p
          without multiplicities.

    Algorithm:
        - naive
    """
    #TODO: Yi, Koutschan dispersion
    R0=p.parent()
    if R0.is_field():
        R0=R.base()
    var=R0.gens()[0]
    R=PolynomialRing(R0.base_ring(),[repr(var)+'0'])
    L=PolynomialRing(R0.base_ring(),[repr(var)+'0',repr(var)])
    var2=L.gens()[0]
    var=L(var)
    l=p.factor()
    orbits=[]
    for i in l:
        found=False
        for j in range(len(orbits)):
            orbit=orbits[j]
            m=max([k[0] for k in R(orbit[0][0].subs({var:var+var2}).resultant(L(i[0]),var)).roots(QQ) if k[0].denominator()==1]+[-Infinity])
            if m!=-Infinity:
                if m<0:
                    orbit.append([R0(i[0]),i[1]])
                else:
                    orbits[j]=[[R0(i[0]),i[1]]]+orbit
                found=True
                break
        if not found:
            orbits.append([[R0(i[0]),i[1]]])
    return orbits


def _super_reduction_shift(M,k):
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
    p=var
    systype=systype_s[0]
    (val,M0)=factorial_expansion(M,1)
    M0=M0[0]

    # Case: k is too small, or greater than the negative valuation, or the roots
    # of p are regular singular (or ordinary) points: there is nothing to do
    # if k<1 or k>=-val or val>=-1:
    #     return (M.parent().one(),M)

    # Order columns of M, get number of rows of order j for each j<k.
    (T,M,kRank,n,vals)=k_rank_shift(M,k,True)

    if val+k<vals[-1]:
        return (T,M)

    # Construct N such that A=p^(-val)*N*diag(I,pI,p^2*I,...)
    N=[]
    s=0
    pval=p**(-val)
    start=0
    for i in range(len(n)):
        if n[i]!=0:
            N=N+[M.columns()[start+j]*pval*p**(s) for j in range(n[i])]
            start=start+n[i]
        s=s+1
    N=MS(N).transpose()
    # Construct G
    G0=factorial_expansion(N,1)[1][0]

    R2=PolynomialRing(K,[repr(var)+'0'])
    F2=PolynomialRing(R2.fraction_field(),[repr(var)])
    F2=F2.quotient(F2(p))
    MS2=MS.change_ring(F2)
    var2=R2.gens()[0]
    h=sum(n[:-1])
    h0=h-n[-2]
    
    G=MS2(G0)+shearing_transformation(MS2,n[-1],h+1,var2+1)-MS2.one()
    # Case G0 is non-singular:
    if det(G)!=0:
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
        d=det(P2)
        P1=P1.with_rescaled_col(P1.ncols()-1,1/d)
        P2=P2.with_rescaled_col(P2.ncols()-1,1/d)
        P1=matrix([[(p**(-vals[h-1]+vals[i]) if i<h else 1) if i==j else 0 for j in range(P1.nrows())] for i in range(h1)])*P1
        I1=matrix([[1 if i==j else 0 for j in range(h1)] for i in range(h1)])
        I2=matrix([[1 if i==j else 0 for j in range(M.nrows()-h)] for i in range(M.nrows()-h)])
        Tb=block_matrix(F,3,3,[[I1,P1,0],[0,P2,0],[0,0,I2]])
        M=apply_transformation(M,Tb,1,systype=systype)
        (Tc,M)=_super_reduction_shift(M,k)
        return (T*Tb*Tc,M)

    #Case: The first h rows of G are lin. dep.
    S=G0.submatrix(0,0,h,h+n[-1])
    r=S.rank()
    if r<h:
        # Get zero rows and then multiply the columns corresponding to order vals[h-1] by p
        # Todo, actually I think S should not start at the zero column, but at the h-1 column
        #Todo: n[-2] probably wrong
        (Tb,nullrows)=__column_reduce(S.transpose(),n[-2])
        Tb=__lift(Tb)
        Tb=block_matrix(F,2,2,[[Tb,0],[matrix([[0 for j in range(Tb.ncols())] for i in range(M.nrows()-Tb.nrows())]),1]])
        Tb=Tb.transpose().inverse()
        M=apply_transformation(M,Tb,1,systype=systype)
        #TODO: Test if TB works correctly here.
        T=T*Tb
        Tb=matrix([[(p**(-vals[h-1]+vals[i]-1) if i<h and i>=h-nullrows else 1) if i==j else 0 for j in range(M.nrows())] for i in range(M.nrows())])
        M=apply_transformation(M,Tb,1,systype=systype)
        (Tc,M)=_super_reduction_shift(M,k)
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
            M=apply_transformation(M,Tb,1,systype=systype)
            (Tc,M)=_super_reduction_shift(M,k)
            return (T*Tb*Tc,M)
        else:
            # Construct shearing transformation
            Tb=MS([[0 if i!=j else p**(0 if ((i+1)>h and i+1<=M.nrows()-q) else -1) for i in range(M.nrows())] for j in range(M.nrows())])
            M=apply_transformation(M,Tb,1,systype=systype)
            (Tc,M)=_super_reduction_shift(M,k)
            return (T*Tb*Tc,M)

def k_rank_shift(M,k,details=False):
    (M,MS,_,_,_,_)=__parent_info(M)
    T=MS.one()
    systype=systype_s[0]
    
    val=-matrix_valuation(M,Infinity)

    # if val<=-1:
    #     if details:
    #         return (T,M,1,[],[])
    #     else:
    #         return 1

    n=[[] for i in range(k+1)]
    vals=[0 for i in range(M.ncols())]
    currentval=0
    for i in range(M.ncols()):
        currentval=-matrix_valuation(M.columns()[i],Infinity)
        deltaval=currentval-val
        #TODO: Correct?
        # plus minus mixup
        if deltaval==-Infinity: deltaval=Infinity
        if deltaval<k:
            n[deltaval]=n[deltaval]+[(i,currentval)]
        if deltaval>=k:
            n[k]=n[k]+[(i,currentval)]

    l=sum(n,[])
    vals=[i[1] for i in l]
    l=[i[0] for i in l]
    T=MS([[1 if i==l[j] else 0 for j in range(M.nrows())] for i in range(M.nrows())])
    M=apply_transformation(M,T,1,systype=systype)
    n=[len(i) for i in n]
    if details:
        return (T,M,-val-1+sum([QQ(n[i])/QQ(M.nrows()**(i+1)) for i in range(k)]),n,vals)
    else:
        return val+1+sum([QQ(n[i])/QQ(M.nrows()**(i+1)) for i in range(k)])


def dispersion(p,q):
    r"""
    Computes the dispersion of q in p.

    Input:
        - p ... a univariate polynomial.
        - q ... a univariate polynomial with the same parent as p.

    Output:
        - The largest integer k such that p(x) and q(x+k) have a non-constant
          gcd, or -Infinity if no such k exists.

    EXAMPLES:
        sage: L.<x>=PolynomialRing(QQ)
        sage: p=x
        sage: q=(x+3)*(x+1/2)
        sage: dispersion(p,q)
        -3
        sage: q=(x+1/2)
        sage: dispersion(p,q)
        -Infinity
        sage: dispersion(L.zero(),q)
        -Infinity
    """
    x=q.variables()[0]
    if p==0 or q==0:
        return -Infinity
    R=PolynomialRing(q.parent().base_ring(),[repr(x)+'0'])
    L=PolynomialRing(q.parent().base_ring(),[repr(x)+'0',repr(x)])
    y=L.gens()[0]
    x=L(x)
    p=L(p)
    q=L(q)
    val=max([i[0] for i in R(q.subs({x:x+y}).resultant(p,x)).roots(QQ) if i[0].denominator()==1]+[-Infinity])
    return val


def shift_minimal_part(p):
    x=p.variables()[0]
    R0=p.parent()
    R=PolynomialRing(R0.base_ring(),[repr(x)+'0'])
    L=PolynomialRing(R0.base_ring(),[repr(x)+'0',repr(x)])
    y=L.gens()[0]
    z=x
    x=L(x)
    q=L(p)
    for j in [i[0] for i in R(q.subs({x:x+y}).resultant(q,x)).roots(QQ) if i[0].denominator()==1 and i[0]!=0]:
        p=p/gcd(p,p.subs({z:z+j}))
    return p
