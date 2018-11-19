"""
fos
==================

"""


#############################################################################
#  Copyright (C) 2018                                                       #
#                Maximilian Jaroschek (maximilian@mjaroschek.com),          #
#                                                                           #
#  Distributed under the terms of the GNU General Public License (GPL)      #
#  either version 2, or (at your option) any later version                  #
#                                                                           #
#  http://www.gnu.org/licenses/                                             #
#############################################################################

from sage.rings.polynomial.polynomial_ring import PolynomialRing_general

__global_systype='d'
__global_systype_warning=True
__systype_d=['diff','d']
__systype_ad=['adj_diff','ad']
__systype_s=['shift','s']
__systype_as=['adj_shift','as']
__systype_error_string="Specify valid system type: " + repr(__systype_d[0]) + " for differential systems, " + repr(__systype_s[0]) + " for difference systems."

def __bit_count(M):
    """
    Estimate the bit size of a first order system.

    Input:
        - M ... a matrix defining a first order system.

    Output:
        - An estimate of the bit size of M.
    """
    total=0
    R=M.parent().base_ring()
    if R.is_field(): R=R.base()
    for i in M.rows():
        for j in i:
            for k in R(j.numerator()).coefficients():
                total=total+ceil(log(abs(k.numerator()),2))
                if abs(k.denominator())!=1:
                    total=total+ceil(log(abs(k.denominator()),2))
            for k in R(j.denominator()).coefficients():
                if k!=1:
                    total=total+ceil(log(abs(k.numerator()),2))
                    if abs(k.denominator())!=1:
                        total=total+ceil(log(abs(k.denominator()),2))
    return total

def __bit_count_op(p):
    """
    Estimate the bit size of an Ore operator.

    Input:
        - p ... An Ore operator

    Output:
        - An estimate of the bit size of p.
    """
    total=0
    p=p.numerator()
    R=p.parent().base_ring()
    if R.is_field(): R=R.base()
    for i in p.coefficients():
        for j in R(i).coefficients():
            total=total+ceil(log(abs(j.numerator()),2))
            if abs(j.denominator())!=1:
                total=total+ceil(log(abs(j.denominator()),2))
    return total

def __column_reduced_form(M,k):
    B=M.submatrix(0,k,M.nrows(),M.ncols()-k)
    T=B.smith_form()[2]
    c=[]
    for i in range(M.nrows()):
        if i<k:
            c.append([1 if i==j else 0 for j in xrange(M.ncols())])
        else:
            row=T.rows()[i-k]
            c.append([(1 if i==j else 0) if j<k else row[j-k] for j in xrange(M.ncols())])
    return M.parent()(c)

def __lift(M):
    """
    Lift all entries of a matrix or vector from a quotient ring to the ambient ring.

    Input:
        - M ... a matrix or vector with entries in a quotient ring.

    Output:
        - A matrix whose entries are the entries of M lifted to the ambient ring of their parent ring.
    """

    if isinstance(M,sage.matrix.matrix_generic_dense.Matrix_generic_dense):
        return matrix([[i.lift() for i in j] for j in M])
    else:
        return vector([i.lift() for i in M])

def __mod(M,p):
    """
    Reduces all entries of a matrix or vector modulo an irreducible polynomial.

    Input:
        - M ... a matrix or vector with rational function entries.
        - p ... an irreducible polynomial.

    Output:
        - A matrix whose entries are the entries of M modulo p.
    """
    R=p.parent()
    if R.is_field():
        R=R.base()
        p=R(p)
    R=p.parent().quotient(p)
    MS=M.parent().change_ring(R)
    if isinstance(M,sage.matrix.matrix_generic_dense.Matrix_generic_dense):
        return MS([[((j.numerator()%p)*(R(j.denominator())**(-1)).lift())%p for j in i] for i in M])
    else:
        return MS([((i.numerator()%p)*(R(i.denominator())**(-1)).lift())%p for i in M])

def __systype_fallback():
    """
    Return a valid systype and possibly print a warning message. Raises an error if no valid global systype is set.

    Output:
        - The global systype.
    """
    if __global_systype==None or not (__global_systype in __systype_d or __global_systype in __systype_s):
        raise ValueError, __systype_error_string
    if __global_systype_warning:
        print "Interpreting as default type: " + repr(__global_systype)
    return __global_systype

def __valuation(M,p):
    """
    Computes the order of an irreducible polynomial in a matrix or vector.

    Input:
        - M ... a matrix or vector with rational function entries.
        - p ... an irreducible polynomial.
    """
    if isinstance(M,sage.matrix.matrix_generic_dense.Matrix_generic_dense):
        return min([min([i.valuation(p) for i in j]) for j in M])
    else:
        return min([i.valuation(p) for i in M])

def _cyclic_vector(M,d,j,k,addDiag,systype=None):
    """
    Computes a cyclic vector for a given first order system.

    Input:
        - M ... a matrix defining a first order system.
        - systype ... a string specifying whether the system is a system of differential or difference equations. Can be either 'shift' or 'diff'.
        - d ... the max. degree of the components of the output vector.
        - j ... the max. number of non-zero components of the output vector.
        - k ... the number of tries to find a cyclic vector. If k=0, then a MonteCarloExcpetion is raised.

    Output:
        - c ... a cyclic vector for the given system.
        - T ... a matrix with with columns of the form \partial^i*c, where \partial is the pseudo-linear map associated to the input system.
    """
    if systype==None: systype=__systype_fallback()

    R=M.parent().base_ring()
    var=R.gens()[0]
    while k>0:
        v=M.parent().row_space()([R.random_element(d) if i <=j else 0 for i in xrange(M.nrows())])
        A=[v]
        op=operator(M,systype)
        for i in xrange(1,M.nrows()):
            if addDiag:
                A.append(op(A[-1])+A[-1])
            else:
                A.append(op(A[-1]))
        A=M.parent()(A)
        if A.rank()==A.nrows(): return (v,A.transpose())
        else:
            if j==M.nrows():
                d=d+1
            j=(j+1)%M.nrows()
            k=k-1
    raise MonteCarloException, "Could not find a cyclic vector."

def _desingularize_diff(M,l=None):
    """
    Desingularize a differential system at a certain poles. Uses the Barkatou-Maddah desingularization algorithm. If no poles are given, then all possible apparent singularities are removed.

    Input:
        - M ... a matrix defining a first order system.
        - l ... a list of irreducible polynomials or a single irreducible polynomial.

    Output:
        - A differential system equivalent to M, desingularized at the poles in l (or all poles if l is None)
    """
    if l!=None and not isinstance(l,list):
        l=[l]
    else:
        l=[i[0] for i in M.denominator().factor() if i[0].degree()>0]
    L=M.base_ring().base()
    var=L.gens()[0]
    T=M.parent().one()
    for p in l:
        (Tb,M,r)=moser_reduction(M,p)
        if r>1:
            continue
        T=T*Tb
        Mr=residue_matrix(M,p)
        c=charpoly(Mr,repr(var)+"0")
        var2=c.parent().gens()[0]
        R=PolynomialRing(PolynomialRing(L.base(),[repr(var2)]),[repr(var)])
        R2=PolynomialRing(L.base(),[repr(var2),repr(var)])
        c=R(R2(c.numerator()))
        g=reduce(lambda u,v:u.gcd(v),c.coefficients())
        ev=[i for i in g.roots(QQ) if i[0].denominator()==1 and i[0]>=0]
        # If the Eigenvalues are not all non-negative integers...
        if g==1 or sum([i[1] for i in ev])!=g.degree():
            continue
        total=0
        for i in ev:
            total=total+i[1]
            for j in range(i[0]):
                Tb=Mr.jordan_form(transformation=True)[1]
                T=T*Tb
                M=apply_transformation(M,Tb,__systype_d[0])
                Tb=shearing_transformation(M.parent(),total,p=p)
                T=T*Tb
                M=apply_transformation(M,Tb,__systype_d[0])
    return (T,M)

def _desingularize_shift(M,l=None):
    """
    Desingularize a difference system at a certain poles. Uses the Barkatou-Jaroschek desingularization algorithm. If no poles are given, then all possible apparent singularities are removed.

    Input:
        - M ... a matrix defining a first order system.
        - l ... a list of irreducible polynomials or a single irreducible polynomial.

    Output:
        - A difference system equivalent to M, desingularized at the poles in l (or all poles if l is None)
    """
    if l!=None:
        if not isinstance(l,list):
            l=[[l]]
        else:
            l=[[i] for i in l]
    else:
        l=sum([_shift_minimal_orbits(i[0]) for i in M.denominator().factor() if i[0].degree()>0],[])
    S=M.parent().one()
    var=M.parent().base_ring().gens()[0]
    d=M.denominator()
    for l2 in l:
        for q in l2:
            valcount=0
            oldVal=None
            while true:
                (v,RA)=padic_expansion(M,q,1)
                if oldVal==None:
                    oldVal=v
                RA=RA[0]
                if(v>=0): break
                r=rank(RA)
                T = M.parent().one()
                disp=dispersion(M.determinant().numerator(),q)
                if (disp==-Infinity): break
                A=copy(M)
                i=0
                d=d/q
                A=A*d
                qs=q
                br=false
                while true:
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
                    A=apply_transformation(A,Ti*T2i,__systype_s[0])
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
    """
    Returns true if q is a shift-minimal factor of p.
    """
    x=q.variables()[0]
    R=PolynomialRing(q.parent().base_ring(),[repr(x)+'0'])
    L=PolynomialRing(q.parent().base_ring(),[repr(x)+'0',repr(x)])
    y=L.gens()[0]
    x=L(x)
    p=L(p)
    q=L(q)
    return p%q==0 and len([i[0] for i in R(q.subs({x:x+y}).resultant(p,x)).roots(QQ) if
             i[0].denominator()==1 and i[0]>=1])==0

def _moser_reduction(M,p,T=None):
    """
    Rational version of Moser Reduction as described by Barkatou.
    """
    #Helper function to find an appropriate left kernel vector
    def __left_kernel_vector(G):
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
            for i in xrange(len(v)-1,-1,-1):
                if v[i]!=0:
                    T=copy(T).with_swapped_rows(i,len(v)-1)
                    break
        v=T*v
        #Normalize last entry.
        if v[-1]!=1:
            v=1/v[-1]*v
        return (T,v)

    #If moser rank is <= 1, then there is nothing to do
    mr=moser_rank(M,p)
    if T==None:
        T=M.parent().one()
    while True:
        if mr<=1: return (T,M)
        #Test if leading coefficient matrix is in column reduced form. If not, apply transformation.
        A=padic_expansion(M,p,2)[1]
        r=A[0].rank()
        (A11,A12,A21,A22)=(A[0].submatrix(0,0,r,r),A[0].submatrix(0,r,nrows=r),A[0].submatrix(r,0,ncols=r),A[0].submatrix(r,r))
        (B12,B22)=(A[1].submatrix(0,r,nrows=r),A[1].submatrix(r,r))
        R=M.parent().base()
        if (R.is_field()): R=R.base()
        if not (A12==A12.parent().zero() and A22==A22.parent().zero()):
            Tb=__lift(A[0].smith_form()[2])
            M=apply_transformation(M,Tb,__systype_d[0])
            T=T*Tb
            continue
        # See if Proposition 1 applies
        if block_matrix(1,2,[A11,B12]).rank()<r:
            Tb=shearing_transformation(M.parent(),r,1,p)
            Mb=apply_transformation(M,Tb,__systype_d[0])
            if moser_rank(Mb,p)<mr: return (T*Tb,Mb)
            return (T,M)
        else:
            # Construct G and determine h
            x=R.gens()[0]
            R2=PolynomialRing(A11.parent().base_ring(),[repr(x)+'0'])
            y=R2.gens()[0]
            G=block_matrix(2,2,[A11,B12,A21,B22+y*B22.parent().one()])
            h=1
            while (G[-h][-h]==y and G.columns()[-h][-h:][1:]==0 and G.rows()[-h][:-h]==0):
                h=h+1
            h=h-1
            # See if Proposition 2 applies
            if (G.submatrix(0,0,r,M.nrows()-r-h).rank()<r):
                Tb=shearing_transformation(M.parent(),r,p=p)*shearing_transformation(M.parent(),h,M.nrows()-h+1,p=p)
                Mb=apply_transformation(M,Tb,__systype_d[0])
                if moser_rank(Mb,p)<mr: return (T*Tb,Mb)
                return (T,M)
            else:
                if h>0:
                    Gh = G.submatrix(0,0,G.nrows()-h,M.nrows()-h)
                    (Tb,v)=__left_kernel_vector(Gh)
                    if Tb==None:
                        return (T,M)
                    v=vector([v[i] if i<len(v) else 0 for i in xrange(G.nrows())])
                    Tc=copy(M.parent().one())
                    Tc.set_block(0,0,Tb)
                    Tb=Tc
                    Tl=matrix([[1 if j==i else 0 for j in xrange(M.nrows())] if i!=G.nrows()-h-1 else v for i in xrange(M.nrows())])
                    Tb=(Tl*Tl.parent()(Tb).inverse()).inverse()
                    M=apply_transformation(M,Tb,__systype_d[0])
                    T=T*Tb
                    continue

                # Apply construction from Proposition 3
                # Find left kernel vector with last entry non-zero. Swap rows if necessary.
                G0=block_matrix(2,2,[A11,B12,A21,B22])
                (Tb,v)=__left_kernel_vector(G0)
                if Tb==None:
                        return (T,M)
                # Construct transformation
                Tl=matrix([[1 if j==i else 0 for j in xrange(M.nrows())] if i!=M.nrows()-1 else v for i in xrange(M.nrows())])
                Tb=(Tl*Tl.parent()(Tb).inverse()).inverse()
                M=apply_transformation(M,Tb,__systype_d[0])
                T=T*Tb

from ore_algebra.nullspace import *
def _polynomial_solutions_diff(M,N=None,recomb=True):
    """
    Computes all polynomial solutions of the pseudo linear system of differential type with matrix M and right hand side N.

    Input:
        - M ... a matrix defining a first order system.
        - N ... a vector whose length is equal to the number of columns in M with rational function entries.

    Output:
        - sol: A basis for the solutions of the homogeneous pseudo linear system of differential type defined by M with polyomial entries.
        - special: One solution for the inhomogeneous pseudo linear system of differential type defined by M and N with polynomial entries.
    """

    # Set right hand side to zero if it is set to None
    if N==None:
        N=VectorSpace(M.parent().base_ring(),M.parent().ncols()).zero()

    R=M.parent().base_ring()
    if R.is_field:
        R=R.base()
    var=R.gens()[0]

    # Compute the indicial polynomial
    ip=det(indicial_matrix(infinity_to_zero(M,systype=__systype_d[0]),x,systype=__systype_d[0]))
    if ip==0:
        # If the indicial polynomial is zero, the system has to be made simple
        print "Non-simple system at " + repr(Infinity) + ". Performing reduction."
        MR=super_reduction(adjoint(infinity_to_zero(M,systype=__systype_d[0]),systype=__systype_d[0]),x,adjoint=True)
        T=MR[0].subs({var:1/var}).transpose().inverse()
        M=adjoint(infinity_to_zero(MR[1],systype=__systype_d[0]),systype=__systype_d[0])
        # Super reducing does not preserve polynomial solutions. So computing rational solutions.
        (sol,special)=rational_solutions(M,T.inverse()*N,systype=__systype_d[0])
        sol=[T*i for i in sol]
        special=T*special
        # Recombine the found solutions to remove the denominator
        if recomb and len(sol)>0:
            sol.append(special)
            d=reduce(lambda x,y:x.lcm(y.denominator()), sol,sol[0].denominator())
            M2=matrix([[R(d*i)%d for i in j] for j in sol]).transpose()
            rels=hermite()(M2,degrees=[0])
            M2=matrix(sol).transpose()
            sol=[]
            specrel=0
            for i in rels:
                if i[-1]==0:
                    sol.append(M2*i)
                else:
                    if specrel!=0:
                        c=i[-1]
                        sol.append(M2*(i/c-specrel))
                    c=i[-1]
                    special=M2*(i/c)
                    specrel=i/c
        return [sol,special]
    # Compute the degree bound
    ip=ip.parent().change_ring(R.base_ring())(ip)
    l=[-i[0] for i in ip.roots(QQ) if i[0].denominator()==1 and i[0]<=0]
    if len(l)==0:
        return [[],[]]
    den=N.denominator().lcm(M.denominator())
    N=den*N
    d=max(max(l),max([R(i).degree() for i in N]))
    op=operator(M,systype=__systype_d[0])
    # Set up the equations and clear denominators
    eqs=block_matrix(1,d+1,[op(var**i) for i in range(d,-1,-1)])
    eqs=block_matrix(1,2,[den*eqs,matrix(-N).transpose()])
    eqs=eqs.parent().change_ring(R)(eqs)
    sol=[]
    special=vector([0 for i in xrange(M.ncols())])
    # Compute the solutions as vectors with entries in Q, compress them to vectors with polynomial entries
    for i in hermite()(eqs,degrees=[0]):
        v=i[:-1]        
        l=[0 for j in range(M.ncols())]
        for k in range(d+1):
            for j in range(M.ncols()):
                l[j]=l[j]+var**(d-k)*v[k*M.ncols()+j]
        if i[-1]!=0:
            if special!=0:
                sol.append(special-vector(l)/i[-1])
            else:
                special=vector(l)/i[-1]
        else:
            sol.append(vector(l))
    return [sol,special]

def _polynomial_solutions_shift(M,N=None):
    pass

def _rational_solutions_diff(M,B=None):
    """
    Computes all rational solutions of the pseudo linear system of differential type with matrix M and right hand side N.

    Input:
        - M ... a matrix defining a first order system.
        - N ... a vector whose length is equal to the number of columns in M with rational function entries.

    Output:
        - sol: A basis for the solutions of the homogeneous pseudo linear system of differential type defined by M with rational function entries.
        - special: One solution for the inhomogeneous pseudo linear system of differential type defined by M and N with rational function entries.
    """

    # Set right hand side to zero if it is set to None
    if B==None:
        B=VectorSpace(M.parent().base_ring(),M.parent().ncols()).zero()

    R=M.parent().base_ring()
    if R.is_field():
        R=R.base()
    var=R.gens()[0]
    R2=PolynomialRing(R.base_ring(),[repr(var)+'0'])

    d1=M.denominator()
    shifts=0
    while d1%var==0:
        M=M.subs({var:var+1})
        B=B.subs({var:var+1})
        d1=d1.subs({var:var+1})
        shifts=shifts+1
    d2=B.denominator()
    d2=(d2/gcd(d2,d1))
    d2=gcd(d2,diff(d2))
    d1=[i[0] for i in d1.factor()]
    f=[0 for i in d1]
    ip=det(indicial_matrix(M,d1[0],systype=__systype_d[0]))
    var2=ip.parent().gens()[0]
    R2=PolynomialRing(PolynomialRing(L.base(),[repr(var2)]),[repr(var)])
    R3=PolynomialRing(L.base(),[repr(var2),repr(var)])
    ip=R2(R3(ip))
    g=reduce(lambda u,v:u.gcd(v),ip.coefficients())
    m=min([j[0] for j in g.roots(QQ) if j[0].denominator()==1])
    f[0]=min(1+__valuation(B,d1[0]),m)
    for i in xrange(1,len(d1)):
        ip=R2(R3(det(indicial_matrix(M,d1[i],systype=__systype_d[0]))))
        while ip==0:
            print "Non-simple system at " + repr(d1[i]) + ". Performing reduction."
            (Tb,M)=super_reduction(M,d1[i])
            ip=R2(R3(det(indicial_matrix(M,d1[i],systype=__systype_d[0]))))
        g=reduce(lambda u,v:u.gcd(v),ip.coefficients())
        m=min([Infinity]+[j[0] for j in g.roots(QQ) if j[0].denominator()==1])
        f[i]=min(1+__valuation(B,d1[i]),m)
    denom=R.fraction_field()(product([d1[i]**f[i] if f[i]<Infinity else 1 for i in xrange(len(d1))]))
    denom=denom/d2
    T=shearing_transformation(M.parent(),M.nrows(),p=denom)
    M=apply_transformation(M,T,__systype_d[0])
    B=T.inverse()*B
    (sol,special)=_polynomial_solutions_diff(M,B,recomb=False)
    denom=denom.subs({var:var-shifts})
    return [[i.subs({var:var-shifts})*denom for i in sol], denom*special.subs({var:var-shifts})]

def _rational_solutions_shift(M,B=None):
    pass

def _shift_minimal_orbits(p):
    """
    Returns a polynomial that contains all shift-minimal factors of p.

    Input:
        - p ... a univariate polynomial.

    Output:
        - A polynomial that's a product of all shift minimal factors of p without multiplicities.
    """
    R0=p.parent()
    if R0.is_field():
        R0=R.base()
    f=R0.one()
    p=R0(p/gcd(p,diff(p)))
    x=R0.gens()[0]
    R=PolynomialRing(R0.base_ring(),[repr(x)+'0'])
    L=PolynomialRing(R0.base_ring(),[repr(x)+'0',repr(x)])
    y=L.gens()[0]
    x=L(x)
    p=L(p)
    l=[i[0] for i in R(p.subs({x:x+y}).resultant(p,x)).roots(QQ) if
       i[0].denominator()==1 and i[0]>=0]
    res=[]
    while len(l)>0:
        d=max(l)
        l.remove(d)
        q=p.subs({x:x+d}).gcd(p)
        p=p.parent()(p/q)
        if q!=1:
            l2=[R0(q)]
            for i in l:
                q2=q.subs({x:x-d+i})
                (p2,r)=p.quo_rem(q2)
                if r==0:
                    p=p2
                    l2.append(R0(q2))
            res.append(l2)
    return res

def super_reduction(M,p,k=None,adjoint=False):
    val=-__valuation(M,p)-1
    if k==None:
        k=val
    else:
        k=min(k,val)
    T=M.parent().one()
    i=1
    while i<=k:
        (Tb,M)=_super_reduction(M,p,i,adjoint)
        if i==1:
            val=-__valuation(M,p)-1
            k=val
        i=i+1
        T=T*Tb
    return (T,M)

def _super_reduction(M,p,k,adjoint=False):
    def __left_kernel_vector(G):
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
            for i in xrange(len(v)-1,-1,-1):
                if v[i]!=0:
                    T=copy(T).with_swapped_rows(i,len(v)-1)
                    break
        v=T*v
        # Normalize last entry.
        if v[-1]!=1:
            v=1/v[-1]*v
        return (T,v)

    if adjoint:
        systype=__systype_ad[0]
    else:
        systype=__systype_d[0]
    R=M.parent().base_ring()
    L=padic_expansion(M,p,1)
    if k>=-L[0]: return (M.parent().one(),M)
    Ta=__lift(L[1][0].smith_form()[2])
    M=apply_transformation(M,Ta,systype)
    A=M
    L=padic_expansion(A,p,1)
    N=L[1][0]
    n=N.rank()
    n0=n
    ns=[0 for i in range(k+1)]
    ns[0]=n0
    T=Ta.parent().one()
    val=L[0]
    b=val+k
    i=0
    
    while  i<k:
        if n==M.ncols(): break
        Tb=shearing_transformation(A.parent(),n0,n-n0+1,p**(-L[0]+1))
        A=A*Tb
        L=padic_expansion(A,p,1)
        if L[0]>=b:
            n0=M.nrows()-n
        else:
            n0=L[1][0].rank()
        i=min(L[0]-val,k)
        ns[i]=n0
        n=n+n0
        if L[0]>b: break
        Tb=__lift(__column_reduced_form(L[1][0],n))
        T=T*Tb
        A=apply_transformation(A,Tb,systype)
        L=padic_expansion(A,p,1)
        N=N.parent()(Tb).inverse()*N*N.parent()(Tb)+L[1][0]

    M=apply_transformation(M,T,systype)
    T=Ta*T
    R2=PolynomialRing(N.parent().base_ring(),[repr(x)+'0'])
    MS=M.parent().change_ring(R2.fraction_field())
    y=R2.gens()[0]
    G=N+shearing_transformation(MS,ns[-1],M.nrows()-ns[-1]+1,y+1)-N.parent().one()
    if det(G)!=0:
        return (T,M)
    else:
        n0=n-ns[-1]
        n1=n0-ns[-2]
        P=matrix(G.submatrix(0,0,M.nrows(),n0).right_kernel().basis()).transpose()
        if P.rows()!=[]:
            P=P.parent().change_ring(R)([[j.parent().base()(j).coefficients()[0].lift() for j in i] for i in P.rows()])
            P1=P.submatrix(0,0,n1,P.ncols())
            P2=P.submatrix(n1,0,ns[-2],P.ncols())
            d=det(P2)
            if d!=1:
                P1=P1.with_rescaled_col(0,1/d)
                P2=P2.with_rescaled_col(0,1/d)
            s=0
            for i in range(len(ns[:-2])):
                for j in range(ns[i]):
                    P1=P1.with_rescaled_row(s+j,p**(k-1-i))
                s=s+ns[i]
            if n1>1:
                Tb=block_matrix(3,3,[[matrix([[1 if i==j else 0 for j in xrange(n1)] for i in xrange(n1)]),P1,matrix([[0 for j in range(ns[-1])] for i in range(ns[-1])])],[matrix([[0 for j in range(n1)] for i in range(P2.ncols())]),P2,matrix([[0 for j in range(ns[-1])] for i in range(P2.ncols())])],[matrix([[0 for j in range(n1)] for i in range(ns[-1])]),matrix([[0 for j in range(P1.ncols())] for i in range(P1.nrows())]),matrix([[1 if i==j else 0 for j in xrange(ns[-1])] for i in xrange(ns[-1])])]])
            else:
                Tb=block_matrix(2,2,[[matrix([[1 if i==j else 0 for j in xrange(n1)] for i in xrange(n1)]),P1],[matrix([[0 for j in range(n1)] for i in range(P2.ncols())]),P2]])
            T=T*Tb
            M=apply_transformation(M,Tb,systype)
            (Tb,M)=_super_reduction(M,p,k,adjoint)
            return (T*Tb,M)
        r=G.submatrix(0,0,G.nrows(),n0).rank()
        if G.submatrix(0,0,n0,G.ncols()).rank()<r:
            Tb=copy(M.parent().one())
            s=0
            for i in range(len(ns[:-1])):
                for j in range(ns[i]):
                    Tb=Tb.with_rescaled_row(s+j,p**(k-i))
                s=s+ns[i]
            M=apply_transformation(M,Tb,systype)
            T=T*Tb
            (Tb,M)=_super_reduction(M,p,k,adjoint)
            return (T*Tb,M)
        y=R2.gens()[0]
        h=1
        while (G[-h][-h]==y and G.columns()[-h][-h:][1:]==0 and G.rows()[-h][:-h]==0):
            h=h+1
        h=h-1
        if (G.submatrix(0,0,M.nrows()-h,M.nrows()-h)(y=0).subs({y:0}).rank()<r):
            Tb=shearing_transformation(M.parent(),r,p=p)*shearing_transformation(M.parent(),h,M.nrows()-h+1,p=p)
            Mb=apply_transformation(M,Tb,systype)
            T=T*Tb
            (Tb,M)=_super_reduction(M,p,k,adjoint)
            return (T*Tb,M)
        else:
            if h==0:
                G0=G.subs({y:0})
                (Tb,v)=__left_kernel_vector(G0)
                if Tb==None:
                    return (T,M)
                Tl=matrix([[1 if j==i else 0 for j in xrange(M.nrows())] if i!=M.nrows()-1 else v for i in xrange(M.nrows())])
                Tb=(Tl*Tl.parent()(Tb).inverse()).inverse()
                M=apply_transformation(M,Tb,systype)
                T=T*Tb
                (Tb,M)=_super_reduction(M,p,k,adjoint)
                return (T*Tb,M)
            else:
                Tb=shearing_transformation(M.parent(),n0,p=p)
                M=apply_transformation(M,Tb,systype)
                T=T*Tb
                (Tb,M)=_super_reduction(M,p,k,adjoint)
                return (T*Tb,M)

def annihilating_system(r,systype=None):
    """
    Computes an annihilating first order system for a rational function.

    Input:
        - r ... A rational function in one variable.
        - systype ...... a string specifying whether the system is a system of differential or difference equations. Can be either 'shift' or 'diff'.

    Output:
        - A matrix of differential or difference type whose associtated pseudo linear operator annihilates r.
    """
    if systype==None: systype=__systype_fallback()

    var=r.parent().gens()[0]
    if systype in __systype_s:
        return matrix([[r.subs({var:var+1})/r]])
    elif systype in __systype_d:
        return matrix([[diff(r,var)/r]])
    else: raise ValueError, __systype_error_string

def apply_transformation(M,T,systype=None):
    """
    Applies a basis transformation to a first order system.

    Input:
        - T ... a matrix defining a basis transformation
        - M ... a matrix defining a first order system.
        - systype ... a string specifying whether the system is a system of differential or difference equations. Can be either 'shift' or 'diff'.

    Output:
        - The defining matrix of the transformed system
    """
    if systype==None: systype=__systype_fallback()

    if systype in __systype_s:
        var=M.parent().base_ring().gens()[0]
        return T.inverse().substitute({var:var+1})*M*T
    elif systype in __systype_as:
        var=M.parent().base_ring().gens()[0]
        return T.inverse().substitute({var:var-1})*M*T
    elif systype in __systype_d:
        return T.inverse()*(M*T-T.parent()(diff(T)))
    elif systype in __systype_ad:
        return T.inverse()*(M*T+T.parent()(diff(T)))
    else: raise ValueError, __systype_error_string

def cyclic_vector(M,addDiag=False,systype=None):
    """
    Computes a cyclic vector for a given first order system. Acts as a wrapper for _cyclic_vector(M,systype,d,j,k)

    Input:
        - M ... a matrix defining a first order system.
        - systype ... a string specifying whether the system is a system of differential or difference equations. Can be either 'shift' or 'diff'.

    Output:
        - c ... a cyclic vector for the given system.
        - T ... a matrix with with columns of the form \partial^i*c, where \partial is the pseudo-linear map associated to the input system.
    """
    return _cyclic_vector(M,0,0,20,addDiag,systype)

def desingularize(M,l=None,systype=None):
    """
    Desingularize M completely or at a given pole.
    """
    if systype==None: systype=__systype_fallback()

    if systype in __systype_s:
        return _desingularize_shift(M,l)
    elif systype in __systype_d:
        return _desingularize_diff(M,l)
    else: raise ValueError, __systype_error_string

def dispersion(p,q):
    """
    Computes the dispersion of q in p.
    """
    x=q.variables()[0]
    R=PolynomialRing(q.parent().base_ring(),[repr(x)+'0'])
    L=PolynomialRing(q.parent().base_ring(),[repr(x)+'0',repr(x)])
    y=L.gens()[0]
    x=L(x)
    p=L(p)
    q=L(q)
    val=max([i[0] for i in R(q.subs({x:x+y}).resultant(p,x)).roots(QQ) if i[0].denominator()==1]+[-Infinity])
    return val

def adjoint(M,systype=None):
    if systype==None: systype=__systype_fallback()

    if systype in __systype_d:
        return M.transpose()
    elif systype in __systype_s:
        var=M.parent().base_ring().gens()[0]
        return M.subs({var:var-1}).transpose()
    else: raise ValueError, __systype_error_string

def indicial_matrix(M,p,systype=None):
    if systype==None: systype=__systype_fallback()

    R=M.parent().base_ring()
    if R.is_field():
        R=R.base()
    var=R.gens()[0]
    D=matrix([[var**(-min(1+__valuation(M.rows()[i], p),0)) if i==j else 0 for i in xrange(M.nrows())] for j in xrange(M.nrows())])
    A=(p/diff(p)*D*M)
    A0=padic_expansion(A,p,1)
    D0=padic_expansion(D,p,1)
    A0=__lift(A0[1][0]) if A0[0]==0 else A.parent().zero()
    D0=__lift(D0[1][0]) if D0[0]==0 else D.parent().zero()
    R2=PolynomialRing(R,[repr(var)+'0'])
    MS=A0.parent().change_ring(R2)
    A0=MS(A0)
    D0=MS(D0)
    var2=R2.gens()[0]
    return var2*D0-A0

def infinity_to_zero(M,systype=None):
    """
    Performs the substitution x->1/x to move the point at infinity to zero.

    Input:
        - M ... a matrix defining a first order system.
        - systype ... a string specifying whether the system is a system of differential or difference equations. Can be either 'shift' or 'diff'.
    """
    if systype==None: systype=__systype_fallback()

    if systype in __systype_d:
        var=M.parent().base_ring().gens()[0]
        return -1/var**2*M.subs({var:1/var})
    elif systype in __systype_s:
        raise NotImplementedError
    else: raise ValueError, __systype_error_string

def is_fuchsian(M):
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
        return (False, Infinity,r)
    return (True,(T,M))

def is_valid_system(M,checkRank=True):
    """
    Checks if a sage object defines a first order system that admits the necessary properties for the algorithms provided in the FOsystem package. Raises a ValueError if the conditions are not met.

    Input:
        - M ... a sage object.
        - checkRank ... (optional) if 'true', a check is performed if M is non-singular.

    Output:
    - 'True' if the input object is a (non-singular) square matrix with entries in (the fraction field of) a polynomial ring over a field of characteristic zero. Otherwise a ValueError is raised.
    """
    MS=M.parent()
    if not isinstance(MS,MatrixSpace):
        raise ValueError, "Parent of input system must be a matrix space."
    if not M.is_square():
        raise ValueError, "Input matrix has to be square."
    R=MS.base_ring()
    if R.is_field(): R=R.base()
    if not isinstance(R, PolynomialRing_general):
        raise ValueError, "Ground ring must be a polynomial ring or a rational function field."
    if not len(R.gens())==1:
        raise ValueError, "Ground ring must be univariate."
    K=R.base()
    if not QQ<=K:
        raise ValueError, "Constant field has to be an extension of the rational numbers."
    if checkRank:
        if not M.rank()==M.nrows():
            raise ValueError, "Input matrix has to be non-singular."
    return true

def lcmatrix(M,p):
    """
    Returns the leading coefficient matrix in the q-adic expansion of M.
    """
    return padic_expansion(M,p,1)[1][0]

def moser_rank(M,p):
    """
    Compute the Moser rank of M at p.
    """
    if M==0:
        return Infinity
    val=__valuation(M,p)
    A=__mod(M*p**(-val),p)
    return abs(val)-1+QQ(A.rank())/A.nrows()

def k_rank(M,p,k):
    if M==0:
        return Infinity
    val=__valuation(M,p)
    r=abs(val)-1
    As=[[] for i in range(k)]
    for i in range(M.ncols()):
        cval=__valuation(M.columns()[i],p)
        if cval<val+k:
            As[cval-val].append(M.columns()[i])
    n=1
    for i in range(k):
        n=n*M.nrows()
        if As[i]!=[]:
            r=r+QQ(padic_expansion(matrix(As[i]),p,1)[1][0].rank())/n
    return r
    
def moser_reduction(M,p):
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

def operator(M,systype=None):
    if systype==None: systype=__systype_fallback()

    var=M.parent().base_ring().gens()[0]
    if systype in __systype_s:
        return lambda x: (M*x -x.subs({var:var+1})).subs({var:var-1})
    elif systype in __systype_as:
        return lambda x: (M*x -x.subs({var:var-1})).subs({var:var+1})
    elif systype in __systype_d:
        return lambda x: M*x - diff(x,var)
    elif systype in __systype_ad:
        return lambda x: M*x + diff(x,var)
    else: raise ValueError, __systype_error_string

def padic_expansion(M,p,k):
    val=__valuation(M,p)
    if val==Infinity:
        return (val,[__mod(M,p)])
    A=M*p**(-val)
    l=[0 for i in xrange(k)]
    for i in xrange(k):
        A0=__mod(A,p)
        l[i]=A0
        if i<k: A=(A-__lift(A0))/p
    return (val,l)

def polynomial_solutions(M,rhs=None,systype=None):
    if systype==None: systype=__systype_fallback()

    if systype in __systype_d:
        return _polynomial_solutions_diff(M,rhs)
    elif systype in __systype_s:
        raise NotImplementedError
    else: raise ValueError, __systype_error_string

def rational_solutions(M,rhs=None,systype=None):
    if systype==None: systype=__systype_fallback()

    if systype in __systype_d:
        return _rational_solutions_diff(M,rhs)
    elif systype in __systype_s:
        raise NotImplementedError
    else: raise ValueError, __systype_error_string

def are_equivalent(M1,M2):
    pass

def residue_matrix(M,p):
    """
    Returns the rational residue matrix of a differential system.
    """
    return __lift(lcmatrix(M,p)/diff(p))

def set_global_systype(systype,warning=True):
    systype=systype.lower()
    if systype in __systype_d:
        print "All systems will now be interpretet as differential systems."
    elif systype in __systype_s:
        print "All systems will now be interpretet as difference systems."
    else:
        raise ValueError, __systype_error_string
    global __global_systype
    global __global_systype_warning
    __global_systype=systype
    __global_systype_warning=warning

def shearing_transformation(MS,length,start=1,p=None):
    """
    Constructs a shearing transformation.
    """
    start=start-1
    length=length-1
    if p==None:
        p=MS.base_ring().gens()[0]
    return MS([[0 if i!=j else (p if (i>=start and i-start<=length) else 1) for j in xrange(MS.nrows())] for i in xrange(MS.nrows())])

def split_system(M):
    pass

def to_first_order_system(p):
    """
    Compute a first order system corresponding to an Ore operator.

    Input:
        - p ... an Ore operator.

    Output:
        - The transposed companion matrix of p.
    """
    return companion_matrix(p.monic()).transpose()

def to_scalar_operator(M,systype=None):
    """
    Computes a scalar operator corresponding to a given first order system.

    Input:
        - M ... a matrix defining a first order system.
        - systype ... a string specifying whether the system is a system of differential or difference equations. Can be either 'shift' or 'diff'. Alternatively, it can be either a shift or a differential Ore algebra.

    Output:
        - An Ore operator whose transposed companion matrix is equivalent to the input matrix.
        - The transformation used to bring the system into companion form
    """
    if systype==None: systype=__systype_fallback()

    if isinstance(systype,str):
        R=M.parent().base_ring()
        if systype in __systype_d:
            pre='D'
        elif systype in __systype_s:
            pre='S'
        else:
            raise ValueError, __systype_error_string
        var=pre+repr(R.gens()[0])
        ore=OreAlgebra(R,var)
    else:
        ore=systype
        
    K=M.parent().base_ring()
    if ore.is_D()==K.gens()[0]:
        dM=adjoint(M,__systype_d[0])
        T=cyclic_vector(dM,systype=__systype_ad[0])[1]
        l=(apply_transformation(dM,T,
                                __systype_ad[0])).columns()[-1]
        D=ore.gen()
        return (sum([l[i]*D**i for i in xrange(len(l))])-D**len(l),T.transpose().inverse())
    elif ore.is_S()==K.gens()[0]:
        dM=adjoint(M,__systype_s[0])
        T=cyclic_vector(dM,addDiag=True,systype=__systype_as[0])[1]
        l=(apply_transformation(dM,T,
                                __systype_as[0])).columns()[-1]
        D=ore.gen()
        var=R.gens()[0]
        return (sum([l[i]*D**i for i in xrange(len(l))])-D**len(l),T.transpose().inverse())
    else: raise ValueError, "Ore Algebra has to be differential or shift."

class MonteCarloException(Exception):
    def __init__(self, message):
        super(MonteCarloException, self).__init__(message)
