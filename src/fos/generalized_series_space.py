"""
generalized_series_space
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

from .tools import padic_expansion
from ore_algebra.generalized_series import GeneralizedSeriesMonoid

from sage.categories.pushout import ConstructionFunctor
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.element import RingElement
from sage.structure.element import Element
from sage.rings.ring import Algebra
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.rings.qqbar import QQbar
from sage.rings.semirings.non_negative_integer_semiring import NN
from sage.structure.parent import Parent
from sage.categories.rings import Rings
from sage.rings.polynomial.polynomial_ring import PolynomialRing_field
from sage.rings.fraction_field import FractionField_1poly_field
from sage.rings.fraction_field_element import FractionFieldElement_1poly_field
from sage.misc.functional import lift
from sage.misc.latex import latex,LatexExpr
from sage.categories.functor import Functor
from sage.rings.number_field.number_field_base import NumberField

class GeneralizedSeriesMultFunctor(ConstructionFunctor):
    
    rank = 15

    def __init__(self, x):
        Functor.__init__(self, Rings(), Rings())
        self.x = x

    def _apply_functor(self, R):
        return GeneralizedSeriesRing(R, self.x)

    def __eq__(self, other):
        return self.x == other.x

    def merge(self, other):
        return self if self == other else None

    def __str__(self):
        return "GeneralizedSeriesMult in " + str(self.x)


class GeneralizedSeriesRing(UniqueRepresentation, Algebra):
    @staticmethod
    def __classcall__(cls, base, x,prec):
        if not (any(base is P for P in [ZZ, QQ, QQbar])
                or isinstance(base, NumberField)):
            raise TypeError("base ring must be ZZ, QQbar or a number field")
        x = str(x)
        if x.find("LOG") >= 0:
            raise ValueError("generator name must not contain the substring 'LOG'")
        return super(GeneralizedSeriesRing, cls).__classcall__(cls, base, x,prec)

    def __init__(self, base, x,prec):
        self.__monoid=GeneralizedSeriesMonoid(base,x)
        self.Element = ContinuousGeneralizedSeriesMult
        self.__prec=NN(prec)
        Parent.__init__(self, base=base, names=(x,), category=Rings())

    def ngens(self):
        return 1

    def prec(self):
        return self.__prec
    
    def var(self):
        r"""
        Returns the variable name associated to this monoid. 
        """
        return self.__monoid.var()

    def gen(self):
        return self.__monoid.gen()

    def exp_ring(self):
        return self.__monoid.exp_ring()
    
    def tail_ring(self):
        return self.__monoid.tail_ring()

    def construction(self):
        return (GeneralizedSeriesMultFunctor(self.var()), self.base())

    def _coerce_map_from_(self, P):
        if isinstance(P, GeneralizedSeriesRing) or isinstance(P,PolynomialRing_field):
            return str(self.var()) == str(P.gen()) and self.base().has_coerce_map_from(P.base())
        elif isinstance(P,FractionField_1poly_field):
            return str(self.var()) == str(P.gen()) and self.base().has_coerce_map_from(P.base().base())
        return (self.base().has_coerce_map_from(P) # to const
                or self.tail_ring().base_ring().has_coerce_map_from(P)) # to power series

    def is_field(self, proof = True):
        return False
    
    def random_element(self):
        r"""
        Returns a random element of this monoid. 
        """
        return NotImplementedError
    
    def _repr_(self):
        return "Ring of continuous generalized series in " + self.var() + " over " + str(self.base())

    def _latex_(self):
        rep=latex(self.__monoid)
        rep = LatexExpr(r"\sum")+rep
        return rep
    
    def is_exact(self):
        r"""
        Returns ``False``, because series objects are inherently approximate. 
        """
        return False

    def get_monoid(self):
        return self.__monoid
    
    def is_commutative(self):
        r"""
        Returns ``True``.
        """
        return True

    def base_extend(self, ext, name='a'):
        if not isinstance(ext, Parent):
            # assuming ext is an irreducible univariate polynomial over self.base()
            ext = self.base().extension(ext, name)

        return GeneralizedSeriesRing(ext, self.var()) 

    def one(self):
        return self(self.__monoid.one())

    def zero(self):
        return self(self.__monoid.zero())
    
class ContinuousGeneralizedSeriesMult(RingElement):
    def __init__(self, parent, series):
        Element.__init__(self, parent)
        if isinstance(series,ContinuousGeneralizedSeriesMult):
            series=series.get_summands()
        m=parent.get_monoid()
        if not type(series) is list:
            series=[series]
        series=[i for i in series if i!=0]
        if len(series)==0:
            series=[parent.get_monoid().zero()]
        for i in range(len(series)):
            if isinstance(series[i],FractionFieldElement_1poly_field):
                var=series[0].parent().gen()
                expansion=padic_expansion(series[i],var,parent.prec())
                series[i]=m(sum([lift(expansion[1][j])*var**j for j in range(len(expansion[1]))]),expansion[0])
        series=[*map(m,series)]
        self.__summands=[series[0]]
        series=series[1:]
        for i in series:
            found=False
            for j in range(len(self.__summands)):
                if self.__summands[j].similar(i):
                    self.__summands[j]=self.__summands[j]+i
                    found=True
            if not found:
                self.__summands.append(i)
                
    def prec(self):
        return self.parent().prec()
        
    def _add_(self,other):
        if self.is_zero():
            return other
        elif other.is_zero():
            return self
        sums=[i for i in self.__summands]
        othersums=other.get_summands()
        for i in othersums:
            found=False
            for j in range(len(sums)):
                if sums[j].similar(i):
                    sums[j]=sums[j]+i
                    found=True
            if not found:
                sums.append(i)
        return ContinuousGeneralizedSeriesMult(self.parent(),sums)
    
    def get_summands(self):
        return self.__summands

    def _repr_(self):
        rep=repr(self.__summands[0])
        for i in self.__summands[1:]:
            rep=rep + " + " + repr(i)
        return rep

    def _latex_(self):
        rep=latex(self.__summands[0])
        for i in self.__summands[1:]:
            rep=rep + " + " + latex(i)
        return rep

    def _mul_(self,other):
        if self.is_zero() or other.is_one():
            return self
        elif other.is_zero() or self.is_one():
            return other

        sums=self.__summands
        othersums=other.get_summands()
        res=[0 for i in range(len(sums)*len(othersums))]
        counter=0
        for i in range(len(sums)):
            for j in range(len(othersums)):
                res[counter]=sums[i]*othersums[j]
                counter=counter+1
        return ContinuousGeneralizedSeriesMult(self.parent(),res)

    def _neg_(self):        
        return ContinuousGeneralizedSeriesMult(self.parent(), [-i for i in self.__summands])

    def __eq__(self, other):
        sums=self.__summands
        othersums=other.get_summands()

        for i in sums:
            for j in othersums:
                if i==j:
                    break
                return False

        return True

    def __copy__(self):
        return ContinuousGeneralizedSeriesMult(self.parent(),copy(self.__summands))

    def __call__(self, arg):
        return sum([i(arg) for i in self.__summands])

    def is_zero(self):
        return len(self.__summands)==1 and self.__summands[0].is_zero()

    def is_one(self):
        return len(self.__summands)==1 and self.__summands[0].is_one()

    def order(self):
        return min([i.order() for i in self.get_summands()])
    
    def derivative(self,var=None):
        if var==None: var=self.parent().gen()
        if str(var)==str(self.parent().gen()):
            return ContinuousGeneralizedSeriesMult(self.parent(),[i.derivative() for i in self.__summands])
        return self.parent().zero()

    def __getitem__(self, key):
        return self.__summands[key]
