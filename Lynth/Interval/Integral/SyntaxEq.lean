import Lynth.Interval.Integral.Math.Integrand

/-! Correctness of the executable expression comparisons used by certificates. -/

namespace Intgrl

deriving instance ReflBEq for Unary, Binary, Term, Region
deriving instance LawfulBEq for Unary, Binary, Term, Region

end Intgrl
