module

import all Lynth.Analysis.SpecialFunctions

/-! Portable analytic bounds used by integration, without interval encodings.
Mirrored in /tmp/intgrl/SpecialBounds.lean. -/

namespace SpecialFunctions

/-- Apply the Euler-transform bound at n=4m. Each of its n coefficients
has modulus at most one, and k^(-Re s) <= (n+1)^m. No special-function
values or transcendental real phases are needed in this magnitude bound. -/
theorem eta_growth (s : ℂ) (m : ℕ) (hm : 0 < s.re+m) :
    ‖Complex.dirichletEta s‖ ≤
      (4*m : ℝ) * (4*m+1 : ℝ)^m +
      2 * Real.exp (s.im^2/2 * ((s.re+m)⁻¹^2+(s.re+m)⁻¹)) *
        (4*m+1 : ℝ)^m / 2^(4*m) := by
  have h1 := eta_euler_error s m (4*m) hm le_rfl
  have h2 := norm_etaApproxC_le s m (4*m) hm
  push_cast at h1 h2
  calc ‖Complex.dirichletEta s‖ ≤ ‖etaApproxC s (4*m)‖ +
      ‖Complex.dirichletEta s - etaApproxC s (4*m)‖ := by
        have := norm_add_le (etaApproxC s (4*m)) (Complex.dirichletEta s - etaApproxC s (4*m))
        simpa using this
    _ ≤ _ := by linarith

end SpecialFunctions
