import Mathlib
import Lynth

/-! Numeric expression regressions for separate real and complex special-function
paths. Reference values were independently computed with mpmath at 70 digits.
Each declaration has its own measured +5% heartbeat cap. -/

namespace IntervalArith.SpecialValues

/- Check semantic proof dependencies and exactly one native computation axiom.
Auxiliary numeric suffixes vary between asynchronous builds and heartbeat counts. -/
open Lean Elab Command in
elab "#check_special_axioms " decl:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo decl
  let axioms ← Lean.collectAxioms name
  let base := #[``propext, ``Classical.choice, ``Quot.sound]
  let extra := axioms.filter fun a => !base.contains a
  unless base.all axioms.contains && extra.size == 1 &&
      (name ++ `_native.native_decide).isPrefixOf extra[0]! do
    throwError "unexpected special-function axiom footprint: {axioms}"

set_option maxHeartbeats 805 in -- measured: 766; +5%
theorem erf_zero : |Real.erf (0) - (0/10^30)| < (1/10^18 : ℝ) := by
  lynth
#check_special_axioms erf_zero

set_option maxHeartbeats 879 in -- measured: 837; +5%
theorem erf_one : |Real.erf (1) - (842700792949714869341220635083/10^30)| < (1/10^18 : ℝ) := by
  lynth
#check_special_axioms erf_one

set_option maxHeartbeats 959 in -- measured: 913; +5%
theorem erf_negative : |Real.erf (-2) - (-995322265018952734162069256367/10^30)| < (1/10^18 : ℝ) := by
  lynth
#check_special_axioms erf_negative

set_option maxHeartbeats 914 in -- measured: 870; +5%
theorem erf_large : |Real.erf (8) - (999999999999999999999999999989/10^30)| < (1/10^18 : ℝ) := by
  lynth
#check_special_axioms erf_large

set_option maxHeartbeats 1005 in -- measured: 957; +5%
theorem erf_rational : |Real.erf (1/3) - (362648111766062933408178640148/10^30)| < (1/10^18 : ℝ) := by
  lynth
#check_special_axioms erf_rational

set_option maxHeartbeats 784 in -- measured: 746; +5%
theorem si_zero : |Real.Si (0) - (0/10^30)| < (1/10^18 : ℝ) := by
  lynth
#check_special_axioms si_zero

set_option maxHeartbeats 877 in -- measured: 835; +5%
theorem si_one : |Real.Si (1) - (946083070367183014941353313823/10^30)| < (1/10^18 : ℝ) := by
  lynth
#check_special_axioms si_one

set_option maxHeartbeats 949 in -- measured: 903; +5%
theorem si_negative : |Real.Si (-10) - (-1658347594218874049330971879390/10^30)| < (1/10^18 : ℝ) := by
  lynth
#check_special_axioms si_negative

set_option maxHeartbeats 912 in -- measured: 868; +5%
theorem si_large : |Real.Si (1000) - (1570233121968771218147962778036/10^30)| < (1/10^18 : ℝ) := by
  lynth
#check_special_axioms si_large

set_option maxHeartbeats 1925 in -- measured: 1833; +5%
theorem eta_zero : |Real.dirichletEta (0) - (500000000000000000000000000000/10^30)| < (1/10^18 : ℝ) := by
  lynth
#check_special_axioms eta_zero

set_option maxHeartbeats 2120 in -- measured: 2019; +5%
theorem eta_one : |Real.dirichletEta (1) - (693147180559945309417232121458/10^30)| < (1/10^18 : ℝ) := by
  lynth
#check_special_axioms eta_one

set_option maxHeartbeats 4017 in -- measured: 3825; +5%
theorem eta_half : |Real.dirichletEta (1/2) - (604898643421630370247265914236/10^30)| < (1/10^18 : ℝ) := by
  lynth
#check_special_axioms eta_half

set_option maxHeartbeats 5107 in -- measured: 4863; +5%
theorem eta_negative : |Real.dirichletEta (-5/2) - (-87841120721362842395232450052/10^30)| < (1/10^18 : ℝ) := by
  lynth
#check_special_axioms eta_negative

set_option maxHeartbeats 889 in -- measured: 846; +5%
theorem airy_zero : |Real.airyAi (0) - (355028053887817239260063186004/10^30)| < (1/10^18 : ℝ) := by
  lynth
#check_special_axioms airy_zero

set_option maxHeartbeats 882 in -- measured: 840; +5%
theorem airy_one : |Real.airyAi (1) - (135292416312881415524147423515/10^30)| < (1/10^18 : ℝ) := by
  lynth
#check_special_axioms airy_one

set_option maxHeartbeats 937 in -- measured: 892; +5%
theorem airy_negative : |Real.airyAi (-10) - (40241238486443190689430314030/10^30)| < (1/10^18 : ℝ) := by
  lynth
#check_special_axioms airy_negative

set_option maxHeartbeats 897 in -- measured: 854; +5%
theorem airy_positive_tail : |Real.airyAi (10) - (110475325528986859336/10^30)| < (1/10^18 : ℝ) := by
  lynth
#check_special_axioms airy_positive_tail

set_option maxHeartbeats 2150 in -- measured: 2047; +5%
theorem erf_nonreal : ‖Complex.erf (1 + Complex.I) - ((1316151281697947644880271080244/10^30) + (190453469237834686284108861969/10^30) * Complex.I)‖ < (1/10^12 : ℝ) := by
  lynth
#check_special_axioms erf_nonreal

set_option maxHeartbeats 2714 in -- measured: 2584; +5%
theorem erf_rational_complex : ‖Complex.erf (1/3 + Complex.I/5) - ((376363430645756905948806308285/10^30) + (204056439065999675612108379184/10^30) * Complex.I)‖ < (1/10^12 : ℝ) := by
  lynth
#check_special_axioms erf_rational_complex

set_option maxHeartbeats 2148 in -- measured: 2045; +5%
theorem si_nonreal : ‖Complex.Si (1 + Complex.I) - ((1104222658235581739558753969850/10^30) + (882453805007917743376124044695/10^30) * Complex.I)‖ < (1/10^12 : ℝ) := by
  lynth
#check_special_axioms si_nonreal

set_option maxHeartbeats 2712 in -- measured: 2582; +5%
theorem si_rational_complex : ‖Complex.Si (1/3 + Complex.I/5) - ((333484584658016881322005164985/10^30) + (196747058075776443371300075191/10^30) * Complex.I)‖ < (1/10^12 : ℝ) := by
  lynth
#check_special_axioms si_rational_complex

set_option maxHeartbeats 7691 in -- measured: 7324; +5%
theorem eta_nonreal : ‖Complex.dirichletEta (1 + Complex.I) - ((726559775062463263201495728547/10^30) + (158095863901207324355426285544/10^30) * Complex.I)‖ < (1/10^12 : ℝ) := by
  lynth
#check_special_axioms eta_nonreal

set_option maxHeartbeats 8679 in -- measured: 8265; +5%
theorem eta_rational_complex : ‖Complex.dirichletEta (1/3 + Complex.I/5) - ((573081415459301125514261706713/10^30) + (40898479451443143607994612648/10^30) * Complex.I)‖ < (1/10^12 : ℝ) := by
  lynth
#check_special_axioms eta_rational_complex

set_option maxHeartbeats 2225 in -- measured: 2119; +5%
theorem airy_nonreal : ‖Complex.airyAi (1 + Complex.I) - ((60458308371838149196532978117/10^30) + (-151889565877181402354947912592/10^30) * Complex.I)‖ < (1/10^12 : ℝ) := by
  lynth
#check_special_axioms airy_nonreal

set_option maxHeartbeats 2788 in -- measured: 2655; +5%
theorem airy_rational_complex : ‖Complex.airyAi (1/3 + Complex.I/5) - ((268847747989814679509589335049/10^30) + (-48701772654664262449171378780/10^30) * Complex.I)‖ < (1/10^12 : ℝ) := by
  lynth
#check_special_axioms airy_rational_complex

set_option maxHeartbeats 9561 in -- measured: 9105; +5%
/-- A complex argument close to a negative integer exercises the stable shift. -/
theorem eta_near_negative_integer :
    ‖Complex.dirichletEta (-999/1000 + Complex.I/5) -
      ((250402914534990690695787052859/10^30) + (53162527704220988001179152826/10^30) * Complex.I)‖ < (1/10^12 : ℝ) := by
  lynth
#check_special_axioms eta_near_negative_integer

set_option maxHeartbeats 2764 in -- measured: 2632; +5%
theorem composition : |Real.erf (Real.Si (1/3)) + Real.airyAi (Real.dirichletEta 1) -
  (551111052678331370484345435285/10^30)| < (1/10^12 : ℝ) := by
  lynth
#check_special_axioms composition

end IntervalArith.SpecialValues
