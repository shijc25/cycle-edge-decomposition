import Cycle12.Foundations.BasicCertificates

namespace Cycle13
open Real

theorem log_rational_enclosure {q l u : ℚ} (hq : 1 ≤ q) (n : ℕ)
    (hl : l ≤ ratLogPartial ((q-1)/(q+1)) n)
    (hu : ratLogUpper ((q-1)/(q+1)) n ≤ u) :
    (l:ℝ) ≤ log (q:ℝ) ∧ log (q:ℝ) ≤ (u:ℝ) := by
  have hh := ratLog_argument_bounds hq n
  exact ⟨((Rat.cast_le (K:=ℝ)).mpr hl).trans hh.1,
    hh.2.trans ((Rat.cast_le (K:=ℝ)).mpr hu)⟩

theorem log_rational_inverse_enclosure {q l u : ℚ}
    (h : (l:ℝ) ≤ log (q:ℝ) ∧ log (q:ℝ) ≤ (u:ℝ)) :
    ((-u:ℚ):ℝ) ≤ log ((1/q:ℚ):ℝ) ∧ log ((1/q:ℚ):ℝ) ≤ ((-l:ℚ):ℝ) := by
  simp only [Rat.cast_neg,Rat.cast_div,Rat.cast_one,one_div,Rat.cast_inv,log_inv]
  exact ⟨neg_le_neg h.2,neg_le_neg h.1⟩

end Cycle13
