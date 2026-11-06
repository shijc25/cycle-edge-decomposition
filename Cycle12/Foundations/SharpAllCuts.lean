import Cycle12.Foundations.AllCutsProbability
import Cycle12.Foundations.FractionalCutCount
import Cycle12.Foundations.ExponentialCountingTail

namespace Cycle13
open SimpleGraph Finset Real MeasureTheory ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def sharpCutFailure (n : ℕ) (ε lam : ℝ) : ℝ :=
  (2*ε^2*lam)/(2*ε^2*lam-2*log n)*exp (-(2*ε^2*lam-2*log n))

theorem edge_split_all_cuts_failure_sharp (G : SimpleGraph V) (q : unitInterval)
    {ε lam : ℝ} (hε : 0 ≤ ε) (hlam : 0 < lam) (hn : 2 ≤ Fintype.card V)
    (hcut : ∀ S : Finset V, S.Nonempty → S≠univ → lam ≤ (cutSize G S:ℝ))
    (hgap : 0 < 2*ε^2*lam-2*log (Fintype.card V:ℝ)) :
    (edgeSplitMeasure V q).real {ω |
      ¬∀ S : Finset V, ((q:ℝ)-ε)*cutSize G S ≤ (cutSize (splitBank G ω true) S:ℝ)} ≤
      sharpCutFailure (Fintype.card V) ε lam := by
  let C := univ.filter (fun S : Finset V => S.Nonempty ∧ S≠univ)
  let E := fun S : Finset V => {ω : Sym2 V→Bool |
    (cutSize (splitBank G ω true) S:ℝ) < ((q:ℝ)-ε)*cutSize G S}
  have hnR : (1:ℝ) < Fintype.card V := by exact_mod_cast (show 1 < Fintype.card V by omega)
  have hn0 : 0 < (Fintype.card V:ℝ) := by linarith
  have hlog : 0 < log (Fintype.card V:ℝ) := log_pos hnR
  let a := 2*log (Fintype.card V:ℝ)/lam
  let b := 2*ε^2
  have hb : 0 < b := by dsimp [b]; nlinarith
  have hba : a < b := (div_lt_iff₀ hlam).mpr (by dsimp [b]; linarith)
  have hcount : ∀ t, lam ≤ t →
      ((C.filter (fun S => (cutSize G S:ℝ) ≤ t)).card:ℝ) ≤ exp (a*t) := by
    intro t ht
    have ht0 : 0 ≤ t := (hlam.trans_le ht).le
    have hat : 2 ≤ 2*t/lam := (le_div_iff₀ hlam).mpr (by linarith)
    have hK : 2*(⌊t⌋₊:ℝ) ≤ (2*t/lam)*lam := by
      rw [div_mul_cancel₀ _ hlam.ne']
      exact mul_le_mul_of_nonneg_left (Nat.floor_le ht0) (by norm_num)
    have hh := simple_proper_cut_count_real G hat hlam hK hn hcut
    have hsub : C.filter (fun S => (cutSize G S:ℝ) ≤ t)⊆
        univ.filter (fun S : Finset V => S.Nonempty ∧ S≠univ ∧ cutSize G S ≤ ⌊t⌋₊) := by
      intro S hS
      obtain ⟨hSC,hsize⟩ := mem_filter.mp hS
      have hproper := (mem_filter.mp hSC).2
      exact mem_filter.mpr ⟨mem_univ _,hproper.1,hproper.2,Nat.le_floor hsize⟩
    apply (Nat.cast_le.mpr (card_le_card hsub)).trans
    apply hh.trans_eq
    rw [rpow_def_of_pos hn0]
    congr 1
    dsimp [a]
    ring
  have hsum := finite_exponential_counting_tail C (fun S => (cutSize G S:ℝ)) hb hba
    (fun S hS => hcut S (mem_filter.mp hS).2.1 (mem_filter.mp hS).2.2) hcount
  have hvalue : b/(b-a)*exp (-(b-a)*lam)=sharpCutFailure (Fintype.card V) ε lam := by
    have he : (b-a)*lam=2*ε^2*lam-2*log (Fintype.card V:ℝ) := by
      dsimp [a,b]
      field_simp
    have hratio : b/(b-a)=(2*ε^2*lam)/(2*ε^2*lam-2*log (Fintype.card V:ℝ)) := by
      rw [← he]
      dsimp [b]
      field_simp
    unfold sharpCutFailure
    rw [hratio,neg_mul,he]
  rw [hvalue] at hsum
  have hsub : {ω | ¬∀ S : Finset V,
      ((q:ℝ)-ε)*cutSize G S ≤ (cutSize (splitBank G ω true) S:ℝ)} ⊆ ⋃ S∈C, E S := by
    intro ω hω
    push_neg at hω
    obtain ⟨S,hS⟩ := hω
    have hSne : S.Nonempty := by
      by_contra! h
      simp only [h,cutSize_empty,Nat.cast_zero,mul_zero,lt_self_iff_false] at hS
    have hSu : S≠univ := by
      rintro rfl
      simp only [cutSize_univ,Nat.cast_zero,mul_zero,lt_self_iff_false] at hS
    exact Set.mem_iUnion.mpr ⟨S,Set.mem_iUnion.mpr ⟨mem_filter.mpr ⟨mem_univ _,hSne,hSu⟩,hS⟩⟩
  apply (measureReal_mono (μ:=edgeSplitMeasure V q) hsub (measure_ne_top _ _)).trans
  apply (measureReal_biUnion_finset_le C E).trans
  apply (sum_le_sum (fun S _ => edge_split_single_cut_failure G q hε S)).trans
  simpa only [b,neg_mul] using hsum

end
end Cycle13
