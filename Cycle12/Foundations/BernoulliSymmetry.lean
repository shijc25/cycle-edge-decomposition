import Cycle12.Foundations.MarkedSamplingCoupling

/-! Exchangeability of the actual marked-subset law. -/
namespace Cycle13
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem subsetBernoulli_mass_perm (W : Finset V) (p : unitInterval) (e : V≃V)
    (hW : W.map e.toEmbedding=W) (S : Finset V) :
    (subsetBernoulli W p).mass (S.map e.toEmbedding)=(subsetBernoulli W p).mass S := by
  have hs : S.map e.toEmbedding⊆W ↔ S⊆W := by
    conv_lhs => rw [← hW]
    exact map_subset_map
  simp only [subsetBernoulli,hs,card_map]

theorem subsetBernoulli_expect_perm (W : Finset V) (p : unitInterval) (e : V≃V)
    (hW : W.map e.toEmbedding=W) (f : Finset V→ℝ) :
    (subsetBernoulli W p).expect (fun S => f (S.map e.toEmbedding))=
      (subsetBernoulli W p).expect f := by
  have hh := e.finsetCongr.sum_comp (fun S => (subsetBernoulli W p).mass S*f S)
  simp only [Equiv.finsetCongr_apply,subsetBernoulli_mass_perm W p e hW] at hh
  exact hh

theorem map_swap_of_mem (W : Finset V) {v w : V} (hv : v∈W) (hw : w∈W) :
    W.map (Equiv.swap v w).toEmbedding=W := by
  ext x
  simp only [mem_map_equiv,Equiv.symm_swap]
  by_cases hxv : x=v
  · subst x; simp [hv,hw]
  · by_cases hxw : x=w
    · subst x; simp [hv,hw]
    · rw [Equiv.swap_apply_of_ne_of_ne hxv hxw]

def markedChoiceWeight (N T : Finset V) (v : V) : ℝ :=
  if v∈N∩T then 1/((N∩T).card:ℝ) else 0

theorem markedChoiceWeight_perm (N T : Finset V) (e : V≃V)
    (hN : N.map e.toEmbedding=N) (v : V) :
    markedChoiceWeight N (T.map e.toEmbedding) (e v)=markedChoiceWeight N T v := by
  have he : N∩T.map e.toEmbedding=(N∩T).map e.toEmbedding := by rw [map_inter,hN]
  simp only [markedChoiceWeight,he,card_map,mem_map_equiv,Equiv.symm_apply_apply]

theorem markedChoiceWeight_equal_mean (W N : Finset V) (p : unitInterval) (hNW : N⊆W)
    {v w : V} (hv : v∈N) (hw : w∈N) :
    (subsetBernoulli W p).expect (fun T => markedChoiceWeight N T v)=
      (subsetBernoulli W p).expect (fun T => markedChoiceWeight N T w) := by
  have hN := map_swap_of_mem N hv hw
  have hW := map_swap_of_mem W (hNW hv) (hNW hw)
  have hh := subsetBernoulli_expect_perm W p (Equiv.swap v w) hW
    (fun T => markedChoiceWeight N T w)
  have he : ∀ T, markedChoiceWeight N (T.map (Equiv.swap v w).toEmbedding) w=
      markedChoiceWeight N T v := by
    intro T
    convert markedChoiceWeight_perm N T (Equiv.swap v w) hN v using 1 <;> simp
  simp_rw [he] at hh
  exact hh

theorem markedChoiceWeight_sum_le_one (N T : Finset V) :
    (∑ v∈N, markedChoiceWeight N T v) ≤ 1 := by
  simp only [markedChoiceWeight]
  rw [← sum_filter]
  have he : N.filter (fun v => v∈N∩T)=N∩T := by ext v; simp [and_assoc]
  rw [he,sum_const,nsmul_eq_mul]
  by_cases h : (N∩T).card=0
  · simp [h]
  · have hr : ((N∩T).card:ℝ)≠0 := by exact_mod_cast h
    field_simp
    exact le_rfl

theorem markedChoiceWeight_mean_le (W N : Finset V) (p : unitInterval) (hNW : N⊆W)
    {v : V} (hv : v∈N) :
    (subsetBernoulli W p).expect (fun T => markedChoiceWeight N T v) ≤ 1/(N.card:ℝ) := by
  have hN : 0<(N.card:ℝ) := by exact_mod_cast (Nonempty.card_pos ⟨v,hv⟩)
  apply (le_div_iff₀ hN).mpr
  have hh := (subsetBernoulli W p).expect_mono (fun T => markedChoiceWeight_sum_le_one N T)
  rw [FiniteLaw.expect_const] at hh
  have hsum : (subsetBernoulli W p).expect (fun T => ∑ w∈N, markedChoiceWeight N T w)=
      (N.card:ℝ)*(subsetBernoulli W p).expect (fun T => markedChoiceWeight N T v) := by
    unfold FiniteLaw.expect
    simp only [mul_sum]
    rw [sum_comm]
    have he : ∀ w∈N, (∑ T, (subsetBernoulli W p).mass T*markedChoiceWeight N T w)=
        (subsetBernoulli W p).expect (fun T => markedChoiceWeight N T v) := by
      intro w hw; exact markedChoiceWeight_equal_mean W N p hNW hw hv
    rw [sum_congr rfl he,sum_const,nsmul_eq_mul]
    rw [← mul_sum]
    rfl
  rw [hsum] at hh
  nlinarith

theorem markedChoiceWeight_bad_mean (W N B : Finset V) (p : unitInterval)
    (hNW : N⊆W) (hBN : B⊆N) :
    (subsetBernoulli W p).expect (fun T => ∑ v∈B, markedChoiceWeight N T v) ≤
      (B.card:ℝ)/(N.card:ℝ) := by
  unfold FiniteLaw.expect
  simp only [mul_sum]
  rw [sum_comm]
  calc
    _ ≤ ∑ _v∈B, 1/(N.card:ℝ) := by
      apply sum_le_sum
      intro v hv
      exact markedChoiceWeight_mean_le W N p hNW (hBN hv)
    _ = _ := by simp [div_eq_mul_inv]

end
end Cycle13
