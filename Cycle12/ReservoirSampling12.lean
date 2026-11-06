import Cycle12.ReservoirSampleTails12
import Cycle12.ThreeLabelLaw12
import Cycle12.Foundations.SampleGraphBounds
import Cycle12.Foundations.ExpansionWithinTools

namespace Cycle12
open Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

structure ReservoirSample (G : SimpleGraph V) (U : Finset V) (z upper : ℝ) : Prop where
  order_upper : (U.card:ℝ) ≤ upper
  neighbors : ∀ v, (15/16)*z ≤ ((neighborsIn G v U).card:ℝ)
  cuts : SampleCutExpansion G U (z/30)

theorem ReservoirSample.induced_expansion {G : SimpleGraph V} {U : Finset V}
    {z upper : ℝ} (h : ReservoirSample G U z upper) :
    OAI.ErdosGallai.CutExpansion (G.induce (U:Set V)) (z/30) :=
  cutExpansion_of_small _ (sample_induced_expansion G U h.cuts)

theorem normalized_reservoir_sample_failure (G : SimpleGraph V) {p : unitInterval} {z R : ℝ}
    (hp : 0 < (p:ℝ)) (hR : 12 ≤ R) (hzR : 1048576*R ≤ z)
    (hlog : 1024*log (Fintype.card V:ℝ) ≤ z)
    (hn : (Fintype.card V:ℝ) = R*z/(p:ℝ))
    (hG : GlobalCutProfile G (z/(p:ℝ)))
    (hdeg : ∀ v, 3*z ≤ (p:ℝ)*G.degree v) :
    (bernoulliSubset p).prob (fun U => ¬ReservoirSample G U (3*z) ((9/8)*R*z)) ≤ 1/32 := by
  have hR0 : 0 < R := by linarith only [hR]
  have hz0 : 0 < z := by linarith only [hR,hzR]
  have hn0 : 0 < (Fintype.card V:ℝ) := by rw [hn]; positivity
  have hmean : (p:ℝ)*Fintype.card V = R*z := by rw [hn]; field_simp
  obtain ⟨hdTail,huTail⟩ := reservoir_sample_tail_bounds hn0 hR hzR hlog
  have hu := bernoulliSubset_card_upper_log (V := V) p (by rw [hmean]; positivity)
    (a := (9/8)*R*z) (by rw [hmean]; nlinarith only [mul_pos hR0 hz0])
  rw [hmean] at hu
  have hd := bernoulliSubset_all_degrees_log G p (μ := 3*z) (δ := (45/16)*z)
    (by positivity) (by positivity) (by linarith only [hz0]) hdeg
  have hc := (normalized_bad_cut_probability reservoirSampleParameters
    (reservoir_sampler_valid hp hR hzR) G hn hG).trans (reservoir_sampler_cut_failure hR hzR)
  change (bernoulliSubset p).prob (BadCutSample G ((45/16)*z) ((1/10)*z) ((9/8)*R*z)) ≤ 1/64 at hc
  let E1 := fun U : Finset V => (9/8)*R*z < (U.card:ℝ)
  let E2 := fun U : Finset V => ∃ v, ((neighborsIn G v U).card:ℝ) < (45/16)*z
  let E3 := BadCutSample G ((45/16)*z) ((1/10)*z) ((9/8)*R*z)
  have hcover : ∀ U, ¬ReservoirSample G U (3*z) ((9/8)*R*z) → E1 U ∨ E2 U ∨ E3 U := by
    intro U hnot
    by_cases h1 : E1 U
    · exact Or.inl h1
    by_cases h2 : E2 U
    · exact Or.inr (Or.inl h2)
    by_cases h3 : E3 U
    · exact Or.inr (Or.inr h3)
    have hupper : (U.card:ℝ) ≤ (9/8)*R*z := le_of_not_gt h1
    have hdegree : ∀ v, (45/16)*z ≤ ((neighborsIn G v U).card:ℝ) :=
      fun v => le_of_not_gt (fun hv => h2 ⟨v,hv⟩)
    apply False.elim
    apply hnot
    refine ⟨hupper,?_,?_⟩
    · intro v
      convert hdegree v using 1 <;> ring
    · convert sample_expansion_of_not_bad_cut G U hupper (fun v _ => hdegree v) h3 using 1 <;> ring
  have hb := (bernoulliSubset p).prob_mono hcover
  have h1 := (bernoulliSubset p).prob_union_le E1 (fun U => E2 U ∨ E3 U)
  have h2 := (bernoulliSubset p).prob_union_le E2 E3
  have hu' := hu.trans huTail
  have hd' := hd.trans hdTail
  change (bernoulliSubset p).prob E1 ≤ 1/1024 at hu'
  change (bernoulliSubset p).prob E2 ≤ 1/1024 at hd'
  change (bernoulliSubset p).prob E3 ≤ 1/64 at hc
  linarith only [hb,h1,h2,hu',hd',hc]

theorem profile_of_triple_expansion (G : SimpleGraph V) {h : ℝ} (hh : 0 ≤ h)
    (hexp : OAI.ErdosGallai.CutExpansion G (3*h)) : GlobalCutProfile G h := by
  have hsmall : ∀ X : Finset V, 2*(X.card:ℝ) ≤ Fintype.card V →
      (3*h)*X.card ≤ (cutSize G X:ℝ) := by
    intro X hX
    have he := hexp X
    rw [← cutSize_eq_interedges] at he
    have hc : (X.card:ℝ) ≤ Xᶜ.card := by
      have hs : X.card+Xᶜ.card = Fintype.card V := card_add_card_compl X
      have hsR : (X.card:ℝ)+(Xᶜ.card:ℝ) = Fintype.card V := by exact_mod_cast hs
      linarith only [hX,hsR]
    simpa only [min_eq_left hc] using he
  refine ⟨?_,?_,?_⟩
  · intro X hX
    have he := hsmall X hX
    have hm := mul_nonneg hh (Nat.cast_nonneg (α := ℝ) X.card)
    linarith only [he,hm]
  · intro X hX
    have he := hsmall X (by linarith only [hX,Nat.cast_nonneg (α := ℝ) X.card])
    have hm := mul_nonneg hh (Nat.cast_nonneg (α := ℝ) X.card)
    linarith only [he,hm]
  · intro X hX
    have he := hsmall X (by linarith only [hX,Nat.cast_nonneg (α := ℝ) X.card])
    have hm := mul_nonneg hh (Nat.cast_nonneg (α := ℝ) X.card)
    linarith only [he,hm]

theorem expansion_min_degree (G : SimpleGraph V) {h : ℝ}
    (hn : 2 ≤ Fintype.card V) (hexp : OAI.ErdosGallai.CutExpansion G h) (v : V) :
    h ≤ (G.degree v:ℝ) := by
  have he := hexp {v}
  rw [← cutSize_eq_interedges,cutSize_singleton] at he
  have hc : (1:ℝ) ≤ ({v}ᶜ:Finset V).card := by
    rw [card_compl,card_singleton]
    exact_mod_cast (show 1 ≤ Fintype.card V-1 by omega)
  simpa only [card_singleton,Nat.cast_one,min_eq_left hc,mul_one] using he

/-- An explicit sufficient vertex-sampling theorem for the scales used by
the coefficient-12 proof. It gives all-original-vertex neighbor bounds. -/
theorem reservoir_sample_failure (G : SimpleGraph V) {p : unitInterval} {h : ℝ}
    (hp : 0 < (p:ℝ)) (hh : 0 < h) (hn : 2 ≤ Fintype.card V)
    (hratio : 4*h ≤ (Fintype.card V:ℝ))
    (hscale : 9437184*(Fintype.card V:ℝ) ≤ (p:ℝ)*h^2)
    (hlog : 3072*log (Fintype.card V:ℝ) ≤ (p:ℝ)*h)
    (hexp : OAI.ErdosGallai.CutExpansion G h) :
    (bernoulliSubset p).prob
      (fun U => ¬ReservoirSample G U ((p:ℝ)*h) ((9/8)*(p:ℝ)*Fintype.card V)) ≤ 1/32 := by
  let z := (p:ℝ)*h/3
  let R := 3*(Fintype.card V:ℝ)/h
  have hR : 12 ≤ R := (le_div_iff₀ hh).mpr (by linarith only [hratio])
  have hzR : 1048576*R ≤ z := by
    dsimp [R,z]
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 3)).mpr
    have hb : 9437184*(Fintype.card V:ℝ)/h ≤ (p:ℝ)*h :=
      (div_le_iff₀ hh).mpr (by nlinarith only [hscale])
    convert hb using 1 <;> ring
  have hlog' : 1024*log (Fintype.card V:ℝ) ≤ z := by dsimp [z]; linarith only [hlog]
  have hn' : (Fintype.card V:ℝ) = R*z/(p:ℝ) := by dsimp [R,z]; field_simp <;> ring
  have heq : 3*(z/(p:ℝ)) = h := by dsimp [z]; field_simp <;> ring
  have hG : GlobalCutProfile G (z/(p:ℝ)) :=
    profile_of_triple_expansion G (by dsimp [z]; positivity) (heq.symm ▸ hexp)
  have hdeg : ∀ v, 3*z ≤ (p:ℝ)*G.degree v := by
    intro v
    have hd := mul_le_mul_of_nonneg_left (expansion_min_degree G hn hexp v) hp.le
    dsimp [z]
    linarith only [hd]
  have hb := normalized_reservoir_sample_failure G hp hR hzR hlog' hn' hG hdeg
  have hZ : 3*z = (p:ℝ)*h := by dsimp [z]; ring
  have hu : (9/8)*R*z = (9/8)*(p:ℝ)*Fintype.card V := by dsimp [R,z]; field_simp <;> ring
  simpa only [hZ,hu] using hb

end
end Cycle12
