import Cycle12.Foundations.TruncatedCutRetention

namespace Cycle12
open SimpleGraph Finset Cycle13
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def cutLightVertices (G : SimpleGraph V) (S : Finset V) (k : ℕ) : Finset V :=
  S.filter (fun v => (neighborsIn G v Sᶜ).card ≤ k)

theorem cut_light_subset (G : SimpleGraph V) (S : Finset V) (k : ℕ) :
    cutLightVertices G S k⊆S := filter_subset _ _

/-- Exact edge accounting for the actual capped cut graph. Every heavy
vertex contributes k edges, and every light vertex keeps all its cut edges. -/
theorem truncated_cut_light_identity (G : SimpleGraph V) (S : Finset V) (k : ℕ) :
    ((truncatedCut G S k).edgeSet.ncard:ℝ)=
      (k:ℝ)*(S\cutLightVertices G S k).card+
        ∑ v∈cutLightVertices G S k, ((neighborsIn G v Sᶜ).card:ℝ) := by
  let L := cutLightVertices G S k
  have hLS : L⊆S := cut_light_subset G S k
  rw [truncatedCut_edge_count,Nat.cast_sum]
  have hh := sum_union (f:=fun v => ((min k (neighborsIn G v Sᶜ).card:ℕ):ℝ))
    (show Disjoint L (S\L) from disjoint_sdiff_self_right)
  rw [union_sdiff_of_subset hLS] at hh
  rw [hh]
  have hl : (∑ v∈L, ((min k (neighborsIn G v Sᶜ).card:ℕ):ℝ))=
      ∑ v∈L, ((neighborsIn G v Sᶜ).card:ℝ) := by
    exact sum_congr rfl (fun v hv => by rw [min_eq_right (mem_filter.mp hv).2])
  have hj : (∑ v∈S\L, ((min k (neighborsIn G v Sᶜ).card:ℕ):ℝ))=(k:ℝ)*(S\L).card := by
    have hp : ∀ v∈S\L, min k (neighborsIn G v Sᶜ).card=k := by
      intro v hv
      have hm := mem_sdiff.mp hv
      have hn : ¬(neighborsIn G v Sᶜ).card ≤ k := fun hd => hm.2 (mem_filter.mpr ⟨hm.1,hd⟩)
      exact min_eq_left (by omega)
    rw [sum_congr rfl (fun v hv => congrArg (fun n : ℕ => (n:ℝ)) (hp v hv))]
    simp only [sum_const,nsmul_eq_mul,mul_comm]
  rw [hl,hj]
  exact add_comm _ _

/-- Use the original expansion profile at the actual light-side order.
Replacing it by the profile of the whole side would lose this information. -/
theorem truncated_cut_full_profile (G : SimpleGraph V) (S : Finset V) (k : ℕ)
    (alpha : ℝ → ℝ) (h N : ℝ)
    (hprofile : ∀ X⊆S, alpha ((X.card:ℝ)/N)*h*X.card ≤ (cutSize G X:ℝ)) :
    (k:ℝ)*(S\cutLightVertices G S k).card+
      alpha (((cutLightVertices G S k).card:ℝ)/N)*h*(cutLightVertices G S k).card-
        ((S\cutLightVertices G S k).card:ℝ)*(cutLightVertices G S k).card ≤
      ((truncatedCut G S k).edgeSet.ncard:ℝ) := by
  let L := cutLightVertices G S k
  have hLS : L⊆S := cut_light_subset G S k
  have hc : ((S\L).card:ℝ)=(S.card:ℝ)-L.card := by
    rw [card_sdiff_of_subset hLS,Nat.cast_sub (card_le_card hLS)]
  have hb := subcut_boundary_bound G S L hLS
  have hbR : (cutSize G L:ℝ) ≤ ((G.interedges L Sᶜ).card:ℝ)+
      (L.card:ℝ)*((S.card:ℝ)-L.card) := by
    have hr := (Nat.cast_le (α:=ℝ)).mpr hb
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub (card_le_card hLS)] using hr
  rw [card_interedges_eq_sum_neighborsIn,Nat.cast_sum] at hbR
  have hp := hprofile L hLS
  rw [truncated_cut_light_identity]
  change (k:ℝ)*(S\L).card+alpha ((L.card:ℝ)/N)*h*L.card-
    ((S\L).card:ℝ)*L.card ≤ (k:ℝ)*(S\L).card+∑ v∈L, ((neighborsIn G v Sᶜ).card:ℝ)
  rw [hc]
  nlinarith only [hbR,hp]

/-- Normalized full-profile inequality for an actual truncated graph.
The light proportion lies in [0,1], so the later finite interval bound
retains the full feasible range instead of optimizing over all reals. -/
theorem truncated_cut_full_profile_scaled (G : SimpleGraph V) (S : Finset V) (k : ℕ)
    (alpha : ℝ → ℝ) {h N lambda : ℝ} (hh : 0<h) (hN : 0<N) (hS : S.Nonempty)
    (hcap : lambda*S.card ≤ (k:ℝ))
    (hprofile : ∀ X⊆S, alpha ((X.card:ℝ)/N)*h*X.card ≤ (cutSize G X:ℝ)) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      (S.card/h)*(1-t)*(lambda-t)+t*alpha (t*(S.card/h)/(N/h)) ≤
        ((truncatedCut G S k).edgeSet.ncard:ℝ)/(h*S.card) := by
  let L := cutLightVertices G S k
  let t : ℝ := L.card/S.card
  have hs : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr hS
  have hl : (L.card:ℝ) ≤ S.card := by exact_mod_cast card_le_card (cut_light_subset G S k)
  have hc : ((S\L).card:ℝ)=(S.card:ℝ)-L.card := by
    rw [card_sdiff_of_subset (cut_light_subset G S k),Nat.cast_sub (cut_light_subset G S k |> card_le_card)]
  refine ⟨t,by positivity, (div_le_one hs).mpr hl,?_⟩
  have hp := truncated_cut_full_profile G S k alpha h N hprofile
  change (k:ℝ)*(S\L).card+alpha ((L.card:ℝ)/N)*h*L.card-
    ((S\L).card:ℝ)*L.card ≤ _ at hp
  have hk := mul_le_mul_of_nonneg_right hcap (Nat.cast_nonneg (α:=ℝ) (S\L).card)
  have harg : t*(S.card/h)/(N/h)=(L.card:ℝ)/N := by
    dsimp [t]
    field_simp
    <;> ring
  rw [harg]
  apply (le_div_iff₀ (mul_pos hh hs)).mpr
  have he : ((S.card/h)*(1-t)*(lambda-t)+t*alpha ((L.card:ℝ)/N))*(h*S.card)=
      (lambda*S.card)*(S\L).card+alpha ((L.card:ℝ)/N)*h*L.card-
        ((S\L).card:ℝ)*L.card := by
    rw [hc]
    dsimp [t]
    field_simp
    <;> ring
  rw [he]
  linarith only [hp,hk]

end
end Cycle12
