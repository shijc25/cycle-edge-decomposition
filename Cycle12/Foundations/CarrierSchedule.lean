import Cycle12.Foundations.OldSchedule
import Mathlib.Data.Sum.Order

/-! The complete two-stage carrier Link schedule and its actual paths.
All common-neighbor inequalities follow from the carrier's missing-edge
bounds, with no unverified schedule-count premise. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

lemma card_filter_sumLex {α β : Type} [Fintype α] [Fintype β]
    (P : α ⊕ₗ β → Prop) [DecidablePred P] :
    (univ.filter P).card =
      (univ.filter (fun a => P (toLex (Sum.inl a)))).card +
      (univ.filter (fun b => P (toLex (Sum.inr b)))).card := by
  have h := (@toLex (α ⊕ β)).sum_comp
    (fun i : α ⊕ₗ β => if P i then (1 : ℕ) else 0)
  calc
    _ = ∑ i : α ⊕ₗ β, (if P i then (1 : ℕ) else 0) := by simp
    _ = ∑ i : α ⊕ β, (if P (toLex i) then (1 : ℕ) else 0) := h.symm
    _ = (∑ a : α, if P (toLex (Sum.inl a)) then (1 : ℕ) else 0) +
        ∑ b : β, (if P (toLex (Sum.inr b)) then (1 : ℕ) else 0) := Fintype.sum_sum_type _
    _ = _ := by simp

lemma priorLinkLoad_map {I B V : Type} [Fintype I] [LinearOrder I]
    [DecidableEq B] [DecidableEq V] (φ : B ↪ V) (a b : I → B) (i : I) (v : B) :
    priorLinkLoad (φ ∘ a) (φ ∘ b) i (φ v) = priorLinkLoad a b i v := by
  unfold priorLinkLoad
  congr 1
  ext j
  simp only [mem_filter,mem_univ,true_and,Function.comp_apply,φ.injective.eq_iff]

abbrev CarrierSlot (p q : ℕ) := CrossSlot p q ⊕ₗ OldSlot p

namespace CarrierSlot
variable {p q : ℕ}
def first (i : CarrierSlot p q) : Fin p ⊕ Fin q :=
  Sum.elim CrossSlot.first (fun j => Sum.inl j.big) (ofLex i)
def second (i : CarrierSlot p q) : Fin p ⊕ Fin q :=
  Sum.elim CrossSlot.second (fun j => Sum.inl j.small) (ofLex i)

theorem endpoints_ne (i : CarrierSlot p q) : first i ≠ second i := by
  induction i using Lex.rec with
  | h i =>
    rcases i with j | j
    · exact Sum.inl_ne_inr
    · exact fun h => (ne_of_lt j.small_lt_big).symm (Sum.inl.inj h)

theorem cross_load (i : CrossSlot p q) (v : Fin p ⊕ Fin q) :
    priorLinkLoad first second (toLex (Sum.inl i)) v =
      priorLinkLoad CrossSlot.first CrossSlot.second i v := by
  unfold priorLinkLoad
  rw [card_filter_sumLex]
  simp only [Sum.Lex.inl_lt_inl_iff,Sum.Lex.not_inr_lt_inl,false_and,
    filter_false,card_empty,Nat.add_zero,first,second,ofLex_toLex,Sum.elim_inl]

theorem old_load (i : OldSlot p) (v : Fin p) :
    priorLinkLoad (first (q := q)) second (toLex (Sum.inr i)) (Sum.inl v) =
      2*q+priorLinkLoad OldSlot.big OldSlot.small i v := by
  unfold priorLinkLoad
  rw [card_filter_sumLex]
  simp only [Sum.Lex.inl_lt_inr,Sum.Lex.inr_lt_inr_iff,true_and,
    first,second,ofLex_toLex,Sum.elim_inl,Sum.elim_inr,Sum.inl.injEq]
  rw [CrossSlot.total_old_load]

/-- Exact arithmetic for every scheduled call, including its second copy. -/
theorem link_room {V : Type} [DecidableEq V] (G : SimpleGraph V) (D : Finset V)
    (φ : (Fin p ⊕ Fin q) ↪ V) (hq : 0 < q) (ρ : ℕ) (r : Fin p → ℕ)
    (hr : ∀ s, r s ≤ s.val+1) (hD : 6*(p+q)+ρ ≤ D.card)
    (hold : ∀ s, missingNeighbors G D (φ (Sum.inl s)) ≤ p+s.val+1+r s)
    (hnew : ∀ v, missingNeighbors G D (φ (Sum.inr v)) ≤ (p+q)+2*p+ρ)
    (i : CarrierSlot p q) :
    missingNeighbors G D (φ (first i)) + missingNeighbors G D (φ (second i)) +
      priorLinkLoad (φ ∘ first) (φ ∘ second) i (φ (first i)) +
      priorLinkLoad (φ ∘ first) (φ ∘ second) i (φ (second i)) < D.card := by
  rw [priorLinkLoad_map,priorLinkLoad_map]
  induction i using Lex.rec with
  | h i =>
    rcases i with c | o
    · rw [cross_load,cross_load]
      change missingNeighbors G D (φ (Sum.inl c.old)) +
        missingNeighbors G D (φ (Sum.inr c.new)) +
        priorLinkLoad CrossSlot.first CrossSlot.second c (Sum.inl c.old) +
        priorLinkLoad CrossSlot.first CrossSlot.second c (Sum.inr c.new) < D.card
      have h₁ := c.old_load_lt
      have h₂ := c.new_load_lt
      have h₃ := hold c.old
      have h₄ := hnew c.new
      have h₅ := hr c.old
      have h₆ := c.old.isLt
      omega
    · change missingNeighbors G D (φ (Sum.inl o.big)) +
        missingNeighbors G D (φ (Sum.inl o.small)) +
        priorLinkLoad first second (toLex (Sum.inr o)) (Sum.inl o.big) +
        priorLinkLoad first second (toLex (Sum.inr o)) (Sum.inl o.small) < D.card
      rw [old_load,old_load]
      have h₁ := o.big_load_lt
      have h₂ := o.small_load_le
      have h₃ := hold o.big
      have h₄ := hold o.small
      have h₅ := hr o.big
      have h₆ := hr o.small
      have h₇ := o.big.isLt
      have h₈ := o.small_lt_big
      omega

theorem exists_paths {V : Type} [DecidableEq V] (G : SimpleGraph V) (D : Finset V)
    (φ : (Fin p ⊕ Fin q) ↪ V) (hout : ∀ v, φ v ∉ D)
    (hq : 0 < q) (ρ : ℕ) (r : Fin p → ℕ)
    (hr : ∀ s, r s ≤ s.val+1) (hD : 6*(p+q)+ρ ≤ D.card)
    (hold : ∀ s, missingNeighbors G D (φ (Sum.inl s)) ≤ p+s.val+1+r s)
    (hnew : ∀ v, missingNeighbors G D (φ (Sum.inr v)) ≤ (p+q)+2*p+ρ) :
    ∃ P : ∀ i : CarrierSlot p q, G.Path (φ (first i)) (φ (second i)),
      Pairwise (fun i j => Disjoint (P i).val.edgeSet (P j).val.edgeSet) ∧
      (∀ i, (P i).val.length=2) ∧
      ∀ i v, φ v ∈ (P i).val.support → v=first i ∨ v=second i := by
  have hD₀ : D.Nonempty := card_pos.mp (by omega)
  obtain ⟨P,hPP,hlen,hinside⟩ := exists_ordered_links G D hD₀ (φ ∘ first) (φ ∘ second)
    (fun i => φ.injective.ne (endpoints_ne i)) (fun i => hout _) (fun i => hout _)
    (link_room G D φ hq ρ r hr hD hold hnew)
  refine ⟨P,hPP,hlen,?_⟩
  intro i v hv
  rcases hinside i (φ v) hv with h | h | h
  · exact Or.inl (φ.injective h)
  · exact Or.inr (φ.injective h)
  · exact False.elim (hout v h)

end CarrierSlot
end
end Cycle13
