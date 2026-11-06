import Cycle12.RationalCutRate

namespace Cycle12

structure RatSideInterval where
  lower : ℚ
  upper : Option ℚ
  deriving DecidableEq

def RatSideInterval.Contains (a : RatSideInterval) (x : ℝ) : Prop :=
  (a.lower:ℝ) ≤ x ∧ ∀ r, a.upper=some r → x ≤ (r:ℝ)

def ratRayChain : ℚ → List RatSideInterval → Prop
  | _, [] => False
  | left, a::as => a.lower ≤ left ∧ match a.upper with
    | none => True
    | some r => ratRayChain r as

instance instDecidableRatRayChain (left : ℚ) (xs : List RatSideInterval) : Decidable (ratRayChain left xs) := by
  induction xs generalizing left with
  | nil => exact instDecidableFalse
  | cons a as ih =>
    unfold ratRayChain
    cases a.upper <;> infer_instance

theorem rat_ray_chain_covers {left : ℚ} {xs : List RatSideInterval} (hc : ratRayChain left xs)
    {x : ℝ} (hx : (left:ℝ) ≤ x) : ∃ a∈xs, a.Contains x := by
  induction xs generalizing left with
  | nil => exact False.elim hc
  | cons a as ih =>
    change a.lower ≤ left ∧ (match a.upper with | none => True | some r => ratRayChain r as) at hc
    have hlo : (a.lower:ℝ) ≤ x := ((Rat.cast_le (K:=ℝ)).mpr hc.1).trans hx
    cases he : a.upper with
    | none =>
      refine ⟨a,List.mem_cons_self,hlo,?_⟩
      intro r hr
      rw [he] at hr
      contradiction
    | some r =>
      by_cases hr : x ≤ (r:ℝ)
      · refine ⟨a,List.mem_cons_self,hlo,?_⟩
        intro r' hr'
        have heq : r=r' := Option.some.inj (he.symm.trans hr')
        simpa only [← heq] using hr
      · have htail : ratRayChain r as := by simpa only [he] using hc.2
        obtain ⟨b,hb,hbnd⟩ := ih htail (le_of_lt (lt_of_not_ge hr))
        exact ⟨b,List.mem_cons_of_mem a hb,hbnd⟩

/-- Closed bounded coverage includes the first endpoint; an empty table
therefore certifies no nonempty interval. -/
def ratClosedChain (right : ℚ) : ℚ → List RatSideInterval → Prop
  | _, [] => False
  | left, a::as => a.lower ≤ left ∧ match a.upper with
    | none => True
    | some r => right ≤ r ∨ ratClosedChain right r as

instance instDecidableRatClosedChain (right left : ℚ) (xs : List RatSideInterval) :
    Decidable (ratClosedChain right left xs) := by
  induction xs generalizing left with
  | nil => exact instDecidableFalse
  | cons a as ih =>
    unfold ratClosedChain
    cases a.upper <;> infer_instance

theorem rat_closed_chain_covers {left right : ℚ} {xs : List RatSideInterval}
    (hc : ratClosedChain right left xs) {x : ℝ} (hx : (left:ℝ) ≤ x) (hxr : x ≤ (right:ℝ)) :
    ∃ a∈xs, a.Contains x := by
  induction xs generalizing left with
  | nil => exact False.elim hc
  | cons a as ih =>
    change a.lower ≤ left ∧ (match a.upper with | none => True | some r => right ≤ r ∨ ratClosedChain right r as) at hc
    have hlo : (a.lower:ℝ) ≤ x := ((Rat.cast_le (K:=ℝ)).mpr hc.1).trans hx
    cases he : a.upper with
    | none =>
      refine ⟨a,List.mem_cons_self,hlo,?_⟩
      intro r hr
      rw [he] at hr
      contradiction
    | some r =>
      by_cases hr : x ≤ (r:ℝ)
      · refine ⟨a,List.mem_cons_self,hlo,?_⟩
        intro r' hr'
        have heq : r=r' := Option.some.inj (he.symm.trans hr')
        simpa only [← heq] using hr
      · have htail : ratClosedChain right r as := by
          have hh := hc.2
          rw [he] at hh
          exact hh.resolve_left (fun h => hr (hxr.trans ((Rat.cast_le (K:=ℝ)).mpr h)))
        obtain ⟨b,hb,hbnd⟩ := ih htail (le_of_lt (lt_of_not_ge hr))
        exact ⟨b,List.mem_cons_of_mem a hb,hbnd⟩

end Cycle12
