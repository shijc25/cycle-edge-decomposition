import Cycle12.RationalRoutedCase
import Cycle12.RationalIntervalCover

namespace Cycle12
open Real Finset SimpleGraph Cycle13 Cycle13.MixedSample

/-- Exact inclusion of a closed interval or ray into another. -/
def ratSideExtends (outer inner : RatSideInterval) : Prop :=
  outer.lower ≤ inner.lower ∧ match outer.upper with
  | none => True
  | some h => match inner.upper with
    | none => False
    | some k => k ≤ h

instance instDecidableRatSideExtends (a b : RatSideInterval) : Decidable (ratSideExtends a b) := by
  unfold ratSideExtends
  cases a.upper <;> cases b.upper <;> infer_instance

theorem rat_side_extends_sound {a b : RatSideInterval} (h : ratSideExtends a b)
    {x : ℝ} (hx : b.Contains x) : a.Contains x := by
  refine ⟨((Rat.cast_le (K:=ℝ)).mpr h.1).trans hx.1,?_⟩
  intro r hr
  have hh := h.2
  rw [hr] at hh
  cases he : b.upper with
  | none => simp only [he] at hh
  | some t =>
    simp only [he] at hh
    exact (hx.2 t he).trans ((Rat.cast_le (K:=ℝ)).mpr hh)

def ratSideChain (target : RatSideInterval) (xs : List RatSideInterval) : Prop :=
  match target.upper with
  | none => ratRayChain target.lower xs
  | some r => ratClosedChain r target.lower xs

instance instDecidableRatSideChain (target : RatSideInterval) (xs : List RatSideInterval) :
    Decidable (ratSideChain target xs) := by
  unfold ratSideChain
  cases target.upper <;> infer_instance

theorem rat_side_chain_covers {target : RatSideInterval} {xs : List RatSideInterval}
    (h : ratSideChain target xs) {x : ℝ} (hx : target.Contains x) :
    ∃ a∈xs, a.Contains x := by
  cases he : target.upper with
  | none => exact rat_ray_chain_covers (by simpa only [ratSideChain,he] using h) hx.1
  | some r => exact rat_closed_chain_covers (by simpa only [ratSideChain,he] using h) hx.1 (hx.2 r he)

def RatCoverRectangle.xInterval (r : RatCoverRectangle) : RatSideInterval := ⟨r.xl,some r.xh⟩
def RatCoverRectangle.sInterval (r : RatCoverRectangle) : RatSideInterval := ⟨r.sl,r.sh⟩

def RatCoverRectangle.JoinX (r : RatCoverRectangle) (xs : List RatCoverRectangle) : Prop :=
  ratSideChain r.xInterval (xs.map RatCoverRectangle.xInterval) ∧
  ∀ a∈xs, ratSideExtends a.sInterval r.sInterval

def RatCoverRectangle.JoinS (r : RatCoverRectangle) (xs : List RatCoverRectangle) : Prop :=
  ratSideChain r.sInterval (xs.map RatCoverRectangle.sInterval) ∧
  ∀ a∈xs, ratSideExtends a.xInterval r.xInterval

instance instDecidableRatCoverJoinX (r : RatCoverRectangle) (xs : List RatCoverRectangle) :
    Decidable (r.JoinX xs) := by unfold RatCoverRectangle.JoinX; infer_instance
instance instDecidableRatCoverJoinS (r : RatCoverRectangle) (xs : List RatCoverRectangle) :
    Decidable (r.JoinS xs) := by unfold RatCoverRectangle.JoinS; infer_instance

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Horizontal assembly preserves the actual graph conclusion, including the
closed endpoints. Numeric inclusion alone does not supply any graph premise. -/
theorem rat_cover_join_x_sound (r : RatCoverRectangle) (xs : List RatCoverRectangle)
    (h : r.JoinX xs) (hsound : ∀ a∈xs, a.Sound) : r.Sound := by
  intro V _ _ G hm hxl hxh hs hbounded hdegree hI
  have hx : r.xInterval.Contains (coverGraphX (Fintype.card V) (Fintype.card G.edgeSet)) := by
    refine ⟨hxl,?_⟩
    intro u hu
    have he : r.xh=u := Option.some.inj hu
    simpa only [← he] using hxh
  obtain ⟨a,ha,hal⟩ := rat_side_chain_covers h.1 hx
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
  have hsr := rat_side_extends_sound (h.2 c hc) (show r.sInterval.Contains
    (sOf (Fintype.card V) (Fintype.card G.edgeSet)) from ⟨hs,hbounded⟩)
  exact hsound c hc G hm hal.1 (hal.2 _ rfl) hsr.1 hsr.2 hdegree hI

/-- Vertical assembly treats unbounded density rays explicitly. -/
theorem rat_cover_join_s_sound (r : RatCoverRectangle) (xs : List RatCoverRectangle)
    (h : r.JoinS xs) (hsound : ∀ a∈xs, a.Sound) : r.Sound := by
  intro V _ _ G hm hxl hxh hs hbounded hdegree hI
  obtain ⟨a,ha,hal⟩ := rat_side_chain_covers h.1
    (show r.sInterval.Contains (sOf (Fintype.card V) (Fintype.card G.edgeSet)) from ⟨hs,hbounded⟩)
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
  have hx : r.xInterval.Contains (coverGraphX (Fintype.card V) (Fintype.card G.edgeSet)) := by
    refine ⟨hxl,?_⟩
    intro u hu
    have he : r.xh=u := Option.some.inj hu
    simpa only [← he] using hxh
  have hxr := rat_side_extends_sound (h.2 c hc) hx
  exact hsound c hc G hm hxr.1 (hxr.2 _ rfl) hal.1 hal.2 hdegree hI

end
end Cycle12
