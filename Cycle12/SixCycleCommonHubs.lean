import Cycle12.SixCycleTwinFree
import Cycle12.SixTwoEarCompatibility

namespace Cycle12
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Rotate the given six-cycle so that one exterior edge runs between
labels 0 and 3. Its vertex set is unchanged. -/
theorem six_cycle_choose_ear_frame (G : SimpleGraph V)
    (hconn : G.Connected) (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    {u x y : V} (c : G.Walk u u) (hc : c.IsCycle) (hlen : c.length=6)
    (hshort : Cycle13.NoCycleAtLeast G 7)
    (hx : x∉c.support) (hy : y∉c.support) (hxy : G.Adj x y) :
    ∃ f : Fin 6 ↪ V, (∀ i, G.Adj (f i) (f (i+1))) ∧
      (∀ v, v∈c.support ↔ ∃ i, f i=v) ∧ G.Adj x (f 0) ∧ G.Adj y (f 3) := by
  obtain ⟨a,ha,b,hb,hab,hxa,hyb⟩ := six_cycle_external_edge_distinct_attachments
    G hconn hrobust c hc hlen hshort hx hy hxy
  have hopp := six_cycle_external_edge_opposite hc hlen hshort ha hb hab hx hy hxa hxy hyb
  have hC6 : (c.rotate a ha).length=6 := by simpa only [Walk.length_rotate] using hlen
  obtain ⟨f,hcycle,hsupport,hprecise⟩ := six_cycle_frame_precise (hc.rotate ha) hC6
  have hf0 : f 0=a := by
    have hh := hprecise 0
    change f 0=(c.rotate a ha).getVert 0 at hh
    simpa only [Walk.getVert_zero] using hh
  have hf3 : f 3=b := (hprecise 3).trans hopp
  refine ⟨f,hcycle,?_,?_,?_⟩
  · intro v
    exact (c.mem_support_rotate_iff a ha).symm.trans (hsupport v)
  · simpa only [hf0] using hxa
  · simpa only [hf3] using hyb

/-- When the exterior is a matching, all its edges attach only to the
same two opposite core vertices. This includes every circle neighbor of
either endpoint, not just the two neighbors used to choose the first ear. -/
theorem six_cycle_matching_common_hubs (G : SimpleGraph V)
    (hconn : G.Connected) (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    {u x y : V} (c : G.Walk u u) (hc : c.IsCycle) (hlen : c.length=6)
    (hshort : Cycle13.NoCycleAtLeast G 7)
    (f : Fin 6 ↪ V) (hcycle : ∀ i, G.Adj (f i) (f (i+1)))
    (hsupport : ∀ v, v∈c.support ↔ ∃ i, f i=v)
    (hx : x∉c.support) (hy : y∉c.support)
    (hxa : G.Adj x (f 0)) (hxy : G.Adj x y) (hyb : G.Adj y (f 3))
    (hmatch : ∀ z w t, z∉c.support → w∉c.support → t∉c.support →
      G.Adj z w → G.Adj z t → w=t) :
    ∀ z w, z∉c.support → w∉c.support → G.Adj z w →
      ∀ v∈c.support, G.Adj z v → v=f 0 ∨ v=f 3 := by
  have h0 : f 0∈c.support := (hsupport _).mpr ⟨0,rfl⟩
  have h3 : f 3∈c.support := (hsupport _).mpr ⟨3,rfl⟩
  have h03 : f 0≠f 3 := f.injective.ne (by decide)
  have hbase := six_cycle_external_edge_attachment_pair hc hlen hshort h0 h3 h03 hx hy hxa hxy hyb
  have hout : ∀ z, z∉c.support → ∀ i, z≠f i := by
    intro z hz i he
    exact hz ((hsupport z).mpr ⟨i,he.symm⟩)
  intro z w hz hw hzw v hv hzv
  by_cases hzx : z=x
  · subst z
    exact hbase.1 v hv hzv
  by_cases hzy : z=y
  · subst z
    exact hbase.2 v hv hzv
  have hwx : w≠x := by
    intro he
    subst w
    exact hzy (hmatch x y z hx hy hz hxy hzw.symm).symm
  have hwy : w≠y := by
    intro he
    subst w
    exact hzx (hmatch y x z hy hx hz hxy.symm hzw.symm).symm
  obtain ⟨a,ha,b,hb,hab,hza,hwb⟩ := six_cycle_external_edge_distinct_attachments
    G hconn hrobust c hc hlen hshort hz hw hzw
  obtain ⟨i,rfl⟩ := (hsupport a).mp ha
  obtain ⟨j,rfl⟩ := (hsupport b).mp hb
  have hij : i≠j := fun he => hab (congrArg f he)
  have hh := six_actual_two_ears_common_hubs f hcycle hshort
    (hout x hx) (hout y hy) (hout z hz) (hout w hw)
    hxy.ne (Ne.symm hzx) hwx.symm (Ne.symm hzy) hwy.symm hzw.ne
    hxa hxy hyb i j hij hza hzw hwb
  have hvpair := (six_cycle_external_edge_attachment_pair hc hlen hshort ha hb hab
    hz hw hza hzw hwb).1 v hv hzv
  rcases hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact hvpair
  · exact hvpair.symm

end Cycle12
