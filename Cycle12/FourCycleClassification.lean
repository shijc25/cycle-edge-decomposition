import Cycle12.FourCycleNeighborhood
import Cycle12.SmallCircumferenceBlocks

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} {G : SimpleGraph V} {a b c d x : V}

/-- Once one external spoke is fixed, all vertices other than its two hubs
have exactly those two hubs as their full neighborhood. -/
theorem four_cycle_two_hub_shape
    (hshort : Cycle13.NoCycleAtLeast G 5) (hn : [a,b,c,d].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hnear : ∀ y, y∉[a,b,c,d] →
      ∃ v∈[a,b,c,d], ∃ w∈[a,b,c,d], v≠w ∧ G.Adj y v ∧ G.Adj y w)
    (hx : x∉[a,b,c,d]) (hxa : G.Adj x a) (hxc : G.Adj x c) :
    ∀ y, y≠a → y≠c → ∀ z, G.Adj y z ↔ z=a ∨ z=c := by
  have hall : ∀ y, y∉[a,b,c,d] →
      G.Adj y a ∧ G.Adj y c ∧ ¬G.Adj y b ∧ ¬G.Adj y d := by
    intro y hy
    rcases four_cycle_external_pair hshort hn hab hbc hcd hda hy (hnear y hy) with h | h
    · exact h
    · by_cases he : x=y
      · exact False.elim (h.2.2.1 (he ▸ hxa))
      · exact False.elim (four_cycle_no_crossing_spokes hshort hn hab hcd
          hx hy he hxa hxc h.1 h.2.1)
  have hbd := four_cycle_spoke_forbids_diagonal hshort hn hab hcd hx hxa hxc
  have hdb : ¬G.Adj d b := fun he => hbd he.symm
  have hbshape : ∀ z, G.Adj b z ↔ z=a ∨ z=c := by
    intro z
    constructor
    · intro h
      by_cases hz : z∈[a,b,c,d]
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact False.elim (h.ne rfl)
        · exact Or.inr rfl
        · exact False.elim (hbd h)
      · exact False.elim ((hall z hz).2.2.1 h.symm)
    · rintro (rfl | rfl)
      · exact hab.symm
      · exact hbc
  have hdshape : ∀ z, G.Adj d z ↔ z=a ∨ z=c := by
    intro z
    constructor
    · intro h
      by_cases hz : z∈[a,b,c,d]
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact False.elim (hdb h)
        · exact Or.inr rfl
        · exact False.elim (h.ne rfl)
      · exact False.elim ((hall z hz).2.2.2 h.symm)
    · rintro (rfl | rfl)
      · exact hda
      · exact hcd.symm
  intro y hya hyc z
  by_cases hy : y∈[a,b,c,d]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact False.elim (hya rfl)
    · exact hbshape z
    · exact False.elim (hyc rfl)
    · exact hdshape z
  · obtain ⟨h₁,h₂,h₃,h₄⟩ := hall y hy
    constructor
    · intro h
      by_cases hz : z∈[a,b,c,d]
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact False.elim (h₃ h)
        · exact Or.inr rfl
        · exact False.elim (h₄ h)
      · exact False.elim (four_cycle_spokes_not_adjacent hshort hn hab hbc
          hy hz h₂ (hall z hz).1 h)
    · rintro (rfl | rfl)
      · exact h₁
      · exact h₂

/-- The arbitrary-order classification of vertex-biconnected graphs with
no cycle of length at least five: above order four they are K₂,t, with
the hub edge optionally present. -/
theorem vertex_robust_no_five_cycle_two_hubs [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    (hshort : Cycle13.NoCycleAtLeast G 5) (horder : 5 ≤ Fintype.card V) :
    ∃ a c, a≠c ∧ ∀ y, y≠a → y≠c → ∀ z, G.Adj y z ↔ z=a ∨ z=c := by
  have hfour : ∃ a, ∃ w : G.Walk a a, w.IsCycle ∧ w.length=4 := by
    by_contra hn
    have hnoc : Cycle13.NoCycleAtLeast G 4 := by
      intro a w hw
      have hh := hshort a w hw
      have hne : w.length≠4 := fun he => hn ⟨a,w,hw,he⟩
      omega
    have hh := vertex_robust_no_four_cycle_order G hconn hrobust hnoc
    omega
  obtain ⟨a,w,hw,hlen⟩ := hfour
  obtain ⟨b,c,d,hn,hab,hbc,hcd,hda,hsupport⟩ := four_cycle_vertices hw hlen
  have hnear : ∀ y, y∉[a,b,c,d] →
      ∃ v∈[a,b,c,d], ∃ z∈[a,b,c,d], v≠z ∧ G.Adj y v ∧ G.Adj y z := by
    intro y hy
    have hyw : y∉w.support := by
      simp only [hsupport,List.mem_cons,List.not_mem_nil,or_false] at *
      tauto
    have hshort' : Cycle13.NoCycleAtLeast G (w.length+1) := by simpa only [hlen] using hshort
    obtain ⟨v,hv,z,hz,hvz,hyv,hyz⟩ :=
      short_longest_cycle_two_neighbors G hconn hrobust w hw (by omega) hshort' y hyw
    refine ⟨v,?_,z,?_,hvz,hyv,hyz⟩ <;>
      simp only [hsupport,List.mem_cons,List.not_mem_nil,or_false] at * <;> tauto
  have houtside : ∃ x, x∉[a,b,c,d] := by
    by_contra hnone
    push_neg at hnone
    have hfull : ([a,b,c,d]:List V).toFinset=univ := by
      apply Finset.eq_univ_of_forall
      intro y
      exact List.mem_toFinset.mpr (hnone y)
    have hh := List.toFinset_card_of_nodup hn
    rw [hfull,Finset.card_univ] at hh
    simp only [List.length_cons,List.length_nil] at hh
    omega
  obtain ⟨x,hx⟩ := houtside
  rcases four_cycle_external_pair hshort hn hab hbc hcd hda hx (hnear x hx) with h | h
  · refine ⟨a,c,?_,four_cycle_two_hub_shape hshort hn hab hbc hcd hda hnear hx h.1 h.2.1⟩
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
    exact hn.1.2.1
  · have hn' : [b,c,d,a].Nodup := by
      simp_all only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.not_mem_nil,
        List.nodup_nil,not_or,not_false_eq_true,and_true,ne_comm] <;> tauto
    have hmem : ∀ z, z∈[b,c,d,a] ↔ z∈[a,b,c,d] := by
      intro z
      simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc,or_left_comm,or_comm]
    have hnear' : ∀ y, y∉[b,c,d,a] →
        ∃ v∈[b,c,d,a], ∃ z∈[b,c,d,a], v≠z ∧ G.Adj y v ∧ G.Adj y z := by
      simpa only [hmem] using hnear
    refine ⟨b,d,?_,four_cycle_two_hub_shape hshort hn' hbc hcd hda hab hnear'
      (by simpa only [hmem] using hx) h.1 h.2.1⟩
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn'
    exact hn'.1.2.1

end
end Cycle12
