import Cycle12.CycleFanBounds

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem cycle_support_card_exact {G : SimpleGraph V} {u : V}
    {c : G.Walk u u} (hc : c.IsCycle) : c.support.toFinset.card=c.length := by
  have he : c.support.toFinset=c.support.tail.toFinset := by
    rw [← c.cons_tail_support,List.toFinset_cons]
    apply Finset.insert_eq_of_mem
    exact List.mem_toFinset.mpr (c.end_mem_tail_support hc.not_nil)
  rw [he,List.toFinset_card_of_nodup hc.support_nodup,List.length_tail,c.length_support]
  omega

theorem exists_cycle_of_vertex_robust (G : SimpleGraph V) (hconn : G.Connected)
    (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    (hn : 3 ≤ Fintype.card V) : ∃ u, ∃ c : G.Walk u u, c.IsCycle := by
  by_contra hnone
  have hacyclic : G.IsAcyclic := by
    intro u c hc
    exact hnone ⟨u,c,hc⟩
  have htree : G.IsTree := ⟨hconn,hacyclic⟩
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v,hv⟩ := htree.exists_vert_degree_one_of_nontrivial
  obtain ⟨a,hva,hunique⟩ := G.degree_eq_one_iff_existsUnique_adj.mp hv
  have hR : (({v,a}:Finset V)ᶜ).Nonempty := by
    apply Finset.card_pos.mp
    have hh := Finset.card_add_card_compl ({v,a}:Finset V)
    rw [Finset.card_pair hva.ne] at hh
    omega
  obtain ⟨b,hb⟩ := hR
  have hbne : b≠v ∧ b≠a := by simpa only [mem_compl,mem_insert,mem_singleton,not_or] using hb
  have hvin : v∈({a}ᶜ : Set V) := hva.ne
  have hbin : b∈({a}ᶜ : Set V) := hbne.2
  obtain ⟨p⟩ := hrobust a ⟨v,hvin⟩ ⟨b,hbin⟩
  have hends : (⟨v,hvin⟩ : ({a}ᶜ : Set V))≠⟨b,hbin⟩ := by
    intro he
    exact hbne.1 (congrArg Subtype.val he).symm
  obtain ⟨z,hz,_,_⟩ := Walk.exists_eq_cons_of_ne hends p
  have hzadj : G.Adj v z.val := hz
  have hza : z.val=a := hunique z.val hzadj
  exact z.property hza

/-- A vertex-biconnected graph with no cycle of length four or more
cannot have more than three vertices. -/
theorem vertex_robust_no_four_cycle_order (G : SimpleGraph V) (hconn : G.Connected)
    (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    (hshort : Cycle13.NoCycleAtLeast G 4) : Fintype.card V ≤ 3 := by
  by_contra hlarge
  obtain ⟨u,c,hc⟩ := exists_cycle_of_vertex_robust G hconn hrobust (by omega)
  have hlen : c.length=3 := by have h₁ := hc.three_le_length; have h₂ := hshort u c hc; omega
  have hs := cycle_support_card_exact hc
  have houtside : ∃ x, x∉c.support := by
    by_contra hn
    push_neg at hn
    have hfull : c.support.toFinset=Finset.univ := by ext x; simp [hn x]
    rw [hfull,Finset.card_univ,hlen] at hs
    omega
  obtain ⟨x,hx⟩ := houtside
  have hsize : 2 ≤ c.support.toFinset.card := by omega
  obtain ⟨a,ha,b,hb,hab,p,q,hp,hq,hpout,hqout,hcommon⟩ :=
    two_fan_to_set G c.support.toFinset hsize hconn hrobust x (by simpa using hx)
  have ha' : a∈c.support := List.mem_toFinset.mp ha
  have hb' : b∈c.support := List.mem_toFinset.mp hb
  have hpout' : ∀ z∈p.support, z≠a → z∉c.support := by simpa only [List.mem_toFinset] using hpout
  have hqout' : ∀ z∈q.support, z≠b → z∉c.support := by simpa only [List.mem_toFinset] using hqout
  have hshort' : Cycle13.NoCycleAtLeast G (c.length+1) := by simpa only [hlen] using hshort
  have hfan := two_fan_longest_cycle_length hc ha' hb' hab hx hp hq hpout' hqout' hcommon hshort'
  have hxa : x≠a := fun he => hx (he ▸ ha')
  have hxb : x≠b := fun he => hx (he ▸ hb')
  have hp₁ : 0 < p.length :=
    Nat.pos_of_ne_zero (fun he => Walk.not_nil_of_ne hxa (Walk.length_eq_zero_iff.mp he))
  have hq₁ : 0 < q.length :=
    Nat.pos_of_ne_zero (fun he => Walk.not_nil_of_ne hxb (Walk.length_eq_zero_iff.mp he))
  omega

end
end Cycle12
