import Cycle12.Foundations.HubColorRouting

/-! The actual simple graph occupied by hub routes. At every non-hub
vertex its degree equals the original indexed demand degree. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def indexedHubGraph (a b hub : I → V) : SimpleGraph V where
  Adj x y := x≠y ∧ ∃ i, ((x=a i ∨ x=b i) ∧ y=hub i) ∨ ((y=a i ∨ y=b i) ∧ x=hub i)
  symm := ⟨by rintro x y ⟨hne,i,h⟩; exact ⟨hne.symm,i,h.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem indexedHubGraph_edge (a b hub : I → V) (e : Sym2 V) :
    e∈(indexedHubGraph a b hub).edgeSet ↔ ∃ i, e∈(hubWalk (a i) (b i) (hub i)).edgeSet := by
  induction e using Sym2.inductionOn with
  | _ x y =>
    change (x≠y ∧ ∃ i, ((x=a i ∨ x=b i) ∧ y=hub i) ∨ ((y=a i ∨ y=b i) ∧ x=hub i)) ↔ _
    simp only [hubWalk_edge]
    constructor
    · rintro ⟨hne,i,(⟨hx,hy⟩ | ⟨hy,hx⟩)⟩
      · exact ⟨i,x,hx,hy ▸ hne,congrArg (fun z => s(x,z)) hy⟩
      · exact ⟨i,y,hy,hx ▸ hne.symm,(Sym2.eq_swap).trans (congrArg (fun z => s(y,z)) hx)⟩
    · rintro ⟨i,z,hz,hne,he⟩
      rcases Sym2.eq_iff.mp he with h | h
      · exact ⟨fun hxy => hne (h.1.symm.trans (hxy.trans h.2)),i,Or.inl ⟨hz.imp h.1.trans h.1.trans,h.2⟩⟩
      · exact ⟨fun hxy => hne (h.2.symm.trans (hxy.symm.trans h.1)),i,Or.inr ⟨hz.imp h.2.trans h.2.trans,h.1⟩⟩

theorem indexedIncident_card_eq (a b : I → V) (hne : ∀ i, a i≠b i) (v : V) :
    (indexedIncident a b v).card=Suppression.incidenceDegree a b v := by
  have hp : ∀ i, (if a i=v ∨ b i=v then (1:ℕ) else 0)=
      (if a i=v then 1 else 0)+(if b i=v then 1 else 0) := by
    intro i
    by_cases ha : a i=v <;> by_cases hb : b i=v
    · exact (hne i (ha.trans hb.symm)).elim
    all_goals simp [ha,hb]
  have hh := sum_congr (s₁:=(univ : Finset I)) rfl (fun i _ => hp i)
  simpa only [sum_boole,Nat.cast_id,indexedIncident,Suppression.incidenceDegree] using hh

theorem indexedHubGraph_degree (a b hub : I → V) (hne : ∀ i, a i≠b i) (v : V)
    (hv : ∀ i, v≠hub i)
    (hinj : Set.InjOn hub {i | a i=v ∨ b i=v}) :
    (indexedHubGraph a b hub).degree v=Suppression.incidenceDegree a b v := by
  have he : (indexedHubGraph a b hub).neighborSet v=hub '' {i | a i=v ∨ b i=v} := by
    ext z
    constructor
    · rintro ⟨hvn,i,(⟨hvi,hz⟩ | ⟨hzi,hv'⟩)⟩
      · exact ⟨i,hvi.imp Eq.symm Eq.symm,hz.symm⟩
      · exact (hv i hv').elim
    · rintro ⟨i,hi,rfl⟩
      exact ⟨hv i,i,Or.inl ⟨hi.imp Eq.symm Eq.symm,rfl⟩⟩
  have hc : (indexedIncident a b v).card={i : I | a i=v ∨ b i=v}.ncard := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp only [indexedIncident,mem_coe,mem_filter,mem_univ,true_and,Set.mem_setOf_eq]
  rw [← ncard_neighborSet,he,hinj.ncard_image,← hc,indexedIncident_card_eq a b hne]

theorem colored_hub_degree (a b : I → V) (hne : ∀ i, a i≠b i) (w : Fin 3 ↪ V)
    (f : (liftingGraph a b).Coloring (Fin 3)) (v : V) (hv : ∀ r, v≠w r) :
    (indexedHubGraph a b (fun i => w (f (.inr i)))).degree v=Suppression.incidenceDegree a b v := by
  apply indexedHubGraph_degree a b _ hne v (fun i => hv _)
  intro i hi j hj he
  by_contra hn
  exact liftingColor_incident a b f hn v (hi.imp Eq.symm Eq.symm) (hj.imp Eq.symm Eq.symm)
    (w.injective he)

theorem colored_hub_avoids_class (a b : I → V) (w : Fin 3 ↪ V)
    (f : (liftingGraph a b).Coloring (Fin 3)) (r : Fin 3) (v : V)
    (hv : ∀ s, v≠w s) (hc : f (.inl v)=r) :
    ¬(indexedHubGraph a b (fun i => w (f (.inr i)))).Adj (w r) v := by
  rintro ⟨hne,i,(⟨hi,hvi⟩ | ⟨hi,hwi⟩)⟩
  · exact hv _ hvi
  · have hh := liftingColor_endpoint a b f i v hi
    have he : r=f (.inr i) := w.injective hwi
    exact hh (he.symm.trans hc.symm)

theorem indexedHubGraph_touches_hubs (a b hub : I → V) {x y : V}
    (h : (indexedHubGraph a b hub).Adj x y) : x∈Set.range hub ∨ y∈Set.range hub := by
  obtain ⟨hne,i,h⟩ := h
  rcases h with h | h
  · exact Or.inr ⟨i,h.2.symm⟩
  · exact Or.inl ⟨i,h.2.symm⟩

end
end Cycle13
