import Cycle12.Foundations.CloneObstruction

/-! A matching of the clone complement gives distinct, loop-free new
edges, all absent from the old graph. This is the well-suppression bridge. -/
namespace Cycle13
open SimpleGraph GallaiEdmonds
noncomputable section
attribute [local instance] Classical.propDecidable

def cloneOrigin {V : Type} (R : Finset V) : V ⊕ R → V := Sum.elim id Subtype.val

namespace CloneMatching
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {R : Finset V}

lemma origin_ne_of_adj {x y : V ⊕ R} (h : (cloneGraph G R)ᶜ.Adj x y) :
    cloneOrigin R x ≠ cloneOrigin R y := by
  have h' := (compl_adj (cloneGraph G R) x y).mp h
  rcases x with x | x <;> rcases y with y | y
  · exact fun he => h'.1 (congrArg Sum.inl he)
  · intro he
    change x=y.val at he
    exact h'.2 (Or.inl (he ▸ y.property))
  · intro he
    change x.val=y at he
    exact h'.2 (Or.inl (he ▸ x.property))
  · exact False.elim (h'.2 (fun he => h'.1 (congrArg Sum.inr he)))

lemma not_adj_of_adj {x y : V ⊕ R} (h : (cloneGraph G R)ᶜ.Adj x y) :
    ¬ G.Adj (cloneOrigin R x) (cloneOrigin R y) := by
  have h' := (compl_adj (cloneGraph G R) x y).mp h
  rcases x with x | x <;> rcases y with y | y
  · exact h'.2
  · exact fun he => h'.2 (Or.inr he)
  · exact fun he => h'.2 (Or.inr he)
  · exact False.elim (h'.2 (fun he => h'.1 (congrArg Sum.inr he)))

lemma origin_eq_of_not_mem {x y : V ⊕ R} (hx : cloneOrigin R x ∉ R)
    (h : cloneOrigin R x=cloneOrigin R y) : x=y := by
  rcases x with x | x <;> rcases y with y | y
  · exact congrArg Sum.inl h
  · exact False.elim (hx (h ▸ y.property))
  · exact False.elim (hx x.property)
  · exact False.elim (hx x.property)

lemma clone_adj_origin_not_mem {x : R} {y : V ⊕ R}
    (h : (cloneGraph G R)ᶜ.Adj (Sum.inr x) y) : cloneOrigin R y ∉ R := by
  have h' := (compl_adj (cloneGraph G R) _ _).mp h
  rcases y with y | y
  · exact fun hy => h'.2 (Or.inl hy)
  · exact False.elim (h'.2 (fun he => h'.1 (congrArg Sum.inr he)))

lemma matched_eq_of_origins (M : (cloneGraph G R)ᶜ.Subgraph) (hM : M.IsMatching)
    {x y a b : V ⊕ R} (hxy : M.Adj x y) (hab : M.Adj a b)
    (hx : cloneOrigin R x=cloneOrigin R a) (hy : cloneOrigin R y=cloneOrigin R b) :
    x=a ∧ y=b := by
  rcases x with x | x <;> rcases a with a | a
  · have he : x=a := hx
    subst a
    exact ⟨rfl,hM.eq_of_adj_left hxy hab⟩
  · have hb := clone_adj_origin_not_mem (M.adj_sub hab)
    have hyb : y=b := (origin_eq_of_not_mem hb hy.symm).symm
    subst b
    exact ⟨hM.eq_of_adj_right hxy hab,rfl⟩
  · have hy' := clone_adj_origin_not_mem (M.adj_sub hxy)
    have hyb : y=b := origin_eq_of_not_mem hy' hy
    subst b
    exact ⟨hM.eq_of_adj_right hxy hab,rfl⟩
  · have he : x=a := Subtype.ext hx
    subst a
    exact ⟨rfl,hM.eq_of_adj_left hxy hab⟩

theorem output_edge_injective (M : (cloneGraph G R)ᶜ.Subgraph) (hM : M.IsMatching) :
    Set.InjOn (Sym2.map (cloneOrigin R)) M.edgeSet := by
  intro e he f hf hef
  induction e using Sym2.ind with
  | h x y =>
    induction f using Sym2.ind with
    | h a b =>
      have hxy : M.Adj x y := he
      have hab : M.Adj a b := hf
      change s(cloneOrigin R x,cloneOrigin R y)=s(cloneOrigin R a,cloneOrigin R b) at hef
      rcases Sym2.eq_iff.mp hef with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · obtain ⟨rfl,rfl⟩ := matched_eq_of_origins M hM hxy hab hx hy
        rfl
      · obtain ⟨rfl,rfl⟩ := matched_eq_of_origins M hM hxy hab.symm hx hy
        exact Sym2.eq_swap

def outputGraph (M : (cloneGraph G R)ᶜ.Subgraph) : SimpleGraph V :=
  M.spanningCoe.map (cloneOrigin R)

theorem output_disjoint (M : (cloneGraph G R)ᶜ.Subgraph) : Disjoint G (outputGraph M) := by
  apply SimpleGraph.disjoint_left.mpr
  intro v w hG hO
  obtain ⟨_,x,y,hxy,hx,hy⟩ := hO
  subst v
  subst w
  exact not_adj_of_adj (M.adj_sub hxy) hG

theorem output_degree (M : (cloneGraph G R)ᶜ.Subgraph) (hM : M.IsMatching) (v : V) :
    (outputGraph M).degree v =
      (Finset.univ.filter (fun x : V ⊕ R => x ∈ M.verts ∧ cloneOrigin R x=v)).card := by
  classical
  let S := Finset.univ.filter (fun x : V ⊕ R => x ∈ M.verts ∧ cloneOrigin R x=v)
  let f : S → (outputGraph M).neighborSet v := fun x =>
    ⟨cloneOrigin R (partner hM x.val),by
      have hx := (Finset.mem_filter.mp x.property).2
      have hadj := partner_adj hM hx.1
      have hO : (outputGraph M).Adj (cloneOrigin R x.val)
          (cloneOrigin R (partner hM x.val)) :=
        SimpleGraph.map_adj_apply' hadj (origin_ne_of_adj (M.adj_sub hadj))
      exact hx.2 ▸ hO⟩
  have hf : Function.Injective f := by
    intro x y h
    have hx := (Finset.mem_filter.mp x.property).2
    have hy := (Finset.mem_filter.mp y.property).2
    have hcol : cloneOrigin R (partner hM x.val)=cloneOrigin R (partner hM y.val) :=
      congrArg Subtype.val h
    have he := matched_eq_of_origins M hM (partner_adj hM hx.1) (partner_adj hM hy.1)
      (hx.2.trans hy.2.symm) hcol
    exact Subtype.ext he.1
  have hs : Function.Surjective f := by
    intro w
    obtain ⟨_,x,y,hxy,hx,hy⟩ := w.property
    let xS : S := ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,M.edge_vert hxy,hx⟩⟩
    refine ⟨xS,Subtype.ext ?_⟩
    change cloneOrigin R (partner hM x)=w.val
    rw [partner_eq hM hxy]
    exact hy
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hf,hs⟩)
  simpa only [Fintype.card_coe,card_neighborSet_eq_degree] using hc.symm

lemma origin_fiber_card (v : V) :
    (Finset.univ.filter (fun x : V ⊕ R => cloneOrigin R x=v)).card =
      1+(if v ∈ R then 1 else 0) := by
  classical
  by_cases hv : v ∈ R
  · have heq : Finset.univ.filter (fun x : V ⊕ R => cloneOrigin R x=v) =
        {Sum.inl v,Sum.inr ⟨v,hv⟩} := by
      ext x
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      rcases x with x | x <;> simp [cloneOrigin,Subtype.ext_iff]
    rw [heq]
    simp [hv]
  · have heq : Finset.univ.filter (fun x : V ⊕ R => cloneOrigin R x=v)={Sum.inl v} := by
      ext x
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      rcases x with x | x
      · simp [cloneOrigin]
      · have hne : x.val ≠ v := fun h => hv (h ▸ x.property)
        simp [cloneOrigin,hne]
    rw [heq]
    simp [hv]

theorem perfect_output_degree (M : (cloneGraph G R)ᶜ.Subgraph) (hM : M.IsMatching)
    (hcover : M.verts=Set.univ) (v : V) :
    (outputGraph M).degree v=1+(if v ∈ R then 1 else 0) := by
  rw [output_degree M hM,hcover]
  simp only [Set.mem_univ,true_and]
  exact origin_fiber_card v

theorem near_perfect_output_degree (M : (cloneGraph G R)ᶜ.Subgraph) (hM : M.IsMatching)
    (z : V ⊕ R) (hcover : M.verts=Set.univ \ {z}) (v : V) :
    (outputGraph M).degree v+(if cloneOrigin R z=v then 1 else 0)=
      1+(if v ∈ R then 1 else 0) := by
  classical
  let F := Finset.univ.filter (fun x : V ⊕ R => cloneOrigin R x=v)
  have heq : Finset.univ.filter (fun x : V ⊕ R =>
      x ∈ M.verts ∧ cloneOrigin R x=v)=F.erase z := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase]
    simp [F,hcover,and_comm]
  rw [output_degree M hM,heq,← origin_fiber_card v]
  change (F.erase z).card+(if cloneOrigin R z=v then 1 else 0)=F.card
  by_cases hz : cloneOrigin R z=v
  · rw [if_pos hz]
    exact Finset.card_erase_add_one (by simp [F,hz])
  · rw [if_neg hz,Finset.erase_eq_of_notMem (by simpa [F] using hz),Nat.add_zero]

end CloneMatching
end
end Cycle13
