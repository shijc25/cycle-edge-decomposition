import Cycle12.BlockEdgePartition12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

/-- The local conditions actually left by the two pairing passes and the
matching grouping imply that full contraction neither deletes nor identifies
retained edges. -/
theorem contracted_retained_edges (H : SimpleGraph V) (A : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hinside : ∀ i x y, x∈A i → y∈A i → ¬H.Adj x y)
    (hpair : ∀ i j, i ≠ j →
      Set.Subsingleton (edgeLabelGraph H (blockLabel A) s(some i,some j)).edgeSet)
    (hout : ∀ i v, v∉blockUnion A →
      Set.Subsingleton {u : V | H.Adj v u ∧ u∈A i}) :
    (∀ {x y}, H.Adj x y → contractVertex A x ≠ contractVertex A y) ∧
      Set.InjOn (Sym2.map (contractVertex A)) H.edgeSet := by
  have proper {x y : V} (hxy : H.Adj x y) : contractVertex A x ≠ contractVertex A y := by
    intro he
    cases hx : contractVertex A x with
    | inl i =>
      have hy := hx.symm.trans he
      exact hinside i x y ((contractVertex_eq_inl_iff A hd x i).mp hx)
        ((contractVertex_eq_inl_iff A hd y i).mp hy.symm) hxy
    | inr v =>
      have hxx := (contractVertex_eq_inr_iff A x v).mp hx
      have hyy := (contractVertex_eq_inr_iff A y v).mp (he.symm.trans hx)
      exact hxy.ne (hxx.trans hyy.symm)
  have oriented {x y u v : V} (hxy : H.Adj x y) (huv : H.Adj u v)
      (hxu : contractVertex A x=contractVertex A u)
      (hyv : contractVertex A y=contractVertex A v) : s(x,y)=s(u,v) := by
    cases hx : contractVertex A x with
    | inl i =>
      have hxi := (contractVertex_eq_inl_iff A hd x i).mp hx
      have hui := (contractVertex_eq_inl_iff A hd u i).mp (hxu.symm.trans hx)
      cases hy : contractVertex A y with
      | inl j =>
        have hyj := (contractVertex_eq_inl_iff A hd y j).mp hy
        have hvj := (contractVertex_eq_inl_iff A hd v j).mp (hyv.symm.trans hy)
        have hij : i ≠ j := by
          intro he
          exact proper hxy (hx.trans ((congrArg Sum.inl he).trans hy.symm))
        apply hpair i j hij
        · exact (block_cross_graph H A hd i j x y).mpr ⟨hxy,Or.inl ⟨hxi,hyj⟩⟩
        · exact (block_cross_graph H A hd i j u v).mpr ⟨huv,Or.inl ⟨hui,hvj⟩⟩
      | inr z =>
        have hyz := (contractVertex_eq_inr_iff A y z).mp hy
        have hvz := (contractVertex_eq_inr_iff A v z).mp (hyv.symm.trans hy)
        have hyv' : y=v := hyz.trans hvz.symm
        have hxu' : x=u := hout i z.val z.property
          ⟨hyz ▸ hxy.symm,hxi⟩ ⟨hvz ▸ huv.symm,hui⟩
        rw [hxu',hyv']
    | inr z =>
      have hxz := (contractVertex_eq_inr_iff A x z).mp hx
      have huz := (contractVertex_eq_inr_iff A u z).mp (hxu.symm.trans hx)
      have hxu' : x=u := hxz.trans huz.symm
      cases hy : contractVertex A y with
      | inl j =>
        have hyj := (contractVertex_eq_inl_iff A hd y j).mp hy
        have hvj := (contractVertex_eq_inl_iff A hd v j).mp (hyv.symm.trans hy)
        have hyv' : y=v := hout j z.val z.property
          ⟨hxz ▸ hxy,hyj⟩ ⟨huz ▸ huv,hvj⟩
        rw [hxu',hyv']
      | inr t =>
        have hyt := (contractVertex_eq_inr_iff A y t).mp hy
        have hvt := (contractVertex_eq_inr_iff A v t).mp (hyv.symm.trans hy)
        rw [hxu',hyt.trans hvt.symm]
  refine ⟨fun {_ _} h => proper h,?_⟩
  intro e he f hf hef
  induction e using Sym2.inductionOn with
  | _ x y =>
    induction f using Sym2.inductionOn with
    | _ u v =>
      change s(contractVertex A x,contractVertex A y)=s(contractVertex A u,contractVertex A v) at hef
      rcases Sym2.eq_iff.mp hef with ⟨hxu,hyv⟩|⟨hxv,hyu⟩
      · exact oriented he hf hxu hyv
      · exact (oriented he (show H.Adj v u from hf.symm) hxv hyu).trans Sym2.eq_swap

end
end Cycle12
