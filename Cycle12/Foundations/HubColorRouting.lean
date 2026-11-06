import Cycle12.Foundations.CliqueHop
import Cycle12.Foundations.LiftingClassBounds

namespace Cycle13
open SimpleGraph Finset

def shiftThree : Fin 3 ≃ Fin 3 where
  toFun r := r+1
  invFun r := r+2
  left_inv := by decide
  right_inv := by decide

theorem three_cycle_order : ∀ r s : Fin 3, r≠s → r=s+1 ∨ s=r+1 := by decide

noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem exists_cyclic_balanced_lifting_coloring (a b : I → V) (w : Fin 3 ↪ V)
    (hsep : ∀ r s i, ¬(a i=w r ∧ b i=w s))
    (hd : ∀ v, Suppression.incidenceDegree a b v ≤ 2) :
    ∃ f : (liftingGraph a b).Coloring (Fin 3), (∀ r, f (.inl (w r))=r+1) ∧
      ∀ r s, colorSize (fun v => f (.inl v)) r ≤ colorSize (fun v => f (.inl v)) s+2 := by
  obtain ⟨f,hfixed,hbalance⟩ := exists_balanced_prescribed_lifting_coloring a b w hsep hd
  let g : (liftingGraph a b).Coloring (Fin 3) := Coloring.mk (fun x => shiftThree (f x))
    (fun {x y} hxy he => f.valid hxy (shiftThree.injective he))
  have hsize : ∀ r, colorSize (fun v => g (.inl v)) r=
      colorSize (fun v => f (.inl v)) (shiftThree.symm r) := by
    intro r
    unfold colorSize
    congr 1
    ext v
    simp only [mem_filter,mem_univ,true_and]
    exact shiftThree.apply_eq_iff_eq_symm_apply
  refine ⟨g,?_,?_⟩
  · intro r
    change shiftThree (f (.inl (w r)))=r+1
    rw [hfixed]
    rfl
  · intro r s
    rw [hsize,hsize]
    exact hbalance _ _

lemma liftingColor_endpoint (a b : I → V) (f : (liftingGraph a b).Coloring (Fin 3))
    (i : I) (x : V) (hx : x=a i ∨ x=b i) : f (.inr i)≠f (.inl x) := by
  apply f.valid
  refine ⟨Sum.inr_ne_inl,x,?_,rfl⟩
  exact hx.imp Eq.symm Eq.symm

lemma liftingColor_incident (a b : I → V) (f : (liftingGraph a b).Coloring (Fin 3))
    {i j : I} (hij : i≠j) (x : V) (hi : x=a i ∨ x=b i) (hj : x=a j ∨ x=b j) :
    f (.inr i)≠f (.inr j) := by
  apply f.valid
  exact ⟨Sum.inr_injective.ne hij,x,hi.imp Eq.symm Eq.symm,hj.imp Eq.symm Eq.symm⟩

theorem hub_color_walks_disjoint (a b : I → V) (w : Fin 3 ↪ V)
    (f : (liftingGraph a b).Coloring (Fin 3)) (hw : ∀ r, f (.inl (w r))=r+1) :
    Pairwise (fun i j => Disjoint (hubWalk (a i) (b i) (w (f (.inr i)))).edgeSet
      (hubWalk (a j) (b j) (w (f (.inr j)))).edgeSet) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro e hei hej
  obtain ⟨x,hx,hxn,hex⟩ := (hubWalk_edge _ _ _ e).mp hei
  obtain ⟨y,hy,hyn,hey⟩ := (hubWalk_edge _ _ _ e).mp hej
  rcases Sym2.eq_iff.mp (hex.symm.trans hey) with ⟨hxy,hcc⟩ | ⟨hxz,hzy⟩
  · exact liftingColor_incident a b f hij x hx (hxy.symm ▸ hy) (w.injective hcc)
  · have hci : f (.inr i)≠f (.inr j)+1 := by
      have hh := liftingColor_endpoint a b f i x hx
      rw [hxz,hw] at hh
      exact hh
    have hcj : f (.inr j)≠f (.inr i)+1 := by
      have hh := liftingColor_endpoint a b f j y hy
      rw [← hzy,hw] at hh
      exact hh
    have hne : f (.inr i)≠f (.inr j) := by
      intro h
      exact hxn (hxz.trans (congrArg w h).symm)
    exact (three_cycle_order _ _ hne).elim hci hcj

def hubColorRouting (a b : I → V) (w : Fin 3 ↪ V)
    (f : (liftingGraph a b).Coloring (Fin 3)) (hw : ∀ r, f (.inl (w r))=r+1) :
    DemandRouting (completeGraph V) a b :=
  ⟨fun i => hubWalk (a i) (b i) (w (f (.inr i))),hub_color_walks_disjoint a b w f hw⟩

end
end Cycle13
