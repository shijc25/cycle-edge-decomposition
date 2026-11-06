import Cycle12.HCoreCoverage
import Cycle12.HFrame
import Cycle12.TerminalRelabeling

namespace Cycle12
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem terminal_h_base00 (G : SimpleGraph V) (f : Fin 5 ↪ V)
    (hcycle : ∀ i, G.Adj (f i) (f (i+1)))
    (hcover : ∀ v, (∃ i, f i=v)) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  apply terminal_affine_of_labeling G f hcover
  simpa only [Fintype.card_fin] using terminal_h_core00 (G.comap f)
    (hcycle 0) (hcycle 1) (hcycle 2) (hcycle 3) (hcycle 4)

theorem terminal_h_base01 (G : SimpleGraph V) (f : Fin 5 ↪ V)
    (hcycle : ∀ i, G.Adj (f i) (f (i+1)))
    (y : V) (hy : ∀ i, y≠f i)
    (hyshape : ∀ v, G.Adj y v ↔ v=f 0 ∨ v=f 3)
    (hcover : ∀ v, (∃ i, f i=v) ∨ v=y) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  have hyrev : ∀ i, f i≠y := fun i => (hy i).symm
  let F : Fin 6 ↪ V := ⟨![f 0,f 1,f 2,f 3,f 4,y],by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f.injective.eq_iff]⟩
  have hF : ∀ i : Fin 5, F (Fin.castAdd 1 i)=f i := by
    intro i; fin_cases i <;> rfl
  have hsurj : Function.Surjective F := by
    intro v
    rcases hcover v with ⟨i,hi⟩ | rfl
    · refine ⟨Fin.castAdd 1 i,?_⟩
      exact (hF i).trans hi
    · exact ⟨5,rfl⟩
  have h5 : ∀ i, (G.comap F).Adj 5 i ↔ i=0 ∨ i=3 := by
    intro i
    change G.Adj y (F i) ↔ _
    rw [hyshape]
    change (F i=F 0 ∨ F i=F 3) ↔ _
    simp only [F.injective.eq_iff]
  apply terminal_affine_of_labeling G F hsurj
  simpa only [Fintype.card_fin] using terminal_h_core01 (G.comap F)
    (hcycle 0) (hcycle 1) (hcycle 2) (hcycle 3) (hcycle 4) h5

theorem terminal_h_base10 (G : SimpleGraph V) (f : Fin 5 ↪ V)
    (hcycle : ∀ i, G.Adj (f i) (f (i+1)))
    (x : V) (hx : ∀ i, x≠f i)
    (hxshape : ∀ v, G.Adj x v ↔ v=f 0 ∨ v=f 2)
    (hcover : ∀ v, (∃ i, f i=v) ∨ v=x) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  have hxrev : ∀ i, f i≠x := fun i => (hx i).symm
  let F : Fin 6 ↪ V := ⟨![f 0,f 1,f 2,f 3,f 4,x],by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f.injective.eq_iff]⟩
  have hF : ∀ i : Fin 5, F (Fin.castAdd 1 i)=f i := by
    intro i; fin_cases i <;> rfl
  have hsurj : Function.Surjective F := by
    intro v
    rcases hcover v with ⟨i,hi⟩ | rfl
    · refine ⟨Fin.castAdd 1 i,?_⟩
      exact (hF i).trans hi
    · exact ⟨5,rfl⟩
  have h5 : ∀ i, (G.comap F).Adj 5 i ↔ i=0 ∨ i=2 := by
    intro i
    change G.Adj x (F i) ↔ _
    rw [hxshape]
    change (F i=F 0 ∨ F i=F 2) ↔ _
    simp only [F.injective.eq_iff]
  apply terminal_affine_of_labeling G F hsurj
  simpa only [Fintype.card_fin] using terminal_h_core10 (G.comap F)
    (hcycle 0) (hcycle 1) (hcycle 2) (hcycle 3) (hcycle 4) h5

theorem terminal_h_base11 (G : SimpleGraph V) (f : Fin 5 ↪ V)
    (hcycle : ∀ i, G.Adj (f i) (f (i+1)))
    (x : V) (hx : ∀ i, x≠f i)
    (hxshape : ∀ v, G.Adj x v ↔ v=f 0 ∨ v=f 2)
    (y : V) (hy : ∀ i, y≠f i)
    (hyshape : ∀ v, G.Adj y v ↔ v=f 0 ∨ v=f 3)
    (hxy : x≠y)
    (hcover : ∀ v, (∃ i, f i=v) ∨ v=x ∨ v=y) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  have hxrev : ∀ i, f i≠x := fun i => (hx i).symm
  have hyrev : ∀ i, f i≠y := fun i => (hy i).symm
  let F : Fin 7 ↪ V := ⟨![f 0,f 1,f 2,f 3,f 4,x,y],by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f.injective.eq_iff]⟩
  have hF : ∀ i : Fin 5, F (Fin.castAdd 2 i)=f i := by
    intro i; fin_cases i <;> rfl
  have hsurj : Function.Surjective F := by
    intro v
    rcases hcover v with ⟨i,hi⟩ | rfl | rfl
    · refine ⟨Fin.castAdd 2 i,?_⟩
      exact (hF i).trans hi
    · exact ⟨5,rfl⟩
    · exact ⟨6,rfl⟩
  have h5 : ∀ i, (G.comap F).Adj 5 i ↔ i=0 ∨ i=2 := by
    intro i
    change G.Adj x (F i) ↔ _
    rw [hxshape]
    change (F i=F 0 ∨ F i=F 2) ↔ _
    simp only [F.injective.eq_iff]
  have h6 : ∀ i, (G.comap F).Adj 6 i ↔ i=0 ∨ i=3 := by
    intro i
    change G.Adj y (F i) ↔ _
    rw [hyshape]
    change (F i=F 0 ∨ F i=F 3) ↔ _
    simp only [F.injective.eq_iff]
  apply terminal_affine_of_labeling G F hsurj
  simpa only [Fintype.card_fin] using terminal_h_core11 (G.comap F)
    (hcycle 0) (hcycle 1) (hcycle 2) (hcycle 3) (hcycle 4) h5 h6

end
end Cycle12
