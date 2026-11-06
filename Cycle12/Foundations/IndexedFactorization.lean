import Cycle12.Foundations.IndexedFactor

/-! Petersen factorization for finite indexed loopless multigraphs.
Two parallel edges are retained as a valid two-vertex factor component. -/
namespace Cycle13
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

lemma indexedDegreeOn_image (a b : I → V) {J : Type} [Fintype J] [DecidableEq J]
    (e : J ↪ I) (F : Finset J) (v : V) :
    indexedDegreeOn a b (F.image e) v=indexedDegreeOn (a ∘ e) (b ∘ e) F v := by
  unfold indexedDegreeOn
  exact sum_image (fun _ _ _ _ h => e.injective h)

lemma indexedDegreeOn_subtype (a b : I → V) (F : Finset I) (v : V) :
    Suppression.incidenceDegree (fun i : F => a i.val) (fun i : F => b i.val) v=
      indexedDegreeOn a b F v := by
  unfold Suppression.incidenceDegree indexedDegreeOn
  exact (sum_subtype F (p:=fun i => i∈F) (fun i => Iff.rfl)
    (fun i => (if a i=v then (1:ℕ) else 0)+(if b i=v then 1 else 0))).symm

theorem exists_two_factor_in (a b : I → V) (hne : ∀ i, a i≠b i)
    (F : Finset I) {k : ℕ} (hk : 0 < k)
    (hdeg : ∀ v, indexedDegreeOn a b F v=2*k) :
    ∃ A : Finset I, A⊆F ∧ ∀ v, indexedDegreeOn a b A v=2 := by
  obtain ⟨A,hA⟩ := exists_indexed_two_factor (fun i : F => a i.val) (fun i : F => b i.val)
    (fun i => hne i.val) hk (fun v => (indexedDegreeOn_subtype a b F v).trans (hdeg v))
  refine ⟨A.image Subtype.val,?_,?_⟩
  · intro i hi
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
    exact j.property
  · intro v
    exact (indexedDegreeOn_image a b (⟨Subtype.val,Subtype.val_injective⟩ : F ↪ I) A v).trans (hA v)

theorem indexed_petersen_factorization (a b : I → V) (hne : ∀ i, a i≠b i)
    (k : ℕ) (F : Finset I) (hdeg : ∀ v, indexedDegreeOn a b F v=2*k) :
    ∃ factors : Fin k → Finset I,
      (∀ r, factors r⊆F) ∧ (Pairwise fun r s => Disjoint (factors r) (factors s)) ∧
      (∀ i∈F, ∃ r, i∈factors r) ∧
      (∀ r v, indexedDegreeOn a b (factors r) v=2) := by
  induction k generalizing F with
  | zero =>
    have hF : F=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hsum := single_le_sum (fun j (_ : j∈F) =>
        Nat.zero_le ((if a j=a i then 1 else 0)+(if b j=a i then 1 else 0))) hi
      have hd := hdeg (a i)
      unfold indexedDegreeOn at hd
      simp only [ite_true,mul_zero] at hsum hd
      omega
    exact ⟨Fin.elim0,fun r => Fin.elim0 r,fun r => Fin.elim0 r,
      by simp [hF],fun r => Fin.elim0 r⟩
  | succ k ih =>
    obtain ⟨A,hAF,hA⟩ := exists_two_factor_in a b hne F (Nat.succ_pos k) hdeg
    have hrest : ∀ v, indexedDegreeOn a b (F\A) v=2*k := by
      intro v
      have hsum : indexedDegreeOn a b (F\A) v+indexedDegreeOn a b A v=
          indexedDegreeOn a b F v := sum_sdiff hAF
      rw [hA v,hdeg v] at hsum
      omega
    obtain ⟨fs,hfs,hdis,hcover,hfd⟩ := ih (F\A) hrest
    let g : Fin (k+1) → Finset I := Fin.cases A fs
    have hzero : ∀ r, Disjoint A (fs r) := by
      intro r
      exact disjoint_left.mpr (fun i hi hj => (mem_sdiff.mp (hfs r hj)).2 hi)
    refine ⟨g,?_,?_,?_,?_⟩
    · intro r
      refine Fin.cases ?_ (fun j => ?_) r
      · exact hAF
      · exact (hfs j).trans sdiff_subset
    · intro r s
      refine Fin.cases ?_ (fun r' => ?_) r
      · refine Fin.cases ?_ (fun s' hrs => ?_) s
        · intro hrs
          exact False.elim (hrs rfl)
        · exact hzero s'
      · refine Fin.cases ?_ (fun s' hrs => ?_) s
        · intro hrs
          exact (hzero r').symm
        · apply hdis
          intro h
          exact hrs (congrArg Fin.succ h)
    · intro i hi
      by_cases ha : i∈A
      · exact ⟨0,ha⟩
      · obtain ⟨r,hr⟩ := hcover i (mem_sdiff.mpr ⟨hi,ha⟩)
        exact ⟨r.succ,hr⟩
    · intro r v
      exact Fin.cases (hA v) (fun r => hfd r v) r

theorem exists_disjoint_indexed_two_factors (a b : I → V) (hne : ∀ i, a i≠b i)
    {k : ℕ} (hk : 2 ≤ k) (hdeg : ∀ v, Suppression.incidenceDegree a b v=2*k) :
    ∃ A B : Finset I, Disjoint A B ∧
      (∀ v, indexedDegreeOn a b A v=2) ∧ (∀ v, indexedDegreeOn a b B v=2) := by
  obtain ⟨fs,_,hdis,_,hdeg⟩ := indexed_petersen_factorization a b hne k univ hdeg
  let r : Fin k := ⟨0,by omega⟩
  let s : Fin k := ⟨1,by omega⟩
  exact ⟨fs r,fs s,hdis (by intro h; have hh := congrArg Fin.val h; dsimp [r,s] at hh; omega),
    hdeg r,hdeg s⟩

end
end Cycle13
