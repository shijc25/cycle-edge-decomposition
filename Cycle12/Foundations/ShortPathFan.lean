import Cycle12.Foundations.HaxellRoutingSelect

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {a b : V}

structure ShortPathFan (G : SimpleGraph V) (a b : V) (ell n : ℕ)
    (Good : G.Walk a b → Prop) where
  path : Fin n → G.Walk a b
  simple : ∀ i, (path i).IsPath
  length_le : ∀ i, (path i).length ≤ ell
  good : ∀ i, Good (path i)
  interior_disjoint : Pairwise fun i j => Disjoint (routeInterior (path i)) (routeInterior (path j))

namespace ShortPathFan
variable {ell n : ℕ} {Good : G.Walk a b → Prop}

def used (P : ShortPathFan G a b ell n Good) : Finset V :=
  Finset.univ.biUnion fun i => routeInterior (P.path i)

theorem used_card_le (P : ShortPathFan G a b ell n Good) : P.used.card ≤ n*ell := by
  calc
    _ ≤ ∑ i, (routeInterior (P.path i)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin n, ell := Finset.sum_le_sum fun i _ =>
      (routeInterior_card_le _).trans (P.length_le i)
    _ = _ := by simp

theorem source_not_mem_used (P : ShortPathFan G a b ell n Good) : a ∉ P.used := by
  simp [used,mem_routeInterior_iff]

theorem target_not_mem_used (P : ShortPathFan G a b ell n Good) : b ∉ P.used := by
  simp [used,mem_routeInterior_iff]

def cons (P : ShortPathFan G a b ell n Good) (p : G.Walk a b)
    (hp : p.IsPath) (hlen : p.length ≤ ell) (hgood : Good p)
    (hd : Disjoint (routeInterior p) P.used) : ShortPathFan G a b ell (n+1) Good where
  path := Fin.cases p P.path
  simple := Fin.cases hp P.simple
  length_le := Fin.cases hlen P.length_le
  good := Fin.cases hgood P.good
  interior_disjoint := by
    intro i j hij
    have hd₁ : ∀ j, Disjoint (routeInterior p) (routeInterior (P.path j)) := by
      intro j
      apply hd.mono_right
      intro v hv
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hv⟩
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => exact hd₁ j
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (hd₁ i).symm
      | succ j => exact P.interior_disjoint (fun h => hij (congrArg Fin.succ h))

theorem sum_weight_le (P : ShortPathFan G a b ell n Good) (w : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) :
    (∑ i, ∑ v ∈ routeInterior (P.path i), w v) ≤ ∑ v, w v := by
  have hd : (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint (fun i => routeInterior (P.path i)) :=
    fun i _ j _ hij => P.interior_disjoint hij
  rw [← Finset.sum_biUnion hd]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => hw v)

theorem exists_weight_le_average {n : ℕ} (hn : 0 < n)
    (P : ShortPathFan G a b ell n Good) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∃ i, (∑ v ∈ routeInterior (P.path i), w v) ≤ (∑ v, w v)/n := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  by_contra! hbad
  have hh := Finset.sum_lt_sum_of_nonempty (s:=Finset.univ) Finset.univ_nonempty
    (fun i _ => hbad i)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have he : (∑ _i : Fin n, (∑ v, w v)/(n:ℝ))=∑ v,w v := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  rw [he] at hh
  exact (not_lt_of_ge (P.sum_weight_le w hw)) hh

end ShortPathFan

/-- Greedy construction of a whole short-path fan. The premise only
requires one path after deleting at most K*ell interior vertices. -/
theorem exists_short_path_fan (Good : G.Walk a b → Prop) {ell K : ℕ}
    (hpath : ∀ X : Finset V, X.card ≤ K*ell → a ∉ X → b ∉ X →
      ∃ p : G.Walk a b, p.IsPath ∧ p.length ≤ ell ∧ Good p ∧
        Disjoint (routeInterior p) X) : Nonempty (ShortPathFan G a b ell (K+1) Good) := by
  have step : ∀ n : ℕ, n ≤ K+1 → Nonempty (ShortPathFan G a b ell n Good) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨{ path := fun i => i.elim0
               simple := fun i => i.elim0
               length_le := fun i => i.elim0
               good := fun i => i.elim0
               interior_disjoint := fun i => i.elim0 }⟩
    | succ n ih =>
      intro hn
      obtain ⟨P⟩ := ih (by omega)
      have hbound : P.used.card ≤ K*ell :=
        P.used_card_le.trans (Nat.mul_le_mul_right _ (by omega))
      obtain ⟨p,hp,hlen,hgood,hd⟩ := hpath P.used hbound P.source_not_mem_used P.target_not_mem_used
      exact ⟨P.cons p hp hlen hgood hd⟩
  exact step (K+1) le_rfl

end
end Cycle13
