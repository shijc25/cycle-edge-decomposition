import Cycle12.Foundations.HighNeighborMatching
import Cycle12.Foundations.NeighborNearMatching
import Cycle12.Foundations.SplitDegrees
import Cycle12.Foundations.RoutingComposition
import Cycle12.Foundations.GraphRelabel

/-! Simultaneously suppress an independent set of high vertices. Distinct
reserved neighbours ensure that each retained vertex loses at most one degree. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

theorem reduce_independent_high_vertices_aux (d D t n : ℕ) :
    ∀ {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V),
    Fintype.card V=n →
    ∀ (A : Finset V) (g : A ↪ V),
      (¬Nonempty (StrongCliqueImmersion t G)) →
      (∀ v, d-1 ≤ G.degree v) →
      (∀ v ∈ A, D+t < G.degree v) →
      (∀ v, v∉A → G.degree v ≤ D+t) →
      (∀ x∈A, ∀ y∈A, ¬G.Adj x y) →
      (∀ x∈A, ∀ y, G.Adj x y → G.degree y ≤ D) →
      (∀ x : A, G.Adj x.val (g x)) →
      (∀ x : A, d ≤ G.degree (g x)) →
      ∃ m : ℕ, 0 < m ∧ ∃ H : SimpleGraph (Fin m),
        Nonempty (EdgeRouting H G) ∧ ∀ v, d-1 ≤ H.degree v ∧ H.degree v ≤ D+t := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ _ G hn A g hno hmin hhigh hout hind hnei hgadj hgdeg
    by_cases hA : A.Nonempty
    · obtain ⟨u,hu⟩ := hA
      let a : A := ⟨u,hu⟩
      have hgu : g a≠u := (hgadj a).ne.symm
      obtain ⟨M,hM,hcov⟩ := exists_neighbor_matching_except G u hno
        (hhigh u hu) (hnei u hu) ⟨g a,hgadj a⟩
      let U := ({u}ᶜ : Set V)
      let H := splitGraph G u M
      letI : Nonempty U := ⟨⟨g a,hgu⟩⟩
      let B : Finset U := univ.filter (fun v => v.val∈A)
      let old : B → A := fun v => ⟨v.val.val,(mem_filter.mp v.property).2⟩
      have hnotu : ∀ x : B, g (old x)≠u := by
        intro x he
        have hadj := hgadj (old x)
        rw [he] at hadj
        exact hind _ (old x).property u hu hadj
      let g' : B ↪ U := {
        toFun := fun x => ⟨g (old x),hnotu x⟩
        inj' := by
          intro x y he
          have hh := g.injective (congrArg Subtype.val he)
          exact Subtype.ext (Subtype.ext (congrArg (fun z : A => z.val) hh)) }
      have hB : ∀ x : U, x∈B ↔ x.val∈A := by intro x; simp [B]
      have hnotnei : ∀ x : U, x∈B → ¬G.Adj u x.val :=
        fun x hx => hind u hu x.val ((hB x).mp hx)
      have hbounds : ∀ x : U, H.degree x ≤ G.degree x.val ∧
          G.degree x.val ≤ H.degree x+1 := by
        intro x
        simpa only [H,← ncard_neighborSet] using split_degree_bounds G u M hM x
      have heqhigh : ∀ x : U, x∈B → H.degree x=G.degree x.val := by
        intro x hx
        simpa only [H,← ncard_neighborSet] using
          split_degree_eq_of_not_neighbor G u M hM x (hnotnei x hx)
      have heqother : ∀ x : U, x.val≠g a → H.degree x=G.degree x.val := by
        intro x hx
        have hh := split_degree_eq_of_covered G u M hM x (by
          intro b hb
          apply hcov b
          intro he
          have hh := congrArg Subtype.val he
          exact hx (hb.symm.trans hh))
        simpa only [H,← ncard_neighborSet] using hh
      have hnewmin : ∀ x : U, d-1 ≤ H.degree x := by
        intro x
        by_cases hx : x.val=g a
        · have hb := (hbounds x).2
          have hm := hgdeg a
          simp only [← ncard_neighborSet] at hb hm ⊢
          rw [hx] at hb
          omega
        · rw [heqother x hx]
          exact hmin _
      have hnewhigh : ∀ x∈B, D+t < H.degree x := by
        intro x hx
        rw [heqhigh x hx]
        exact hhigh _ ((hB x).mp hx)
      have hnewout : ∀ x : U, x∉B → H.degree x ≤ D+t := by
        intro x hx
        exact (hbounds x).1.trans (hout _ (fun h => hx ((hB x).mpr h)))
      have hnewind : ∀ x∈B, ∀ y∈B, ¬H.Adj x y := by
        intro x hx y hy hxy
        apply hind _ ((hB x).mp hx) _ ((hB y).mp hy)
        exact (split_adj_iff_of_not_neighbor G u M x y (hnotnei x hx)).mp hxy
      have hnewnei : ∀ x∈B, ∀ y, H.Adj x y → H.degree y ≤ D := by
        intro x hx y hxy
        have hadj := (split_adj_iff_of_not_neighbor G u M x y (hnotnei x hx)).mp hxy
        exact (hbounds y).1.trans (hnei _ ((hB x).mp hx) _ hadj)
      have hnewgadj : ∀ x : B, H.Adj x.val (g' x) := by
        intro x
        apply (split_adj_iff_of_not_neighbor G u M x.val (g' x) (hnotnei _ x.property)).mpr
        exact hgadj (old x)
      have hnewgdeg : ∀ x : B, d ≤ H.degree (g' x) := by
        intro x
        have hne : (g' x).val≠g a := by
          intro he
          have hh := g.injective he
          exact x.val.property (congrArg Subtype.val hh)
        rw [heqother (g' x) hne]
        exact hgdeg (old x)
      have hnewno : ¬Nonempty (StrongCliqueImmersion t H) := fun hm =>
        hno (strong_clique_lifts_through_split G u M hM hm)
      have hsmall : Fintype.card U < n := by
        have hc : Fintype.card U=Fintype.card V-1 := by
          dsimp [U]
          rw [Fintype.card_compl_set]
          simp
        have hp : 0<Fintype.card V := Fintype.card_pos
        omega
      obtain ⟨m,hm,K,⟨R⟩,hK⟩ := ih (Fintype.card U) hsmall H rfl B g'
        hnewno hnewmin hnewhigh hnewout hnewind hnewnei hnewgadj hnewgdeg
      exact ⟨m,hm,K,⟨(vertexSplitRouting G u M hM).compose R⟩,hK⟩
    · have hAe : A=∅ := not_nonempty_iff_eq_empty.mp hA
      let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
      refine ⟨Fintype.card V,Fintype.card_pos,G.comap e,
        ⟨EdgeRouting.ofCopy (graphRelabelIso G e).toCopy⟩,?_⟩
      intro v
      rw [degree_comap_equiv]
      exact ⟨hmin _,hout _ (by simp [hAe])⟩

theorem exists_bounded_degree_reduction {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) {d t : ℕ} (hd : 0<d)
    (hmin : ∀ v, d ≤ G.degree v) (hno : ¬Nonempty (StrongCliqueImmersion t G)) :
    ∃ m : ℕ, 0 < m ∧ ∃ H : SimpleGraph (Fin m), Nonempty (EdgeRouting H G) ∧
      ∀ v, d-1 ≤ H.degree v ∧ H.degree v ≤ d+t := by
  obtain ⟨K,hKG,hKmin,hends⟩ := exists_edge_minimal_min_degree G hmin
  let f : K.Copy G := {
    toHom := {toFun := id, map_rel' := fun h => hKG h}
    injective' := Function.injective_id }
  have hKno : ¬Nonempty (StrongCliqueImmersion t K) := fun ⟨M⟩ => hno ⟨M.mapCopy f⟩
  let A := univ.filter (fun v => d+t < K.degree v)
  have hA : ∀ v∈A, d < K.degree v := by intro v hv; have h := (mem_filter.mp hv).2; omega
  obtain ⟨g,hg⟩ := exists_distinct_high_neighbors K hd hends A hA
  obtain ⟨m,hm,H,⟨R⟩,hH⟩ := reduce_independent_high_vertices_aux d d t (Fintype.card V)
    K rfl A g hKno (fun v => by have hv := hKmin v; omega)
    (fun _ hv => (mem_filter.mp hv).2)
    (fun v hv => by simpa [A] using hv)
    (fun x hx y hy => high_vertices_independent K hends (hA x hx) (hA y hy))
    (fun x hx y hxy => ((hends x y hxy).resolve_left (Nat.ne_of_gt (hA x hx))).le)
    (fun x => (hg x).1) (fun x => (hg x).2.ge)
  exact ⟨m,hm,H,⟨(EdgeRouting.ofCopy f).compose R⟩,hH⟩

end
end Cycle13
