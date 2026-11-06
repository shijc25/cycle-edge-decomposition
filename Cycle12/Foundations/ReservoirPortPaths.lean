import Cycle12.Foundations.ReservoirPortCuts

/-! Lowering port paths to original graph paths whose noninitial vertices
all lie in the reservoir. -/
namespace Cycle13.ReservoirPorts
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) (A U B : Finset V) (c : ℕ)

lemma inside_edge_walk (e : G.edgeSet) {v w : V}
    (hv : v ∈ e.val) (hw : w ∈ e.val) (hvU : v ∈ U) (hwU : w ∈ U) :
    ∃ r : G.Walk v w, (∀ f ∈ r.edges, f = e.val) ∧ ∀ x ∈ r.support, x ∈ U := by
  by_cases h : v = w
  · subst w
    exact ⟨Walk.nil, by simp, by simpa using hvU⟩
  · have he := (Sym2.mem_and_mem_iff h).mp ⟨hv, hw⟩
    have hadj : G.Adj v w := by rw [← G.mem_edgeSet, ← he]; exact e.property
    refine ⟨Walk.cons hadj Walk.nil, ?_, ?_⟩
    · simpa [he]
    · intro x hx
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hvU
      · exact hwU

lemma lower_edge_path (hBU : B ⊆ U) :
    ∀ {a z : Vertex G A B c} (p : (graph G A U B c).Walk a z),
      (∀ a' : A, Sum.inl a' ∉ p.support) →
      ∀ q : B × Fin c, z = Sum.inr (Sum.inr q) →
        (∀ q', Sum.inr (Sum.inr q') ∈ p.support → q' = q) →
      ∀ e : G.edgeSet, a = Sum.inr (Sum.inl e) →
      ∀ v : V, v ∈ U → v ∈ e.val →
      ∃ r : G.Walk v q.1.val, (∀ x ∈ r.support, x ∈ U) ∧
        ∀ f ∈ r.edges, ∃ e' : G.edgeSet,
          Sum.inr (Sum.inl e') ∈ p.support ∧ f = e'.val := by
  intro a z p
  induction p with
  | nil =>
    intro hsrc q hz ht e ha v hvU hve
    simp_all
  | @cons a y z hay p ih =>
    intro hsrc q hz ht e ha v hvU hve
    subst a; subst z
    have hsrc' : ∀ a' : A, Sum.inl a' ∉ p.support := by
      intro a' h
      exact hsrc a' (by simp [h])
    have ht' : ∀ q', Sum.inr (Sum.inr q') ∈ p.support → q' = q := by
      intro q' h
      exact ht q' (by simp [h])
    rcases y with a' | y
    · exact (hsrc' a' p.start_mem_support).elim
    · rcases y with e' | q'
      · have hay' : e ≠ e' ∧ ∃ w ∈ U, w ∈ e.val ∧ w ∈ e'.val := hay
        obtain ⟨hne, w, hwU, hwe, hwe'⟩ := hay' 
        obtain ⟨r₁, hr₁e, hr₁U⟩ := inside_edge_walk G U e hve hwe hvU hwU
        obtain ⟨r₂, hr₂U, hr₂e⟩ := ih hsrc' q rfl ht' e' rfl w hwU hwe'
        refine ⟨r₁.append r₂, ?_, ?_⟩
        · intro x hx
          rw [Walk.mem_support_append_iff] at hx
          rcases hx with hx | hx
          · exact hr₁U x hx
          · exact hr₂U x hx
        · intro f hf
          rw [Walk.edges_append, List.mem_append] at hf
          rcases hf with hf | hf
          · exact ⟨e, by simp, hr₁e f hf⟩
          · obtain ⟨e'', he'', hfe⟩ := hr₂e f hf
            exact ⟨e'', by simp [he''], hfe⟩
      · have hq : q' = q := ht' q' p.start_mem_support
        subst q'
        obtain ⟨r, hre, hrU⟩ := inside_edge_walk G U e hve hay hvU (hBU q.1.property)
        exact ⟨r, hrU, fun f hf => ⟨e, by simp, hre f hf⟩⟩

/-- A single source-to-slot port path gives a simple original path whose
tail lies entirely in `U`, and whose edges retain their port witnesses. -/
theorem extract_reservoir_path (hAU : Disjoint A U) (hBU : B ⊆ U)
    (a : A) (q : B × Fin c)
    (p : (graph G A U B c).Walk (Sum.inl a) (Sum.inr (Sum.inr q)))
    (hp : p.IsPath)
    (hs : ∀ a' : A, Sum.inl a' ∈ p.support → a' = a)
    (ht : ∀ q', Sum.inr (Sum.inr q') ∈ p.support → q' = q) :
    ∃ r : G.Walk a.val q.1.val, r.IsPath ∧
      (∀ v ∈ r.support.tail, v ∈ U) ∧
      ∀ f ∈ r.edges, ∃ e : G.edgeSet,
        Sum.inr (Sum.inl e) ∈ p.support ∧ f = e.val := by
  obtain ⟨y, hay, p', rfl⟩ := Walk.exists_eq_cons_of_ne (by simp) p
  have hp' := (Walk.cons_isPath_iff hay p').mp hp
  rcases y with a' | y
  · exact False.elim hay
  · rcases y with e | q'
    · have hay' : ∃ u ∈ U, e.val = s(a.val, u) := hay
      obtain ⟨u, huU, heu⟩ := hay' 
      have hsrc : ∀ a' : A, Sum.inl a' ∉ p'.support := by
        intro a' ha'
        have he : a' = a := hs a' (by simp [ha'])
        subst a'
        exact hp'.2 ha'
      have ht' : ∀ q', Sum.inr (Sum.inr q') ∈ p'.support → q' = q := by
        intro q' hq'
        exact ht q' (by simp [hq'])
      obtain ⟨r, hrU, hre⟩ := lower_edge_path G A U B c hBU p' hsrc q rfl ht' e rfl u huU
        (by rw [heu]; exact Sym2.mem_mk_right _ _)
      have hau : G.Adj a.val u := by rw [← G.mem_edgeSet, ← heu]; exact e.property
      let w := Walk.cons hau r
      have hwe : ∀ f ∈ w.edges, ∃ e' : G.edgeSet,
          Sum.inr (Sum.inl e') ∈ (Walk.cons (show (graph G A U B c).Adj
            (Sum.inl a) (Sum.inr (Sum.inl e)) from ⟨u, huU, heu⟩) p').support ∧ f = e'.val := by
        intro f hf
        simp only [w, Walk.edges_cons, List.mem_cons] at hf
        rcases hf with rfl | hf
        · exact ⟨e, by simp [p'.start_mem_support], heu.symm⟩
        · obtain ⟨e', he', hfe⟩ := hre f hf
          exact ⟨e', by simp [he'], hfe⟩
      refine ⟨w.bypass, Walk.bypass_isPath _, ?_, ?_⟩
      · intro v hv
        have hnd := (Walk.bypass_isPath w).support_nodup
        rw [← Walk.cons_tail_support] at hnd
        have hva : v ≠ a.val := by
          intro h
          exact (List.nodup_cons.mp hnd).1 (h ▸ hv)
        have hvw := Walk.support_bypass_subset_support w (List.mem_of_mem_tail hv)
        simp only [w, Walk.support_cons, List.mem_cons] at hvw
        exact hrU v (hvw.resolve_left hva)
      · intro f hf
        exact hwe f (Walk.edges_bypass_subset_edges w hf)
    · exact False.elim hay

end
end Cycle13.ReservoirPorts
