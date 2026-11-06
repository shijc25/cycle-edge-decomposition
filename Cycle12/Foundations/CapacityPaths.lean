import Cycle12.Foundations.CapacityNetwork

/-! Removing the auxiliary source, sink and capacity slots from integral
paths. The resulting paths use only original graph edges. -/
namespace Cycle13.CapacityNetwork
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) (A B : Finset V) (c : ℕ)

def originalHom : G →g graph G A B c where
  toFun := Sum.inl
  map_rel' := fun h => h

/-- A simple path from an original vertex to the sink, avoiding the source,
consists of original graph edges followed by one branch capacity slot. -/
theorem original_to_sink :
    ∀ {a z : Vertex B c} (p : (graph G A B c).Walk a z), p.IsPath →
      source B c ∉ p.support → ∀ x : V, a = Sum.inl x → z = sink B c →
      ∃ (b : B) (j : Fin c) (r : G.Walk x b.val),
        (∀ e ∈ r.edges, Sym2.map Sum.inl e ∈ p.edges) ∧
        s(Sum.inr (Sum.inl (b, j)), sink B c) ∈ p.edges := by
  intro a z p
  induction p with
  | nil =>
    intro hp hs x hx hz
    simp_all [sink]
  | @cons a y z hay q ih =>
    intro hp hs x hx hz
    subst a; subst z
    have hpq := (Walk.cons_isPath_iff hay q).mp hp
    have hsq : source B c ∉ q.support := fun h => hs (by simp [h])
    rcases y with y | y
    · obtain ⟨b, j, r, hr, hj⟩ := ih hpq.1 hsq y rfl rfl
      have hxy : G.Adj x y := hay
      refine ⟨b, j, Walk.cons hxy r, ?_, ?_⟩
      · intro e he
        simp only [Walk.edges_cons, List.mem_cons] at he ⊢
        rcases he with rfl | he
        · exact Or.inl rfl
        · exact Or.inr (hr e he)
      · simpa only [Walk.edges_cons, List.mem_cons] using Or.inr hj
    · rcases y with bj | pole
      · have hxb : x = bj.1.val := hay
        obtain ⟨w, hyw, q', rfl⟩ := Walk.exists_eq_cons_of_ne
          (by simp [sink]) q
        have hpq' := (Walk.cons_isPath_iff hyw q').mp hpq.1
        rcases w with w | w
        · have hwb : w = bj.1.val := hyw
          have : Sum.inl x ∈ (Walk.cons hyw q').support := by
            apply List.mem_cons_of_mem
            rw [hxb, ← hwb]
            exact q'.start_mem_support
          exact (hpq.2 this).elim
        · rcases w with w | pole
          · exact False.elim hyw
          · have hpole : pole = true := hyw
            subst pole
            have hn : q' = Walk.nil := Walk.isPath_iff_eq_nil.mp hpq'.1
            subst q'
            subst x
            refine ⟨bj.1, bj.2, Walk.nil, ?_, ?_⟩
            · simp
            · exact List.mem_cons_of_mem _ (List.mem_cons_self)
      · have hpole : pole = false ∧ x ∈ A := hay
        have : source B c ∈ q.support := by
          simpa [source, hpole.1] using q.start_mem_support
        exact (hsq this).elim

/-- The first auxiliary edge identifies one source; the final auxiliary
edge identifies one branch slot. Keeping those edges in the statement
makes the subsequent injectivity and capacity proof explicit. -/
theorem extract_path (p : (graph G A B c).Walk (source B c) (sink B c))
    (hp : p.IsPath) :
    ∃ (a : A) (b : B) (j : Fin c) (r : G.Walk a.val b.val),
      r.IsPath ∧
      s(source B c, Sum.inl a.val) ∈ p.edges ∧
      s(Sum.inr (Sum.inl (b, j)), sink B c) ∈ p.edges ∧
      ∀ e ∈ r.edges, Sym2.map Sum.inl e ∈ p.edges := by
  obtain ⟨y, hsy, q, rfl⟩ := Walk.exists_eq_cons_of_ne (by simp [source, sink]) p
  have hpq := (Walk.cons_isPath_iff hsy q).mp hp
  rcases y with y | y
  · have hy : y ∈ A := hsy.2
    obtain ⟨b, j, r, hr, hj⟩ := original_to_sink G A B c q hpq.1 hpq.2 y rfl rfl
    refine ⟨⟨y, hy⟩, b, j, r.bypass, Walk.bypass_isPath _, ?_, ?_, ?_⟩
    · simp
    · simpa only [Walk.edges_cons, List.mem_cons] using Or.inr hj
    · intro e he
      exact List.mem_cons_of_mem _ (hr e (Walk.edges_bypass_subset_edges _ he))
  · rcases y with y | y
    · have : false = true := hsy
      contradiction
    · exact False.elim hsy

/-- One path for each source vertex, with injectively used branch slots.
This is an actual integral routing in `G`; paths may share vertices. -/
structure Routing where
  branch : A → B
  slot : A → Fin c
  path : ∀ a : A, G.Walk a.val (branch a).val
  isPath : ∀ a, (path a).IsPath
  disjoint : Pairwise (fun a a' => Disjoint (path a).edgeSet (path a').edgeSet)
  slot_injective : Function.Injective (fun a => (branch a, slot a))

/-- The injective slot assignment gives the advertised integer load bound
at every branch. -/
theorem Routing.branch_load (R : Routing G A B c) (b : B) :
    (univ.filter (fun a : A => R.branch a = b)).card ≤ c := by
  let X := univ.filter (fun a : A => R.branch a = b)
  have hi : Function.Injective (fun a : X => R.slot a.val) := by
    intro a a' h
    apply Subtype.ext
    apply R.slot_injective
    apply Prod.ext
    · exact (mem_filter.mp a.property).2.trans (mem_filter.mp a'.property).2.symm
    · exact h
  have hcard := Fintype.card_le_of_injective _ hi
  simpa only [Fintype.card_coe, Fintype.card_fin, X] using hcard

theorem exists_routing
    (hcut : ∀ X : Finset V, A.card ≤ cutSize G X + (A \ X).card + c * (B ∩ X).card) :
    Nonempty (Routing G A B c) := by
  obtain ⟨p, hp, hd⟩ := paths_of_capacity_cuts G A B c hcut
  choose a b j r hr ha hj he using fun i => extract_path G A B c (p i) (hp i)
  have hainj : Function.Injective a := by
    intro i i' hii
    by_contra hne
    apply Set.disjoint_left.mp (hd i i' hne) (ha i)
    simpa only [hii, Walk.mem_edgeSet] using ha i'
  have hslotinj : Function.Injective (fun i => (b i, j i)) := by
    intro i i' hii
    by_contra hne
    apply Set.disjoint_left.mp (hd i i' hne) (hj i)
    simpa only [hii, Walk.mem_edgeSet] using hj i'
  have hasurj : Function.Surjective a :=
    ((Fintype.bijective_iff_injective_and_card a).mpr ⟨hainj, by simp⟩).2
  let e : Fin A.card ≃ A := Equiv.ofBijective a ⟨hainj, hasurj⟩
  refine ⟨{
    branch := fun x => b (e.symm x)
    slot := fun x => j (e.symm x)
    path := fun x => (r (e.symm x)).copy (e.apply_symm_apply x |> congrArg Subtype.val) rfl
    isPath := fun x => by simpa using hr (e.symm x)
    disjoint := ?_
    slot_injective := ?_ }⟩
  · intro x y hxy
    apply Set.disjoint_left.mpr
    intro z hx hy
    have hx' : z ∈ (r (e.symm x)).edges := by simpa using hx
    have hy' : z ∈ (r (e.symm y)).edges := by simpa using hy
    exact Set.disjoint_left.mp (hd _ _ (fun h => hxy (e.symm.injective h)))
      (he _ z hx') (he _ z hy')
  · intro x y h
    exact e.symm.injective (hslotinj h)

end
end Cycle13.CapacityNetwork
