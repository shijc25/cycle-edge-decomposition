import Cycle12.Foundations.ReservoirPortPaths

/-! Integral source-to-branch routing with all noninitial vertices in the
reservoir, derived from the directed-source cut condition. -/
namespace Cycle13.ReservoirPorts
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) (A U B : Finset V) (c : ℕ)

structure Routing where
  branch : A → B
  slot : A → Fin c
  path : ∀ a : A, G.Walk a.val (branch a).val
  isPath : ∀ a, (path a).IsPath
  tail_inside : ∀ a, ∀ v ∈ (path a).support.tail, v ∈ U
  disjoint : Pairwise (fun a a' => Disjoint (path a).edgeSet (path a').edgeSet)
  slot_injective : Function.Injective (fun a => (branch a, slot a))

theorem Routing.branch_load (R : Routing G A U B c) (b : B) :
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

theorem exists_routing (hAU : Disjoint A U) (hBU : B ⊆ U)
    (hcut : CutCondition G A U B c) : Nonempty (Routing G A U B c) := by
  obtain ⟨P, hP, hd⟩ := port_paths_of_cuts G A U B c hAU hcut
  have hsa : ∀ i, ∃ a : A, (P i).1 = Sum.inl a := by
    intro i
    obtain ⟨a, _, ha⟩ := mem_image.mp (hP i).1
    exact ⟨a, ha.symm⟩
  have hsq : ∀ i, ∃ q : B × Fin c, (P i).2.1 = Sum.inr (Sum.inr q) := by
    intro i
    obtain ⟨q, _, hq⟩ := mem_image.mp (hP i).2.1
    exact ⟨q, hq.symm⟩
  choose a ha using hsa
  choose q hq using hsq
  let p := fun i => (P i).2.2.copy (ha i) (hq i)
  have hp : ∀ i, (p i).IsPath := by
    intro i
    simpa only [p, Walk.isPath_copy] using (hP i).2.2.1
  have hpd : ∀ i j, i ≠ j → ∀ v ∈ (p i).support, v ∉ (p j).support := by
    intro i j hij
    simpa only [p, Walk.support_copy] using hd i j hij
  have hs : ∀ i, ∀ a' : A, Sum.inl a' ∈ (p i).support → a' = a i := by
    intro i a' ha'
    have h := (hP i).2.2.2.1 (Sum.inl a') (by simpa only [p, Walk.support_copy] using ha')
      (by simp [sources])
    rw [ha i] at h
    exact Sum.inl.inj h
  have ht : ∀ i, ∀ q', Sum.inr (Sum.inr q') ∈ (p i).support → q' = q i := by
    intro i q' hq'
    have h := (hP i).2.2.2.2 (Sum.inr (Sum.inr q'))
      (by simpa only [p, Walk.support_copy] using hq') (by simp [targets])
    rw [hq i] at h
    exact Sum.inr.inj (Sum.inr.inj h)
  choose r hr hU he using fun i =>
    extract_reservoir_path G A U B c hAU hBU (a i) (q i) (p i) (hp i) (hs i) (ht i)
  have hai : Function.Injective a := by
    intro i j hij
    by_contra hne
    apply hpd i j hne _ (p i).start_mem_support
    simpa only [hij] using (p j).start_mem_support
  have hqi : Function.Injective q := by
    intro i j hij
    by_contra hne
    apply hpd i j hne _ (p i).end_mem_support
    simpa only [hij] using (p j).end_mem_support
  have hrd : Pairwise (fun i j => Disjoint (r i).edgeSet (r j).edgeSet) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    obtain ⟨e, hei, hze⟩ := he i z hzi
    obtain ⟨f, hfj, hzf⟩ := he j z hzj
    have hef : e = f := Subtype.ext (hze.symm.trans hzf)
    exact hpd i j hij _ hei (hef ▸ hfj)
  have hab : Function.Bijective a :=
    (Fintype.bijective_iff_injective_and_card a).mpr ⟨hai, by simp⟩
  let e : Fin A.card ≃ A := Equiv.ofBijective a hab
  refine ⟨{
    branch := fun x => (q (e.symm x)).1
    slot := fun x => (q (e.symm x)).2
    path := fun x => (r (e.symm x)).copy (congrArg Subtype.val (e.apply_symm_apply x)) rfl
    isPath := fun x => by simpa using hr (e.symm x)
    tail_inside := fun x => by simpa only [Walk.support_copy] using hU (e.symm x)
    disjoint := ?_
    slot_injective := ?_ }⟩
  · intro x y hxy
    simpa only [Walk.edgeSet_copy] using
      hrd (fun h => hxy (e.symm.injective h))
  · intro x y hxy
    exact e.symm.injective (hqi hxy)

end
end Cycle13.ReservoirPorts
