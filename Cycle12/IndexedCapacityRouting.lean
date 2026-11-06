import Cycle12.Foundations.CapacityPaths

/-! Integral capacity routing with a separately indexed occurrence for
each source. Repeated source vertices and zero-length original paths are
allowed. Pendant vertices reduce it to the proved simple-graph network. -/
namespace Cycle12.IndexedCapacity
open SimpleGraph Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def Adj (G : SimpleGraph V) (a : I → V) : V ⊕ I → V ⊕ I → Prop
  | .inl x, .inl y => G.Adj x y
  | .inl x, .inr i => x = a i
  | .inr i, .inl x => x = a i
  | .inr _, .inr _ => False

def graph (G : SimpleGraph V) (a : I → V) : SimpleGraph (V ⊕ I) where
  Adj := Adj G a
  symm := ⟨by
    intro x y h
    rcases x with x | x <;> rcases y with y | y
    · exact h.symm
    all_goals exact h⟩
  loopless := ⟨by
    intro x
    rcases x with x | x
    · exact G.irrefl
    · exact not_false⟩

def sources : Finset (V ⊕ I) := univ.image Sum.inr
def branches (B : Finset V) : Finset (V ⊕ I) := B.image Sum.inl
def originalSide (S : Finset (V ⊕ I)) : Finset V :=
  univ.filter (fun v => Sum.inl v ∈ S)

@[simp] theorem mem_originalSide (S : Finset (V ⊕ I)) (v : V) :
    v ∈ originalSide S ↔ Sum.inl v ∈ S := by simp [originalSide]

@[simp] theorem sources_card : (sources (V := V) (I := I)).card = Fintype.card I := by
  rw [sources, card_image_of_injective _ Sum.inr_injective, card_univ]

theorem branches_inter_card (B : Finset V) (S : Finset (V ⊕ I)) :
    (branches B ∩ S).card = (B ∩ originalSide S).card := by
  have he : branches B ∩ S = (B ∩ originalSide S).image Sum.inl := by
    ext x
    rcases x with x | i <;> simp [branches]
  rw [he, card_image_of_injective _ Sum.inl_injective]

theorem pendant_cut_lower (G : SimpleGraph V) (a : I → V)
    (S : Finset (V ⊕ I)) :
    cutSize G (originalSide S) +
      (univ.filter (fun i => a i ∉ originalSide S ∧ Sum.inr i ∈ S)).card ≤
        cutSize (graph G a) S := by
  let J := univ.filter (fun i => a i ∉ originalSide S ∧ Sum.inr i ∈ S)
  let T := (cutGraph G (originalSide S)).edgeSet ⊕ J
  let f : T → Sym2 (V ⊕ I) := fun t => match t with
    | .inl e => Sym2.map Sum.inl e.val
    | .inr i => s(Sum.inr i.val, Sum.inl (a i.val))
  have hf : ∀ t, f t ∈ (cutGraph (graph G a) S).edgeSet := by
    intro t
    rcases t with e | i
    · rcases e with ⟨e,he⟩
      induction e using Sym2.inductionOn with
      | _ x y =>
        change G.Adj x y ∧ _ at he
        change G.Adj x y ∧ _
        simpa only [mem_coe, mem_originalSide, Set.mem_compl_iff,
          Prod.map_fst, Prod.map_snd] using he
    · have hi := (mem_filter.mp i.property).2
      change a i.val = a i.val ∧ _
      exact ⟨rfl, Or.inl ⟨hi.2, by simpa using hi.1⟩⟩
  have hinj : Function.Injective f := by
    intro t u h
    rcases t with e | i <;> rcases u with e' | j
    · exact congrArg Sum.inl (Subtype.ext (Sym2.map.injective Sum.inl_injective h))
    · have hm : Sum.inr j.val ∈ f (.inr j) := by simp [f]
      rw [← h] at hm
      simpa [f] using hm
    · have hm : Sum.inr i.val ∈ f (.inr i) := by simp [f]
      rw [h] at hm
      simpa [f] using hm
    · have hij : i.val = j.val := by
        have hh : i.val = j.val ∧ a i.val = a j.val := by simpa [f, Sym2.eq_iff] using h
        exact hh.1
      exact congrArg Sum.inr (Subtype.ext hij)
  have hc := Fintype.card_le_of_injective
    (fun t : T => (⟨f t,hf t⟩ : (cutGraph (graph G a) S).edgeSet))
    (fun t u h => hinj (congrArg Subtype.val h))
  simpa only [T, Fintype.card_sum, Fintype.card_coe, Set.fintypeCard_eq_ncard,
    cutSize, J] using hc

theorem pendant_capacity_cuts (G : SimpleGraph V) (a : I → V) (B : Finset V) (c : ℕ)
    (hcut : ∀ X : Finset V, Fintype.card I ≤ cutSize G X +
      (univ.filter (fun i => a i ∉ X)).card + c * (B ∩ X).card)
    (S : Finset (V ⊕ I)) :
    (sources (V := V) (I := I)).card ≤ cutSize (graph G a) S +
      (sources \ S).card + c * (branches B ∩ S).card := by
  let J := univ.filter (fun i => a i ∉ originalSide S)
  have hsplit := card_filter_add_card_filter_not (s := J) (p := fun i => Sum.inr i ∈ S)
  have hfirst : (J.filter (fun i => Sum.inr i ∈ S)).card =
      (univ.filter (fun i => a i ∉ originalSide S ∧ Sum.inr i ∈ S)).card := by
    congr 1
    ext i
    simp [J]
  have hsecond : (J.filter (fun i => Sum.inr i ∉ S)).card ≤ (sources \ S).card := by
    apply card_le_card_of_injOn Sum.inr
    · intro i hi
      exact mem_sdiff.mpr ⟨by simp [sources], (mem_filter.mp hi).2⟩
    · exact fun _ _ _ _ h => Sum.inr_injective h
  have hbound := pendant_cut_lower G a S
  have hinput := hcut (originalSide S)
  rw [sources_card, branches_inter_card]
  rw [hfirst] at hsplit
  change _ + _ = (univ.filter (fun i => a i ∉ originalSide S)).card at hsplit
  omega

theorem original_path (G : SimpleGraph V) (a : I → V) :
    ∀ {u v : V ⊕ I} (p : (graph G a).Walk u v), p.IsPath →
      ∀ x y : V, u = Sum.inl x → v = Sum.inl y →
      ∃ r : G.Walk x y, ∀ e ∈ r.edges, Sym2.map Sum.inl e ∈ p.edges := by
  intro u v p
  induction p with
  | nil =>
    intro hp x y hx hy
    have hxy : x = y := Sum.inl_injective (hx.symm.trans hy)
    subst y
    exact ⟨Walk.nil, by simp⟩
  | @cons u v w huv p ih =>
    intro hp x y hx hy
    subst u; subst w
    have hpp := (Walk.cons_isPath_iff huv p).mp hp
    rcases v with v | i
    · obtain ⟨r,hr⟩ := ih hpp.1 v y rfl rfl
      refine ⟨Walk.cons (show G.Adj x v from huv) r, ?_⟩
      intro e he
      simp only [Walk.edges_cons, List.mem_cons] at he ⊢
      rcases he with rfl | he
      · exact Or.inl rfl
      · exact Or.inr (hr e he)
    · have hxi : x = a i := huv
      obtain ⟨z,hiz,q,rfl⟩ := Walk.exists_eq_cons_of_ne (by simp) p
      rcases z with z | j
      · have hzi : z = a i := hiz
        exact (hpp.2 (by
          apply List.mem_cons_of_mem
          rw [hxi, ← hzi]
          exact q.start_mem_support)).elim
      · exact False.elim hiz

theorem extract_path (G : SimpleGraph V) (a : I → V) (i : I) (b : V)
    (p : (graph G a).Walk (Sum.inr i) (Sum.inl b)) (hp : p.IsPath) :
    ∃ r : G.Walk (a i) b, r.IsPath ∧
      ∀ e ∈ r.edges, Sym2.map Sum.inl e ∈ p.edges := by
  obtain ⟨v,hiv,q,rfl⟩ := Walk.exists_eq_cons_of_ne (by simp) p
  have hpq := (Walk.cons_isPath_iff hiv q).mp hp
  rcases v with v | j
  · have hv : v = a i := hiv
    subst v
    obtain ⟨r,hr⟩ := original_path G a q hpq.1 (a i) b rfl rfl
    refine ⟨r.bypass, Walk.bypass_isPath _, ?_⟩
    intro e he
    exact List.mem_cons_of_mem _ (hr e (Walk.edges_bypass_subset_edges _ he))
  · exact False.elim hiv

structure Routing (G : SimpleGraph V) (a : I → V) (B : Finset V) (c : ℕ) where
  branch : I → B
  slot : I → Fin c
  path : ∀ i, G.Walk (a i) (branch i).val
  isPath : ∀ i, (path i).IsPath
  disjoint : Pairwise (fun i j => Disjoint (path i).edgeSet (path j).edgeSet)
  slot_injective : Function.Injective (fun i => (branch i, slot i))

theorem Routing.branch_load {G : SimpleGraph V} {a : I → V} {B : Finset V} {c : ℕ}
    (R : Routing G a B c) (b : B) :
    (univ.filter (fun i => R.branch i = b)).card ≤ c := by
  let X := univ.filter (fun i => R.branch i = b)
  have hi : Function.Injective (fun i : X => R.slot i.val) := by
    intro i j h
    apply Subtype.ext
    apply R.slot_injective
    exact Prod.ext ((mem_filter.mp i.property).2.trans (mem_filter.mp j.property).2.symm) h
  have hc := Fintype.card_le_of_injective _ hi
  simpa only [Fintype.card_coe, Fintype.card_fin, X] using hc

theorem exists_routing (G : SimpleGraph V) (a : I → V) (B : Finset V) (c : ℕ)
    (hcut : ∀ X : Finset V, Fintype.card I ≤ cutSize G X +
      (univ.filter (fun i => a i ∉ X)).card + c * (B ∩ X).card) :
    Nonempty (Routing G a B c) := by
  obtain ⟨R⟩ := CapacityNetwork.exists_routing (graph G a) sources (branches B) c
    (pendant_capacity_cuts G a B c hcut)
  let src : I → sources (V := V) (I := I) := fun i => ⟨Sum.inr i, by simp [sources]⟩
  have hsrc : Function.Injective src := by
    intro i j h
    exact Sum.inr_injective (congrArg Subtype.val h)
  have hb : ∀ i, ∃ b : B, (R.branch (src i)).val = Sum.inl b.val := by
    intro i
    obtain ⟨b,hb,he⟩ := mem_image.mp (R.branch (src i)).property
    exact ⟨⟨b,hb⟩,he.symm⟩
  choose b hb using hb
  let q := fun i => (R.path (src i)).copy rfl (hb i)
  choose r hr he using fun i => extract_path G a i (b i).val (q i)
    (by simpa [q] using R.isPath (src i))
  refine ⟨{
    branch := b
    slot := fun i => R.slot (src i)
    path := r
    isPath := hr
    disjoint := ?_
    slot_injective := ?_ }⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro e hei hej
    have hi := he i e hei
    have hj := he j e hej
    have hd := R.disjoint (hsrc.ne hij)
    exact Set.disjoint_left.mp hd (by simpa [q] using hi) (by simpa [q] using hj)
  · intro i j h
    apply hsrc
    apply R.slot_injective
    refine Prod.ext ?_ (congrArg (fun z : B × Fin c => z.2) h)
    apply Subtype.ext
    rw [hb i, hb j, congrArg (fun z : B × Fin c => z.1.val) h]

end
end Cycle12.IndexedCapacity
