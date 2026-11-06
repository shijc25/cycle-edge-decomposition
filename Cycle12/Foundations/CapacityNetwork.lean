import Cycle12.Foundations.CutMenger

/-! An undirected integral source-to-capacity network, represented by a
simple graph. A slot subdivides each parallel branch-to-sink edge. -/
namespace Cycle13.CapacityNetwork
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

abbrev Vertex (B : Finset V) (c : ℕ) := V ⊕ ((B × Fin c) ⊕ Bool)

def source (B : Finset V) (c : ℕ) : Vertex B c := .inr (.inr false)
def sink (B : Finset V) (c : ℕ) : Vertex B c := .inr (.inr true)

def Adj (G : SimpleGraph V) (A B : Finset V) (c : ℕ) : Vertex B c → Vertex B c → Prop
  | .inl x, .inl y => G.Adj x y
  | .inl x, .inr (.inl q) => x = q.1.val
  | .inr (.inl q), .inl x => x = q.1.val
  | .inl x, .inr (.inr b) => b = false ∧ x ∈ A
  | .inr (.inr b), .inl x => b = false ∧ x ∈ A
  | .inr (.inl _), .inr (.inr b) => b = true
  | .inr (.inr b), .inr (.inl _) => b = true
  | _, _ => False

def graph (G : SimpleGraph V) (A B : Finset V) (c : ℕ) : SimpleGraph (Vertex B c) where
  Adj := Adj G A B c
  symm := ⟨by
    intro x y h
    rcases x with x | x <;> rcases y with y | y
    · exact h.symm
    · rcases y with y | y <;> exact h
    · rcases x with x | x <;> exact h
    · rcases x with x | x <;> rcases y with y | y <;> exact h⟩
  loopless := ⟨by
    intro x
    rcases x with x | x
    · exact G.irrefl
    · rcases x with x | x <;> exact not_false⟩

def originalSide {B : Finset V} {c : ℕ} (S : Finset (Vertex B c)) : Finset V :=
  univ.filter (fun v => Sum.inl v ∈ S)

@[simp] theorem mem_originalSide {B : Finset V} {c : ℕ}
    (S : Finset (Vertex B c)) (v : V) : v ∈ originalSide S ↔ Sum.inl v ∈ S := by
  simp [originalSide]

/-- One witness edge for every branch slot on the source side. Exactly one
of the two edges of its subdivision must cross the source/sink cut. -/
def slotBoundary {B : Finset V} {c : ℕ} (S : Finset (Vertex B c))
    (q : B × Fin c) : Sym2 (Vertex B c) :=
  if Sum.inr (Sum.inl q) ∈ S then s(Sum.inr (Sum.inl q), sink B c)
  else s(Sum.inl q.1.val, Sum.inr (Sum.inl q))

theorem slotBoundary_injective {B : Finset V} {c : ℕ} (S : Finset (Vertex B c)) :
    Function.Injective (slotBoundary S) := by
  intro p q h
  unfold slotBoundary at h
  split_ifs at h <;> simp only [sink, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl, and_false, false_and, or_false, false_or,
    Bool.false_eq_true, and_true, true_and, reduceCtorEq] at h
  all_goals aesop

def originalEmbedding (B : Finset V) (c : ℕ) : V ↪ Vertex B c :=
  ⟨Sum.inl, Sum.inl_injective⟩

/-- The cut in the auxiliary simple graph is at least the usual integer
capacity cut: original edges, unserved sources and branch slots. -/
theorem capacity_cut_lower_bound (G : SimpleGraph V) (A B : Finset V) (c : ℕ)
    (S : Finset (Vertex B c)) (hs : source B c ∈ S) (ht : sink B c ∉ S) :
    cutSize G (originalSide S) + (A \ originalSide S).card +
      c * (B ∩ originalSide S).card ≤ cutSize (graph G A B c) S := by
  let X := originalSide S
  let I := (cutGraph G X).edgeSet ⊕ (↥(A \ X) ⊕ (↥(B ∩ X) × Fin c))
  let f : I → Sym2 (Vertex B c) := fun z => match z with
    | .inl e => Sym2.map Sum.inl e.val
    | .inr (.inl a) => s(source B c, Sum.inl a.val)
    | .inr (.inr (b, j)) => slotBoundary S (⟨b.val, (mem_inter.mp b.property).1⟩, j)
  have hf : ∀ z, f z ∈ (cutGraph (graph G A B c) S).edgeSet := by
    intro z
    rcases z with e | z
    · rcases e with ⟨e, he⟩
      induction e using Sym2.inductionOn with
      | _ x y =>
        change G.Adj x y ∧ _ at he
        change G.Adj x y ∧ _
        simpa only [X, mem_coe, mem_originalSide, Set.mem_compl_iff, Prod.map_fst, Prod.map_snd] using he
    · rcases z with a | ⟨b, j⟩
      · have ha := mem_sdiff.mp a.property
        change (false = false ∧ a.val ∈ A) ∧ _
        refine ⟨⟨rfl, ha.1⟩, Or.inl ⟨hs, ?_⟩⟩
        simpa only [X, mem_originalSide, mem_coe, Set.mem_compl_iff] using ha.2
      · have hb := mem_inter.mp b.property
        change slotBoundary S (⟨b.val, hb.1⟩, j) ∈ _
        unfold slotBoundary
        split_ifs with hslot
        · change true = true ∧ _
          exact ⟨rfl, Or.inl ⟨hslot, ht⟩⟩
        · change b.val = b.val ∧ _
          refine ⟨rfl, Or.inl ⟨?_, hslot⟩⟩
          simpa only [X, mem_originalSide, mem_coe, Set.mem_compl_iff] using hb.2
  have hinj : Function.Injective f := by
    intro p q h
    rcases p with e | p <;> rcases q with e' | q
    · apply congrArg Sum.inl
      apply Subtype.ext
      exact Sym2.map.injective Sum.inl_injective h
    · rcases q with a | ⟨b, j⟩
      · have hm : source B c ∈ f (Sum.inr (Sum.inl a)) := by simp [f]
        rw [← h] at hm
        simpa [f, source] using hm
      · have hm : Sum.inr (Sum.inl (⟨b.val, (mem_inter.mp b.property).1⟩, j)) ∈
            f (Sum.inr (Sum.inr (b, j))) := by
          simp only [f, slotBoundary]
          split_ifs <;> simp
        rw [← h] at hm
        simpa [f] using hm
    · rcases p with a | ⟨b, j⟩
      · have hm : source B c ∈ f (Sum.inr (Sum.inl a)) := by simp [f]
        rw [h] at hm
        simpa [f, source] using hm
      · have hm : Sum.inr (Sum.inl (⟨b.val, (mem_inter.mp b.property).1⟩, j)) ∈
            f (Sum.inr (Sum.inr (b, j))) := by
          simp only [f, slotBoundary]
          split_ifs <;> simp
        rw [h] at hm
        simpa [f] using hm
    · rcases p with a | ⟨b, j⟩ <;> rcases q with a' | ⟨b', j'⟩
      · have ha : a.val = a'.val := by simpa [f, source, Sym2.eq_iff] using h
        exact congrArg (fun a => Sum.inr (Sum.inl a)) (Subtype.ext ha)
      · simp only [f] at h
        unfold slotBoundary at h
        split_ifs at h <;> simp [source, sink, Sym2.eq_iff] at h
      · simp only [f] at h
        unfold slotBoundary at h
        split_ifs at h <;> simp [source, sink, Sym2.eq_iff] at h
      · have he := slotBoundary_injective S h
        have hb : b = b' := Subtype.ext (congrArg (fun z : B × Fin c => z.1.val) he)
        have hj : j = j' := congrArg Prod.snd he
        subst b'; subst j'; rfl
  have hcard := Fintype.card_le_of_injective (fun z : I =>
    (⟨f z, hf z⟩ : (cutGraph (graph G A B c) S).edgeSet))
    (fun p q h => hinj (congrArg Subtype.val h))
  simp only [I, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_coe, Set.fintypeCard_eq_ncard] at hcard
  simpa only [cutSize, X, Nat.mul_comm, Nat.add_assoc] using hcard


/-- Integral auxiliary paths exist under the exact source-capacity cut
condition. Every path is simple and every original or auxiliary edge is
used by at most one path. -/
theorem paths_of_capacity_cuts (G : SimpleGraph V) (A B : Finset V) (c : ℕ)
    (hcut : ∀ X : Finset V, A.card ≤ cutSize G X + (A \ X).card + c * (B ∩ X).card) :
    ∃ p : Fin A.card → (graph G A B c).Walk (source B c) (sink B c),
      (∀ i, (p i).IsPath) ∧
      ∀ i j, i ≠ j → Disjoint (p i).edgeSet (p j).edgeSet := by
  apply disjoint_paths_of_cut_bound
  intro S hs ht
  exact (hcut _).trans (capacity_cut_lower_bound G A B c S hs ht)

end
end Cycle13.CapacityNetwork
