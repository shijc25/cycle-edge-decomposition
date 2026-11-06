import Cycle12.TerminalSupportedCertificate

namespace Cycle12.TerminalCert
open SimpleGraph Finset
variable {V I : Type} [Fintype V] [DecidableEq V] [DecidableEq I]

def chordEdges (B : Finset (Sym2 V)) (chord : I → Sym2 V) (S : Finset I) :
    Finset (Sym2 V) := B ∪ S.image chord

theorem chord_edges_mono (B : Finset (Sym2 V)) (chord : I → Sym2 V)
    {S T : Finset I} (h : S⊆T) : chordEdges B chord S ⊆ chordEdges B chord T :=
  union_subset_union (Subset.refl _) (image_subset_image h)

theorem valid_mono {d : ℕ} {E F : Finset (Sym2 V)} (hEF : E⊆F)
    (hF : ∀ e∈F, ¬e.IsDiag) (words : Fin d → CycleWord V)
    (hw : Valid E words) : Valid F words := by
  refine ⟨hF,?_,hw.2.2⟩
  intro i
  refine ⟨(hw.2.1 i).1,(hw.2.1 i).2.1,?_⟩
  exact (hw.2.1 i).2.2.imp (fun _ _ h => ⟨hEF h.1,h.2⟩)

theorem covered_subset_of_valid {d : ℕ} {E : Finset (Sym2 V)}
    (words : Fin d → CycleWord V) (hw : Valid E words) : covered words⊆E := by
  intro e he
  obtain ⟨i,_,hi⟩ := mem_biUnion.mp he
  have hh := (words i).toWalk (graph E) (hw.2.1 i) |>.edges_subset_edgeSet
  change ((words i).toWalk (graph E) (hw.2.1 i)).edgeSet ⊆ (graph E).edgeSet at hh
  rw [(words i).edgeSet_toWalk,edgeSet_graph E hw.1] at hh
  exact hh hi

/-- One witness covers a whole interval of chord choices. A packing uses
only its required chords and remains affordable up to the stated cap;
a long cycle excludes every extension of its required chords. -/
structure ChordCertificate (I V : Type) where
  required : Finset I
  cap : ℕ
  decision : DecisionCertificate V

def ChordCertificate.Accepts (c : ChordCertificate I V) (S : Finset I) : Prop :=
  c.required⊆S ∧ match c.decision with
    | .pack _ => S.card ≤ c.cap
    | .long _ => True

instance (c : ChordCertificate I V) (S : Finset I) : Decidable (c.Accepts S) := by
  unfold ChordCertificate.Accepts
  cases c.decision <;> infer_instance

def ChordCertificate.Checks (B : Finset (Sym2 V)) (chord : I → Sym2 V)
    (order : ℕ) (c : ChordCertificate I V) : Prop :=
  match c.decision with
  | .pack words => Valid (chordEdges B chord c.required) words.get ∧
      42*words.length+17*(B.card+c.cap) ≤
        19*(order-1)+23*(covered words.get).card
  | .long word => word.Valid (graph (chordEdges B chord c.required)) ∧
      7 ≤ word.tail.length+1

instance (B : Finset (Sym2 V)) (chord : I → Sym2 V) (order : ℕ)
    (c : ChordCertificate I V) : Decidable (c.Checks B chord order) := by
  unfold ChordCertificate.Checks
  cases c.decision <;> infer_instance

/-- The interval arithmetic is proved once, independently of any finite
table. Every covered choice yields the original exact-cost certificate. -/
theorem ChordCertificate.checksAt (B : Finset (Sym2 V)) (chord : I → Sym2 V)
    (order : ℕ) (c : ChordCertificate I V) (S : Finset I)
    (hcheck : c.Checks B chord order) (haccept : c.Accepts S)
    (hE : ∀ e∈chordEdges B chord S, ¬e.IsDiag) :
    c.decision.ChecksAt (chordEdges B chord S)
      (19*(order-1)+6*(chordEdges B chord S).card) := by
  have hsub := chord_edges_mono B chord haccept.1
  cases hd : c.decision with
  | pack words =>
    simp only [ChordCertificate.Checks,hd] at hcheck
    simp only [ChordCertificate.Accepts,hd] at haccept
    simp only [DecisionCertificate.ChecksAt]
    have hv := valid_mono hsub hE words.get hcheck.1
    refine ⟨hv,?_⟩
    have hcovered := covered_subset_of_valid words.get hv
    have hcard := card_sdiff_add_card_eq_card hcovered
    have he : (chordEdges B chord S).card ≤ B.card+c.cap := by
      exact (card_union_le B (S.image chord)).trans
        (Nat.add_le_add_left ((card_image_le).trans haccept.2) _)
    have hb := hcheck.2
    omega
  | long word =>
    simp only [ChordCertificate.Checks,hd] at hcheck
    simp only [DecisionCertificate.ChecksAt]
    refine ⟨⟨hcheck.1.1,hcheck.1.2.1,?_⟩,hcheck.2⟩
    exact hcheck.1.2.2.imp (fun _ _ h => ⟨hsub h.1,h.2⟩)

end Cycle12.TerminalCert
