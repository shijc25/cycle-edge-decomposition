import Cycle12.Foundations.CarrierSchedule
import Cycle12.Foundations.CarrierModel

/-! Turning the two-stage Link schedule into the prepared carrier used by
the balanced-color construction. Only the missing-edge carrier hypotheses
remain; no reserved-path existence assumption remains in the final theorem. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

lemma exists_reoriented_path {V : Type} {G : SimpleGraph V} {a b x y : V}
    (P : G.Path a b) (he : s(x,y)=s(a,b)) :
    ∃ Q : G.Path x y, Q.val.edgeSet=P.val.edgeSet ∧
      ∀ v, v ∈ Q.val.support ↔ v ∈ P.val.support := by
  rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨P,rfl,fun _ => Iff.rfl⟩
  · exact ⟨⟨P.val.reverse,P.property.reverse⟩,by simp,by simp⟩

namespace CarrierSlot
variable {p q : ℕ}
def primary (s : CarrierSlot p q) : Prop :=
  match ofLex s with
  | Sum.inl c => c.copy=0
  | Sum.inr _ => True
def secondary (s : CarrierSlot p q) : Prop :=
  match ofLex s with
  | Sum.inl c => c.copy=1
  | Sum.inr _ => False

lemma not_primary_secondary (s : CarrierSlot p q) : ¬(s.primary ∧ s.secondary) := by
  induction s using Lex.rec with
  | h s =>
    rcases s with c | o
    · change ¬(c.copy=0 ∧ c.copy=1)
      omega
    · exact fun h => h.2

theorem exists_primary_edge (x y : Fin p ⊕ Fin q) (hne : x ≠ y)
    (hnew : ¬∃ u v : Fin q, x=Sum.inr u ∧ y=Sum.inr v) :
    ∃ s : CarrierSlot p q, s.primary ∧ s(first s,second s)=s(x,y) := by
  rcases x with x | x <;> rcases y with y | y
  · have hxy : x ≠ y := fun h => hne (congrArg Sum.inl h)
    rcases lt_or_gt_of_ne hxy with h | h
    · refine ⟨toLex (Sum.inr ⟨toLex (OrderDual.toDual y,OrderDual.toDual x),h⟩), trivial, ?_⟩
      exact Sym2.eq_swap
    · exact ⟨toLex (Sum.inr ⟨toLex (OrderDual.toDual x,OrderDual.toDual y),h⟩),trivial,rfl⟩
  · exact ⟨toLex (Sum.inl (toLex (OrderDual.toDual x,toLex (y,0)))),rfl,rfl⟩
  · exact ⟨toLex (Sum.inl (toLex (OrderDual.toDual y,toLex (x,0)))),rfl,Sym2.eq_swap⟩
  · exact False.elim (hnew ⟨x,y,rfl,rfl⟩)
end CarrierSlot

namespace CarrierPreparation
variable {V : Type} {p q : ℕ} {G : SimpleGraph V}
    (E : Fin (p+q) ≃ (Fin p ⊕ Fin q)) (φ : (Fin p ⊕ Fin q) ↪ V)

def oldSet : Finset (Fin (p+q)) := univ.image (fun s : Fin p => E.symm (Sum.inl s))
def newSet : Finset (Fin (p+q)) := univ.image (fun s : Fin q => E.symm (Sum.inr s))

lemma mem_oldSet (i : Fin (p+q)) : i ∈ oldSet E ↔ ∃ s : Fin p, E i=Sum.inl s := by
  simp only [oldSet,mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨s,E.apply_symm_apply _⟩
  · rintro ⟨s,hs⟩
    exact ⟨s,E.symm_apply_eq.mpr hs.symm⟩

lemma mem_newSet (i : Fin (p+q)) : i ∈ newSet E ↔ ∃ s : Fin q, E i=Sum.inr s := by
  simp only [newSet,mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨s,E.apply_symm_apply _⟩
  · rintro ⟨s,hs⟩
    exact ⟨s,E.symm_apply_eq.mpr hs.symm⟩

lemma oldSet_card : (oldSet E).card=p := by
  rw [oldSet,card_image_of_injective _
    (show Function.Injective (fun s : Fin p => E.symm (Sum.inl s)) from
      fun _ _ h => Sum.inl.inj (E.symm.injective h)),
    card_univ,Fintype.card_fin]
lemma newSet_card : (newSet E).card=q := by
  rw [newSet,card_image_of_injective _
    (show Function.Injective (fun s : Fin q => E.symm (Sum.inr s)) from
      fun _ _ h => Sum.inr.inj (E.symm.injective h)),
    card_univ,Fintype.card_fin]

def residual : SimpleGraph (Fin (p+q)) where
  Adj i j := i ≠ j ∧ i ∈ newSet E ∧ j ∈ newSet E
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def branch : Fin (p+q) ↪ V := E.toEmbedding.trans φ

lemma baseSlot_exists (e : CliquePair (p+q)) (he : ¬(residual E).Adj e.1.1 e.1.2) :
    ∃ s : CarrierSlot p q, s.primary ∧
      s(CarrierSlot.first s,CarrierSlot.second s)=s(E e.1.1,E e.1.2) := by
  apply CarrierSlot.exists_primary_edge _ _ (E.injective.ne (ne_of_lt e.2))
  rintro ⟨u,v,hu,hv⟩
  exact he ⟨ne_of_lt e.2,(mem_newSet E _).mpr ⟨u,hu⟩,(mem_newSet E _).mpr ⟨v,hv⟩⟩

def baseSlot (e : CliquePair (p+q)) (he : ¬(residual E).Adj e.1.1 e.1.2) : CarrierSlot p q :=
  (baseSlot_exists E e he).choose
lemma baseSlot_primary (e : CliquePair (p+q)) (he : ¬(residual E).Adj e.1.1 e.1.2) :
    (baseSlot E e he).primary := (baseSlot_exists E e he).choose_spec.1
lemma baseSlot_edge (e : CliquePair (p+q)) (he : ¬(residual E).Adj e.1.1 e.1.2) :
    s(CarrierSlot.first (baseSlot E e he),CarrierSlot.second (baseSlot E e he))=
      s(E e.1.1,E e.1.2) := (baseSlot_exists E e he).choose_spec.2

def spokeSlot (a : oldSet E) (v : newSet E) : CarrierSlot p q :=
  toLex (Sum.inl (toLex (OrderDual.toDual ((mem_oldSet E a.val).mp a.property).choose,
    toLex (((mem_newSet E v.val).mp v.property).choose,1))))

lemma spokeSlot_secondary (a : oldSet E) (v : newSet E) : (spokeSlot E a v).secondary := rfl
lemma spokeSlot_first (a : oldSet E) (v : newSet E) : CarrierSlot.first (spokeSlot E a v)=E a.val :=
  ((mem_oldSet E a.val).mp a.property).choose_spec.symm
lemma spokeSlot_second (a : oldSet E) (v : newSet E) : CarrierSlot.second (spokeSlot E a v)=E v.val :=
  ((mem_newSet E v.val).mp v.property).choose_spec.symm

variable (P : ∀ s : CarrierSlot p q, G.Path (φ (CarrierSlot.first s)) (φ (CarrierSlot.second s)))

lemma basePath_exists (e : CliquePair (p+q)) (he : ¬(residual E).Adj e.1.1 e.1.2) :
    ∃ Q : G.Path (branch E φ e.1.1) (branch E φ e.1.2),
      Q.val.edgeSet=(P (baseSlot E e he)).val.edgeSet ∧
      ∀ v, v ∈ Q.val.support ↔ v ∈ (P (baseSlot E e he)).val.support := by
  apply exists_reoriented_path
  exact congrArg (Sym2.map φ) (baseSlot_edge E e he).symm

def basePath (e : CliquePair (p+q)) (he : ¬(residual E).Adj e.1.1 e.1.2) :
    G.Path (branch E φ e.1.1) (branch E φ e.1.2) := (basePath_exists E φ P e he).choose

lemma basePath_spec (e : CliquePair (p+q)) (he : ¬(residual E).Adj e.1.1 e.1.2) :
    (basePath E φ P e he).val.edgeSet=(P (baseSlot E e he)).val.edgeSet ∧
      ∀ v, v ∈ (basePath E φ P e he).val.support ↔ v ∈ (P (baseSlot E e he)).val.support :=
  (basePath_exists E φ P e he).choose_spec

lemma spokePath_exists (a : oldSet E) (v : newSet E) :
    ∃ Q : G.Path (branch E φ a.val) (branch E φ v.val),
      Q.val.edgeSet=(P (spokeSlot E a v)).val.edgeSet ∧
      ∀ w, w ∈ Q.val.support ↔ w ∈ (P (spokeSlot E a v)).val.support := by
  apply exists_reoriented_path
  rw [spokeSlot_first,spokeSlot_second]
  rfl

def spokePath (a : oldSet E) (v : newSet E) : G.Path (branch E φ a.val) (branch E φ v.val) :=
  (spokePath_exists E φ P a v).choose

lemma spokePath_spec (a : oldSet E) (v : newSet E) :
    (spokePath E φ P a v).val.edgeSet=(P (spokeSlot E a v)).val.edgeSet ∧
      ∀ w, w ∈ (spokePath E φ P a v).val.support ↔ w ∈ (P (spokeSlot E a v)).val.support :=
  (spokePath_exists E φ P a v).choose_spec

def prepared (hPP : Pairwise (fun i j => Disjoint (P i).val.edgeSet (P j).val.edgeSet))
    (havoid : ∀ s v, φ v ∈ (P s).val.support → v=CarrierSlot.first s ∨ v=CarrierSlot.second s) :
    PreparedCarrier G (residual E) (oldSet E) (newSet E) where
  branch := branch E φ
  supported := fun h => h.2
  base := basePath E φ P
  spoke := spokePath E φ P
  base_disjoint := by
    intro e d he hd hed
    rw [(basePath_spec E φ P e he).1,(basePath_spec E φ P d hd).1]
    apply hPP
    intro h
    have heq : s(E e.1.1,E e.1.2)=s(E d.1.1,E d.1.2) := by
      rw [← baseSlot_edge E e he,← baseSlot_edge E d hd,h]
    exact hed (CliquePair.edge_injective (Sym2.map.injective E.injective heq))
  spoke_disjoint := by
    intro a v b w hne
    rw [(spokePath_spec E φ P a v).1,(spokePath_spec E φ P b w).1]
    apply hPP
    intro h
    have h₁ := congrArg CarrierSlot.first h
    have h₂ := congrArg CarrierSlot.second h
    rw [spokeSlot_first,spokeSlot_first] at h₁
    rw [spokeSlot_second,spokeSlot_second] at h₂
    exact hne (Prod.ext (Subtype.ext (E.injective h₁)) (Subtype.ext (E.injective h₂)))
  base_spoke_disjoint := by
    intro e he a v
    rw [(basePath_spec E φ P e he).1,(spokePath_spec E φ P a v).1]
    apply hPP
    intro h
    exact CarrierSlot.not_primary_secondary _
      ⟨h ▸ baseSlot_primary E e he,spokeSlot_secondary E a v⟩
  base_avoids := by
    intro e he i hi
    have hs := (basePath_spec E φ P e he).2 _ |>.mp hi
    have hv := havoid (baseSlot E e he) (E i) hs
    have hm := Sym2.mem_iff.mpr hv
    rw [baseSlot_edge] at hm
    exact (Sym2.mem_iff.mp hm).imp (fun h => E.injective h) (fun h => E.injective h)
  spoke_avoids := by
    intro a v i hi
    have hs := (spokePath_spec E φ P a v).2 _ |>.mp hi
    have hv := havoid (spokeSlot E a v) (E i) hs
    rw [spokeSlot_first,spokeSlot_second] at hv
    exact hv.imp (fun h => E.injective h) (fun h => E.injective h)

end CarrierPreparation

theorem budgeted_model_of_large_carrier {V : Type} [Fintype V] [DecidableEq V]
    {p q : ℕ} (G : SimpleGraph V) (D : Finset V) (φ : (Fin p ⊕ Fin q) ↪ V)
    (hout : ∀ v, φ v ∉ D) (hq : 0 < q) (ht : 4 ≤ p+q) (heven : Even (p+q))
    (hlarge : 3*(p+q) < 4*p) (ρ : ℕ) (r : Fin p → ℕ)
    (hr : ∀ s, r s ≤ s.val+1) (hD : 6*(p+q)+ρ ≤ D.card)
    (hold : ∀ s, missingNeighbors G D (φ (Sum.inl s)) ≤ p+s.val+1+r s)
    (hnew : ∀ v, missingNeighbors G D (φ (Sum.inr v)) ≤ (p+q)+2*p+ρ) :
    ∃ M : WeakCliqueImmersion (p+q) G,
      ∀ i, 10*{e ∈ M.used | M.branch i ∈ e}.ncard ≤ 11*(p+q) := by
  obtain ⟨P,hPP,_,havoid⟩ := CarrierSlot.exists_paths G D φ hout hq ρ r hr hD hold hnew
  let E : Fin (p+q) ≃ (Fin p ⊕ Fin q) := finSumFinEquiv.symm
  let K := CarrierPreparation.prepared E φ P hPP havoid
  obtain ⟨M,_,hM⟩ := K.exists_budgeted_model ht heven
    (by rw [CarrierPreparation.oldSet_card]; omega)
    (by rw [CarrierPreparation.oldSet_card,CarrierPreparation.newSet_card]; omega)
    (by simpa only [CarrierPreparation.oldSet_card] using hlarge)
  exact ⟨M,hM⟩

end
end Cycle13
