import Cycle12.Foundations.Definitions

/-! Actual paths for strong clique immersions, and a verified edge-routing
interface that lifts them through vertex-splitting operations. -/
namespace Cycle13
open SimpleGraph
universe u v

structure EdgeRouting {V : Type u} {W : Type v} (H : SimpleGraph V) (G : SimpleGraph W) where
  vertex : V ↪ W
  route : ∀ {x y : V}, H.Adj x y → G.Walk (vertex x) (vertex y)
  disjoint : ∀ {x y a b : V} (hxy : H.Adj x y) (hab : H.Adj a b),
    s(x,y) ≠ s(a,b) → Disjoint (route hxy).edgeSet (route hab).edgeSet
  avoids : ∀ {x y : V} (hxy : H.Adj x y) (a : V),
    vertex a ∈ (route hxy).support → a = x ∨ a = y

namespace EdgeRouting
variable {V : Type u} {W : Type v} {H : SimpleGraph V} {G : SimpleGraph W}

def liftWalk (R : EdgeRouting H G) {x y : V} : H.Walk x y → G.Walk (R.vertex x) (R.vertex y)
  | .nil => .nil
  | .cons h p => (R.route h).append (R.liftWalk p)

theorem liftWalk_support (R : EdgeRouting H G) {x y : V} (p : H.Walk x y)
    (a : V) (ha : R.vertex a ∈ (R.liftWalk p).support) : a ∈ p.support := by
  induction p with
  | nil => simpa [liftWalk] using ha
  | @cons x y z h p ih =>
    have hsup : R.vertex a ∈ (R.route h).support ∨ R.vertex a ∈ (R.liftWalk p).support := by
      simpa only [liftWalk, Walk.mem_support_append_iff] using ha
    rcases hsup with hr | hp
    · rcases R.avoids h a hr with rfl | rfl
      · simp
      · simp [p.start_mem_support]
    · exact List.mem_cons_of_mem _ (ih hp)

theorem liftWalk_edge_origin (R : EdgeRouting H G) {x y : V} (p : H.Walk x y)
    {e : Sym2 W} (he : e ∈ (R.liftWalk p).edgeSet) :
    ∃ (a b : V) (hab : H.Adj a b), s(a,b) ∈ p.edgeSet ∧ e ∈ (R.route hab).edgeSet := by
  induction p with
  | nil => simpa [liftWalk] using he
  | @cons x y z h p ih =>
    have hm : e ∈ (R.route h).edgeSet ∨ e ∈ (R.liftWalk p).edgeSet := by
      simpa only [liftWalk, Walk.edgeSet_append, Set.mem_union] using he
    rcases hm with hr | hp
    · exact ⟨x, y, h, by simp, hr⟩
    · obtain ⟨a, b, hab, heab, hroute⟩ := ih hp
      exact ⟨a, b, hab, by simpa using Or.inr heab, hroute⟩

theorem liftWalk_disjoint (R : EdgeRouting H G) {x y a b : V}
    (p : H.Walk x y) (q : H.Walk a b) (hd : Disjoint p.edgeSet q.edgeSet) :
    Disjoint (R.liftWalk p).edgeSet (R.liftWalk q).edgeSet := by
  apply Set.disjoint_left.mpr
  intro e hep heq
  obtain ⟨u, v, huv, hp, her⟩ := R.liftWalk_edge_origin p hep
  obtain ⟨s, t, hst, hq, heq⟩ := R.liftWalk_edge_origin q heq
  have hne : s(u,v) ≠ s(s,t) := fun he => Set.disjoint_left.mp hd hp (he ▸ hq)
  exact Set.disjoint_left.mp (R.disjoint huv hst hne) her heq

end EdgeRouting

def CliquePair (t : ℕ) := {p : Fin t × Fin t // p.1 < p.2}

structure StrongCliqueImmersion {V : Type u} (t : ℕ) (G : SimpleGraph V) where
  branch : Fin t ↪ V
  route : ∀ p : CliquePair t, G.Path (branch p.1.1) (branch p.1.2)
  disjoint : Pairwise (fun p q => Disjoint (route p).val.edgeSet (route q).val.edgeSet)
  avoids : ∀ (p : CliquePair t) (i : Fin t),
    branch i ∈ (route p).val.support → i = p.1.1 ∨ i = p.1.2

namespace StrongCliqueImmersion
variable {V : Type u} {W : Type v} {H : SimpleGraph V} {G : SimpleGraph W} {t : ℕ}

noncomputable def lift (M : StrongCliqueImmersion t H) (R : EdgeRouting H G) :
    StrongCliqueImmersion t G := by
  classical
  refine {
    branch := M.branch.trans R.vertex
    route := fun p => (R.liftWalk (M.route p).val).toPath
    disjoint := ?_
    avoids := ?_ }
  · intro p q hpq
    exact (R.liftWalk_disjoint _ _ (M.disjoint hpq)).mono
      (R.liftWalk (M.route p).val).edges_toPath_subset_edges
      (R.liftWalk (M.route q).val).edges_toPath_subset_edges
  · intro p i hi
    exact M.avoids p i (R.liftWalk_support _ (M.branch i)
      ((R.liftWalk (M.route p).val).support_toPath_subset_support hi))

def ofCompleteEmbedding (f : completeGraph (Fin t) ↪g G) : StrongCliqueImmersion t G where
  branch := f.toEmbedding
  route p := SimpleGraph.Path.singleton (f.toHom.map_adj (by exact ne_of_lt p.2))
  disjoint := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    intro e hep heq
    have hep' : e = s(f p.1.1, f p.1.2) := by simpa [Path.singleton, Adj.toWalk] using hep
    have heq' : e = s(f q.1.1, f q.1.2) := by simpa [Path.singleton, Adj.toWalk] using heq
    have he : s(f p.1.1, f p.1.2) = s(f q.1.1, f q.1.2) := hep'.symm.trans heq'
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hpq (Subtype.ext (Prod.ext (f.injective h1) (f.injective h2)))
    · have h1' := f.injective h1
      have h2' := f.injective h2
      have hp := p.2
      have hq := q.2
      omega
  avoids := by
    intro p i hi
    have hi' : f i = f p.1.1 ∨ f i = f p.1.2 := by simpa [Path.singleton, Adj.toWalk] using hi
    exact hi'.imp (fun h => f.injective h) (fun h => f.injective h)

theorem exists_of_not_cliqueFree {V : Type} {G : SimpleGraph V} {t : ℕ}
    (h : ¬G.CliqueFree t) : Nonempty (StrongCliqueImmersion t G) :=
  ⟨ofCompleteEmbedding (G.topEmbeddingOfNotCliqueFree h)⟩

end StrongCliqueImmersion
end Cycle13
