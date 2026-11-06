import Cycle12.Foundations.H128Candidate
import Cycle12.Foundations.H128CoverChoice

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V ι τ : Type} [Fintype V] [Fintype ι] [Fintype τ]
  [DecidableEq V] [DecidableEq ι] [DecidableEq τ]

theorem routeInterior_mapLe {G H : SimpleGraph V} (hGH : G ≤ H)
    {a b : V} (p : G.Walk a b) : routeInterior (p.mapLe hGH)=routeInterior p := by
  simp only [routeInterior,SimpleGraph.Walk.support_mapLe_eq_support]

theorem routeResources_disjoint_of_avoid {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (c : τ) (Z : Finset (Sym2 V ⊕ (τ × V)))
    (he : ∀ e ∈ p.edges.toFinset, e ∉ Z.toLeft)
    (hv : Disjoint (routeInterior p) (teamMarkers Z.toRight c)) :
    Disjoint (routeResources c p) Z := by
  rw [Finset.disjoint_left]
  intro x hx hZ
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨e,he',rfl⟩ := Finset.mem_map.mp hx
    exact he e he' (Finset.mem_toLeft.mpr hZ)
  · obtain ⟨v,hv',rfl⟩ := Finset.mem_map.mp hx
    apply Finset.disjoint_left.mp hv hv'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_toRight.mpr hZ⟩

/-- The complete H128 grouped routing theorem. It constructs actual
simple paths simultaneously. Resource covers, pruning, the short-path
fan and soft-weight averaging are all proved, not supplied as premises.
The only inputs are the stated graph expansion, load and numeric bounds. -/
theorem h128_weighted_routing (G : SimpleGraph V)
    (source target : ι → V) (team : ι → τ) (hard : ι → Finset V)
    (w : ι → V → ℝ) {h B k : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hk₀ : 0 ≤ k)
    (hexp : OAI.ErdosGallai.CutExpansion G h)
    (hrh : 4 ≤ (Fintype.card V:ℝ)/h)
    (hk : k ≤ (5/6)*B)
    (hcube : 16384*B^2*Fintype.card V ≤ h^3)
    (hend : ∀ v, (endpointLoad source target v:ℝ) ≤ k)
    (hteam : ∀ c, (teamLoad team c:ℝ) ≤ B)
    (hhard : ∀ i, ((hard i).card:ℝ) ≤ h/128)
    (hw : ∀ i v, 0 ≤ w i v) :
    ∃ p : ∀ i, G.Walk (source i) (target i),
      (∀ i, (p i).IsPath ∧ (p i).length ≤ h128Length (Fintype.card V) h ∧
        Disjoint (routeInterior (p i)) (hard i) ∧
        (∑ v ∈ routeInterior (p i), w i v) ≤
          (16*h128Length (Fintype.card V) h/h)*∑ v,w i v) ∧
      (∀ i j, i ≠ j → Disjoint (p i).edges.toFinset (p j).edges.toFinset) ∧
      (∀ i j, i ≠ j → team i=team j →
        Disjoint (routeInterior (p i)) (routeInterior (p j))) := by
  let r : ℝ := Fintype.card V
  let ell := h128Length r h
  have hr : 0 < r := by
    have hrh' := (le_div_iff₀ hh).mp hrh
    dsimp [r]
    linarith
  have hell : 0 < ell := h128_length_pos hrh
  have hcapacity : 20*B*ell ≤ h := h128_capacity hh hB.le hr.le hcube
  let Good : ∀ i, G.Walk (source i) (target i) → Prop := fun i p =>
    Disjoint (routeInterior p) (hard i) ∧
      (∑ v ∈ routeInterior p,w i v) ≤ (16*ell/h)*∑ v,w i v
  have havoid : ∀ I : Finset ι, I.Nonempty →
      ∀ Z : Finset (Sym2 V ⊕ (τ × V)), Z.card < 4*ell*I.card →
      ∃ i ∈ I, ∃ p : G.Walk (source i) (target i),
        p.IsPath ∧ p.length ≤ ell ∧ Good i p ∧ Disjoint (routeResources (team i) p) Z := by
    intro I hI Z hZ
    let F := Z.toLeft
    let Y := Z.toRight
    have hZreal : (Z.card:ℝ) < 4*(ell:ℝ)*I.card := by exact_mod_cast hZ
    have hsplit : (F.card:ℝ)+Y.card=(Z.card:ℝ) := by
      exact_mod_cast (Finset.card_toLeft_add_card_toRight (u:=Z))
    have hZsplit : (F.card:ℝ)+Y.card < 4*(ell:ℝ)*I.card := by linarith only [hsplit,hZreal]
    have hIall : (I.card:ℝ) ≤ Fintype.card ι := by exact_mod_cast Finset.card_le_univ I
    have hIbound : 2*(I.card:ℝ) ≤ k*r := by
      have hh := total_demands_le source target hend
      nlinarith only [hh,hIall]
    have hFle : (F.card:ℝ) ≤ Z.card := by exact_mod_cast (Finset.card_toLeft_le (u:=Z))
    have hFbudget : (F.card:ℝ) < (25/297)*h*r :=
      h128_edge_cover_budget hh hr hB.le (Nat.cast_nonneg _) hk hcapacity hIbound hFle hZreal
    obtain ⟨R,hRhalf,hR,hRetained⟩ := exists_pruned_six_elevenths G F hh hexp hFbudget
    obtain ⟨i,hi,ha,hb,hmark⟩ := h128_exists_good_demand source target team I R F Y
      hh hB hk₀ hk hcapacity hend hteam hR hZsplit
    let W := ((hard i)∪teamMarkers Y (team i)).erase (source i) |>.erase (target i)
    have hWle : W.card ≤ (hard i).card+(teamMarkers Y (team i)).card := by
      have h₁ : W.card ≤ (((hard i)∪teamMarkers Y (team i)).erase (source i)).card :=
        Finset.card_erase_le
      exact (h₁.trans Finset.card_erase_le).trans (Finset.card_union_le _ _)
    have hW : (W.card:ℝ) ≤ (1/5+1/128)*h := by
      have hWR : (W.card:ℝ) ≤ ((hard i).card:ℝ)+(teamMarkers Y (team i)).card := by exact_mod_cast hWle
      linarith [hhard i]
    have haW : source i ∉ W := by simp [W]
    have hbW : target i ∉ W := by simp [W]
    obtain ⟨p,hp,hlen,hsupport,hdisW,hweight⟩ := h128_weighted_candidate
      (G:=G.deleteEdges F) hh hrh le_rfl hRetained (Finset.mem_compl.mpr ha)
      (Finset.mem_compl.mpr hb) haW hbW hW (w i) (hw i)
    have hdisAll : Disjoint (routeInterior p) ((hard i)∪teamMarkers Y (team i)) := by
      rw [Finset.disjoint_left]
      intro v hv hAv
      have hv' := (mem_routeInterior_iff p v).mp hv
      apply Finset.disjoint_left.mp hdisW hv
      exact Finset.mem_erase.mpr ⟨hv'.2.2,Finset.mem_erase.mpr ⟨hv'.2.1,hAv⟩⟩
    let q := p.mapLe (G.deleteEdges_le (F:Set (Sym2 V)))
    have hqi : routeInterior q=routeInterior p := routeInterior_mapLe _ _
    have hgood : Good i q := by
      constructor
      · rw [hqi]
        exact hdisAll.mono_right Finset.subset_union_left
      · rw [hqi]
        exact hweight
    have hmarkers : Disjoint (routeInterior q) (teamMarkers Z.toRight (team i)) := by
      rw [hqi]
      exact hdisAll.mono_right Finset.subset_union_right
    have hedges : ∀ e ∈ q.edges.toFinset, e ∉ Z.toLeft := by
      intro e he
      have he' : e ∈ p.edges := by
        simpa only [q,SimpleGraph.Walk.edges_mapLe_eq_edges,List.mem_toFinset] using he
      have hh := p.edges_subset_edgeSet he'
      rw [SimpleGraph.edgeSet_deleteEdges] at hh
      exact hh.2
    exact ⟨i,hi,q,hp.mapLe _,by simpa only [q,SimpleGraph.Walk.length_mapLe] using hlen,
      hgood,routeResources_disjoint_of_avoid q (team i) Z hedges hmarkers⟩
  obtain ⟨p,hp,hdis,hteamDis⟩ := haxell_select_routes source target team Good hell havoid
  refine ⟨p,?_,hdis,hteamDis⟩
  intro i
  exact ⟨(hp i).1,(hp i).2.1,((hp i).2.2).1,((hp i).2.2).2⟩

end
end Cycle13
