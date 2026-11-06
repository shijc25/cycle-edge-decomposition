import Cycle12.RoutingCandidate
import Cycle12.RoutingLoad
import Cycle12.AdaptiveCore
import Cycle12.Foundations.H128Routing

/-! Arbitrary endpoint/team load ratio: actual simultaneous routing, with all
the resource-cover, expanding-core, fan, and averaging steps proved. -/
namespace Cycle12
open SimpleGraph Finset Real Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V ι τ : Type} [Fintype V] [Fintype ι] [Fintype τ]

theorem grouped_weighted_routing (G : SimpleGraph V)
    (source target : ι → V) (team : ι → τ) (hard : ι → Finset V)
    (w : ι → V → ℝ) {h B k q a R γ L : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hk₀ : 0 ≤ k)
    (hq : 0 < q) (ha : 0 < a) (ha1 : a < 1)
    (hgap : 1+q+a*q < 2*a^2*(q+2)) (hR : 4*(1+q)/a < R)
    (hγ : 0 < γ) (hr : 0 < routingRetained a R γ) (hL : 1/32 < L)
    (hcoef : 8/routingRetained a R γ < (L-1/32)^2)
    (hexp : CutExpands G h) (hnh : 4096 ≤ (Fintype.card V:ℝ)/h)
    (hk : k ≤ q*B) (hcube : R^2*L^2*B^2*Fintype.card V ≤ h^3)
    (hend : ∀ v, (endpointLoad source target v:ℝ) ≤ k)
    (hteam : ∀ c, (teamLoad team c:ℝ) ≤ B)
    (hhard : ∀ i, ((hard i).card:ℝ) ≤ h/128) (hw : ∀ i v, 0 ≤ w i v) :
    ∃ p : ∀ i, G.Walk (source i) (target i),
      (∀ i, (p i).IsPath ∧ (p i).length ≤ routingLength (Fintype.card V) h L ∧
        Disjoint (routeInterior (p i)) (hard i) ∧
        (∑ v ∈ routeInterior (p i), w i v) ≤ (γ/B)*∑ v,w i v) ∧
      (∀ i j, i ≠ j → Disjoint (p i).edges.toFinset (p j).edges.toFinset) ∧
      (∀ i j, i ≠ j → team i=team j →
        Disjoint (routeInterior (p i)) (routeInterior (p j))) := by
  let n : ℝ := Fintype.card V
  let ell := routingLength n h L
  have hn : 0 < n := by
    have h := (le_div_iff₀ hh).mp hnh
    dsimp [n]
    linarith
  have hnNat : 0 < Fintype.card V := by dsimp [n] at hn; exact_mod_cast hn
  have hell : 0 < ell := routing_length_pos hL hnh
  have hellR : (0:ℝ) < ell := by exact_mod_cast hell
  have hRpos : 0 < R := (by positivity : 0 < 4*(1+q)/a).trans hR
  have hLp : 0 < L := by linarith
  have hcapacity : R*B*ell ≤ h := routing_capacity hh hRpos.le hLp.le hB.le hn.le hcube
  have hR' : 4*(1+q) < R*a := (div_lt_iff₀ ha).mp hR
  have hsmallcap : 4*B*ell*(1+q) ≤ a*h := by
    have hm := mul_le_mul_of_nonneg_right hR'.le (by positivity : 0 ≤ B*ell)
    have hc := mul_le_mul_of_nonneg_left hcapacity ha.le
    nlinarith only [hm,hc]
  let Good : ∀ i, G.Walk (source i) (target i) → Prop := fun i p =>
    Disjoint (routeInterior p) (hard i) ∧
      (∑ v ∈ routeInterior p,w i v) ≤ (γ/B)*∑ v,w i v
  have havoid : ∀ I : Finset ι, I.Nonempty →
      ∀ Z : Finset (Sym2 V ⊕ (τ × V)), Z.card < 4*ell*I.card →
      ∃ i ∈ I, ∃ p : G.Walk (source i) (target i),
        p.IsPath ∧ p.length ≤ ell ∧ Good i p ∧ Disjoint (routeResources (team i) p) Z := by
    intro I hI Z hZ
    let F := Z.toLeft
    let Y := Z.toRight
    let D : ℝ := 4*ell*I.card
    have hIR : (0:ℝ) < I.card := by exact_mod_cast hI.card_pos
    have hD : 0 < D := by positivity
    have hsplit : (F.card:ℝ)+Y.card=(Z.card:ℝ) := by
      exact_mod_cast (Finset.card_toLeft_add_card_toRight (u:=Z))
    have hZreal : (Z.card:ℝ) < D := by dsimp [D]; exact_mod_cast hZ
    have hZsplit : (F.card:ℝ)+Y.card < D := by linarith only [hsplit,hZreal]
    let x : ℝ := F.card/D
    have hx : 0 ≤ x := by positivity
    have hx1 : x < 1 := by
      apply (div_lt_one hD).mpr
      have hY : (0:ℝ) ≤ Y.card := Nat.cast_nonneg _
      linarith only [hZsplit,hY]
    have hF : (F.card:ℝ)=x*D := by dsimp [x]; field_simp
    have hIall : (I.card:ℝ) ≤ Fintype.card ι := by exact_mod_cast Finset.card_le_univ I
    have hIbound : 2*(I.card:ℝ) ≤ k*n := by
      have hb := total_demands_le source target hend
      nlinarith only [hb,hIall]
    have hFbudget : (F.card:ℝ) ≤ q*a*x/(2*(1+q))*h*n :=
      routing_obstacle_budget hn.le hq hx hellR.le hk hIbound hF hsmallcap
    obtain ⟨z,t,S,hz,hz1,ht,hretain,hcharge,hS,hcore⟩ :=
      adaptive_pruned_core hnNat hh hexp hq ha ha1 hgap hx hx1 F hFbudget
    have hchargeCap : B*D*(1+q) ≤ a*h*I.card := by
      have hc := mul_le_mul_of_nonneg_right hsmallcap hIR.le
      dsimp [D]
      nlinarith only [hc]
    have hbad : k*F.card/(z*h)+B*Y.card/(t*h) < I.card :=
      routing_charge_bound hh hB ha hz ht (Nat.cast_nonneg _) hk hF hZsplit hcharge hchargeCap
    obtain ⟨i,hi,hu,hv,hmark⟩ := routing_exists_good_demand source target team I S F Y
      hh hz ht hB.le hk₀ hend hteam hS hbad
    let W := ((hard i)∪teamMarkers Y (team i)).erase (source i) |>.erase (target i)
    have hWle : W.card ≤ (hard i).card+(teamMarkers Y (team i)).card := by
      exact (Finset.card_erase_le.trans Finset.card_erase_le).trans (Finset.card_union_le _ _)
    have hW : (W.card:ℝ) ≤ (t+1/128)*h := by
      have hWR : (W.card:ℝ) ≤ ((hard i).card:ℝ)+(teamMarkers Y (team i)).card := by exact_mod_cast hWle
      linarith [hhard i]
    have huW : source i ∉ W := by simp [W]
    have hvW : target i ∉ W := by simp [W]
    obtain ⟨p,hp,hlen,hsupport,hdisW,hweight⟩ := routing_weighted_candidate
      (G:=G.deleteEdges F) hh hRpos hγ hr hL hcoef hnh le_rfl hretain hcore
      (Finset.mem_compl.mpr hu) (Finset.mem_compl.mpr hv) huW hvW hW (w i) (hw i)
    have hdisAll : Disjoint (routeInterior p) ((hard i)∪teamMarkers Y (team i)) := by
      rw [Finset.disjoint_left]
      intro v hv hAv
      have hv' := (mem_routeInterior_iff p v).mp hv
      apply Finset.disjoint_left.mp hdisW hv
      exact Finset.mem_erase.mpr ⟨hv'.2.2,Finset.mem_erase.mpr ⟨hv'.2.1,hAv⟩⟩
    let path := p.mapLe (G.deleteEdges_le (F:Set (Sym2 V)))
    have hpi : routeInterior path=routeInterior p := routeInterior_mapLe _ _
    have hpay : R*γ*ell/h ≤ γ/B := by
      apply (div_le_div_iff₀ hh hB).mpr
      have hc := mul_le_mul_of_nonneg_left hcapacity hγ.le
      nlinarith only [hc]
    have hgood : Good i path := by
      constructor
      · rw [hpi]
        exact hdisAll.mono_right Finset.subset_union_left
      · rw [hpi]
        exact hweight.trans (mul_le_mul_of_nonneg_right hpay
          (Finset.sum_nonneg (fun v _ => hw i v)))
    have hmarkers : Disjoint (routeInterior path) (teamMarkers Z.toRight (team i)) := by
      rw [hpi]
      exact hdisAll.mono_right Finset.subset_union_right
    have hedges : ∀ e ∈ path.edges.toFinset, e ∉ Z.toLeft := by
      intro e he
      have he' : e ∈ p.edges := by
        simpa only [path,SimpleGraph.Walk.edges_mapLe_eq_edges,List.mem_toFinset] using he
      have heG := p.edges_subset_edgeSet he'
      rw [SimpleGraph.edgeSet_deleteEdges] at heG
      exact heG.2
    exact ⟨i,hi,path,hp.mapLe _,by simpa only [path,SimpleGraph.Walk.length_mapLe] using hlen,
      hgood,routeResources_disjoint_of_avoid path (team i) Z hedges hmarkers⟩
  obtain ⟨p,hp,hdis,hteamDis⟩ := haxell_select_routes source target team Good hell havoid
  refine ⟨p,?_,hdis,hteamDis⟩
  intro i
  exact ⟨(hp i).1,(hp i).2.1,((hp i).2.2).1,((hp i).2.2).2⟩

end
end Cycle12
