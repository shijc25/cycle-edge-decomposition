import Cycle12.RoutingArithmetic
import Cycle12.InducedExpansion
import Cycle12.Foundations.RoutingLoadCounts
import Cycle12.Foundations.HaxellRoutingSelect

namespace Cycle12
open Real Finset SimpleGraph Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V ι : Type} [Fintype V] [Fintype ι]

/-- Haxell selection with only actual edges as resources. -/
theorem haxell_select_edge_routes (G : SimpleGraph V) (source target : ι → V)
    {ell : ℕ} (hell : 0 < ell)
    (havoid : ∀ I : Finset ι, I.Nonempty → ∀ F : Finset (Sym2 V), F.card < 2*ell*I.card →
      ∃ i∈I, ∃ p : G.Walk (source i) (target i), p.IsPath ∧ p.length ≤ ell ∧ Disjoint p.edges.toFinset F) :
    ∃ p : ∀ i, G.Walk (source i) (target i),
      (∀ i, (p i).IsPath ∧ (p i).length ≤ ell) ∧
      (∀ i j, i≠j → Disjoint (p i).edges.toFinset (p j).edges.toFinset) := by
  classical
  let H : ι → Finset (Sym2 V) → Prop := fun i e =>
    ∃ p : G.Walk (source i) (target i), p.IsPath ∧ p.length ≤ ell ∧ e=p.edges.toFinset
  have hsize : ∀ i e, H i e → e.card ≤ ell := by
    rintro i e ⟨p,hp,hlen,rfl⟩
    exact (List.toFinset_card_le p.edges).trans (by simpa using hlen)
  have hcond : ∀ I : Finset ι, I.Nonempty → ∀ F : Finset (Sym2 V),
      F.card ≤ 2*ell*(I.card-1) → ∃ i∈I, ∃ e, H i e ∧ Disjoint e F := by
    intro I hI F hF
    have hi := hI.card_pos
    have hF' : F.card < 2*ell*I.card := by
      have he : I.card=I.card-1+1 := by omega
      nlinarith
    obtain ⟨i,hi,p,hp,hlen,hdis⟩ := havoid I hI F hF'
    exact ⟨i,hi,p.edges.toFinset,⟨p,hp,hlen,rfl⟩,hdis⟩
  obtain ⟨f,hf,hdis⟩ := Lovasz.Haxell.haxell hsize hcond
  choose p hp hlen he using hf
  refine ⟨p,fun i => ⟨hp i,hlen i⟩,?_⟩
  intro i j hij
  simpa only [he i,he j] using hdis i j hij

/-- The direct-pairing constant 324, including its required n/h ≥ 4096.
This theorem has no team, vertex-disjointness or soft-cost claim. -/
theorem direct_edge_routing_324 (G : SimpleGraph V) (source target : ι → V)
    {h k : ℝ} (hh : 0 < h) (hk : 0 < k) (hexp : CutExpands G h)
    (hnh : 4096 ≤ (Fintype.card V:ℝ)/h)
    (hcube : 324*k^2*(Fintype.card V:ℝ) ≤ h^3)
    (hend : ∀ v, (endpointLoad source target v:ℝ) ≤ k) :
    ∃ p : ∀ i, G.Walk (source i) (target i),
      (∀ i, (p i).IsPath ∧ (p i).length ≤ routingLength (Fintype.card V) h (57/10)) ∧
      (∀ i j, i≠j → Disjoint (p i).edges.toFinset (p j).edges.toFinset) := by
  classical
  let ell := routingLength (Fintype.card V) h (57/10)
  have hell : 0 < ell := routing_length_pos (by norm_num) hnh
  have hellR : (0:ℝ) < ell := by exact_mod_cast hell
  have hn : (0:ℝ) < Fintype.card V := by
    have hm := (le_div_iff₀ hh).mp hnh
    linarith only [hm,hh]
  have hcapacity := routing_capacity (n:=(Fintype.card V:ℝ)) (R:=(60/19:ℝ)) (L:=(57/10:ℝ)) (B:=k)
    hh (by norm_num) (by norm_num) hk.le hn.le (by norm_num at hcube ⊢; exact hcube)
  have hcap : k*(ell:ℝ) ≤ (19/60)*h := by dsimp [ell]; linarith only [hcapacity]
  apply haxell_select_edge_routes G source target hell
  intro I hI F hF
  have hIR : (0:ℝ) < I.card := by exact_mod_cast hI.card_pos
  have hFreal : (F.card:ℝ) < 2*(ell:ℝ)*I.card := by exact_mod_cast hF
  have hIall : (I.card:ℝ) ≤ Fintype.card ι := by exact_mod_cast card_le_univ I
  have hItotal := total_demands_le source target hend
  have hIbound : 2*(I.card:ℝ) ≤ k*(Fintype.card V:ℝ) := by linarith only [hIall,hItotal]
  have hFbound : (F.card:ℝ) < k*(ell:ℝ)*(Fintype.card V:ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hIbound hellR.le
    nlinarith only [hm,hFreal]
  have hprune : (2-(1/4:ℝ))*(F.card:ℝ) < (1-(1/4:ℝ))^2*h*(Fintype.card V:ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hcap hn.le
    have hhN := mul_pos hh hn
    nlinarith only [hm,hFbound,hhN]
  obtain ⟨S,hS,hcore⟩ := prune_expanding_core hh (by norm_num : (0:ℝ)<1/4) (by norm_num) hexp F hprune
  have hbad := (endpoint_bad_card_le source target hend I S).trans
    (mul_le_mul_of_nonneg_left hS hk.le)
  have hbadlt : ((I.filter fun i => source i∈S ∨ target i∈S).card:ℝ) < I.card := by
    have hd : 0 < (1-(1/4:ℝ))*h := by positivity
    have hs' := (le_div_iff₀ hd).mp hS
    have hbad0 := endpoint_bad_card_le source target hend I S
    have hprod := mul_le_mul_of_nonneg_left hs' hk.le
    have hsmall := mul_lt_mul_of_pos_left hFreal hk
    have hbudget := mul_le_mul_of_nonneg_right hcap hIR.le
    have hbadprod := mul_le_mul_of_nonneg_right hbad0 hd.le
    have hIh := mul_pos hIR hh
    apply (mul_lt_mul_iff_right₀ hh).mp
    nlinarith only [hprod,hsmall,hbudget,hbadprod,hIh]
  have hnot : ¬I ⊆ I.filter (fun i => source i∈S ∨ target i∈S) := by
    intro hi
    have hh := (Nat.cast_le (α:=ℝ)).mpr (card_le_card hi)
    linarith only [hh,hbadlt]
  obtain ⟨i,hi,hgood⟩ := Finset.not_subset.mp hnot
  have hends : source i∉S ∧ target i∉S := by simpa only [mem_filter,hi,true_and,not_or] using hgood
  obtain ⟨p,hp,hsupport,hlen⟩ := expanding_induced_short_path (by positivity : (0:ℝ)<(1/4)*h)
    hcore (source i) (target i) (mem_compl.mpr hends.1) (mem_compl.mpr hends.2)
  have hScard : (Sᶜ.card:ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ Sᶜ
  have hshort : p.length ≤ ell := routing_natural_length_bound hh (by norm_num : (0:ℝ)<1/4)
    (by norm_num : (1/32:ℝ)<57/10) (by norm_num) hScard hnh hlen
  let path := p.mapLe (G.deleteEdges_le (F:Set (Sym2 V)))
  refine ⟨i,hi,path,hp.mapLe _,by simpa only [path,Walk.length_mapLe] using hshort,?_⟩
  rw [Finset.disjoint_left]
  intro e he heF
  have he' : e∈p.edges := by simpa only [path,Walk.edges_mapLe_eq_edges,List.mem_toFinset] using he
  have heG := p.edges_subset_edgeSet he'
  rw [edgeSet_deleteEdges] at heG
  exact heG.2 heF

end
end Cycle12
