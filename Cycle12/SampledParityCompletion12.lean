import Cycle12.ParityThreeReservoir12

namespace Cycle12
open Cycle13 SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

/-- Simultaneous actual samples and both actual closing passes give an
n-cycle completion with a residue on fewer than 4pn vertices, plus
at most one outside singleton per original odd vertex. -/
theorem sampled_parity_completion [Nonempty V]
    (G H₁ H₂ : SimpleGraph V) (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G)
    (hdis : Disjoint H₁.edgeSet H₂.edgeSet)
    {p : unitInterval} {h : ℝ} (hp : 0 < (p:ℝ)) (hp3 : 3*(p:ℝ) ≤ 1) (hh : 0 < h)
    (hn : 2 ≤ Fintype.card V) (hratio : 4*h ≤ (Fintype.card V:ℝ))
    (hscale : 9437184*(Fintype.card V:ℝ) ≤ (p:ℝ)*h^2)
    (hz : 8192 ≤ (p:ℝ)*h) (hlog : 8192*log (Fintype.card V:ℝ) ≤ (p:ℝ)*h)
    (hsquare : 2112*(Fintype.card V:ℝ) ≤ ((p:ℝ)*h)^2)
    (hexp₁ : OAI.ErdosGallai.CutExpansion H₁ h) (hexp₂ : OAI.ErdosGallai.CutExpansion H₂ h) :
    ∃ U : Finset V, (U.card:ℝ) < 4*(p:ℝ)*Fintype.card V ∧
      ∃ P : CyclePacking G, P.count ≤ Fintype.card V ∧
        ∀ v,v∉U → P.residue.degree v=if Even (G.degree v) then 0 else 1 := by
  let banks : Fin 3 → SimpleGraph V := ![H₁,H₁,H₂]
  have hl : 3072*log (Fintype.card V:ℝ) ≤ (p:ℝ)*h := by
    have hn1 : (1:ℝ) ≤ Fintype.card V := by exact_mod_cast (show 1 ≤ Fintype.card V by omega)
    have hlog0 := log_nonneg hn1
    linarith only [hlog,hlog0]
  obtain ⟨U,hUdis,hU,_,hUcard⟩ := three_reservoir_samples banks hp hp3 hh hn hratio hscale hl
    (fun i => by fin_cases i <;> assumption)
  have hzr : (p:ℝ)*h ≤ (Fintype.card V:ℝ) := by
    have hp1 := p.property.2
    nlinarith only [hp1,hh,hratio]
  obtain ⟨P,hP,hres⟩ := parity_three_reservoir_completion G H₁ H₂ h₁ h₂ hdis
    (U 0) (U 1) (U 2) (hUdis (by decide)) (hUdis (by decide)) (hUdis (by decide))
    (hU 0) (hU 1) (hU 2) hz hzr hlog hsquare
  refine ⟨univ.biUnion U,hUcard,P,hP,?_⟩
  intro v hv
  have hi : U 0 ∪ U 1 ∪ U 2 ⊆ univ.biUnion U := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · rcases mem_union.mp hv with hv | hv
      · exact mem_biUnion.mpr ⟨0,mem_univ _,hv⟩
      · exact mem_biUnion.mpr ⟨1,mem_univ _,hv⟩
    · exact mem_biUnion.mpr ⟨2,mem_univ _,hv⟩
  exact hres v (fun h => hv (hi h))

end
end Cycle12
