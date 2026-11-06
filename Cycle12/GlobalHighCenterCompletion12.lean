import Cycle12.HighCenterGeometry12
import Cycle12.HighCenterScaleBounds12

namespace Cycle12.Even12
open Cycle13 SimpleGraph Finset Real
open Cycle12.Global12 OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The high-center branch is an actual graph construction at every
current active scale. Its extra vertices and low-path color overhead fit
the existing 1/2048 coefficient; parity is charged only on the core. -/
theorem high_center_completion_at_scale [Nonempty V] (G : SimpleGraph V) (U : Finset V)
    {w d K : ℝ} (hw : wA ≤ w) (hn : 2 ≤ Fintype.card V) (hK : 0 ≤ K)
    (hrlo : (2:ℝ)^(s*w) ≤ (U.card:ℝ)) (hrhi : (U.card:ℝ) ≤ (2:ℝ)^(rho*w))
    (hexp : OAI.ErdosGallai.Scale.CutExpansionOn G U (completion_bank*(2:ℝ)^(s*w)))
    (hdeg : ∀ v,v∉U → d ≤ ((neighborsIn G v U).card:ℝ))
    (hload : ∀ v∈U,((neighborsIn G v Uᶜ).card:ℝ) ≤ (2:ℝ)^(alpha*w))
    (hd : sqrt (2*(2:ℝ)^(alpha*w)*U.card) ≤ d)
    (hdup : d ≤ sqrt (2*(2:ℝ)^(alpha*w)*U.card)+1)
    (heven : ∀ v,v∉U → Even (G.degree v))
    (ih : ∀ m,m<Fintype.card V → ∀ H : SimpleGraph (Fin m),
      ∃ Q : CyclePacking H,Q.weight ≤ K*m) :
    ∃ P : CyclePacking G,P.weight+d/2+2*(2:ℝ)^(alpha*w) ≤
      (1+23/42+K*eta+1/2048)*(U.card:ℝ) := by
  let a := (2:ℝ)^(alpha*w)
  let h := completion_bank*(2:ℝ)^(s*w)
  let r : ℝ := U.card
  let n : ℝ := Fintype.card V
  let q : ℝ := Uᶜ.card
  have hr : 0<r := (rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).trans_le hrlo
  have ha0 : 0<a := rpow_pos_of_pos (by norm_num) _
  obtain ⟨ha,hsep,_,_⟩ := high_center_scale_bounds (n:=r) hw hrlo hrhi
    (by nlinarith only [hr]) hr
  have hqd : q*d ≤ a*r := by
    have hh := high_centers_incidence_budget G U Uᶜ
      (fun v hv => hdeg v (mem_compl.mp hv)) hload
    simpa only [q,a,r,mul_comm] using hh
  obtain ⟨hqsmall,hfee⟩ := high_center_rounding_budget ha hsep (Nat.cast_nonneg Uᶜ.card) hd hdup hqd
  have hnexact : n=r+q := by
    have hh := card_add_card_compl U
    dsimp only [n,r,q]
    exact_mod_cast hh.symm
  have horder : n ≤ (1+1/2048)*r := by linarith only [hqsmall,hnexact]
  have hn0 : 0<n := by dsimp only [n]; exact_mod_cast (show 0<Fintype.card V by omega)
  obtain ⟨_,_,hmin,hlog⟩ := high_center_scale_bounds hw hrlo hrhi horder hn0
  have hd0 : 0<d := (sqrt_pos.2 (show 0<2*a*r by positivity)).trans_le hd
  have hsq : 2*a*r ≤ d^2 := by
    have hh := (sq_le_sq₀ (sqrt_nonneg (2*a*r)) hd0.le).mpr hd
    rwa [sq_sqrt (show 0 ≤ 2*a*r by positivity)] at hh
  have hh0 : 0 ≤ h := mul_nonneg (by norm_num [completion_bank]) (rpow_nonneg (by norm_num) _)
  obtain ⟨ha₀,ha₀a,hg,hg2⟩ := high_center_effective_geometry ha0.le hr hh0 hd0.le hsep hsq
  have hfew : q ≤ d/2 := by nlinarith only [hqd,hsq,hd0]
  have hexpG := high_center_cut_extension G U hh0 hd0.le hexp hdeg hfew
  obtain ⟨P,hP⟩ := high_center_completion_weight G U hn hK horder hmin hlog hg hg2 (by convert hexpG using 1) heven ih
  refine ⟨P,?_⟩
  change P.weight+d/2+2*a ≤ (1+23/42+K*eta+1/2048)*r
  change P.weight ≤ n+(K*eta+23/42)*r at hP
  nlinarith only [hP,hfee,hnexact]

end
end Cycle12.Even12
