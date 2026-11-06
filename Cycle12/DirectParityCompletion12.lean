import Cycle12.SampledParityCompletion12
import Cycle12.InducedPackingWithSingles12

namespace Cycle12
open Cycle13 SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

/-- Direct completion on arbitrary graphs. Every expansion, sampling,
routing and smaller-order hypothesis is explicit; none is an oracle for
the desired packing. -/
theorem direct_parity_completion_weight [Nonempty V] (G : SimpleGraph V)
    {h K : ℝ} {p : unitInterval} (hn : 2≤Fintype.card V) (hh : 512≤h)
    (hexp : OAI.ErdosGallai.CutExpansion G h)
    (hbank : 4*log (Fintype.card V:ℝ)+8≤h/524288)
    (hp : 0<(p:ℝ)) (hp4 : 4*(p:ℝ)≤1) (hK : 0≤K)
    (hscale : 9437184*(Fintype.card V:ℝ)≤(p:ℝ)*((511/1024)*h)^2)
    (hz : 8192≤(p:ℝ)*((511/1024)*h))
    (hlog : 8192*log (Fintype.card V:ℝ)≤(p:ℝ)*((511/1024)*h))
    (hsquare : 2112*(Fintype.card V:ℝ)≤((p:ℝ)*((511/1024)*h))^2)
    (ih : ∀ m,m<Fintype.card V → ∀ H : SimpleGraph (Fin m),
      ∃ Q : CyclePacking H,Q.weight≤K*m) :
    ∃ P : CyclePacking G,P.weight≤(1+K*(4*(p:ℝ)))*Fintype.card V+
      (23/42:ℝ)*(univ.filter (fun v => ¬Even (G.degree v))).card := by
  have hh0 : 0<h := by linarith only [hh]
  obtain ⟨H₁,H₂,h₁,h₂,hdis,hexp₁,hexp₂⟩ := balanced_completion_banks G hn hh0 hexp hbank
  have hratio := Global12.balanced_sample_order_ratio G hn hh hexp
  obtain ⟨U,hU,P,hP,hd⟩ := sampled_parity_completion G H₁ H₂ h₁ h₂ hdis hp
    (by linarith only [hp,hp4]) (mul_pos (by norm_num) hh0) hn hratio hscale hz hlog hsquare hexp₁ hexp₂
  exact parity_completion_induction_step P U hp4 hK hP hU hd ih

end
end Cycle12
