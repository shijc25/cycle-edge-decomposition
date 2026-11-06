import Cycle12.Pruning
import Cycle12.GeneralRouter
import Cycle12.RouterParameters

/-! Connect the universally quantified scalar choice to a real induced graph core. -/
namespace Cycle12

universe u
variable {V : Type u} [Fintype V]
open scoped Classical

theorem adaptive_pruned_core {G : SimpleGraph V} {h q a x : ℝ}
    (hn : 0 < Fintype.card V) (hh : 0 < h) (hG : CutExpands G h)
    (hq : 0 < q) (ha : 0 < a) (ha1 : a < 1)
    (hgap : 1+q+a*q < 2*a^2*(q+2)) (hx : 0 ≤ x) (hx1 : x < 1)
    (F : Finset (Sym2 V))
    (hF : (F.card : ℝ) ≤ q*a*x/(2*(1+q))*h*(Fintype.card V : ℝ)) :
    ∃ (z τ : ℝ) (S : Finset V), 0 < z ∧ z < 1 ∧ 0 < τ ∧
      1-z-τ=1-a ∧ q*x/z+(1-x)/τ=(1+q)/a ∧
      (S.card : ℝ) ≤ F.card/(z*h) ∧
      CutExpandsOn (G.deleteEdges F) Sᶜ ((1-z)*h) := by
  obtain ⟨z, τ, hz, hz1, hτ, hretain, hcharge, hcut⟩ :=
    general_router_choice hq ha ha1 hgap hx hx1
  have hnR : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hn
  have hb : (F.card : ℝ) < z^2/(1+z)*h*(Fintype.card V : ℝ) :=
    hF.trans_lt (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hcut hh) hnR)
  obtain ⟨S, hS, hcore⟩ := prune_expanding_core_ratio hh hz hz1 hG F hb
  exact ⟨z, τ, S, hz, hz1, hτ, hretain, hcharge, hS, hcore⟩

theorem accepted_parameters_pruned_core {G : SimpleGraph V} {h x : ℝ}
    (hn : 0 < Fintype.card V) (hh : 0 < h) (hG : CutExpands G h)
    (hx : 0 ≤ x) (hx1 : x < 1) (F : Finset (Sym2 V))
    (hF : (F.card : ℝ) ≤ Parameters.q*Parameters.a*x/(2*(1+Parameters.q))*h*
      (Fintype.card V : ℝ)) :
    ∃ (z τ : ℝ) (S : Finset V), 0 < z ∧ z < 1 ∧ 0 < τ ∧
      1-z-τ=1-Parameters.a ∧
      Parameters.q*x/z+(1-x)/τ=(1+Parameters.q)/Parameters.a ∧
      (S.card : ℝ) ≤ F.card/(z*h) ∧
      CutExpandsOn (G.deleteEdges F) Sᶜ ((1-z)*h) := by
  obtain ⟨hq, ha, ha1, hgap, _⟩ := Parameters.router_parameters_valid
  exact adaptive_pruned_core hn hh hG hq ha ha1 hgap hx hx1 F hF

end Cycle12
