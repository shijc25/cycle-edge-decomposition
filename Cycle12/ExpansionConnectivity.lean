import Cycle12.Pruning

namespace Cycle12

universe u
variable {V : Type u} [Fintype V]
open scoped Classical
open Finset

theorem cutExpands_preconnected {G : SimpleGraph V} {h : ℝ}
    (hh : 0 < h) (hG : CutExpands G h) : G.Preconnected := by
  intro u v
  by_contra huv
  let S : Finset V := univ.filter (G.Reachable u)
  have huS : u ∈ S := by simp [S]
  have hvS : v ∈ Sᶜ := by simp [S, huv]
  have hScard : 0 < S.card := card_pos.mpr ⟨u, huS⟩
  have hCcard : 0 < Sᶜ.card := card_pos.mpr ⟨v, hvS⟩
  have hcut : boundaryCount G S = 0 := by
    apply cutCount_zero_of_no_edges
    intro x hx y hy hxy
    have hux : G.Reachable u x := (mem_filter.mp hx).2
    have huy := hux.trans hxy.reachable
    exact (mem_compl.mp hy) (mem_filter.mpr ⟨mem_univ _, huy⟩)
  have hcompcut : boundaryCount G Sᶜ = 0 := by
    simpa only [boundaryCount, compl_compl, cutCount_comm G Sᶜ S] using hcut
  have hsum : Sᶜ.card + S.card = Fintype.card V := by simp
  by_cases hs : 2*S.card ≤ Fintype.card V
  · have hb := hG S hs
    rw [hcut, Nat.cast_zero] at hb
    have hp : 0 < h*(S.card : ℝ) := mul_pos hh (by exact_mod_cast hScard)
    linarith
  · have hb := hG Sᶜ (by omega)
    rw [hcompcut, Nat.cast_zero] at hb
    have hp : 0 < h*(Sᶜ.card : ℝ) := mul_pos hh (by exact_mod_cast hCcard)
    linarith

theorem cutExpands_connected [Nonempty V] {G : SimpleGraph V} {h : ℝ}
    (hh : 0 < h) (hG : CutExpands G h) : G.Connected :=
  ⟨cutExpands_preconnected hh hG⟩

end Cycle12
