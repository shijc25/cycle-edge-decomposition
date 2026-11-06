import Cycle12.CutCounting

/-! Extraction of an expanding induced core after edge deletion.
This is the graph theorem, with cuts counted from the original undirected edge set. -/
namespace Cycle12

universe u
variable {V : Type u} [Fintype V]
open scoped Classical
open Finset

def CutExpands (G : SimpleGraph V) (h : ℝ) : Prop :=
  ∀ S : Finset V, 2*S.card ≤ Fintype.card V → h*S.card ≤ (boundaryCount G S : ℝ)

/-- Precisely the cut expansion of the subgraph induced on `U`; the cut stays inside `U`. -/
def CutExpandsOn (G : SimpleGraph V) (U : Finset V) (h : ℝ) : Prop :=
  ∀ T : Finset V, T ⊆ U → 2*T.card ≤ U.card → h*T.card ≤ (cutCount G T (U \ T) : ℝ)

theorem prune_expanding_core {G : SimpleGraph V} {h a : ℝ}
    (hh : 0 < h) (ha : 0 < a) (ha1 : a < 1) (hG : CutExpands G h)
    (F : Finset (Sym2 V))
    (hbudget : (2-a)*(F.card : ℝ) < (1-a)^2*h*(Fintype.card V : ℝ)) :
    ∃ S : Finset V, (S.card : ℝ) ≤ F.card/((1-a)*h) ∧
      CutExpandsOn (G.deleteEdges F) Sᶜ (a*h) := by
  let H := G.deleteEdges (F : Set (Sym2 V))
  let bad : Finset (Finset V) := univ.filter fun S =>
    2*S.card ≤ Fintype.card V ∧ (boundaryCount H S : ℝ) ≤ a*h*S.card
  have hempty : ∅ ∈ bad := by simp [bad, boundaryCount_empty]
  obtain ⟨S, hSbad, hmax⟩ := exists_max_image bad Finset.card ⟨∅, hempty⟩
  have hS : 2*S.card ≤ Fintype.card V ∧
      (boundaryCount H S : ℝ) ≤ a*h*S.card := (mem_filter.mp hSbad).2
  have hSbudget : (1-a)*h*(S.card : ℝ) ≤ F.card := by
    have he := hG S hS.1
    have hd : (boundaryCount G S : ℝ) ≤ F.card + (boundaryCount H S : ℝ) := by
      exact_mod_cast boundary_delete_loss G F S
    nlinarith [hS.2]
  have hden : 0 < (1-a)*h := mul_pos (sub_pos.mpr ha1) hh
  refine ⟨S, (le_div_iff₀ hden).mpr (by nlinarith [hSbudget]), ?_⟩
  intro T hTS hTsmall
  by_contra hT
  have hTcut : (cutCount H T (Sᶜ \ T) : ℝ) < a*h*T.card := lt_of_not_ge hT
  have hTpos : 0 < T.card := by
    by_contra hzero
    have ht0 : T.card = 0 := by omega
    simp only [ht0, Nat.cast_zero, mul_zero] at hTcut
    exact (Nat.cast_nonneg _).not_gt hTcut
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro v hvS hvT
    exact (Finset.mem_compl.mp (hTS hvT)) hvS
  have hUnion : (S ∪ T).card = S.card + T.card := card_union_of_disjoint hST
  have hRest : Sᶜ \ T = (S ∪ T)ᶜ := by
    ext v
    simp only [mem_sdiff, mem_compl, mem_union]
    tauto
  rw [hRest] at hTcut
  have hlarge : Fintype.card V < 2*(S ∪ T).card := by
    by_contra hhsmall
    have hUsmall : 2*(S ∪ T).card ≤ Fintype.card V := by omega
    have hUcut : (boundaryCount H (S ∪ T) : ℝ) ≤ a*h*(S ∪ T).card := by
      have hhcut : (boundaryCount H (S ∪ T) : ℝ) ≤
          (boundaryCount H S : ℝ) + cutCount H T (S ∪ T)ᶜ := by
        exact_mod_cast boundary_union_le H S T
      rw [hUnion, Nat.cast_add]
      nlinarith [hS.2]
    have hUbad : S ∪ T ∈ bad := mem_filter.mpr ⟨mem_univ _, hUsmall, hUcut⟩
    have hm := hmax (S ∪ T) hUbad
    omega
  let R := (S ∪ T)ᶜ
  have hScard : S.card ≤ Fintype.card V := card_le_univ S
  have hUcard : (S ∪ T).card ≤ Fintype.card V := card_le_univ _
  have hSc : Sᶜ.card + S.card = Fintype.card V := by simp
  have hsum : S.card + T.card + R.card = Fintype.card V := by
    dsimp [R]
    rw [card_compl, hUnion]
    omega
  have hRsmall : 2*R.card ≤ Fintype.card V := by omega
  have hTsmallG : 2*T.card ≤ Fintype.card V := by omega
  have htr : 2*(S.card + T.card) ≤ Fintype.card V + S.card := by omega
  have heS := hG S hS.1
  have heT := hG T hTsmallG
  have heR := hG R hRsmall
  have hthree : (boundaryCount G S : ℝ) + boundaryCount G T + boundaryCount G R ≤
      2*(F.card : ℝ) + 2*((boundaryCount H S : ℝ) + cutCount H T R) := by
    exact_mod_cast three_cut_delete_bound G F S T hST
  have hsumR : (S.card : ℝ) + T.card + R.card = Fintype.card V := by exact_mod_cast hsum
  have htrR : 2*((S.card : ℝ) + T.card) ≤ (Fintype.card V : ℝ) + S.card := by
    exact_mod_cast htr
  have hah : 0 ≤ a*h := (mul_pos ha hh).le
  have hprod := mul_le_mul_of_nonneg_left htrR hah
  have hmain : (1-a)*h*(Fintype.card V : ℝ) <
      2*(F.card : ℝ) + a*h*S.card := by
    change (cutCount H T R : ℝ) < a*h*T.card at hTcut
    nlinarith [hS.2]
  have hm := mul_lt_mul_of_pos_left hmain (sub_pos.mpr ha1)
  have hb := mul_le_mul_of_nonneg_left hSbudget ha.le
  nlinarith

theorem prune_expanding_core_ratio {G : SimpleGraph V} {h z : ℝ}
    (hh : 0 < h) (hz : 0 < z) (hz1 : z < 1) (hG : CutExpands G h)
    (F : Finset (Sym2 V))
    (hbudget : (F.card : ℝ) < z^2/(1+z)*h*(Fintype.card V : ℝ)) :
    ∃ S : Finset V, (S.card : ℝ) ≤ F.card/(z*h) ∧
      CutExpandsOn (G.deleteEdges F) Sᶜ ((1-z)*h) := by
  have hb : (2-(1-z))*(F.card : ℝ) <
      (1-(1-z))^2*h*(Fintype.card V : ℝ) := by
    have hd : 0 < 1+z := by linarith
    have hm := mul_lt_mul_of_pos_left hbudget hd
    field_simp at hm
    nlinarith
  simpa only [sub_sub_cancel] using
    prune_expanding_core hh (by linarith : 0 < 1-z) (by linarith : 1-z < 1) hG F hb

end Cycle12
