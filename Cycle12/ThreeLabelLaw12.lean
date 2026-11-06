import Cycle12.Foundations.FiniteProductLaw
import Cycle12.Foundations.FiniteBernoulli

namespace Cycle12
open Cycle13 Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem finiteLaw_ext {Ω : Type} [Fintype Ω] {μ ν : FiniteLaw Ω}
    (h : μ.mass = ν.mass) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

def pushLaw {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    (μ : FiniteLaw Ω) (f : Ω → Ξ) : FiniteLaw Ξ where
  mass ξ := μ.prob (fun ω => f ω = ξ)
  nonneg ξ := μ.prob_nonneg _
  total := by
    unfold FiniteLaw.prob
    rw [← FiniteLaw.expect_sum]
    simp

theorem pushLaw_expect {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    (μ : FiniteLaw Ω) (f : Ω → Ξ) (g : Ξ → ℝ) :
    (pushLaw μ f).expect g = μ.expect (fun ω => g (f ω)) := by
  unfold FiniteLaw.expect pushLaw FiniteLaw.prob FiniteLaw.expect
  simp only [sum_mul,mul_assoc]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  simp [ite_mul,mul_ite]

theorem pushLaw_prob {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    (μ : FiniteLaw Ω) (f : Ω → Ξ) (E : Ξ → Prop) :
    (pushLaw μ f).prob E = μ.prob (fun ω => E (f ω)) :=
  pushLaw_expect μ f _

def threeLabelLaw (p : unitInterval) (hp : 3*(p:ℝ) ≤ 1) : FiniteLaw (Fin 4) where
  mass j := if j = 3 then 1-3*(p:ℝ) else (p:ℝ)
  nonneg j := by split_ifs <;> linarith only [hp,p.2.1]
  total := by norm_num [Fin.sum_univ_succ]; ring

theorem threeLabelLaw_marginal (p : unitInterval) (hp : 3*(p:ℝ) ≤ 1) (i : Fin 3) :
    (threeLabelLaw p hp).prob (fun j => j = i.castSucc) = (p:ℝ) ∧
    (threeLabelLaw p hp).prob (fun j => j ≠ i.castSucc) = 1-(p:ℝ) := by
  fin_cases i <;> norm_num [FiniteLaw.prob,FiniteLaw.expect,threeLabelLaw,Fin.sum_univ_succ] <;> ring

variable {V : Type} [Fintype V] [DecidableEq V]

def threeLabelSample (ω : V → Fin 4) (i : Fin 3) : Finset V :=
  univ.filter (fun v => ω v = i.castSucc)

theorem threeLabelSample_disjoint (ω : V → Fin 4) :
    Pairwise (fun i j => Disjoint (threeLabelSample ω i) (threeLabelSample ω j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  apply hij
  apply Fin.castSucc_injective
  exact ((mem_filter.mp hvi).2).symm.trans (mem_filter.mp hvj).2

theorem threeLabelSample_law (p : unitInterval) (hp : 3*(p:ℝ) ≤ 1) (i : Fin 3) :
    pushLaw (FiniteLaw.independent (fun _v : V => threeLabelLaw p hp))
      (fun ω => threeLabelSample ω i) = bernoulliSubset p := by
  apply finiteLaw_ext
  funext S
  change (FiniteLaw.independent (fun _v : V => threeLabelLaw p hp)).prob
    (fun ω => threeLabelSample ω i = S) = (p:ℝ)^S.card*(1-(p:ℝ))^(Fintype.card V-S.card)
  have he : ∀ ω : V → Fin 4, (@ite ℝ (threeLabelSample ω i = S) (Classical.propDecidable _) 1 0) =
      ∏ v, if (ω v = i.castSucc ↔ v ∈ S) then (1:ℝ) else 0 := by
    intro ω
    rw [Fintype.prod_boole]
    congr 1
    apply propext
    constructor
    · intro h v
      have hh := congrArg (fun T : Finset V => v ∈ T) h
      simpa [threeLabelSample] using (Iff.of_eq hh)
    · intro h
      ext v
      simpa [threeLabelSample] using h v
  unfold FiniteLaw.prob
  rw [show (fun ω => @ite ℝ (threeLabelSample ω i = S) (Classical.propDecidable _) 1 0) =
      (fun ω => ∏ v, if (ω v = i.castSucc ↔ v ∈ S) then (1:ℝ) else 0) from funext he]
  rw [FiniteLaw.independent_expect_product (fun _v : V => threeLabelLaw p hp)
    (fun v j => if (j = i.castSucc ↔ v ∈ S) then (1:ℝ) else 0)]
  have hlocal : ∀ v, (threeLabelLaw p hp).expect (fun j =>
      if (j = i.castSucc ↔ v ∈ S) then (1:ℝ) else 0) =
      if v ∈ S then (p:ℝ) else 1-(p:ℝ) := by
    intro v
    fin_cases i <;> by_cases hv : v ∈ S <;>
      simp [hv,FiniteLaw.expect,threeLabelLaw,Fin.sum_univ_succ] <;> ring
  simp_rw [hlocal]
  rw [prod_ite]
  simp only [filter_mem_eq_inter,univ_inter,prod_const]
  have hcomp : (univ.filter (fun v => v ∉ S)).card = Fintype.card V-S.card := by
    have he : univ.filter (fun v => v ∉ S) = Sᶜ := by ext v; simp
    rw [he,card_compl]
  rw [hcomp]

theorem threeLabelSample_probability (p : unitInterval) (hp : 3*(p:ℝ) ≤ 1)
    (i : Fin 3) (E : Finset V → Prop) :
    (FiniteLaw.independent (fun _v : V => threeLabelLaw p hp)).prob
      (fun ω => E (threeLabelSample ω i)) = (bernoulliSubset p).prob E := by
  rw [← pushLaw_prob,threeLabelSample_law]

/-- Three marginal failure estimates give simultaneous disjoint samples;
no independence between the three good-sample events is assumed. -/
theorem exists_three_disjoint_samples (p : unitInterval) (hp : 3*(p:ℝ) ≤ 1)
    (good : Fin 3 → Finset V → Prop)
    (hbad : ∀ i, (bernoulliSubset p).prob (fun U => ¬good i U) ≤ 1/32) :
    ∃ U : Fin 3 → Finset V, Pairwise (fun i j => Disjoint (U i) (U j)) ∧ ∀ i, good i (U i) := by
  let μ := FiniteLaw.independent (fun _v : V => threeLabelLaw p hp)
  have hb := μ.prob_exists_le_sum (fun i ω => ¬good i (threeLabelSample ω i))
  have hsum : (∑ i : Fin 3, μ.prob (fun ω => ¬good i (threeLabelSample ω i))) ≤ 3/32 := by
    calc
      _ ≤ ∑ _i : Fin 3, (1/32:ℝ) := sum_le_sum (fun i _ => by
        dsimp only [μ]
        rw [threeLabelSample_probability p hp i (fun U => ¬good i U)]
        exact hbad i)
      _ = _ := by norm_num
  have hex : ∃ ω : V → Fin 4, ∀ i, good i (threeLabelSample ω i) := by
    by_contra! h
    have he : (fun ω => ∃ i, ¬good i (threeLabelSample ω i)) = fun _ => True := by
      funext ω
      exact propext ⟨fun _ => trivial,fun _ => h ω⟩
    rw [he] at hb
    simp only [FiniteLaw.prob,ite_true,FiniteLaw.expect_const] at hb
    change 1 ≤ ∑ i : Fin 3, μ.prob (fun ω => ¬good i (threeLabelSample ω i)) at hb
    linarith only [hb,hsum]
  obtain ⟨ω,hω⟩ := hex
  exact ⟨threeLabelSample ω,threeLabelSample_disjoint ω,hω⟩

end
end Cycle12
