import ARA.Helpers.MultiGraph

/-! Cut counting by contraction. Sets and their complements are counted
separately; the two trivial cuts are included in the finite family. -/
namespace Cycle13
open Finset ARA ARA.MultiGraph
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type} [DecidableEq V]

def smallCuts (g : MultiGraph V) (K : ℕ) : Finset (Finset V) :=
  g.verts.powerset.filter (fun S => g.cutValue S ≤ K)

lemma mem_smallCuts (g : MultiGraph V) (K : ℕ) (S : Finset V) :
    S ∈ smallCuts g K ↔ S ⊆ g.verts ∧ g.cutValue S ≤ K := by
  simp [smallCuts]

lemma noncrossing_membership {e : Sym2 V} {S : Finset V}
    (hnc : ¬Crossing S e) {x y : V} (hx : x ∈ e) (hy : y ∈ e) :
    x ∈ S ↔ y ∈ S := by
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ∈ S ↔ b ∈ S := by simpa using hnc
    rcases Sym2.mem_iff.mp hx with rfl | rfl <;>
      rcases Sym2.mem_iff.mp hy with rfl | rfl <;> simp_all

lemma contract_image_membership {e : Sym2 V} {w : V} (hw : w ∈ e)
    {S : Finset V} (hnc : ¬Crossing S e) (x : V) :
    redirectTo e w x ∈ S.image (redirectTo e w) ↔ x ∈ S := by
  refine ⟨?_, fun hx => mem_image.mpr ⟨x,hx,rfl⟩⟩
  rintro hx
  obtain ⟨y,hy,hyx⟩ := mem_image.mp hx
  by_cases hxe : x ∈ e <;> by_cases hye : y ∈ e
  · exact (noncrossing_membership hnc hye hxe).mp hy
  · have h : y=w := by simpa [redirectTo,hye,hxe] using hyx
    exact False.elim (hye (h ▸ hw))
  · have h : w=x := by simpa [redirectTo,hye,hxe] using hyx
    exact False.elim (hxe (h ▸ hw))
  · have h : y=x := by simpa [redirectTo,hye,hxe] using hyx
    exact h ▸ hy

lemma surviving_smallCuts_bound (g : MultiGraph V) (hwf : g.WF) (K : ℕ)
    (e : Sym2 V) (w : V) (hw : w ∈ e) :
    ((smallCuts g K).filter (fun S => ¬Crossing S e)).card ≤
      (smallCuts (g.contractEdgeTo e w) K).card := by
  apply card_le_card_of_injOn (fun S => S.image (redirectTo e w))
  · intro S hS
    obtain ⟨hS,hnc⟩ := mem_filter.mp hS
    obtain ⟨hsub,hval⟩ := (mem_smallCuts g K S).mp hS
    apply (mem_smallCuts _ _ _).mpr
    refine ⟨?_,?_⟩
    · rintro x hx
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
      by_cases hye : y ∈ e
      · simp [redirectTo,hye]
      · simp [redirectTo,hye,hsub hy]
    · rw [cutValue_contractEdgeTo_of_pointwise hwf
        (fun x _ => contract_image_membership hw hnc x)]
      exact hval
  · intro S hS T hT heq
    change S.image (redirectTo e w)=T.image (redirectTo e w) at heq
    ext x
    rw [← contract_image_membership hw (mem_filter.mp hS).2 x,
      ← contract_image_membership hw (mem_filter.mp hT).2 x,heq]

lemma list_countP_eq_sum {A : Type} (l : List A) (P : A → Prop) [DecidablePred P] :
    l.countP (fun x => decide (P x)) =
      ∑ i : Fin l.length, if P l[i.val] then 1 else 0 := by
  rw [Fin.sum_univ_fun_getElem l (fun x => if P x then (1:ℕ) else 0)]
  induction l with
  | nil => simp
  | cons a l ih => simp [List.countP_cons,ih,add_comm]

theorem survival_count_identity (g : MultiGraph V) (C : Finset (Finset V)) :
    (∑ i : Fin g.edges.length, (C.filter (fun S => ¬Crossing S g.edges[i.val])).card) +
      (∑ S ∈ C, g.cutValue S) = g.edges.length*C.card := by
  have hcross : (∑ S ∈ C, g.cutValue S) =
      ∑ i : Fin g.edges.length, (C.filter (fun S => Crossing S g.edges[i.val])).card := by
    simp_rw [cutValue,list_countP_eq_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    simp
  rw [hcross,← sum_add_distrib]
  have hpair : ∀ i : Fin g.edges.length,
      (C.filter (fun S => ¬Crossing S g.edges[i.val])).card+
      (C.filter (fun S => Crossing S g.edges[i.val])).card=C.card := by
    intro i
    simpa [add_comm] using card_filter_add_card_filter_not (s:=C)
      (fun S => Crossing S g.edges[i.val])
  simp_rw [hpair]
  simp

lemma contraction_count_arithmetic {n d K l m C B : ℕ}
    (hl : 0 < l) (hK : 2*K ≤ d*l) (hn : d<n) (hhand : n*l ≤ 2*m)
    (hcount : m*C ≤ m*B+K*C) : (n-d)*C ≤ n*B := by
  by_cases hCB : C ≤ B
  · exact (Nat.mul_le_mul_right C (Nat.sub_le _ _)).trans (Nat.mul_le_mul_left n hCB)
  have hBC : B ≤ C := by omega
  have hsub := Nat.sub_add_cancel hBC
  have hm : m*(C-B) ≤ K*C := by nlinarith
  have hhand' := Nat.mul_le_mul_right (C-B) hhand
  have hmul : l*(n*(C-B)) ≤ l*(d*C) := by
    nlinarith [Nat.mul_le_mul_right C hK]
  have hrec : n*(C-B) ≤ d*C := (mul_le_mul_iff_right₀ hl).mp (by simpa [mul_comm] using hmul)
  have hnsub := Nat.sub_add_cancel (show d≤n by omega)
  nlinarith

theorem smallCuts_contraction_step (g : MultiGraph V) (hwf : g.WF)
    {d K l B : ℕ} (hd : 2 ≤ d) (hl : 0 < l) (hK : 2*K ≤ d*l)
    (hmin : l ≤ g.minCutValue) (hn : d<g.verts.card)
    (hB : ∀ e ∈ g.edges,
      (smallCuts (g.contractEdgeTo e e.out.1) (K)).card ≤ B) :
    (g.verts.card-d)*(smallCuts g (K)).card ≤ g.verts.card*B := by
  have hhand : g.verts.card*l ≤ 2*g.edges.length :=
    (Nat.mul_le_mul_left _ hmin).trans (card_mul_minCutValue_le g hwf (by omega))
  have hsurv : (∑ i : Fin g.edges.length,
      ((smallCuts g (K)).filter (fun S => ¬Crossing S g.edges[i.val])).card) ≤
      g.edges.length*B := by
    calc
      _ ≤ ∑ _i : Fin g.edges.length, B := by
        apply sum_le_sum
        intro i _
        exact (surviving_smallCuts_bound g hwf (K) _ _ (Sym2.out_fst_mem _)).trans
          (hB _ (List.getElem_mem _))
      _ = _ := by simp
  have hcross : (∑ S ∈ smallCuts g (K), g.cutValue S) ≤
      K*(smallCuts g (K)).card := by
    calc
      _ ≤ ∑ _S ∈ smallCuts g (K), K :=
        sum_le_sum (fun S hS => ((mem_smallCuts g _ S).mp hS).2)
      _ = _ := by simp [mul_comm]
  have hid := survival_count_identity g (smallCuts g (K))
  apply contraction_count_arithmetic hl hK hn hhand
  omega

theorem smallCuts_binomial_bound (g : MultiGraph V) (hwf : g.WF)
    {d K l : ℕ} (hd : 2 ≤ d) (hl : 0 < l) (hK : 2*K ≤ d*l) (hmin : l ≤ g.minCutValue)
    (hn : d ≤ g.verts.card) :
    (smallCuts g (K)).card ≤ 2^(d)*g.verts.card.choose (d) := by
  have main : ∀ n, ∀ g : MultiGraph V, g.verts.card=n → g.WF →
      l ≤ g.minCutValue → d ≤ n →
      (smallCuts g (K)).card ≤ 2^(d)*n.choose (d) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro g hcard hwf hmin hn
      by_cases heq : n=d
      · have hsmall : (smallCuts g (K)).card ≤ 2^n := by
          calc
            _ ≤ g.verts.powerset.card := card_le_card (filter_subset _ _)
            _ = _ := by simp [hcard]
        simpa [heq] using hsmall
      have hlt : d<n := by omega
      have hstep : (n-d)*(smallCuts g (K)).card ≤
          n*(2^(d)*(n-1).choose (d)) := by
        rw [← hcard] at hlt ⊢
        apply smallCuts_contraction_step g hwf hd hl hK hmin hlt
        intro e he
        have hfresh : e.out.1 ∉ g.verts.filter (· ∉ e) := by simp [Sym2.out_fst_mem]
        have hcontract := card_verts_contractEdgeTo hfresh (hwf.incidence e he) (hwf.loopless e he)
        have hc : (g.contractEdgeTo e e.out.1).verts.card=n-1 := by omega
        rw [hcard]
        apply ih (n-1) (by omega) _ hc hwf.contractEdgeTo
        · exact hmin.trans (minCutValue_le_contractEdgeTo hwf hfresh
            (hwf.incidence e he) (hwf.loopless e he) (by omega))
        · omega
      have hchoose := Nat.choose_mul_succ_eq (n-1) (d)
      rw [Nat.sub_add_cancel (show 1≤n by omega)] at hchoose
      have hscale : n*(2^(d)*(n-1).choose (d)) =
          (n-d)*(2^(d)*n.choose (d)) := by
        calc
          _ = 2^(d)*((n-1).choose (d)*n) := by ring
          _ = _ := by rw [hchoose]; ring
      rw [hscale] at hstep
      exact (mul_le_mul_iff_right₀ (show 0<n-d by omega)).mp (by simpa [mul_comm] using hstep)
  exact main _ g rfl hwf hmin hn

theorem smallCuts_polynomial_bound (g : MultiGraph V) (hwf : g.WF)
    {d K l : ℕ} (hd : 2 ≤ d) (hl : 0 < l) (hK : 2*K ≤ d*l) (hmin : l ≤ g.minCutValue)
    (hn : 2 ≤ g.verts.card) :
    (smallCuts g (K)).card ≤ 2*g.verts.card^(d) := by
  by_cases hnk : d ≤ g.verts.card
  · have hfac : 2^(d) ≤ 2*(d).factorial := by
      have h := @Nat.factorial_mul_pow_le_factorial 1 (d-1)
      have he : 1+(d-1)=d := by omega
      norm_num only [Nat.factorial_one,one_mul,he,Nat.reduceAdd] at h
      have hp : 2^(d)=2*2^(d-1) := by
        rw [← pow_succ',Nat.sub_add_cancel (show 1≤d by omega)]
      rw [hp]
      omega
    calc
      _ ≤ 2^(d)*g.verts.card.choose (d) := smallCuts_binomial_bound g hwf hd hl hK hmin hnk
      _ ≤ (2*(d).factorial)*g.verts.card.choose (d) := Nat.mul_le_mul_right _ hfac
      _ = 2*g.verts.card.descFactorial (d) := by rw [Nat.descFactorial_eq_factorial_mul_choose]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _)
  · have hsmall : (smallCuts g (K)).card ≤ 2^g.verts.card := by
      calc
        _ ≤ g.verts.powerset.card := card_le_card (filter_subset _ _)
        _ = _ := by simp
    apply hsmall.trans
    calc
      _ ≤ g.verts.card^g.verts.card := Nat.pow_le_pow_left hn _
      _ ≤ g.verts.card^(d) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ _ := by omega

end
end Cycle13
