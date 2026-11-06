import Cycle12.Foundations.LiftingGraph

/-! Balancing a prescribed set of vertices while fixing one marked vertex
of every color. Bichromatic components contain at most two marked vertices. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {W C : Type} [Fintype W] [Fintype C] [DecidableEq W] [DecidableEq C]

def markedColorSize (f : W → C) (M : Finset W) (a : C) : ℕ :=
  (M.filter (fun v => f v=a)).card
def markedRegionSize (f : W → C) (M : Finset W) (S : Set W) (a : C) : ℕ :=
  (M.filter (fun v => v∈S ∧ f v=a)).card
def markedEnergy (f : W → C) (M : Finset W) : ℕ :=
  ∑ a, (markedColorSize f M a)^2

lemma marked_partition (f : W → C) (M : Finset W) (S : Set W) (a : C) :
    markedColorSize f M a=markedRegionSize f M S a+markedRegionSize f M Sᶜ a := by
  have h := card_filter_add_card_filter_not (s:=M.filter (fun v => f v=a)) (fun v => v∈S)
  simpa only [filter_filter,Set.mem_compl_iff,and_comm,markedColorSize,markedRegionSize] using h.symm

lemma marked_switch_counts (f : W → C) (M : Finset W) (S : Set W) (a b x : C) :
    markedColorSize (switchColors f a b S) M x+markedRegionSize f M S x=
      markedColorSize f M x+markedRegionSize f M S (Equiv.swap a b x) := by
  have hin : markedRegionSize (switchColors f a b S) M S x=
      markedRegionSize f M S (Equiv.swap a b x) := by
    unfold markedRegionSize
    congr 1
    ext v
    simp only [mem_filter]
    by_cases hv : v∈S <;> simp [switchColors,hv,Equiv.swap_apply_eq_iff]
  have hout : markedRegionSize (switchColors f a b S) M Sᶜ x=
      markedRegionSize f M Sᶜ x := by
    unfold markedRegionSize
    congr 1
    ext v
    simp only [mem_filter]
    by_cases hv : v∈S <;> simp [switchColors,hv]
  rw [marked_partition (switchColors f a b S) M S,marked_partition f M S,hin,hout]
  omega

lemma sum_marked_component_sizes (H : SimpleGraph W) (f : W → C) (M : Finset W) (a : C) :
    ∑ c : H.ConnectedComponent, markedRegionSize f M c.supp a=markedColorSize f M a := by
  have h := card_eq_sum_card_fiberwise (f:=H.connectedComponentMk)
    (s:=M.filter (fun v => f v=a)) (t:=univ) (fun _ _ => mem_univ _)
  unfold markedColorSize
  rw [h]
  apply sum_congr rfl
  intro c _
  unfold markedRegionSize
  congr 1
  ext v
  simp only [mem_filter]
  change (v∈M ∧ H.connectedComponentMk v=c ∧ f v=a) ↔
    ((v∈M ∧ f v=a) ∧ H.connectedComponentMk v=c)
  tauto

lemma marked_two_colors_le (f : W → C) (M : Finset W) (S : Set W) (a b : C) (hab : a≠b) :
    markedRegionSize f M S a+markedRegionSize f M S b ≤ (M.filter (fun v => v∈S)).card := by
  have hd : Disjoint (M.filter (fun v => v∈S ∧ f v=a)) (M.filter (fun v => v∈S ∧ f v=b)) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact hab ((mem_filter.mp hv).2.2.symm.trans (mem_filter.mp hw).2.2)
  unfold markedRegionSize
  rw [← card_union_of_disjoint hd]
  apply card_le_card
  intro v hv
  rcases mem_union.mp hv with hv | hv <;> exact mem_filter.mpr ⟨(mem_filter.mp hv).1,(mem_filter.mp hv).2.1⟩

theorem component_marked_le_two (H : SimpleGraph W) (M : Finset W)
    (hd : ∀ v, H.degree v ≤ 2) (hm : ∀ v∈M, H.degree v ≤ 1)
    (c : H.ConnectedComponent) : (M.filter (fun v => v∈c.supp)).card ≤ 2 := by
  let N := (univ : Finset c).filter (fun v => v.val∈M)
  have hc : N.card=(M.filter (fun v => v∈c.supp)).card := by
    apply card_bij (fun v _ => v.val)
    · intro v hv
      exact mem_filter.mpr ⟨(mem_filter.mp hv).2,v.property⟩
    · intro v hv w hw he
      exact Subtype.ext he
    · intro v hv
      exact ⟨⟨v,(mem_filter.mp hv).2⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).1⟩,rfl⟩
  rw [← hc]
  apply connected_marked_le_two c.toSimpleGraph c.connected_toSimpleGraph N
  · intro v
    rw [component_degree_eq]
    exact hd v.val
  · intro v hv
    rw [component_degree_eq]
    exact hm v.val (mem_filter.mp hv).2

theorem exists_marked_balanced_coloring (H : SimpleGraph W) (M : Finset W)
    (seed : C → W) (hseed : ∀ a, seed a∈M)
    (f₀ : H.Coloring C) (hfixed₀ : ∀ a, f₀ (seed a)=a)
    (hcomponents : ∀ (f : H.Coloring C) (a b : C), a≠b →
      ∀ c : (twoColorGraph H f a b).ConnectedComponent,
        (M.filter (fun v => v∈c.supp)).card ≤ 2) :
    ∃ f : H.Coloring C, (∀ a, f (seed a)=a) ∧
      ∀ a b, markedColorSize f M a ≤ markedColorSize f M b+2 := by
  have hex : ∃ n : ℕ, ∃ f : H.Coloring C, (∀ a, f (seed a)=a) ∧ markedEnergy f M=n :=
    ⟨markedEnergy f₀ M,f₀,hfixed₀,rfl⟩
  obtain ⟨f,hfixed,henergy⟩ := Nat.find_spec hex
  have hmin : ∀ g : H.Coloring C, (∀ a, g (seed a)=a) → markedEnergy f M ≤ markedEnergy g M := by
    intro g hg
    rw [henergy]
    exact Nat.find_min' hex ⟨g,hg,rfl⟩
  refine ⟨f,hfixed,?_⟩
  intro a b
  by_contra! hgap
  have hab : a≠b := by intro h; subst b; omega
  let T := twoColorGraph H f a b
  let c₀ := T.connectedComponentMk (seed a)
  have hpositive : ∃ c : T.ConnectedComponent, c≠c₀ ∧
      markedRegionSize f M c.supp b < markedRegionSize f M c.supp a := by
    by_contra h
    push Not at h
    have hpoint : ∀ c : T.ConnectedComponent,
        markedRegionSize f M c.supp a ≤ markedRegionSize f M c.supp b+(if c=c₀ then 2 else 0) := by
      intro c
      by_cases he : c=c₀
      · have hlim := hcomponents f a b hab c
        have hh := marked_two_colors_le f M c.supp a b hab
        simp only [← Set.ncard_coe_finset,coe_filter] at hh hlim
        simp only [if_pos he]
        omega
      · simpa only [if_neg he,add_zero] using h c he
    have hh := sum_le_sum (fun c (_ : c∈(univ : Finset T.ConnectedComponent)) => hpoint c)
    rw [sum_add_distrib,sum_marked_component_sizes,sum_marked_component_sizes] at hh
    simp only [sum_ite_eq',mem_univ,ite_true] at hh
    omega
  obtain ⟨c,hc₀,hpos⟩ := hpositive
  have hsmall : markedRegionSize f M c.supp a+markedRegionSize f M c.supp b ≤ 2 := by
    have hlim := hcomponents f a b hab c
    have hh := marked_two_colors_le f M c.supp a b hab
    simp only [← Set.ncard_coe_finset,coe_filter] at hh hlim
    exact hh.trans hlim
  have hbzero : markedRegionSize f M c.supp b=0 := by omega
  have haone : markedRegionSize f M c.supp a=1 ∨ markedRegionSize f M c.supp a=2 := by omega
  have hsa : seed a∉c.supp := by
    intro h
    exact hc₀ (by change T.connectedComponentMk (seed a)=c at h; exact h.symm)
  have hsb : seed b∉c.supp := by
    intro h
    have hp : 0 < markedRegionSize f M c.supp b := by
      simp only [markedRegionSize,← Set.ncard_coe_finset,coe_filter]
      rw [Set.ncard_pos]
      exact ⟨seed b,hseed b,h,hfixed b⟩
    omega
  let g := switchComponent H f a b c
  have hgfixed : ∀ x, g (seed x)=x := by
    intro x
    change switchColors f a b c.supp (seed x)=x
    by_cases hx : seed x∈c.supp
    · have hxa : x≠a := by intro h; subst x; exact hsa hx
      have hxb : x≠b := by intro h; subst x; exact hsb hx
      simp only [switchColors,if_pos hx,hfixed,Equiv.swap_apply_of_ne_of_ne hxa hxb]
    · simp only [switchColors,if_neg hx,hfixed]
  have hga : markedColorSize g M a+markedRegionSize f M c.supp a=markedColorSize f M a := by
    have h := marked_switch_counts f M c.supp a b a
    rw [Equiv.swap_apply_left,hbzero,add_zero] at h
    exact h
  have hgb : markedColorSize g M b=markedColorSize f M b+markedRegionSize f M c.supp a := by
    have h := marked_switch_counts f M c.supp a b b
    rw [Equiv.swap_apply_right,hbzero,add_zero] at h
    exact h
  have hother : ∀ x, x≠a → x≠b → markedColorSize g M x=markedColorSize f M x := by
    intro x hxa hxb
    have h := marked_switch_counts f M c.supp a b x
    rw [Equiv.swap_apply_of_ne_of_ne hxa hxb] at h
    exact Nat.add_right_cancel h
  have hless : markedEnergy g M < markedEnergy f M := by
    unfold markedEnergy
    rw [sum_split_two _ hab,sum_split_two _ hab]
    have hrest : (∑ x∈(univ.erase a).erase b, (markedColorSize g M x)^2)=
        ∑ x∈(univ.erase a).erase b, (markedColorSize f M x)^2 := by
      apply sum_congr rfl
      intro x hx
      rw [hother x (mem_erase.mp (mem_erase.mp hx).2).1 (mem_erase.mp hx).1]
    rw [hrest]
    rcases haone with ha | ha <;> rw [ha] at hga hgb <;> nlinarith
  exact (not_lt_of_ge (hmin g hgfixed)) hless

end
end Cycle13
