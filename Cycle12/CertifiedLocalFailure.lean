import Cycle12.CoverGlobalSplitApplication
import Cycle12.FixedRestrictedFailure

namespace Cycle12
open Finset SimpleGraph Cycle13 Real

def RatCutGroup.LocalMatches (g : RatCutGroup) (count : RatCountingCertificate)
    (budgets : Fin g.cells.length → RatMinorityBudgetCertificate) : Prop :=
  g.population.witness.kind=.localCut ∧ g.upper=none ∧ g.lower=g.population.nu ∧ g.cap=1/40 ∧
  g.population.Rlo=g.geometry.Rlo ∧ g.population.Wlo=g.geometry.Wlo ∧
  g.population.witness.zlo=g.geometry.zlo ∧ g.population.witness.qmark=g.geometry.qmark ∧
  count.slope=g.population.slope ∧ count.intercept=g.population.intercept ∧
  count.M=g.geometry.M ∧ count.D=g.geometry.Dlo ∧ count.pl=g.geometry.inputs.pl ∧
  ∀ i, (budgets i).Rlo=g.geometry.Rlo ∧ (budgets i).qmark=g.geometry.qmark ∧
    (budgets i).slope=g.population.slope ∧ (budgets i).intercept=g.population.intercept ∧
    (budgets i).cap=g.population.cap ∧ (budgets i).rho=(g.cells.get i).entropy.rho ∧
    (budgets i).ymax=(g.cells.get i).region.bin.residual.retention.ymax

instance instDecidableRatLocalMatches (g : RatCutGroup) (count : RatCountingCertificate)
    (budgets : Fin g.cells.length → RatMinorityBudgetCertificate) :
    Decidable (g.LocalMatches count budgets) := by
  unfold RatCutGroup.LocalMatches
  infer_instance

noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem certified_local_failure (g : RatCutGroup) (count : RatCountingCertificate)
    (budgets : Fin g.cells.length → RatMinorityBudgetCertificate) (reverse : RatReverseLocalCertificate)
    (hmatch : g.LocalMatches count budgets) (hrg : reverse.geometry=g.geometry) (hrp : reverse.population=g.population)
    (hg : g.NumericValid) (hcs : ∀ c∈g.cells, c.Sound)
    (hce : ∀ c∈g.cells, c.entropy.Valid) (hcpm : ∀ c∈g.cells, c.population=g.population)
    (hpv : g.population.Valid) (hps : g.population.Sound)
    (hwv : g.population.witness.Valid) (hws : g.population.witness.Sound)
    (hcv : count.Valid) (hcount : count.Sound)
    (hbs : ∀ i, (budgets i).Sound) (hrs : reverse.Sound)
    (G : SimpleGraph V) (st : CoverMarkedGraphState g.geometry G)
    (hI : CoverSparseCutIrreducible G) :
    (fixedSizeLaw (univ:Finset V) st.N).prob
      (FixedRestrictedCutFailure G univ st.N st.z g.population.witness.dm g.population.witness.beta (1/125)) ≤
      (2*exp (-(count.aa:ℝ)*st.R)+exp (-(reverse.exponent:ℝ)*st.R)+
        (g.cells.length:ℝ)*(2*exp (-(g.exponent:ℝ)*st.R)))/(g.population.witness.omega:ℝ) := by
  obtain ⟨hkind,hupper,hlower,hcap,hRmatch,hWmatch,hzmatch,hqmatch,hslmatch,himatch,
    hMmatch,hDmatch,hcountpl,hbudgetmatch⟩ := hmatch
  obtain ⟨hinput,hdm,hbeta,hzlo,hq,hL,homega,hK,hdelta,hmean,hmean3,hwbranch⟩ := hwv
  rw [RatWitnessCertificate.BranchValid,hkind] at hwbranch
  obtain ⟨herr,hcmajor,hwbound⟩ := hwbranch
  obtain ⟨_,_,hpopsl,_,hnup,_,hpbranch⟩ := hpv
  rw [RatPopulationCertificate.BranchValid,hkind] at hpbranch
  have hdmR : (0:ℝ) < (g.population.witness.dm:ℝ) := by exact_mod_cast hdm
  have htD : st.t < Fintype.card V := st.mark_lt_sample.trans_le st.sample_le_order
  have htheta : (0:ℝ) < (count.theta:ℝ) := by exact_mod_cast hcv.1
  have hh : 0 < st.z/st.p := div_pos st.z_pos st.fraction_pos
  let ell : ℝ := (count.theta:ℝ)*(count.slope:ℝ)*st.p
  have hscaleEq : ell/(count.theta:ℝ)=(g.population.slope:ℝ)*st.p := by
    dsimp only [ell]
    rw [hslmatch]
    field_simp [htheta.ne']
  have hscale : 0 < ell/(count.theta:ℝ) := by
    rw [hscaleEq]
    exact mul_pos (by exact_mod_cast hpopsl) st.fraction_pos
  have hresle : (st.residual:ℝ) ≤ st.p := by
    rw [st.residual_fraction,st.sample_fraction]
    exact fixed_residual_probability_le_sample _ _ _ st.sample_le_order st.mark_lt_sample
  have hmgf0 := hcount.1 st.p st.residual st.fraction_pos.le
    (by rw [hcountpl]; exact st.fraction_lower) hresle
  have hmgf : 1-((st.N-st.t:ℕ):ℝ)/(Fintype.card V-st.t)+
      ((st.N-st.t:ℕ):ℝ)/(Fintype.card V-st.t)*exp (count.theta:ℝ) ≤ exp ell := by
    simpa only [st.residual_fraction,Nat.cast_sub htD.le,ell] using hmgf0
  have hpopbound := hps st.p st.z st.R st.fraction_pos
    (by rw [hzmatch]; exact st.z_lower) (by rw [hRmatch]; exact st.scale_lower)
    (by rw [hWmatch]; exact st.weight_lower)
  rw [RatPopulationCertificate.BranchBound,hkind] at hpopbound
  have hwactual := hws.2 st.z (by rw [hzmatch]; exact st.z_lower)
  have hwlower := hwactual.2.1
  rw [RatWitnessCertificate.LowerBound,hkind] at hwlower
  have hvote : (g.population.witness.majority.inputs.mean:ℝ) ≤
      ((st.t:ℝ)/st.N)*((g.population.witness.dm:ℝ)*st.z) := by
    have hv := cover_marked_vote_mean g.geometry G st hdmR.le
    rw [← hqmatch] at hv
    have he : (g.population.witness.majority.inputs.mean:ℝ)=
        (g.population.witness.dm:ℝ)*(g.population.witness.qmark:ℝ) := by exact_mod_cast hmean
    rwa [he]
  have hNp : (st.N:ℝ)=st.p*(Fintype.card V:ℝ) := by
    rw [st.sample_fraction]
    exact (div_mul_cancel₀ _ st.order_pos.ne').symm
  have hrev := hrs (Fintype.card V) st.N st.p st.z st.R st.residual st.t st.fraction_pos st.scale_pos
    (by rw [hrg]; exact st.fraction_upper) (by rw [hrg]; exact st.z_lower)
    st.order_identity st.sample_identity (by rw [hrg]; exact st.mark_upper)
    (by rw [hrg]; exact st.residual_lower)
  rw [hrg,hrp] at hrev
  let mean : ℝ := (g.geometry.ps:ℝ)*(st.z/40-st.p*(g.geometry.M:ℝ))*st.R
  let size : ℝ := (Fintype.card V:ℝ)/40
  let nu : ℝ := (g.population.nu:ℝ)*(st.z/st.p)
  let cell := fun i : Fin g.cells.length => g.cells.get i
  let eligible := fun (i : Fin g.cells.length) (T A : Finset V) (xi : V → Finset V) =>
    (cell i).region.interval.Contains (((fixedMajoritySide univ T A xi).card:ℝ)/(st.z/st.p)) ∧
    ((fixedMajoritySide univ T A xi).card:ℝ) < size
  have hcoverage : ∀ T : Finset V, T.card=st.t → ∀ A⊆T, ∀ xi,
      nu ≤ ((fixedMajoritySide univ T A xi).card:ℝ) →
      ((fixedMajoritySide univ T A xi).card:ℝ) < size → ∃ i, eligible i T A xi := by
    intro T _ A _ xi hnu hsize
    have hside : g.interval.Contains (((fixedMajoritySide univ T A xi).card:ℝ)/(st.z/st.p)) := by
      refine ⟨?_,?_⟩
      · change (g.lower:ℝ) ≤ _
        rw [hlower]
        exact (le_div_iff₀ hh).mpr hnu
      · intro r hr
        change g.upper=some r at hr
        rw [hupper] at hr
        contradiction
    obtain ⟨c,hmem,hinterval⟩ := rat_cut_group_covers g hg hside
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hmem
    exact ⟨i,by simpa only [eligible,cell,hi] using And.intro hinterval hsize⟩
  have hvalid (i : Fin g.cells.length) (T : Finset V) (hT : T.card=st.t)
      (A : Finset V) (xi : V → Finset V) (hel : eligible i T A xi) :
      RoundedCutLabelValid G (fixedMajoritySide univ T A xi) T st.residual
        (cell i).region.bin.residual.retention.lambda
        (((cell i).region.bin.residual.kappa:ℝ)*(st.z/st.p)*(fixedMajoritySide univ T A xi).card)
        (cell i).region.bin.tau (2*exp (-((cell i).region.bin.gamma:ℝ)*st.z)) ∧
      ((g.population.witness.beta:ℝ)+(g.population.witness.error:ℝ))*st.z*
        (((ell/(count.theta:ℝ))*(fixedMajoritySide univ T A xi).card+(g.population.intercept:ℝ)*st.z)/
          (1-((g.population.witness.error:ℝ)+2*(g.population.witness.beta:ℝ))/(g.population.witness.dm:ℝ))) ≤
        ((cell i).region.bin.tau:ℝ)*((((cell i).region.bin.residual.kappa:ℝ)*(st.z/st.p)*
          (fixedMajoritySide univ T A xi).card)*(st.residual:ℝ)^2) ∧
      (exp 1-1)*((st.t:ℝ)/st.N)*
        (((ell/(count.theta:ℝ))*(fixedMajoritySide univ T A xi).card+(g.population.intercept:ℝ)*st.z)/
          (1-((g.population.witness.error:ℝ)+2*(g.population.witness.beta:ℝ))/(g.population.witness.dm:ℝ)))+6 ≤
        ((cell i).entropy.rho:ℝ)*st.t := by
    let c := cell i
    let S := fixedMajoritySide univ T A xi
    have hmem : c∈g.cells := List.get_mem _ _
    have hsound := hcs c hmem
    obtain ⟨hRl,hcp,hexp,hcx,hch,hM,hpmax,hDlo,hzlower,hps,_,_⟩ := hg.2.2.2 c hmem
    have hcapS : (S.card:ℝ) ≤ (c.region.cap:ℝ)*Fintype.card V := by
      rw [hcp,hcap]
      have h := hel.2
      change (S.card:ℝ) < (Fintype.card V:ℝ)/40 at h
      norm_num
      linarith only [h]
    have hb := rat_cut_region_side_bounds c.region hsound.1 hh
      (by rw [hRl]; exact st.scale_lower) st.order_identity hel.1 hcapS
    have hcut := hsound.2.1 G S T st.R st.z st.p st.residual st.order_pos st.mass_pos hI
      (by rw [hcx]; exact st.x_lower) (by rw [hch]; exact st.x_upper) st.expansion_identity st.scale_pos.le
      st.fraction_pos (by rw [hpmax]; exact st.fraction_upper) (by rw [hzlower]; exact st.z_lower)
      (by rw [hDlo]; exact st.scale_ratio) (by rw [hps]; exact st.residual_lower)
      (by rw [hT,hM]; exact st.mark_upper) hb.1 hb.2
    have hthreshold := hsound.2.2.1 st.p st.z st.residual S.card st.fraction_pos st.z_pos hb.1
      (by change (c.region.bin.ps:ℝ)*st.p ≤ (st.residual:ℝ); rw [hps]; exact st.residual_lower)
      (by change (c.population.Wlo:ℝ) ≤ st.p*st.z; rw [hcpm c hmem,hWmatch]; exact st.weight_lower)
    rw [RatCutThresholdCertificate.Bound,RatCutCellCertificate.threshold,hcpm c hmem,hkind] at hthreshold
    obtain ⟨hbr,hbq,hbsl,hbi,hbc,hbrho,hby⟩ := hbudgetmatch i
    have hlabels := hbs i (Fintype.card V) st.N st.p st.z st.R st.t S.card
      (((g.population.witness.error:ℝ)+2*(g.population.witness.beta:ℝ))/(g.population.witness.dm:ℝ))
      st.order_pos st.fraction_pos st.z_pos (by rw [hbr]; exact st.scale_lower)
      (by rw [hbq]; exact st.mark_lower) (Nat.cast_nonneg _) (by rw [hby]; exact hb.2)
      hNp st.sample_identity (by rw [hbc]; exact_mod_cast hpbranch.1)
    rw [hbsl,hbi,hbrho] at hlabels
    exact ⟨hcut,by simpa only [hscaleEq] using hthreshold,by simpa only [hscaleEq] using hlabels⟩
  have hfrac : ((g.population.witness.error:ℝ)+2*(g.population.witness.beta:ℝ))/(g.population.witness.dm:ℝ) < 1 := by
    exact_mod_cast hpbranch.1.trans_lt hpbranch.2.1
  have hbe : (0:ℝ) ≤ (g.population.witness.beta:ℝ)+(g.population.witness.error:ℝ) := by
    have hb : (0:ℝ) < (g.population.witness.beta:ℝ) := by exact_mod_cast hbeta
    have he : (0:ℝ) < (g.population.witness.error:ℝ) := by exact_mod_cast herr
    linarith only [hb,he]
  have hbound := fixed_restricted_failure_bound (I:=Fin g.cells.length) G st.sample_le_order st.mark_lt_sample.le htD
    (z:=st.z) (dm:=(g.population.witness.dm:ℝ)) (beta:=(g.population.witness.beta:ℝ))
    (err:=(g.population.witness.error:ℝ)) (eta:=1/125) (q:=6) (theta:=(count.theta:ℝ)) (ell:=ell)
    (intercept:=(g.population.intercept:ℝ)*st.z) (nu:=nu) (size:=size) (reverseMean:=mean) (reverseFraction:=1/2)
    st.z_pos hbe hfrac htheta hscale (by simpa only [nu,hscaleEq,mul_div_assoc] using hpopbound)
    hmgf hrev.1 (by norm_num) (by norm_num)
    (by simpa only [size,st.residual_fraction] using hrev.2.1) hrev.2.2.1
    st.residual st.residual_pos st.residual_half st.residual_mean
    (voteLambda:=(g.population.witness.majority.inputs.mean:ℝ))
    (K:=(g.population.witness.majority.bound:ℝ)) (omega:=(g.population.witness.omega:ℝ))
    hdmR (by exact_mod_cast herr) hwactual.1 (by exact_mod_cast hmean3) hvote (by exact_mod_cast hK)
    (fun r hr0 hr1 => by simpa only [hcmajor,Rat.cast_one] using (hwactual.2.2 r hr0 hr1).1)
    (fun r hr0 hr1 => by simpa only [hcmajor,Rat.cast_one] using (hwactual.2.2 r hr0 hr1).2)
    hws.1 hwlower
    (fun i _ _ _ => (cell i).region.bin.residual.retention.lambda)
    (fun i T A xi => ((cell i).region.bin.residual.kappa:ℝ)*(st.z/st.p)*(fixedMajoritySide univ T A xi).card)
    (fun i _ _ _ => (cell i).region.bin.tau) eligible
    (fun i => (cell i).entropy.rho) (fun i => 2*exp (-((cell i).region.bin.gamma:ℝ)*st.z))
    (fun i => by exact_mod_cast (hce (cell i) (List.get_mem _ _)).1) (fun _ => by positivity)
    hcoverage (fun i T hT A _ xi hel => hvalid i T hT A xi hel)
  have hcoun := hcount.2 (R:=st.R) (z:=st.z) (p:=st.p) (t:=st.t) st.scale_pos
    (by rw [hDmatch]; exact st.scale_ratio) (by rw [hcountpl]; exact st.fraction_lower)
    (by rw [hMmatch]; exact st.mark_upper)
  rw [himatch] at hcoun
  have hsum : (∑ i : Fin g.cells.length,
      exp ((st.t:ℝ)*cappedLabelEntropy ((cell i).entropy.rho:ℝ))*
        (2*exp (-((cell i).region.bin.gamma:ℝ)*st.z))) ≤
      (g.cells.length:ℝ)*(2*exp (-(g.exponent:ℝ)*st.R)) := by
    calc
      _ ≤ ∑ _i : Fin g.cells.length, 2*exp (-(g.exponent:ℝ)*st.R) := by
        apply Finset.sum_le_sum
        intro i _
        have hmem : cell i∈g.cells := List.get_mem _ _
        obtain ⟨_,_,hexp,_,_,hM,_,hD,_,_,_,_⟩ := hg.2.2.2 (cell i) hmem
        have hb := (hcs (cell i) hmem).2.2.2 st.R st.z st.t st.scale_pos.le
          (by change (((cell i).region.bin.residual.Dlo:ℝ)*st.R ≤ st.z); rw [hD]; exact st.scale_ratio)
          (by change ((st.t:ℝ) ≤ ((cell i).region.bin.residual.M:ℝ)*st.R); rw [hM]; exact st.mark_upper)
        change _ ≤ 2*exp (-((cell i).exponent:ℝ)*st.R) at hb
        rwa [hexp] at hb
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  apply hbound.trans
  apply div_le_div_of_nonneg_right _ hws.1.le
  exact add_le_add (add_le_add (by simpa only [ell] using hcoun) hrev.2.2.2) hsum

end
end Cycle12
