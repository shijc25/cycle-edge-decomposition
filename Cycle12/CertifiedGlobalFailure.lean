import Cycle12.CoverGlobalSplitApplication
import Cycle12.FixedCappedGlobalFailure

namespace Cycle12
open Finset SimpleGraph Cycle13 Real

def RatCutGroup.GlobalMatches (small large : RatCutGroup) (count : RatCountingCertificate)
    (labels : RatLabelEntropyCertificate) (minority : RatMinorityBudgetCertificate) : Prop :=
  small.population.witness.kind=.globalCut ∧ small.upper=some large.lower ∧ large.upper=none ∧
  small.lower=small.population.nu ∧ small.cap=1/2 ∧ large.cap=1/2 ∧
  small.entropyBound=some labels.bound ∧ large.entropyBound=some ratCoverLogTwoBudget ∧
  small.population.Rlo=small.geometry.Rlo ∧ small.population.Wlo=small.geometry.Wlo ∧
  small.population.witness.zlo=small.geometry.zlo ∧ small.population.witness.qmark=small.geometry.qmark ∧
  count.slope=small.population.slope ∧ count.intercept=small.population.intercept ∧
  count.M=small.geometry.M ∧ count.D=small.geometry.Dlo ∧ count.pl=small.geometry.inputs.pl ∧
  minority.Rlo=small.geometry.Rlo ∧ minority.qmark=small.geometry.qmark ∧
  minority.slope=small.population.slope ∧ minority.intercept=small.population.intercept ∧
  minority.cap=small.population.cap ∧ minority.rho=labels.rho ∧
  min (large.lower/small.geometry.Rlo) (1/2) ≤ minority.ymax

instance instDecidableRatGlobalMatches (small large : RatCutGroup) (count : RatCountingCertificate)
    (labels : RatLabelEntropyCertificate) (minority : RatMinorityBudgetCertificate) :
    Decidable (small.GlobalMatches large count labels minority) := by
  unfold RatCutGroup.GlobalMatches
  infer_instance

noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem certified_global_failure (small large : RatCutGroup) (count : RatCountingCertificate)
    (labels : RatLabelEntropyCertificate) (minority : RatMinorityBudgetCertificate)
    (hmatch : small.GlobalMatches large count labels minority)
    (hgeometry : large.geometry=small.geometry) (hpopulation : large.population=small.population)
    (hgs : small.NumericValid) (hgl : large.NumericValid)
    (hcss : ∀ c∈small.cells, c.Sound) (hcls : ∀ c∈large.cells, c.Sound)
    (hcsn : ∀ c∈small.cells, c.NumericValid) (hcln : ∀ c∈large.cells, c.NumericValid)
    (hcsp : ∀ c∈small.cells, c.population=small.population)
    (hclp : ∀ c∈large.cells, c.population=large.population)
    (hpv : small.population.Valid) (hps : small.population.Sound)
    (hwv : small.population.witness.Valid) (hws : small.population.witness.Sound)
    (hcv : count.Valid) (hcount : count.Sound) (hlv : labels.Valid)
    (hmv : minority.Valid) (hms : minority.Sound)
    (G : SimpleGraph V) (st : CoverMarkedGraphState small.geometry G)
    (hI : CoverSparseCutIrreducible G) :
    (fixedSizeLaw (univ:Finset V) st.N).prob
      (FixedExpansionFailure G univ st.N st.z small.population.witness.dm small.population.witness.beta) ≤
      (2*exp (-(count.aa:ℝ)*st.R)+
        (2*exp (-(small.exponent:ℝ)*st.R)+2*exp (-(large.exponent:ℝ)*st.R)))/
        (small.population.witness.omega:ℝ) := by
  obtain ⟨hkind,hupper,hlargeupper,hlower,hscap,hlcap,hsentropy,hlentropy,hRmatch,hWmatch,hzmatch,hqmatch,
    hslmatch,himatch,hMmatch,hDmatch,hcountpl,hmR,hmq,hmsl,hmi,hmcap,hmrho,hmy⟩ := hmatch
  obtain ⟨hinput,hdm,hbeta,hzlo,hq,hL,homega,hK,hdelta,hmean,hmean3,hwbranch⟩ := hwv
  rw [RatWitnessCertificate.BranchValid,hkind] at hwbranch
  obtain ⟨hbf,hfd,hcmajor,hwbound⟩ := hwbranch
  obtain ⟨_,_,hpopsl,_,hnup,_,hpbranch⟩ := hpv
  rw [RatPopulationCertificate.BranchValid,hkind] at hpbranch
  have hdmR : (0:ℝ) < (small.population.witness.dm:ℝ) := by exact_mod_cast hdm
  have htD : st.t < Fintype.card V := st.mark_lt_sample.trans_le st.sample_le_order
  have htheta : (0:ℝ) < (count.theta:ℝ) := by exact_mod_cast hcv.1
  have hh : 0 < st.z/st.p := div_pos st.z_pos st.fraction_pos
  let ell : ℝ := (count.theta:ℝ)*(count.slope:ℝ)*st.p
  have hscaleEq : ell/(count.theta:ℝ)=(small.population.slope:ℝ)*st.p := by
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
  have hvote : (small.population.witness.majority.inputs.mean:ℝ) ≤
      ((st.t:ℝ)/st.N)*((small.population.witness.dm:ℝ)*st.z) := by
    have hv := cover_marked_vote_mean small.geometry G st hdmR.le
    rw [← hqmatch] at hv
    have he : (small.population.witness.majority.inputs.mean:ℝ)=
        (small.population.witness.dm:ℝ)*(small.population.witness.qmark:ℝ) := by exact_mod_cast hmean
    rwa [he]
  let cutoff : ℝ := min ((large.lower:ℝ)*(st.z/st.p)) ((Fintype.card V:ℝ)/2)
  have hRlo : (0:ℝ) < (small.geometry.Rlo:ℝ) := by rw [← hmR]; exact_mod_cast hmv.1
  have hsplit : (0:ℝ) < (large.lower:ℝ) := by exact_mod_cast hgl.1
  have hcutoff := cover_split_cutoff_upper hh hRlo st.scale_lower st.order_identity hsplit.le
    (show min ((large.lower:ℝ)/(small.geometry.Rlo:ℝ)) (1/2) ≤ (minority.ymax:ℝ) by
      have hb := (Rat.cast_le (K:=ℝ)).mpr hmy
      norm_num only [Rat.cast_min,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hb ⊢
      exact hb)
  have hNp : (st.N:ℝ)=st.p*(Fintype.card V:ℝ) := by
    rw [st.sample_fraction]
    exact (div_mul_cancel₀ _ st.order_pos.ne').symm
  have hminor := hms (Fintype.card V) st.N st.p st.z st.R st.t cutoff
    (((small.population.witness.factor:ℝ)-(small.population.witness.beta:ℝ))/
      ((small.population.witness.factor:ℝ)+((small.population.witness.dm:ℝ)-(small.population.witness.beta:ℝ))/2))
    st.order_pos st.fraction_pos st.z_pos (by rw [hmR]; exact st.scale_lower)
    (by rw [hmq]; exact st.mark_lower) hcutoff.1 hcutoff.2 hNp st.sample_identity
    (by rw [hmcap]; exact_mod_cast hpbranch.1)
  rw [hmsl,hmi,hmrho] at hminor
  let tailSmall : ℝ := 2*exp (-((small.exponent:ℝ)+(small.geometry.M:ℝ)*(labels.bound:ℝ))*st.R)
  let tailLarge : ℝ := 2*exp (-((large.exponent:ℝ)+(small.geometry.M:ℝ)*(ratCoverLogTwoBudget:ℝ))*st.R)
  let nu : ℝ := (small.population.nu:ℝ)*(st.z/st.p)
  have hexists (T A : Finset V) (xi : V → Finset V) (hT : T.card=st.t)
      (hnu : nu ≤ ((fixedMajoritySmallSide T A xi).card:ℝ)) :
      ∃ l m f : ℝ,
        RoundedCutLabelValid G (fixedMajoritySmallSide T A xi) T st.residual l m f
          (if ((fixedMajoritySmallSide T A xi).card:ℝ) ≤ cutoff then tailSmall else tailLarge) ∧
        (small.population.witness.factor:ℝ)*st.z*
          (((small.population.slope:ℝ)*st.p)*(fixedMajoritySmallSide T A xi).card+
            (small.population.intercept:ℝ)*st.z) ≤ f*(m*(st.residual:ℝ)^2) := by
    let S := fixedMajoritySmallSide T A xi
    have hhalf : (S.card:ℝ) ≤ (1/2:ℝ)*Fintype.card V := by
      have hh := smallerCutSide_small (fixedMajoritySide univ T A xi)
      have hhR : 2*(S.card:ℝ) ≤ Fintype.card V := by exact_mod_cast hh
      linarith only [hhR]
    by_cases hsmall : (S.card:ℝ) ≤ cutoff
    · have hside : small.interval.Contains ((S.card:ℝ)/(st.z/st.p)) := by
        refine ⟨?_,?_⟩
        · change (small.lower:ℝ) ≤ (S.card:ℝ)/(st.z/st.p)
          rw [hlower]
          exact (le_div_iff₀ hh).mpr hnu
        · intro r hr
          change small.upper=some r at hr
          rw [hupper] at hr
          have he := Option.some.inj hr
          rw [← he]
          exact (div_le_iff₀ hh).mpr (hsmall.trans (min_le_left _ _))
      obtain ⟨c,hmem,hcut,hthreshold⟩ := cover_group_uniform_actual_cut small G st hgs hcss hcsn hcsp
        hWmatch hI hsentropy S T hT hside (by rw [hscap]; norm_num; exact hhalf)
      rw [RatCutThresholdCertificate.Bound,RatCutCellCertificate.threshold,hcsp c hmem,hkind] at hthreshold
      refine ⟨c.region.bin.residual.retention.lambda,(c.region.bin.residual.kappa:ℝ)*(st.z/st.p)*S.card,
        c.region.bin.tau,?_,hthreshold⟩
      change RoundedCutLabelValid G S T _ _ _ _ (if (S.card:ℝ) ≤ cutoff then tailSmall else tailLarge)
      rwa [if_pos hsmall]
    · have hsplitSide : (large.lower:ℝ)*(st.z/st.p) < (S.card:ℝ) := by
        by_contra! h
        apply hsmall
        exact le_min h (by linarith only [hhalf])
      have hside : large.interval.Contains ((S.card:ℝ)/(st.z/st.p)) := by
        refine ⟨(le_div_iff₀ hh).mpr hsplitSide.le,?_⟩
        intro r hr
        change large.upper=some r at hr
        rw [hlargeupper] at hr
        contradiction
      obtain ⟨c,hmem,hcut,hthreshold⟩ := cover_group_uniform_actual_cut_of_geometry large G st hgeometry
        hgl hcls hcln hclp (by rw [hpopulation,hgeometry]; exact hWmatch) hI hlentropy
        S T hT hside (by rw [hlcap]; norm_num; exact hhalf)
      rw [RatCutThresholdCertificate.Bound,RatCutCellCertificate.threshold,hclp c hmem,hpopulation,hkind] at hthreshold
      refine ⟨c.region.bin.residual.retention.lambda,(c.region.bin.residual.kappa:ℝ)*(st.z/st.p)*S.card,
        c.region.bin.tau,?_,hthreshold⟩
      change RoundedCutLabelValid G S T _ _ _ _ (if (S.card:ℝ) ≤ cutoff then tailSmall else tailLarge)
      rwa [if_neg hsmall]
  have hchoice : ∀ T A xi, ∃ y : ℝ×ℝ×ℝ, T.card=st.t →
      nu ≤ ((fixedMajoritySmallSide T A xi).card:ℝ) →
      RoundedCutLabelValid G (fixedMajoritySmallSide T A xi) T st.residual y.1 y.2.1 y.2.2
        (if ((fixedMajoritySmallSide T A xi).card:ℝ) ≤ cutoff then tailSmall else tailLarge) ∧
      (small.population.witness.factor:ℝ)*st.z*
        (((small.population.slope:ℝ)*st.p)*(fixedMajoritySmallSide T A xi).card+
          (small.population.intercept:ℝ)*st.z) ≤ y.2.2*(y.2.1*(st.residual:ℝ)^2) := by
    intro T A xi
    by_cases hT : T.card=st.t
    · by_cases hnu : nu ≤ ((fixedMajoritySmallSide T A xi).card:ℝ)
      · obtain ⟨l,m,f,h⟩ := hexists T A xi hT hnu
        exact ⟨(l,m,f),fun _ _ => h⟩
      · exact ⟨(0,0,0),fun _ h => False.elim (hnu h)⟩
    · exact ⟨(0,0,0),fun h _ => False.elim (hT h)⟩
  choose choice hchoice using hchoice
  have hbound := fixed_global_split_expansion_failure_bound_capped G st.sample_le_order st.mark_lt_sample.le htD
    (z:=st.z) (dm:=(small.population.witness.dm:ℝ)) (beta:=(small.population.witness.beta:ℝ))
    (tau:=(small.population.witness.factor:ℝ)) (q:=6) (theta:=(count.theta:ℝ)) (ell:=ell)
    (err:=(small.population.intercept:ℝ)*st.z) (nu:=nu) (rho:=(labels.rho:ℝ)) (cutoff:=cutoff)
    (etaSmall:=tailSmall) (etaLarge:=tailLarge)
    st.z_pos (by exact_mod_cast hbeta) (by exact_mod_cast hbf) (by exact_mod_cast hbf.trans hfd)
    htheta hscale (mul_pos (by exact_mod_cast hnup) hh) (by exact_mod_cast hlv.1)
    (by dsimp only [tailSmall]; positivity) (by dsimp only [tailLarge]; positivity)
    (by simpa only [hscaleEq,nu,mul_div_assoc] using hpopbound)
    hmgf (by simpa only [hscaleEq] using hminor)
    st.residual st.residual_pos st.residual_half st.residual_mean
    (voteLambda:=(small.population.witness.majority.inputs.mean:ℝ))
    (K:=(small.population.witness.majority.bound:ℝ)) (omega:=(small.population.witness.omega:ℝ))
    hwactual.1 (by exact_mod_cast hmean3) hvote (by exact_mod_cast hK)
    (fun r hr0 hr1 => by
      have h := (hwactual.2.2 r hr0 hr1).1
      rw [hcmajor] at h
      simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_one] using h)
    (fun r hr0 hr1 => by
      have h := (hwactual.2.2 r hr0 hr1).2
      rw [hcmajor] at h
      simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_one] using h)
    hws.1 hwlower
    (fun T A xi => (choice T A xi).1) (fun T A xi => (choice T A xi).2.1)
    (fun T A xi => (choice T A xi).2.2)
    (fun T hT A _ xi hnu => by simpa only [hscaleEq] using hchoice T A xi hT hnu)
  have hcoun := hcount.2 (R:=st.R) (z:=st.z) (p:=st.p) (t:=st.t) st.scale_pos
    (by rw [hDmatch]; exact st.scale_ratio) (by rw [hcountpl]; exact st.fraction_lower)
    (by rw [hMmatch]; exact st.mark_upper)
  rw [himatch] at hcoun
  have hlabels := rat_label_entropy_certificate_sound labels hlv
  have hsmall := cover_capped_label_uniform_tail st.mark_upper hlabels.1 hlabels.2 (exponent:=(small.exponent:ℝ))
  have hlarge := cover_all_label_uniform_tail st.mark_upper cover_log_two_budget (exponent:=(large.exponent:ℝ))
  apply hbound.trans
  apply div_le_div_of_nonneg_right _ hws.1.le
  exact add_le_add (by simpa only [ell] using hcoun) (add_le_add hsmall hlarge)

end
end Cycle12
