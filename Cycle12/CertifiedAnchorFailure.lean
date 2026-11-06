import Cycle12.CoverGroupApplication
import Cycle12.FixedAnchorFailure
import Cycle12.MarkedWitnessAssembly
import Cycle12.RationalReverseLocal

namespace Cycle12
open Finset SimpleGraph Cycle13 Real

def RatCutGroup.AnchorMatches (g : RatCutGroup) (count : RatCountingCertificate) : Prop :=
  g.population.witness.kind=.anchor ∧ g.upper=none ∧ g.lower=g.population.nu ∧ g.cap=1/2 ∧
  g.entropyBound=some ratCoverLogTwoBudget ∧
  g.population.Rlo=g.geometry.Rlo ∧ g.population.Wlo=g.geometry.Wlo ∧
  g.population.pl=g.geometry.inputs.pl ∧ g.population.witness.zlo=g.geometry.zlo ∧
  g.population.witness.qmark=g.geometry.qmark ∧
  count.slope=g.population.slope ∧ count.intercept=g.population.intercept ∧
  count.M=g.geometry.M ∧ count.D=g.geometry.Dlo ∧ count.pl=g.geometry.inputs.pl

instance instDecidableRatAnchorMatches (g : RatCutGroup) (count : RatCountingCertificate) :
    Decidable (g.AnchorMatches count) := by
  unfold RatCutGroup.AnchorMatches
  infer_instance

noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem cover_all_label_uniform_tail {M R exponent upper : ℝ} {t : ℕ}
    (ht : (t:ℝ) ≤ M*R) (hu : log 2 ≤ upper) :
    (2:ℝ)^t*(2*exp (-(exponent+M*upper)*R)) ≤ 2*exp (-exponent*R) := by
  have hup : 0 ≤ upper := (log_pos (by norm_num : (1:ℝ) < 2)).le.trans hu
  have hh := (mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg (α:=ℝ) t)).trans
    (mul_le_mul_of_nonneg_right ht hup)
  rw [cover_all_labels_exp]
  calc
    _ = 2*exp ((t:ℝ)*log 2+(-(exponent+M*upper)*R)) := by rw [exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith only [hh])) (by norm_num)

/-- All graph cut hypotheses are discharged from the finite interval table.
The remaining hypotheses are the separately kernel-checked certificate data. -/
theorem certified_anchor_failure (g : RatCutGroup) (count : RatCountingCertificate)
    (hmatch : g.AnchorMatches count) (hg : g.NumericValid)
    (hcs : ∀ c∈g.cells, c.Sound) (hcn : ∀ c∈g.cells, c.NumericValid)
    (hpopmatch : ∀ c∈g.cells, c.population=g.population)
    (hpv : g.population.Valid) (hps : g.population.Sound)
    (hwv : g.population.witness.Valid) (hws : g.population.witness.Sound)
    (hcv : count.Valid) (hcount : count.Sound)
    (G : SimpleGraph V) (st : CoverMarkedGraphState g.geometry G)
    (hI : CoverSparseCutIrreducible G) :
    (fixedSizeLaw (univ:Finset V) st.N).prob
      (FixedAnchorFailure G st.N st.z g.population.witness.dm g.population.witness.beta g.population.witness.L) ≤
      (2*exp (-(count.aa:ℝ)*st.R)+2*exp (-(g.exponent:ℝ)*st.R))/(g.population.witness.omega:ℝ) := by
  obtain ⟨hkind,hupper,hlower,hcap,hentropy,hRmatch,hWmatch,hplmatch,hzmatch,hqmatch,
    hslmatch,himatch,hMmatch,hDmatch,hcountpl⟩ := hmatch
  obtain ⟨hinput,hdm,hbeta,hzlo,hq,hL,homega,hK,hdelta,hmean,hmean3,hwbranch⟩ := hwv
  rw [RatWitnessCertificate.BranchValid,hkind] at hwbranch
  obtain ⟨hew,hcmajor,hfull1,hfullbound,hwbound⟩ := hwbranch
  obtain ⟨_,_,hpopsl,_,hnup,_,hpbranch⟩ := hpv
  rw [RatPopulationCertificate.BranchValid,hkind] at hpbranch
  have hce : (0:ℝ) < (g.population.ce:ℝ) := by exact_mod_cast hpbranch.2.1
  have hdmR : (0:ℝ) < (g.population.witness.dm:ℝ) := by exact_mod_cast hdm
  have htD : st.t < Fintype.card V := st.mark_lt_sample.trans_le st.sample_le_order
  have htheta : (0:ℝ) < (count.theta:ℝ) := by exact_mod_cast hcv.1
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
  have hpopulation := hps st.p st.z st.R st.fraction_pos
    (by rw [hzmatch]; exact st.z_lower) (by rw [hRmatch]; exact st.scale_lower)
    (by rw [hWmatch]; exact st.weight_lower)
  rw [RatPopulationCertificate.BranchBound,hkind] at hpopulation
  have hnid : st.z*st.R/st.p=(Fintype.card V:ℝ) := by rw [st.order_identity]; ring
  rw [hnid,← st.sample_identity] at hpopulation
  have hNlower : (g.population.pl:ℝ)*Fintype.card V ≤ (st.N:ℝ) := by
    apply (le_div_iff₀ st.order_pos).mp
    rw [hplmatch,← st.sample_fraction]
    exact st.fraction_lower
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
  let tail : ℝ := 2*exp (-((g.exponent:ℝ)+(g.geometry.M:ℝ)*(ratCoverLogTwoBudget:ℝ))*st.R)
  let nu : ℝ := (g.population.nu:ℝ)*(st.z/st.p)
  have hexists (T A : Finset V) (xi : V → Finset V) (hT : T.card=st.t)
      (hnu : nu ≤ ((fixedMajoritySmallSide T A xi).card:ℝ)) :
      ∃ l m f : ℝ,
        RoundedCutLabelValid G (fixedMajoritySmallSide T A xi) T st.residual l m f tail ∧
        (((1+(g.population.witness.factor:ℝ))*(g.population.witness.L:ℝ))/(g.population.ce:ℝ))*
          (fixedMajoritySmallSide T A xi).card ≤ f*(m*(st.residual:ℝ)^2) := by
    let S := fixedMajoritySmallSide T A xi
    have hside : g.interval.Contains ((S.card:ℝ)/(st.z/st.p)) := by
      refine ⟨?_,?_⟩
      · change (g.lower:ℝ) ≤ (S.card:ℝ)/(st.z/st.p)
        rw [hlower]
        exact (le_div_iff₀ (div_pos st.z_pos st.fraction_pos)).mpr hnu
      · intro r hr
        change g.upper=some r at hr
        rw [hupper] at hr
        contradiction
    have hhalf : (S.card:ℝ) ≤ (g.cap:ℝ)*Fintype.card V := by
      have hh := smallerCutSide_small (fixedMajoritySide univ T A xi)
      have hhR : 2*(S.card:ℝ) ≤ Fintype.card V := by exact_mod_cast hh
      rw [hcap]
      norm_num
      linarith only [hhR]
    obtain ⟨c,hmem,hcut,hthreshold⟩ := cover_group_uniform_actual_cut g G st hg hcs hcn hpopmatch
      hWmatch hI hentropy S T hT hside hhalf
    rw [RatCutThresholdCertificate.Bound,RatCutCellCertificate.threshold,hpopmatch c hmem,hkind] at hthreshold
    exact ⟨c.region.bin.residual.retention.lambda,
      (c.region.bin.residual.kappa:ℝ)*(st.z/st.p)*S.card,c.region.bin.tau,hcut,hthreshold⟩
  have hchoice : ∀ T A xi, ∃ y : ℝ×ℝ×ℝ, T.card=st.t →
      nu ≤ ((fixedMajoritySmallSide T A xi).card:ℝ) →
      RoundedCutLabelValid G (fixedMajoritySmallSide T A xi) T st.residual y.1 y.2.1 y.2.2 tail ∧
      (((1+(g.population.witness.factor:ℝ))*(g.population.witness.L:ℝ))/(g.population.ce:ℝ))*
        (fixedMajoritySmallSide T A xi).card ≤ y.2.2*(y.2.1*(st.residual:ℝ)^2) := by
    intro T A xi
    by_cases hT : T.card=st.t
    · by_cases hnu : nu ≤ ((fixedMajoritySmallSide T A xi).card:ℝ)
      · obtain ⟨l,m,f,h⟩ := hexists T A xi hT hnu
        exact ⟨(l,m,f),fun _ _ => h⟩
      · exact ⟨(0,0,0),fun _ h => False.elim (hnu h)⟩
    · exact ⟨(0,0,0),fun h _ => False.elim (hT h)⟩
  choose choice hchoice using hchoice
  have hbound := fixed_anchor_failure_bound G st.sample_le_order st.mark_lt_sample.le htD
    (z:=st.z) (dm:=(g.population.witness.dm:ℝ)) (beta:=(g.population.witness.beta:ℝ))
    (L:=(g.population.witness.L:ℝ)) (ew:=(g.population.witness.factor:ℝ)) (miss:=1/8)
    (theta:=(count.theta:ℝ)) (ell:=ell) (intercept:=(g.population.intercept:ℝ)*st.z)
    (raw:=(g.population.raw:ℝ)) (pLower:=(g.population.pl:ℝ)) (ce:=(g.population.ce:ℝ)) (nu:=nu)
    st.z_pos hdmR (by exact_mod_cast hbeta) (by exact_mod_cast hL) (by exact_mod_cast hew.le)
    (by norm_num) htheta hscale hce hpopulation.1 hpopulation.2.1 hNlower
    (by simpa only [hscaleEq] using hpopulation.2.2.1)
    (by simpa only [hscaleEq,nu,mul_div_assoc] using hpopulation.2.2.2)
    hmgf st.residual st.residual_pos st.residual_half st.residual_mean
    (show 0 ≤ tail by dsimp only [tail]; positivity)
    (voteLambda:=(g.population.witness.majority.inputs.mean:ℝ))
    (K:=(g.population.witness.majority.bound:ℝ)) (Kfull:=(g.population.witness.fullCorrection:ℝ))
    (omega:=(g.population.witness.omega:ℝ))
    (Nat.zero_lt_of_lt st.mark_lt_sample) (by exact_mod_cast hew) (by norm_num)
    hwactual.1 (by exact_mod_cast hmean3) hvote (by exact_mod_cast hK)
    (fun r hr0 hr1 => by simpa only [hcmajor,Rat.cast_one] using (hwactual.2.2 r hr0 hr1).1)
    (fun r hr0 hr1 => by simpa only [hcmajor,Rat.cast_one] using (hwactual.2.2 r hr0 hr1).2)
    (by exact_mod_cast hfull1) hwlower.1 hws.1 hwlower.2
    (fun T A xi => (choice T A xi).1) (fun T A xi => (choice T A xi).2.1)
    (fun T A xi => (choice T A xi).2.2)
    (fun T hT A _ xi hnu => hchoice T A xi hT hnu)
  have hcoun := hcount.2 (R:=st.R) (z:=st.z) (p:=st.p) (t:=st.t) st.scale_pos
    (by rw [hDmatch]; exact st.scale_ratio) (by rw [hcountpl]; exact st.fraction_lower)
    (by rw [hMmatch]; exact st.mark_upper)
  rw [himatch] at hcoun
  have htbound := cover_all_label_uniform_tail st.mark_upper cover_log_two_budget
    (exponent:=(g.exponent:ℝ))
  apply hbound.trans
  apply div_le_div_of_nonneg_right _ hws.1.le
  exact add_le_add (by simpa only [ell] using hcoun) htbound

end
end Cycle12
