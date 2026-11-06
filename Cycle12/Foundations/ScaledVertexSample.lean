import Cycle12.Foundations.SampleTailScale

namespace Cycle13
open Real Finset SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem residual_lower_of_identity_bound {p q ρ : unitInterval}
    (hpq : (p:ℝ)*(q:ℝ) < 1)
    (hρ : (1-(p:ℝ)*(q:ℝ))*(ρ:ℝ) ≤ (p:ℝ)*(1-(q:ℝ))) :
    (ρ:ℝ) ≤ (residualProbability p q hpq:ℝ) := by
  apply (le_div_iff₀ (by linarith : 0 < 1-(p:ℝ)*(q:ℝ))).mpr
  nlinarith

theorem scaledMark_domain {p q : unitInterval} {s : ℝ} (hs : 1 ≤ s)
    (hpq : (p:ℝ)*(q:ℝ) < 1) : (p:ℝ)*(scaledMark q s hs:ℝ) < 1 :=
  (mul_le_mul_of_nonneg_left (scaledMark_le q s hs) p.2.1).trans_lt hpq

namespace VertexSamplingData

def scale (D : VertexSamplingData) (s : ℝ) (hs : 1 ≤ s)
    (ρm ρa : unitInterval) : VertexSamplingData where
  main := D.main.scale s
  anchor := D.anchor.scale s
  markMain := scaledMark D.markMain s hs
  residualMain := ρm
  markAnchor := scaledMark D.markAnchor s hs
  residualAnchor := ρa
  degreeMean := s*D.degreeMean
  edgeDeviation := s^3*D.edgeDeviation
  incidentFraction := D.incidentFraction

def scalarFailureSum (D : VertexSamplingData) (p : unitInterval) (n m : ℝ) : ℝ :=
  exp (-poissonRate ((p:ℝ)*n) D.anchor.lower)+
  exp (-poissonRate ((p:ℝ)*n) D.main.upper)+
  n*exp (-poissonRate D.degreeMean D.main.δ)+
  D.main.failureBound p D.markMain D.residualMain n+
  D.anchor.failureBound p D.markAnchor D.residualAnchor n+
  sampleEdgeFailureScalar (p:ℝ) n m D.edgeDeviation+
  incidentFailureScalar (p:ℝ) n m D.incidentFraction

theorem failureSum_eq_scalar (D : VertexSamplingData) (G : SimpleGraph V) (p : unitInterval) :
    D.failureSum G p=D.scalarFailureSum p (Fintype.card V) (Fintype.card G.edgeSet) := rfl

/-- Numerical premises at a possibly nonintegral base order. The graph profile and
minimum degree are supplied only for the actual graph at the chosen scale. -/
structure ScaleCertificate (D : VertexSamplingData) (p : unitInterval) (n m : ℝ) : Prop where
  main_valid : D.main.Valid p D.markMain D.residualMain n
  anchor_valid : D.anchor.Valid p D.markAnchor D.residualAnchor n
  main_mark_domain : (p:ℝ)*(D.markMain:ℝ) < 1
  anchor_mark_domain : (p:ℝ)*(D.markAnchor:ℝ) < 1
  main_residual_lower : (1-(p:ℝ)*(D.markMain:ℝ))*(D.residualMain:ℝ) ≤ (p:ℝ)*(1-(D.markMain:ℝ))
  anchor_residual_lower : (1-(p:ℝ)*(D.markAnchor:ℝ))*(D.residualAnchor:ℝ) ≤ (p:ℝ)*(1-(D.markAnchor:ℝ))
  match_degree : D.anchor.δ=D.main.δ
  match_expansion : D.anchor.β=D.main.β
  match_order : D.anchor.upper=D.main.upper
  order_lower_pos : 0 < D.anchor.lower
  order_lower_mean : D.anchor.lower ≤ (p:ℝ)*n
  order_upper_mean : (p:ℝ)*n ≤ D.main.upper
  degree_mean_pos : 0 < D.degreeMean
  degree_threshold : D.main.δ ≤ D.degreeMean
  edge_deviation_pos : 0 < D.edgeDeviation
  edge_count_pos : 0 < m
  sample_lt_one : (p:ℝ) < 1
  incident_threshold : 2*(p:ℝ)-(p:ℝ)^2 < D.incidentFraction
  main_cap_pos : 0 < D.main.cap
  anchor_cap_pos : 0 < D.anchor.cap
  anchor_intercept_nonneg : 0 ≤ D.anchor.b
  degree_rate : 2 ≤ poissonRate D.degreeMean D.main.δ
  main_mgf_rate : (p:ℝ)*(D.markMain:ℝ)*exp (D.main.θ*(1-D.main.slope*(p:ℝ)))*n ≤ D.main.θ*D.main.b
  main_janson_rate : (p:ℝ)*(D.markMain:ℝ)*n ≤ D.main.jansonRate D.residualMain
  anchor_mgf_rate : (p:ℝ)*(D.markAnchor:ℝ)*exp (D.anchor.θ*(1-D.anchor.slope*(p:ℝ)))*n ≤ D.anchor.θ*D.anchor.b
  anchor_janson_rate : (p:ℝ)*(D.markAnchor:ℝ)*n ≤ D.anchor.jansonRate D.residualAnchor

theorem ScaleCertificate.order_pos {D : VertexSamplingData} {p : unitInterval} {n m : ℝ}
    (hD : D.ScaleCertificate p n m) : 0 < n :=
  (mul_pos (by norm_num : (0:ℝ) < 9) hD.main_valid.scale_pos).trans_le hD.main_valid.order_scale

theorem scalarFailureSum_scale_le (D : VertexSamplingData) {p ρm ρa : unitInterval} {n m s : ℝ}
    (hD : D.ScaleCertificate p n m) (hs : 1 ≤ s)
    (hm : (D.residualMain:ℝ) ≤ (ρm:ℝ)) (ha : (D.residualAnchor:ℝ) ≤ (ρa:ℝ)) :
    (D.scale s hs ρm ρa).scalarFailureSum p (s^2*n) (s^3*m) ≤ D.scalarFailureSum p n m := by
  have hmean : 0 < (p:ℝ)*n := mul_pos hD.main_valid.p_pos hD.order_pos
  have hlo := order_chernoff_scale hs hmean hD.order_lower_pos
  have hhi := order_chernoff_scale hs hmean (hmean.trans_le hD.order_upper_mean)
  have hdeg := degree_chernoff_scale hs hD.order_pos.le hD.degree_rate
  have hmain := D.main.failureBound_mono_scale hD.main_valid hs hm hD.main_mgf_rate hD.main_janson_rate
  have hanc := D.anchor.failureBound_mono_scale hD.anchor_valid hs ha hD.anchor_mgf_rate hD.anchor_janson_rate
  have hedge := sampleEdgeFailureScalar_scale p.2.1 p.2.2 hD.order_pos.le hD.edge_count_pos.le hD.edge_deviation_pos hs
  have hinc := incidentFailureScalar_scale hD.main_valid.p_pos hD.sample_lt_one hD.order_pos
    hD.edge_count_pos.le hD.incident_threshold hs
  dsimp only [scalarFailureSum,scale,GlobalCutParameters.scale,AnchorParameters.scale]
  have he : (p:ℝ)*(s^2*n)=s^2*((p:ℝ)*n) := by ring
  rw [he]
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hlo hhi) hdeg) hmain) hanc) hedge) hinc

theorem valid_above_scale (D : VertexSamplingData) {p : unitInterval} {n m s : ℝ}
    (hD : D.ScaleCertificate p n m) (hs : 1 ≤ s) (G : SimpleGraph V)
    (hn : (Fintype.card V:ℝ)=s^2*n) (hm : (Fintype.card G.edgeSet:ℝ)=s^3*m)
    (hmain : GlobalCutProfile G (s*D.main.h)) (hanc : GlobalCutProfile G (s*D.anchor.h))
    (hdeg : ∀ v, s*D.degreeMean ≤ (p:ℝ)*G.degree v) :
    (D.scale s hs
      (residualProbability p (scaledMark D.markMain s hs) (scaledMark_domain hs hD.main_mark_domain))
      (residualProbability p (scaledMark D.markAnchor s hs) (scaledMark_domain hs hD.anchor_mark_domain))).Valid G p := by
  have hs0 : 0 < s := by linarith
  have hρm := (residual_lower_of_identity_bound hD.main_mark_domain hD.main_residual_lower).trans
    (residualProbability_antitone_mark p D.markMain (scaledMark D.markMain s hs)
      (scaledMark_le _ _ hs) hD.main_mark_domain (scaledMark_domain hs hD.main_mark_domain))
  have hρa := (residual_lower_of_identity_bound hD.anchor_mark_domain hD.anchor_residual_lower).trans
    (residualProbability_antitone_mark p D.markAnchor (scaledMark D.markAnchor s hs)
      (scaledMark_le _ _ hs) hD.anchor_mark_domain (scaledMark_domain hs hD.anchor_mark_domain))
  refine {
    main_valid := by rw [hn]; exact D.main.valid_scale hD.main_valid hs hρm hD.main_cap_pos
    anchor_valid := by rw [hn]; exact D.anchor.valid_scale hD.anchor_valid hs hρa hD.anchor_cap_pos hD.anchor_intercept_nonneg
    main_profile := hmain
    anchor_profile := hanc
    main_mark_domain := scaledMark_domain hs hD.main_mark_domain
    anchor_mark_domain := scaledMark_domain hs hD.anchor_mark_domain
    main_residual := residualProbability_identity p (scaledMark D.markMain s hs) (scaledMark_domain hs hD.main_mark_domain)
    anchor_residual := residualProbability_identity p (scaledMark D.markAnchor s hs) (scaledMark_domain hs hD.anchor_mark_domain)
    match_degree := by dsimp only [scale,GlobalCutParameters.scale,AnchorParameters.scale]; rw [hD.match_degree]
    match_expansion := by dsimp only [scale,GlobalCutParameters.scale,AnchorParameters.scale]; rw [hD.match_expansion]
    match_order := by dsimp only [scale,GlobalCutParameters.scale,AnchorParameters.scale]; rw [hD.match_order]
    order_lower_pos := mul_pos (sq_pos_of_pos hs0) hD.order_lower_pos
    order_lower_mean := ?_
    order_upper_mean := ?_
    degree_mean_pos := mul_pos hs0 hD.degree_mean_pos
    degree_threshold := mul_le_mul_of_nonneg_left hD.degree_threshold hs0.le
    degree_mean := hdeg
    edge_deviation_pos := mul_pos (pow_pos hs0 3) hD.edge_deviation_pos
    edge_count_pos := by rw [hm]; exact mul_pos (pow_pos hs0 3) hD.edge_count_pos
    sample_lt_one := hD.sample_lt_one
    incident_threshold := hD.incident_threshold }
  · dsimp only [scale,AnchorParameters.scale]
    rw [hn]
    nlinarith [mul_le_mul_of_nonneg_left hD.order_lower_mean (sq_nonneg s)]
  · dsimp only [scale,GlobalCutParameters.scale]
    rw [hn]
    nlinarith [mul_le_mul_of_nonneg_left hD.order_upper_mean (sq_nonneg s)]

theorem exists_sample_above_scale (D : VertexSamplingData) {p : unitInterval} {n m s : ℝ}
    (hD : D.ScaleCertificate p n m) (hs : 1 ≤ s) (G : SimpleGraph V)
    (hn : (Fintype.card V:ℝ)=s^2*n) (hm : (Fintype.card G.edgeSet:ℝ)=s^3*m)
    (hmain : GlobalCutProfile G (s*D.main.h)) (hanc : GlobalCutProfile G (s*D.anchor.h))
    (hdeg : ∀ v, s*D.degreeMean ≤ (p:ℝ)*G.degree v)
    (hsum : D.scalarFailureSum p n m < 1) :
    ∃ U : Finset V, GoodVertexSample G U (s*D.main.δ) (s*D.main.β) D.anchor.L
      (s^2*D.anchor.lower) (s^2*D.main.upper)
      (s^3*(m*(p:ℝ)^2-D.edgeDeviation)) (s^3*(D.incidentFraction*m)) := by
  let ρm := residualProbability p (scaledMark D.markMain s hs) (scaledMark_domain hs hD.main_mark_domain)
  let ρa := residualProbability p (scaledMark D.markAnchor s hs) (scaledMark_domain hs hD.anchor_mark_domain)
  have hρm := (residual_lower_of_identity_bound hD.main_mark_domain hD.main_residual_lower).trans
    (residualProbability_antitone_mark p D.markMain (scaledMark D.markMain s hs)
      (scaledMark_le _ _ hs) hD.main_mark_domain (scaledMark_domain hs hD.main_mark_domain))
  have hρa := (residual_lower_of_identity_bound hD.anchor_mark_domain hD.anchor_residual_lower).trans
    (residualProbability_antitone_mark p D.markAnchor (scaledMark D.markAnchor s hs)
      (scaledMark_le _ _ hs) hD.anchor_mark_domain (scaledMark_domain hs hD.anchor_mark_domain))
  have hbound : (D.scale s hs ρm ρa).failureSum G p < 1 := by
    rw [failureSum_eq_scalar,hn,hm]
    exact (D.scalarFailureSum_scale_le hD hs hρm hρa).trans_lt hsum
  obtain ⟨U,hU⟩ := (D.scale s hs ρm ρa).exists_sample G p
    (D.valid_above_scale hD hs G hn hm hmain hanc hdeg) hbound
  refine ⟨U,?_⟩
  dsimp only [Good,scale,GlobalCutParameters.scale,AnchorParameters.scale] at hU
  rw [hm] at hU
  convert hU using 1 <;> ring

end VertexSamplingData
end
end Cycle13
