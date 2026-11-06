import Mathlib

namespace Cycle13
open Real Set
noncomputable section

/-- The one-variable perspective used by both terms in the mixed cover. -/
def positivePerspective (f : ℝ → ℝ) (x : ℝ) : ℝ := x*f ((1+x)/x)

theorem convexOn_positivePerspective {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ici 0) f) :
    ConvexOn ℝ (Ioi 0) (positivePerspective f) := by
  refine ⟨convex_Ioi _,?_⟩
  intro x hx y hy a b ha hb hab
  change 0<x at hx
  change 0<y at hy
  let z := a*x+b*y
  have hz : 0<z := by
    have hh := (convex_Ioi (0:ℝ)) hx hy ha hb hab
    simpa only [smul_eq_mul,Set.mem_Ioi] using hh
  have hw : a*x/z+b*y/z=1 := by rw [← add_div]; exact div_self hz.ne'
  have harg : (a*x/z)*((1+x)/x)+(b*y/z)*((1+y)/y)=(1+z)/z := by
    field_simp
    nlinarith [hab]
  have hh := hf.2 (by change 0≤(1+x)/x; positivity : (1+x)/x ∈ Ici 0)
    (by change 0≤(1+y)/y; positivity : (1+y)/y ∈ Ici 0)
    (by positivity : 0≤a*x/z) (by positivity : 0≤b*y/z) hw
  simp only [smul_eq_mul] at hh
  rw [harg] at hh
  have hm := mul_le_mul_of_nonneg_left hh hz.le
  have he : z*((a*x/z)*f ((1+x)/x)+(b*y/z)*f ((1+y)/y))=
      a*(x*f ((1+x)/x))+b*(y*f ((1+y)/y)) := by field_simp <;> ring
  rw [he] at hm
  exact hm

def powerPerspective (p x : ℝ) : ℝ := positivePerspective (fun y => y^p) x

theorem powerPerspective_convex {p : ℝ} (hp : 1≤p) :
    ConvexOn ℝ (Ioi 0) (powerPerspective p) :=
  convexOn_positivePerspective (convexOn_rpow hp)

theorem powerPerspective_eq {x p : ℝ} (hx : 0<x) :
    powerPerspective p x=(1+x)^p*x^(1-p) := by
  unfold powerPerspective positivePerspective
  dsimp only
  rw [div_rpow (by linarith : 0≤1+x) hx.le,rpow_sub hx,rpow_one]
  ring

/-- The linear density term and the two perspective powers in the
normalized finite-stage core fee. The linear coefficient can have either sign. -/
def coreShapeFee (linear cube square x : ℝ) : ℝ :=
  (1+x)*linear+cube*powerPerspective (4/3) x+square*powerPerspective (3/2) x

theorem coreShapeFee_convex {linear cube square : ℝ} (hc : 0 ≤ cube) (hs : 0 ≤ square) :
    ConvexOn ℝ (Ioi 0) (coreShapeFee linear cube square) := by
  have hl : ConvexOn ℝ (Ioi 0) (fun x : ℝ => (1+x)*linear) := by
    refine ⟨convex_Ioi _,?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    nlinarith [congrArg (fun q => q*linear) hab]
  have h₁ := (powerPerspective_convex (by norm_num : (1:ℝ)≤4/3)).smul hc
  have h₂ := (powerPerspective_convex (by norm_num : (1:ℝ)≤3/2)).smul hs
  convert (hl.add h₁).add h₂ using 1
  ext x
  simp [coreShapeFee,smul_eq_mul]

/-- Both endpoints must use the same cover parameters. No minimum of
two unrelated convex functions is taken. -/
theorem coreShapeFee_endpoint_bound {linear cube square lo hi x fee : ℝ}
    (hc : 0 ≤ cube) (hs : 0 ≤ square) (hlo : 0<lo) (hhi : 0<hi)
    (hx : x∈Icc lo hi)
    (hl : coreShapeFee linear cube square lo≤fee)
    (hh : coreShapeFee linear cube square hi≤fee) :
    coreShapeFee linear cube square x≤fee := by
  exact ((coreShapeFee_convex hc hs).le_max_of_mem_Icc hlo hhi hx).trans (max_le hl hh)

end
end Cycle13
