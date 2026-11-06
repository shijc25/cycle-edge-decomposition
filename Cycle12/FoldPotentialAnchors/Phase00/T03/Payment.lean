import Cycle12.FoldPotentialAnchors.Phase00.T03.Total
import Cycle12.FoldPointCertificate12
import Cycle12.Phase00

namespace Cycle12.Global12.FoldAnchors.Phase00.T03
open Real
noncomputable section
set_option maxHeartbeats 1000000

theorem feeTerm0 : (2:ℝ)^((((-20154618933510405361587/583898436288774103240):ℚ):ℝ))  ≤  (((40667387876477/1000000000000000000000000):ℚ):ℝ) := by
  exact (Cycle13.certified_power_two (y:=(281826336596688251813/583898436288774103240)) (-35)
    (q:=(-20154618933510405361587/583898436288774103240)) (L:=(10166846969119/250000000000000000000000)) (U:=(40667387876477/1000000000000000000000000))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2

theorem feeTerm1 : (2:ℝ)^((((-236890588223203767309/116779687257754820648):ℚ):ℝ))  ≤  (((122552716957080796659679/500000000000000000000000):ℚ):ℝ) := by
  exact (Cycle13.certified_power_two (y:=(113448473550060694635/116779687257754820648)) (-3)
    (q:=(-236890588223203767309/116779687257754820648)) (L:=(61276358478540398220013/250000000000000000000000)) (U:=(122552716957080796659679/500000000000000000000000))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2

theorem feeTerm2 : (2:ℝ)^((((0/1):ℚ):ℝ))  ≤  (((1/1):ℚ):ℝ) := by
  exact (Cycle13.certified_power_two (y:=(0/1)) (0)
    (q:=(0/1)) (L:=(1/1)) (U:=(1/1))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2

theorem coefficient_row :
    foldMassCoefficient (Cycle12.Phase00.threshold 3) (((2311587725257500000000/14597460907219352581):ℚ):ℝ)  ≤  0 := by
  have hp : Cycle12.Phase00.threshold 3=(((227787269/25000000):ℚ):ℝ) := by
    norm_num [Cycle12.Phase00.threshold]
  rw [hp]
  have hl : globalLoss (b*(((2311587725257500000000/14597460907219352581):ℚ):ℝ))  ≤  (((75584419291859940845187/1000000000000000000000000):ℚ):ℝ) := by
    have he : b*(((2311587725257500000000/14597460907219352581):ℚ):ℝ)=(((13888667319631906663815/116779687257754820648):ℚ):ℝ) := by norm_num [b]
    rw [he]
    exact loss_bound
  have h0 : (2:ℝ)^((rho-s-alpha)*(((2311587725257500000000/14597460907219352581):ℚ):ℝ)-growth*((((2311587725257500000000/14597460907219352581):ℚ):ℝ)-wA))  ≤  (((40667387876477/1000000000000000000000000):ℚ):ℝ) := by
    have he : (rho-s-alpha)*(((2311587725257500000000/14597460907219352581):ℚ):ℝ)-growth*((((2311587725257500000000/14597460907219352581):ℚ):ℝ)-wA)=(((-20154618933510405361587/583898436288774103240):ℚ):ℝ) := by norm_num [rho,s,alpha,lam,growth,wA]
    rw [he]
    exact feeTerm0
  have h1 : (2:ℝ)^((rho-s-lam)*(((2311587725257500000000/14597460907219352581):ℚ):ℝ))  ≤  (((122552716957080796659679/500000000000000000000000):ℚ):ℝ) := by
    have he : (rho-s-lam)*(((2311587725257500000000/14597460907219352581):ℚ):ℝ)=(((-236890588223203767309/116779687257754820648):ℚ):ℝ) := by norm_num [rho,s,alpha,lam,growth,wA]
    rw [he]
    exact feeTerm1
  have h2 : (2:ℝ)^(-growth*((((2311587725257500000000/14597460907219352581):ℚ):ℝ)-wA))  ≤  (((1/1):ℚ):ℝ) := by
    have he : -growth*((((2311587725257500000000/14597460907219352581):ℚ):ℝ)-wA)=(((0/1):ℚ):ℝ) := by norm_num [rho,s,alpha,lam,growth,wA]
    rw [he]
    exact feeTerm2
  exact (folding_point_bound (p:=(((227787269/25000000):ℚ):ℝ)) (by norm_num [wA]) hl h0 h1 h2).trans (by
    norm_num [C,eta,sigma,c,kappa])

end
end Cycle12.Global12.FoldAnchors.Phase00.T03
