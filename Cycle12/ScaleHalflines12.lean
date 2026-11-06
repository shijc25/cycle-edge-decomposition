import Cycle12.LinearPowerEnvelope
import Cycle12.ScaleEndpointCertificates12

namespace Cycle12.Global12
open Real
noncomputable section

theorem log_two_lower : (69/100:ℝ)≤log 2 := by
  have hh := Cycle13.log_two_24_digits.1
  norm_num at hh
  linarith only [hh]

theorem entropy_base0 : (1001/1000:ℝ)+(rho-s)*w0≤(2:ℝ)^((theta0-s)*w0) := by
  have he : (theta0-s)*w0=(((29374029300399668672799/5000000000000000000000):ℚ):ℝ) := by norm_num [rho,s,theta0,theta1,theta2,w0,wA]
  rw [he]
  exact (show (1001/1000:ℝ)+(rho-s)*w0≤(((58680361761946101470726977/1000000000000000000000000):ℚ):ℝ) by
    norm_num [rho,s,theta0,theta1,theta2,w0,wA]).trans entropyPoint0.1

theorem entropy_slope0 : rho-s≤log 2*(theta0-s)*((1001/1000:ℝ)+(rho-s)*w0) := by
  have hh := log_two_lower
  norm_num [rho,s,theta0,theta1,theta2,w0,wA]
  nlinarith only [hh]

theorem entropy_halfline0 {w : ℝ} (hw : w0≤w) :
    (2:ℝ)^(s*w)*((1001/1000:ℝ)+(rho-s)*w)≤(2:ℝ)^(theta0*w) := by
  exact entropy_rate_halfline (by norm_num [rho,s,theta0,theta1,theta2,w0,wA]) entropy_base0 entropy_slope0 hw

theorem entropy_base1 : (1001/1000:ℝ)+(rho-s)*(w0/theta1)≤(2:ℝ)^((theta1-s)*(w0/theta1)) := by
  have he : (theta1-s)*(w0/theta1)=(((21937435430753467253871/4023922936400000000000):ℚ):ℝ) := by norm_num [rho,s,theta0,theta1,theta2,w0,wA]
  rw [he]
  exact (show (1001/1000:ℝ)+(rho-s)*(w0/theta1)≤(((10941611796109088420236209/250000000000000000000000):ℚ):ℝ) by
    norm_num [rho,s,theta0,theta1,theta2,w0,wA]).trans entropyPoint1.1

theorem entropy_slope1 : rho-s≤log 2*(theta1-s)*((1001/1000:ℝ)+(rho-s)*(w0/theta1)) := by
  have hh := log_two_lower
  norm_num [rho,s,theta0,theta1,theta2,w0,wA]
  nlinarith only [hh]

theorem entropy_halfline1 {w : ℝ} (hw : (w0/theta1)≤w) :
    (2:ℝ)^(s*w)*((1001/1000:ℝ)+(rho-s)*w)≤(2:ℝ)^(theta1*w) := by
  exact entropy_rate_halfline (by norm_num [rho,s,theta0,theta1,theta2,w0,wA]) entropy_base1 entropy_slope1 hw

theorem entropy_base2 : (1001/1000:ℝ)+(rho-s)*wA≤(2:ℝ)^((theta2-s)*wA) := by
  have he : (theta2-s)*wA=(((3369360930445557049803/583898436288774103240):ℚ):ℝ) := by norm_num [rho,s,theta0,theta1,theta2,w0,wA]
  rw [he]
  exact (show (1001/1000:ℝ)+(rho-s)*wA≤(((10917185729129118228174991/200000000000000000000000):ℚ):ℝ) by
    norm_num [rho,s,theta0,theta1,theta2,w0,wA]).trans entropyPoint2.1

theorem entropy_slope2 : rho-s≤log 2*(theta2-s)*((1001/1000:ℝ)+(rho-s)*wA) := by
  have hh := log_two_lower
  norm_num [rho,s,theta0,theta1,theta2,w0,wA]
  nlinarith only [hh]

theorem entropy_halfline2 {w : ℝ} (hw : wA≤w) :
    (2:ℝ)^(s*w)*((1001/1000:ℝ)+(rho-s)*w)≤(2:ℝ)^(theta2*w) := by
  exact entropy_rate_halfline (by norm_num [rho,s,theta0,theta1,theta2,w0,wA]) entropy_base2 entropy_slope2 hw

theorem overlap_base_positive : 0<1-(2:ℝ)^(-delta*w0)-2*(2:ℝ)^(-rho*w0) := by
  have h1 := dfsDeltaPoint.2
  have h2 := dfsOrderPoint.2
  have hde : -delta*w0=(((-35138194233034754854443/5000000000000000000000):ℚ):ℝ) := by norm_num [delta,w0]
  have hre : -rho*w0=(((-1118837691750425709098157/10000000000000000000000):ℚ):ℝ) := by norm_num [rho,w0]
  rw [hde,hre]
  generalize (2:ℝ)^(((-35138194233034754854443/5000000000000000000000):ℚ):ℝ)=x at h1 ⊢
  generalize (2:ℝ)^(((-1118837691750425709098157/10000000000000000000000):ℚ):ℝ)=y at h2 ⊢
  linarith only [h1,h2]

theorem overlap_base_coefficient :
    2≤overlap*(1-(2:ℝ)^(-delta*w0)-2*(2:ℝ)^(-rho*w0)) := by
  have h1 := dfsDeltaPoint.2
  have h2 := dfsOrderPoint.2
  have hde : -delta*w0=(((-35138194233034754854443/5000000000000000000000):ℚ):ℝ) := by norm_num [delta,w0]
  have hre : -rho*w0=(((-1118837691750425709098157/10000000000000000000000):ℚ):ℝ) := by norm_num [rho,w0]
  rw [hde,hre]
  generalize (2:ℝ)^(((-35138194233034754854443/5000000000000000000000):ℚ):ℝ)=x at h1 ⊢
  generalize (2:ℝ)^(((-1118837691750425709098157/10000000000000000000000):ℚ):ℝ)=y at h2 ⊢
  unfold overlap
  linarith only [h1,h2]

theorem overlap_halfline {w : ℝ} (hw : w0≤w) :
    (2:ℝ)^((1+eps)*w)+2<(2:ℝ)^(rho*w) ∧
    2*(2:ℝ)^((1+eps)*w)/((2:ℝ)^(rho*w)-(2:ℝ)^((1+eps)*w)-2)≤
      overlap*(2:ℝ)^(-delta*w) := by
  have he : rho-1-eps=delta := by norm_num [rho,eps,delta]
  have hh := power_overlap_bound
    (eps:=eps) (rho:=rho) (w0:=w0) (w:=w) (chi:=overlap)
    (by norm_num [rho,eps]) (by norm_num [rho]) hw (by norm_num [overlap])
    (by simpa only [he] using overlap_base_positive)
    (by simpa only [he] using overlap_base_coefficient)
  simpa only [he] using hh

end
end Cycle12.Global12
