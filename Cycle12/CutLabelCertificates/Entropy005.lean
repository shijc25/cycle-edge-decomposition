import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy005

def certificate100 : RatLabelEntropyCertificate := ⟨(90681524223415999/62500000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid100 : certificate100.Valid := by decide +kernel
theorem sound100 : 0 ≤ cappedLabelEntropy (certificate100.rho:ℝ) ∧ cappedLabelEntropy (certificate100.rho:ℝ) ≤ (certificate100.bound:ℝ) := rat_label_entropy_certificate_sound certificate100 valid100

def certificate101 : RatLabelEntropyCertificate := ⟨(726749994225033979/500000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid101 : certificate101.Valid := by decide +kernel
theorem sound101 : 0 ≤ cappedLabelEntropy (certificate101.rho:ℝ) ∧ cappedLabelEntropy (certificate101.rho:ℝ) ≤ (certificate101.bound:ℝ) := rat_label_entropy_certificate_sound certificate101 valid101

def certificate102 : RatLabelEntropyCertificate := ⟨(2268279131877791/1562500000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid102 : certificate102.Valid := by decide +kernel
theorem sound102 : 0 ≤ cappedLabelEntropy (certificate102.rho:ℝ) ∧ cappedLabelEntropy (certificate102.rho:ℝ) ≤ (certificate102.bound:ℝ) := rat_label_entropy_certificate_sound certificate102 valid102

def certificate103 : RatLabelEntropyCertificate := ⟨(181919524406903377/125000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid103 : certificate103.Valid := by decide +kernel
theorem sound103 : 0 ≤ cappedLabelEntropy (certificate103.rho:ℝ) ∧ cappedLabelEntropy (certificate103.rho:ℝ) ≤ (certificate103.bound:ℝ) := rat_label_entropy_certificate_sound certificate103 valid103

def certificate104 : RatLabelEntropyCertificate := ⟨(1455539756424112271/1000000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid104 : certificate104.Valid := by decide +kernel
theorem sound104 : 0 ≤ cappedLabelEntropy (certificate104.rho:ℝ) ∧ cappedLabelEntropy (certificate104.rho:ℝ) ≤ (certificate104.bound:ℝ) := rat_label_entropy_certificate_sound certificate104 valid104

def certificate105 : RatLabelEntropyCertificate := ⟨(1457755849111309407/1000000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid105 : certificate105.Valid := by decide +kernel
theorem sound105 : 0 ≤ cappedLabelEntropy (certificate105.rho:ℝ) ∧ cappedLabelEntropy (certificate105.rho:ℝ) ≤ (certificate105.bound:ℝ) := rat_label_entropy_certificate_sound certificate105 valid105

def certificate106 : RatLabelEntropyCertificate := ⟨(36502466971941923/25000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid106 : certificate106.Valid := by decide +kernel
theorem sound106 : 0 ≤ cappedLabelEntropy (certificate106.rho:ℝ) ∧ cappedLabelEntropy (certificate106.rho:ℝ) ≤ (certificate106.bound:ℝ) := rat_label_entropy_certificate_sound certificate106 valid106

def certificate107 : RatLabelEntropyCertificate := ⟨(1459743206984645613/1000000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid107 : certificate107.Valid := by decide +kernel
theorem sound107 : 0 ≤ cappedLabelEntropy (certificate107.rho:ℝ) ∧ cappedLabelEntropy (certificate107.rho:ℝ) ≤ (certificate107.bound:ℝ) := rat_label_entropy_certificate_sound certificate107 valid107

def certificate108 : RatLabelEntropyCertificate := ⟨(730567686038212161/500000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid108 : certificate108.Valid := by decide +kernel
theorem sound108 : 0 ≤ cappedLabelEntropy (certificate108.rho:ℝ) ∧ cappedLabelEntropy (certificate108.rho:ℝ) ≤ (certificate108.bound:ℝ) := rat_label_entropy_certificate_sound certificate108 valid108

def certificate109 : RatLabelEntropyCertificate := ⟨(1466671825125291763/1000000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid109 : certificate109.Valid := by decide +kernel
theorem sound109 : 0 ≤ cappedLabelEntropy (certificate109.rho:ℝ) ∧ cappedLabelEntropy (certificate109.rho:ℝ) ≤ (certificate109.bound:ℝ) := rat_label_entropy_certificate_sound certificate109 valid109

def certificate110 : RatLabelEntropyCertificate := ⟨(1465525777410708881/1000000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid110 : certificate110.Valid := by decide +kernel
theorem sound110 : 0 ≤ cappedLabelEntropy (certificate110.rho:ℝ) ∧ cappedLabelEntropy (certificate110.rho:ℝ) ≤ (certificate110.bound:ℝ) := rat_label_entropy_certificate_sound certificate110 valid110

def certificate111 : RatLabelEntropyCertificate := ⟨(1467522896407304481/1000000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid111 : certificate111.Valid := by decide +kernel
theorem sound111 : 0 ≤ cappedLabelEntropy (certificate111.rho:ℝ) ∧ cappedLabelEntropy (certificate111.rho:ℝ) ≤ (certificate111.bound:ℝ) := rat_label_entropy_certificate_sound certificate111 valid111

def certificate112 : RatLabelEntropyCertificate := ⟨(1469887073642918433/1000000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid112 : certificate112.Valid := by decide +kernel
theorem sound112 : 0 ≤ cappedLabelEntropy (certificate112.rho:ℝ) ∧ cappedLabelEntropy (certificate112.rho:ℝ) ≤ (certificate112.bound:ℝ) := rat_label_entropy_certificate_sound certificate112 valid112

def certificate113 : RatLabelEntropyCertificate := ⟨(147164091751246659/100000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid113 : certificate113.Valid := by decide +kernel
theorem sound113 : 0 ≤ cappedLabelEntropy (certificate113.rho:ℝ) ∧ cappedLabelEntropy (certificate113.rho:ℝ) ≤ (certificate113.bound:ℝ) := rat_label_entropy_certificate_sound certificate113 valid113

def certificate114 : RatLabelEntropyCertificate := ⟨(368413679019128993/250000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid114 : certificate114.Valid := by decide +kernel
theorem sound114 : 0 ≤ cappedLabelEntropy (certificate114.rho:ℝ) ∧ cappedLabelEntropy (certificate114.rho:ℝ) ≤ (certificate114.bound:ℝ) := rat_label_entropy_certificate_sound certificate114 valid114

def certificate115 : RatLabelEntropyCertificate := ⟨(368979443809480281/250000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid115 : certificate115.Valid := by decide +kernel
theorem sound115 : 0 ≤ cappedLabelEntropy (certificate115.rho:ℝ) ∧ cappedLabelEntropy (certificate115.rho:ℝ) ≤ (certificate115.bound:ℝ) := rat_label_entropy_certificate_sound certificate115 valid115

def certificate116 : RatLabelEntropyCertificate := ⟨(737849288326602389/500000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid116 : certificate116.Valid := by decide +kernel
theorem sound116 : 0 ≤ cappedLabelEntropy (certificate116.rho:ℝ) ∧ cappedLabelEntropy (certificate116.rho:ℝ) ≤ (certificate116.bound:ℝ) := rat_label_entropy_certificate_sound certificate116 valid116

def certificate117 : RatLabelEntropyCertificate := ⟨(296236711591295629/200000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid117 : certificate117.Valid := by decide +kernel
theorem sound117 : 0 ≤ cappedLabelEntropy (certificate117.rho:ℝ) ∧ cappedLabelEntropy (certificate117.rho:ℝ) ≤ (certificate117.bound:ℝ) := rat_label_entropy_certificate_sound certificate117 valid117

def certificate118 : RatLabelEntropyCertificate := ⟨(740824507963772581/500000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid118 : certificate118.Valid := by decide +kernel
theorem sound118 : 0 ≤ cappedLabelEntropy (certificate118.rho:ℝ) ∧ cappedLabelEntropy (certificate118.rho:ℝ) ≤ (certificate118.bound:ℝ) := rat_label_entropy_certificate_sound certificate118 valid118

def certificate119 : RatLabelEntropyCertificate := ⟨(1480787779058735909/1000000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid119 : certificate119.Valid := by decide +kernel
theorem sound119 : 0 ≤ cappedLabelEntropy (certificate119.rho:ℝ) ∧ cappedLabelEntropy (certificate119.rho:ℝ) ≤ (certificate119.bound:ℝ) := rat_label_entropy_certificate_sound certificate119 valid119

end Cycle12.CutLabelCertificates.Entropy005
