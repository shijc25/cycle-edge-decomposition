import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy003

def certificate60 : RatLabelEntropyCertificate := ⟨(66642689790204293/250000000000000000),⟨(250000000000000000/66642689790204293),1,15,(661057778909979689/500000000000000000)⟩,⟨(250000000000000000/183357310209795707),0,9,(62004830778532711/200000000000000000)⟩,(579818127777700061/1000000000000000000)⟩
theorem valid60 : certificate60.Valid := by decide +kernel
theorem sound60 : 0 ≤ cappedLabelEntropy (certificate60.rho:ℝ) ∧ cappedLabelEntropy (certificate60.rho:ℝ) ≤ (certificate60.bound:ℝ) := rat_label_entropy_certificate_sound certificate60 valid60

def certificate61 : RatLabelEntropyCertificate := ⟨(136110929950737707/500000000000000000),⟨(500000000000000000/136110929950737707),1,14,(650568941877320731/500000000000000000)⟩,⟨(500000000000000000/363889070049262293),0,9,(1588795149219409/5000000000000000)⟩,(23418250017730003/40000000000000000)⟩
theorem valid61 : certificate61.Valid := by decide +kernel
theorem sound61 : 0 ≤ cappedLabelEntropy (certificate61.rho:ℝ) ∧ cappedLabelEntropy (certificate61.rho:ℝ) ≤ (certificate61.bound:ℝ) := rat_label_entropy_certificate_sound certificate61 valid61

def certificate62 : RatLabelEntropyCertificate := ⟨(136460496359518109/500000000000000000),⟨(500000000000000000/136460496359518109),1,15,(649286464821079459/500000000000000000)⟩,⟨(500000000000000000/363539503640481891),0,9,(31872013158866383/100000000000000000)⟩,(586142529951949029/1000000000000000000)⟩
theorem valid62 : certificate62.Valid := by decide +kernel
theorem sound62 : 0 ≤ cappedLabelEntropy (certificate62.rho:ℝ) ∧ cappedLabelEntropy (certificate62.rho:ℝ) ≤ (certificate62.bound:ℝ) := rat_label_entropy_certificate_sound certificate62 valid62

def certificate63 : RatLabelEntropyCertificate := ⟨(69346172255492957/250000000000000000),⟨(250000000000000000/69346172255492957),1,14,(160293745901277597/125000000000000000)⟩,⟨(250000000000000000/180653827744507043),0,9,(81219567940170213/250000000000000000)⟩,(590466260250291603/1000000000000000000)⟩
theorem valid63 : certificate63.Valid := by decide +kernel
theorem sound63 : 0 ≤ cappedLabelEntropy (certificate63.rho:ℝ) ∧ cappedLabelEntropy (certificate63.rho:ℝ) ≤ (certificate63.bound:ℝ) := rat_label_entropy_certificate_sound certificate63 valid63

def certificate64 : RatLabelEntropyCertificate := ⟨(140170226952360613/500000000000000000),⟨(500000000000000000/140170226952360613),1,14,(1271750507626323051/1000000000000000000)⟩,⟨(500000000000000000/359829773047639387),0,9,(328977031447548509/1000000000000000000)⟩,(593274575688838049/1000000000000000000)⟩
theorem valid64 : certificate64.Valid := by decide +kernel
theorem sound64 : 0 ≤ cappedLabelEntropy (certificate64.rho:ℝ) ∧ cappedLabelEntropy (certificate64.rho:ℝ) ≤ (certificate64.bound:ℝ) := rat_label_entropy_certificate_sound certificate64 valid64

def certificate65 : RatLabelEntropyCertificate := ⟨(283561702334919239/1000000000000000000),⟨(1000000000000000000/283561702334919239),1,13,(1260325534575199917/1000000000000000000)⟩,⟨(1000000000000000000/716438297665080761),0,10,(166731575865231897/500000000000000000)⟩,(119257165368023363/200000000000000000)⟩
theorem valid65 : certificate65.Valid := by decide +kernel
theorem sound65 : 0 ≤ cappedLabelEntropy (certificate65.rho:ℝ) ∧ cappedLabelEntropy (certificate65.rho:ℝ) ≤ (certificate65.bound:ℝ) := rat_label_entropy_certificate_sound certificate65 valid65

def certificate66 : RatLabelEntropyCertificate := ⟨(8963572015422101/31250000000000000),⟨(31250000000000000/8963572015422101),1,13,(624425283102412037/500000000000000000)⟩,⟨(31250000000000000/22286427984577899),0,10,(338041493551966207/1000000000000000000)⟩,(585246855891333/976562500000000)⟩
theorem valid66 : certificate66.Valid := by decide +kernel
theorem sound66 : 0 ≤ cappedLabelEntropy (certificate66.rho:ℝ) ∧ cappedLabelEntropy (certificate66.rho:ℝ) ≤ (certificate66.bound:ℝ) := rat_label_entropy_certificate_sound certificate66 valid66

def certificate67 : RatLabelEntropyCertificate := ⟨(72526702439674817/250000000000000000),⟨(250000000000000000/72526702439674817),1,13,(309376528574540119/250000000000000000)⟩,⟨(250000000000000000/177473297560325183),0,10,(342640756543306193/1000000000000000000)⟩,(301123645322572033/500000000000000000)⟩
theorem valid67 : certificate67.Valid := by decide +kernel
theorem sound67 : 0 ≤ cappedLabelEntropy (certificate67.rho:ℝ) ∧ cappedLabelEntropy (certificate67.rho:ℝ) ≤ (certificate67.bound:ℝ) := rat_label_entropy_certificate_sound certificate67 valid67

def certificate68 : RatLabelEntropyCertificate := ⟨(146716683407820811/500000000000000000),⟨(500000000000000000/146716683407820811),1,13,(38315771721189361/31250000000000000)⟩,⟨(500000000000000000/353283316592179189),0,10,(347337766818887307/1000000000000000000)⟩,(302598652612107811/500000000000000000)⟩
theorem valid68 : certificate68.Valid := by decide +kernel
theorem sound68 : 0 ≤ cappedLabelEntropy (certificate68.rho:ℝ) ∧ cappedLabelEntropy (certificate68.rho:ℝ) ≤ (certificate68.bound:ℝ) := rat_label_entropy_certificate_sound certificate68 valid68

def certificate69 : RatLabelEntropyCertificate := ⟨(296776908670212357/1000000000000000000),⟨(1000000000000000000/296776908670212357),1,13,(1214774571691938077/1000000000000000000)⟩,⟨(1000000000000000000/703223091329787643),0,10,(687658389942599/1953125000000000)⟩,(608108598600115739/1000000000000000000)⟩
theorem valid69 : certificate69.Valid := by decide +kernel
theorem sound69 : 0 ≤ cappedLabelEntropy (certificate69.rho:ℝ) ∧ cappedLabelEntropy (certificate69.rho:ℝ) ≤ (certificate69.bound:ℝ) := rat_label_entropy_certificate_sound certificate69 valid69

def certificate70 : RatLabelEntropyCertificate := ⟨(150060826061701783/500000000000000000),⟨(500000000000000000/150060826061701783),1,13,(120356737944369937/100000000000000000)⟩,⟨(500000000000000000/349939173938298217),0,10,(44606093473683253/125000000000000000)⟩,(38185458900325133/62500000000000000)⟩
theorem valid70 : certificate70.Valid := by decide +kernel
theorem sound70 : 0 ≤ cappedLabelEntropy (certificate70.rho:ℝ) ∧ cappedLabelEntropy (certificate70.rho:ℝ) ≤ (certificate70.bound:ℝ) := rat_label_entropy_certificate_sound certificate70 valid70

def certificate71 : RatLabelEntropyCertificate := ⟨(303573628541551123/1000000000000000000),⟨(1000000000000000000/303573628541551123),1,12,(238426219948957709/200000000000000000)⟩,⟨(1000000000000000000/696426371458448877),0,10,(45224150442743783/125000000000000000)⟩,(306930945803901863/500000000000000000)⟩
theorem valid71 : certificate71.Valid := by decide +kernel
theorem sound71 : 0 ≤ cappedLabelEntropy (certificate71.rho:ℝ) ∧ cappedLabelEntropy (certificate71.rho:ℝ) ≤ (certificate71.bound:ℝ) := rat_label_entropy_certificate_sound certificate71 valid71

def certificate72 : RatLabelEntropyCertificate := ⟨(304411539656241961/1000000000000000000),⟨(1000000000000000000/304411539656241961),1,12,(1189374744198561257/1000000000000000000)⟩,⟨(1000000000000000000/695588460343758039),0,10,(22687317883729793/62500000000000000)⟩,(153638995341725297/250000000000000000)⟩
theorem valid72 : certificate72.Valid := by decide +kernel
theorem sound72 : 0 ≤ cappedLabelEntropy (certificate72.rho:ℝ) ∧ cappedLabelEntropy (certificate72.rho:ℝ) ≤ (certificate72.bound:ℝ) := rat_label_entropy_certificate_sound certificate72 valid72

def certificate73 : RatLabelEntropyCertificate := ⟨(78084005150508109/250000000000000000),⟨(250000000000000000/78084005150508109),1,12,(116367568160028109/100000000000000000)⟩,⟨(250000000000000000/171915994849491891),0,11,(374454962393754659/1000000000000000000)⟩,(124191404241479031/200000000000000000)⟩
theorem valid73 : certificate73.Valid := by decide +kernel
theorem sound73 : 0 ≤ cappedLabelEntropy (certificate73.rho:ℝ) ∧ cappedLabelEntropy (certificate73.rho:ℝ) ≤ (certificate73.bound:ℝ) := rat_label_entropy_certificate_sound certificate73 valid73

def certificate74 : RatLabelEntropyCertificate := ⟨(38899281418905871/125000000000000000),⟨(125000000000000000/38899281418905871),1,12,(58366897968510981/50000000000000000)⟩,⟨(125000000000000000/86100718581094129),0,10,(372795980013847757/1000000000000000000)⟩,(620052876446791823/1000000000000000000)⟩
theorem valid74 : certificate74.Valid := by decide +kernel
theorem sound74 : 0 ≤ cappedLabelEntropy (certificate74.rho:ℝ) ∧ cappedLabelEntropy (certificate74.rho:ℝ) ≤ (certificate74.bound:ℝ) := rat_label_entropy_certificate_sound certificate74 valid74

def certificate75 : RatLabelEntropyCertificate := ⟨(1398665045297796437/1000000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid75 : certificate75.Valid := by decide +kernel
theorem sound75 : 0 ≤ cappedLabelEntropy (certificate75.rho:ℝ) ∧ cappedLabelEntropy (certificate75.rho:ℝ) ≤ (certificate75.bound:ℝ) := rat_label_entropy_certificate_sound certificate75 valid75

def certificate76 : RatLabelEntropyCertificate := ⟨(31812134711327303/100000000000000000),⟨(100000000000000000/31812134711327303),1,11,(286330593573718103/250000000000000000)⟩,⟨(100000000000000000/68187865288672697),0,10,(382903565288378283/1000000000000000000)⟩,(78180657984252677/125000000000000000)⟩
theorem valid76 : certificate76.Valid := by decide +kernel
theorem sound76 : 0 ≤ cappedLabelEntropy (certificate76.rho:ℝ) ∧ cappedLabelEntropy (certificate76.rho:ℝ) ≤ (certificate76.bound:ℝ) := rat_label_entropy_certificate_sound certificate76 valid76

def certificate77 : RatLabelEntropyCertificate := ⟨(700997269895750717/500000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid77 : certificate77.Valid := by decide +kernel
theorem sound77 : 0 ≤ cappedLabelEntropy (certificate77.rho:ℝ) ∧ cappedLabelEntropy (certificate77.rho:ℝ) ≤ (certificate77.bound:ℝ) := rat_label_entropy_certificate_sound certificate77 valid77

def certificate78 : RatLabelEntropyCertificate := ⟨(703207085816960767/500000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid78 : certificate78.Valid := by decide +kernel
theorem sound78 : 0 ≤ cappedLabelEntropy (certificate78.rho:ℝ) ∧ cappedLabelEntropy (certificate78.rho:ℝ) ≤ (certificate78.bound:ℝ) := rat_label_entropy_certificate_sound certificate78 valid78

def certificate79 : RatLabelEntropyCertificate := ⟨(1405337917440630993/1000000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid79 : certificate79.Valid := by decide +kernel
theorem sound79 : 0 ≤ cappedLabelEntropy (certificate79.rho:ℝ) ∧ cappedLabelEntropy (certificate79.rho:ℝ) ≤ (certificate79.bound:ℝ) := rat_label_entropy_certificate_sound certificate79 valid79

end Cycle12.CutLabelCertificates.Entropy003
