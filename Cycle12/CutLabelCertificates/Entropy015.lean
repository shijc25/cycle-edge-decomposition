import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy015

def certificate300 : RatLabelEntropyCertificate := ⟨(47113474562935679/500000000000000000),⟨(500000000000000000/47113474562935679),3,9,(1181024527087661023/500000000000000000)⟩,⟨(500000000000000000/452886525437064321),0,6,(98966500042371757/1000000000000000000)⟩,(156104932369152139/500000000000000000)⟩
theorem valid300 : certificate300.Valid := by decide +kernel
theorem sound300 : 0 ≤ cappedLabelEntropy (certificate300.rho:ℝ) ∧ cappedLabelEntropy (certificate300.rho:ℝ) ≤ (certificate300.bound:ℝ) := rat_label_entropy_certificate_sound certificate300 valid300

def certificate301 : RatLabelEntropyCertificate := ⟨(48659503022969541/500000000000000000),⟨(500000000000000000/48659503022969541),3,9,(2329760974374837241/1000000000000000000)⟩,⟨(500000000000000000/451340496977030459),0,5,(12798257695563389/125000000000000000)⟩,(159575987085434333/500000000000000000)⟩
theorem valid301 : certificate301.Valid := by decide +kernel
theorem sound301 : 0 ≤ cappedLabelEntropy (certificate301.rho:ℝ) ∧ cappedLabelEntropy (certificate301.rho:ℝ) ≤ (certificate301.bound:ℝ) := rat_label_entropy_certificate_sound certificate301 valid301

def certificate302 : RatLabelEntropyCertificate := ⟨(99221585519392613/1000000000000000000),⟨(1000000000000000000/99221585519392613),3,8,(2310399692400258433/1000000000000000000)⟩,⟨(1000000000000000000/900778414480607387),0,5,(104495984494157209/1000000000000000000)⟩,(64673849579141539/200000000000000000)⟩
theorem valid302 : certificate302.Valid := by decide +kernel
theorem sound302 : 0 ≤ cappedLabelEntropy (certificate302.rho:ℝ) ∧ cappedLabelEntropy (certificate302.rho:ℝ) ≤ (certificate302.bound:ℝ) := rat_label_entropy_certificate_sound certificate302 valid302

def certificate303 : RatLabelEntropyCertificate := ⟨(3140128943942533/31250000000000000),⟨(31250000000000000/3140128943942533),3,7,(574438878038884801/250000000000000000)⟩,⟨(31250000000000000/28109871056057467),0,6,(105898578394467133/1000000000000000000)⟩,(326145407152363893/1000000000000000000)⟩
theorem valid303 : certificate303.Valid := by decide +kernel
theorem sound303 : 0 ≤ cappedLabelEntropy (certificate303.rho:ℝ) ∧ cappedLabelEntropy (certificate303.rho:ℝ) ≤ (certificate303.bound:ℝ) := rat_label_entropy_certificate_sound certificate303 valid303

def certificate304 : RatLabelEntropyCertificate := ⟨(10231761387322933/100000000000000000),⟨(100000000000000000/10231761387322933),3,7,(2279673442221651687/1000000000000000000)⟩,⟨(100000000000000000/89768238612677067),0,6,(107938963525090233/1000000000000000000)⟩,(330145653351543997/1000000000000000000)⟩
theorem valid304 : certificate304.Valid := by decide +kernel
theorem sound304 : 0 ≤ cappedLabelEntropy (certificate304.rho:ℝ) ∧ cappedLabelEntropy (certificate304.rho:ℝ) ≤ (certificate304.bound:ℝ) := rat_label_entropy_certificate_sound certificate304 valid304

def certificate305 : RatLabelEntropyCertificate := ⟨(104378108535081541/1000000000000000000),⟨(1000000000000000000/104378108535081541),3,7,(112986765694128241/50000000000000000)⟩,⟨(1000000000000000000/895621891464918459),0,6,(22047390241107181/200000000000000000)⟩,(66919504920203779/200000000000000000)⟩
theorem valid305 : certificate305.Valid := by decide +kernel
theorem sound305 : 0 ≤ cappedLabelEntropy (certificate305.rho:ℝ) ∧ cappedLabelEntropy (certificate305.rho:ℝ) ≤ (certificate305.bound:ℝ) := rat_label_entropy_certificate_sound certificate305 valid305

def certificate306 : RatLabelEntropyCertificate := ⟨(106408914181029927/1000000000000000000),⟨(1000000000000000000/106408914181029927),3,7,(560116481421758697/250000000000000000)⟩,⟨(1000000000000000000/893591085818970073),0,6,(22501401371994193/200000000000000000)⟩,(84735201208549307/250000000000000000)⟩
theorem valid306 : certificate306.Valid := by decide +kernel
theorem sound306 : 0 ≤ cappedLabelEntropy (certificate306.rho:ℝ) ∧ cappedLabelEntropy (certificate306.rho:ℝ) ≤ (certificate306.bound:ℝ) := rat_label_entropy_certificate_sound certificate306 valid306

def certificate307 : RatLabelEntropyCertificate := ⟨(54240241553286131/500000000000000000),⟨(500000000000000000/54240241553286131),3,6,(2221185001383925803/1000000000000000000)⟩,⟨(500000000000000000/445759758446713869),0,6,(114827949721794427/1000000000000000000)⟩,(85831645070259407/250000000000000000)⟩
theorem valid307 : certificate307.Valid := by decide +kernel
theorem sound307 : 0 ≤ cappedLabelEntropy (certificate307.rho:ℝ) ∧ cappedLabelEntropy (certificate307.rho:ℝ) ≤ (certificate307.bound:ℝ) := rat_label_entropy_certificate_sound certificate307 valid307

def certificate308 : RatLabelEntropyCertificate := ⟨(54832352634944713/500000000000000000),⟨(500000000000000000/54832352634944713),3,6,(138145481382613179/62500000000000000)⟩,⟨(500000000000000000/445167647365055287),0,6,(116157151551199271/1000000000000000000)⟩,(345813747764407461/1000000000000000000)⟩
theorem valid308 : certificate308.Valid := by decide +kernel
theorem sound308 : 0 ≤ cappedLabelEntropy (certificate308.rho:ℝ) ∧ cappedLabelEntropy (certificate308.rho:ℝ) ≤ (certificate308.bound:ℝ) := rat_label_entropy_certificate_sound certificate308 valid308

def certificate309 : RatLabelEntropyCertificate := ⟨(111736201072270221/1000000000000000000),⟨(1000000000000000000/111736201072270221),3,6,(2191614533450410029/1000000000000000000)⟩,⟨(1000000000000000000/888263798927729779),0,6,(23697301848443743/200000000000000000)⟩,(175064979501851733/500000000000000000)⟩
theorem valid309 : certificate309.Valid := by decide +kernel
theorem sound309 : 0 ≤ cappedLabelEntropy (certificate309.rho:ℝ) ∧ cappedLabelEntropy (certificate309.rho:ℝ) ≤ (certificate309.bound:ℝ) := rat_label_entropy_certificate_sound certificate309 valid309

def certificate310 : RatLabelEntropyCertificate := ⟨(711587355682637/6250000000000000),⟨(6250000000000000/711587355682637),3,5,(16975301218373741/7812500000000000)⟩,⟨(6250000000000000/5538412644317363),0,6,(120873530342124557/1000000000000000000)⟩,(177248954493211967/500000000000000000)⟩
theorem valid310 : certificate310.Valid := by decide +kernel
theorem sound310 : 0 ≤ cappedLabelEntropy (certificate310.rho:ℝ) ∧ cappedLabelEntropy (certificate310.rho:ℝ) ≤ (certificate310.bound:ℝ) := rat_label_entropy_certificate_sound certificate310 valid310

def certificate311 : RatLabelEntropyCertificate := ⟨(116002132788897637/1000000000000000000),⟨(1000000000000000000/116002132788897637),3,5,(2154146701933608351/1000000000000000000)⟩,⟨(1000000000000000000/883997867211102363),0,6,(123300629004528103/1000000000000000000)⟩,(71776620966051713/200000000000000000)⟩
theorem valid311 : certificate311.Valid := by decide +kernel
theorem sound311 : 0 ≤ cappedLabelEntropy (certificate311.rho:ℝ) ∧ cappedLabelEntropy (certificate311.rho:ℝ) ≤ (certificate311.bound:ℝ) := rat_label_entropy_certificate_sound certificate311 valid311

def certificate312 : RatLabelEntropyCertificate := ⟨(29539772764097847/250000000000000000),⟨(250000000000000000/29539772764097847),3,4,(2135723333270054041/1000000000000000000)⟩,⟨(250000000000000000/220460227235902153),0,6,(125743614592317699/1000000000000000000)⟩,(181620495596530147/500000000000000000)⟩
theorem valid312 : certificate312.Valid := by decide +kernel
theorem sound312 : 0 ≤ cappedLabelEntropy (certificate312.rho:ℝ) ∧ cappedLabelEntropy (certificate312.rho:ℝ) ≤ (certificate312.bound:ℝ) := rat_label_entropy_certificate_sound certificate312 valid312

def certificate313 : RatLabelEntropyCertificate := ⟨(11933672840703037/100000000000000000),⟨(100000000000000000/11933672840703037),3,5,(2125806131316006311/1000000000000000000)⟩,⟨(100000000000000000/88066327159296963),0,6,(1588499221164443/12500000000000000)⟩,(45700172827692899/125000000000000000)⟩
theorem valid313 : certificate313.Valid := by decide +kernel
theorem sound313 : 0 ≤ cappedLabelEntropy (certificate313.rho:ℝ) ∧ cappedLabelEntropy (certificate313.rho:ℝ) ≤ (certificate313.bound:ℝ) := rat_label_entropy_certificate_sound certificate313 valid313

def certificate314 : RatLabelEntropyCertificate := ⟨(30101741681722529/250000000000000000),⟨(250000000000000000/30101741681722529),3,4,(2116877884601275157/1000000000000000000)⟩,⟨(250000000000000000/219898258318277471),0,6,(32073985167037937/250000000000000000)⟩,(73547012125000361/200000000000000000)⟩
theorem valid314 : certificate314.Valid := by decide +kernel
theorem sound314 : 0 ≤ cappedLabelEntropy (certificate314.rho:ℝ) ∧ cappedLabelEntropy (certificate314.rho:ℝ) ≤ (certificate314.bound:ℝ) := rat_label_entropy_certificate_sound certificate314 valid314

def certificate315 : RatLabelEntropyCertificate := ⟨(15188363798597513/125000000000000000),⟨(125000000000000000/15188363798597513),3,4,(1053892071095535657/500000000000000000)⟩,⟨(125000000000000000/109811636201402487),0,6,(506043896518007/3906250000000000)⟩,(369916691813639373/1000000000000000000)⟩
theorem valid315 : certificate315.Valid := by decide +kernel
theorem sound315 : 0 ≤ cappedLabelEntropy (certificate315.rho:ℝ) ∧ cappedLabelEntropy (certificate315.rho:ℝ) ≤ (certificate315.bound:ℝ) := rat_label_entropy_certificate_sound certificate315 valid315

def certificate316 : RatLabelEntropyCertificate := ⟨(30651203162804759/250000000000000000),⟨(250000000000000000/30651203162804759),3,3,(2098789001346572297/1000000000000000000)⟩,⟨(250000000000000000/219348796837195241),0,6,(2043715240515099/15625000000000000)⟩,(74416594190050213/200000000000000000)⟩
theorem valid316 : certificate316.Valid := by decide +kernel
theorem sound316 : 0 ≤ cappedLabelEntropy (certificate316.rho:ℝ) ∧ cappedLabelEntropy (certificate316.rho:ℝ) ≤ (certificate316.bound:ℝ) := rat_label_entropy_certificate_sound certificate316 valid316

def certificate317 : RatLabelEntropyCertificate := ⟨(15465249466064187/125000000000000000),⟨(125000000000000000/15465249466064187),3,3,(2089718200285724771/1000000000000000000)⟩,⟨(125000000000000000/109534750533935813),0,6,(132071881918360177/1000000000000000000)⟩,(374275791357347431/1000000000000000000)⟩
theorem valid317 : certificate317.Valid := by decide +kernel
theorem sound317 : 0 ≤ cappedLabelEntropy (certificate317.rho:ℝ) ∧ cappedLabelEntropy (certificate317.rho:ℝ) ≤ (certificate317.bound:ℝ) := rat_label_entropy_certificate_sound certificate317 valid317

def certificate318 : RatLabelEntropyCertificate := ⟨(24968711337512169/200000000000000000),⟨(200000000000000000/24968711337512169),3,2,(1040346936008872223/500000000000000000)⟩,⟨(200000000000000000/175031288662487831),0,6,(133352616248897899/1000000000000000000)⟩,(47058203087937727/125000000000000000)⟩
theorem valid318 : certificate318.Valid := by decide +kernel
theorem sound318 : 0 ≤ cappedLabelEntropy (certificate318.rho:ℝ) ∧ cappedLabelEntropy (certificate318.rho:ℝ) ≤ (certificate318.bound:ℝ) := rat_label_entropy_certificate_sound certificate318 valid318

def certificate319 : RatLabelEntropyCertificate := ⟨(62990007780174409/500000000000000000),⟨(500000000000000000/62990007780174409),2,16,(2071631991273924373/1000000000000000000)⟩,⟨(500000000000000000/437009992219825591),0,6,(134652038096421219/1000000000000000000)⟩,(47334100342225849/125000000000000000)⟩
theorem valid319 : certificate319.Valid := by decide +kernel
theorem sound319 : 0 ≤ cappedLabelEntropy (certificate319.rho:ℝ) ∧ cappedLabelEntropy (certificate319.rho:ℝ) ≤ (certificate319.bound:ℝ) := rat_label_entropy_certificate_sound certificate319 valid319

end Cycle12.CutLabelCertificates.Entropy015
