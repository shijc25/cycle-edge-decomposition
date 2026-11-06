import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy019

def certificate380 : RatLabelEntropyCertificate := ⟨(1061472989336639/62500000000000000),⟨(62500000000000000/1061472989336639),5,14,(2037754500327340979/500000000000000000)⟩,⟨(62500000000000000/61438527010663361),0,3,(53529508206713/3125000000000000)⟩,(86055207127320249/1000000000000000000)⟩
theorem valid380 : certificate380.Valid := by decide +kernel
theorem sound380 : 0 ≤ cappedLabelEntropy (certificate380.rho:ℝ) ∧ cappedLabelEntropy (certificate380.rho:ℝ) ≤ (certificate380.bound:ℝ) := rat_label_entropy_certificate_sound certificate380 valid380

def certificate381 : RatLabelEntropyCertificate := ⟨(4458123103497209/250000000000000000),⟨(250000000000000000/4458123103497209),5,13,(4026733069215853671/1000000000000000000)⟩,⟨(250000000000000000/245541876896502791),0,3,(8996703592307093/500000000000000000)⟩,(17895845359488487/200000000000000000)⟩
theorem valid381 : certificate381.Valid := by decide +kernel
theorem sound381 : 0 ≤ cappedLabelEntropy (certificate381.rho:ℝ) ∧ cappedLabelEntropy (certificate381.rho:ℝ) ≤ (certificate381.bound:ℝ) := rat_label_entropy_certificate_sound certificate381 valid381

def certificate382 : RatLabelEntropyCertificate := ⟨(18582764410933997/1000000000000000000),⟨(1000000000000000000/18582764410933997),5,13,(398552077243691707/100000000000000000)⟩,⟨(1000000000000000000/981417235589066003),0,3,(1875759323369093/100000000000000000)⟩,(46235509433396019/500000000000000000)⟩
theorem valid382 : certificate382.Valid := by decide +kernel
theorem sound382 : 0 ≤ cappedLabelEntropy (certificate382.rho:ℝ) ∧ cappedLabelEntropy (certificate382.rho:ℝ) ≤ (certificate382.bound:ℝ) := rat_label_entropy_certificate_sound certificate382 valid382

def certificate383 : RatLabelEntropyCertificate := ⟨(386828636916971/20000000000000000),⟨(20000000000000000/386828636916971),5,12,(986376439058695477/250000000000000000)⟩,⟨(20000000000000000/19613171363083029),0,3,(19530924693440581/1000000000000000000)⟩,(95464899326214177/1000000000000000000)⟩
theorem valid383 : certificate383.Valid := by decide +kernel
theorem sound383 : 0 ≤ cappedLabelEntropy (certificate383.rho:ℝ) ∧ cappedLabelEntropy (certificate383.rho:ℝ) ≤ (certificate383.bound:ℝ) := rat_label_entropy_certificate_sound certificate383 valid383

def certificate384 : RatLabelEntropyCertificate := ⟨(20239774309014273/1000000000000000000),⟨(1000000000000000000/20239774309014273),5,11,(3900105585365443757/1000000000000000000)⟩,⟨(1000000000000000000/979760225690985727),0,3,(4089480983158881/200000000000000000)⟩,(98970810884216279/1000000000000000000)⟩
theorem valid384 : certificate384.Valid := by decide +kernel
theorem sound384 : 0 ≤ cappedLabelEntropy (certificate384.rho:ℝ) ∧ cappedLabelEntropy (certificate384.rho:ℝ) ≤ (certificate384.bound:ℝ) := rat_label_entropy_certificate_sound certificate384 valid384

def certificate385 : RatLabelEntropyCertificate := ⟨(10517683327702621/500000000000000000),⟨(500000000000000000/10517683327702621),5,12,(120673441605049403/31250000000000000)⟩,⟨(500000000000000000/489482316672297379),0,3,(166091893676411/7812500000000000)⟩,(51020839182553541/500000000000000000)⟩
theorem valid385 : certificate385.Valid := by decide +kernel
theorem sound385 : 0 ≤ cappedLabelEntropy (certificate385.rho:ℝ) ∧ cappedLabelEntropy (certificate385.rho:ℝ) ≤ (certificate385.bound:ℝ) := rat_label_entropy_certificate_sound certificate385 valid385

def certificate386 : RatLabelEntropyCertificate := ⟨(21992643139220211/1000000000000000000),⟨(1000000000000000000/21992643139220211),5,10,(3817047284311610751/1000000000000000000)⟩,⟨(1000000000000000000/978007356860779789),0,3,(11119043311538449/500000000000000000)⟩,(52847985544635693/500000000000000000)⟩
theorem valid386 : certificate386.Valid := by decide +kernel
theorem sound386 : 0 ≤ cappedLabelEntropy (certificate386.rho:ℝ) ∧ cappedLabelEntropy (certificate386.rho:ℝ) ≤ (certificate386.bound:ℝ) := rat_label_entropy_certificate_sound certificate386 valid386

def certificate387 : RatLabelEntropyCertificate := ⟨(11409830196632553/500000000000000000),⟨(500000000000000000/11409830196632553),5,10,(3780132816636810847/1000000000000000000)⟩,⟨(500000000000000000/488590169803367447),0,3,(23084058909892783/1000000000000000000)⟩,(21763727128431921/200000000000000000)⟩
theorem valid387 : certificate387.Valid := by decide +kernel
theorem sound387 : 0 ≤ cappedLabelEntropy (certificate387.rho:ℝ) ∧ cappedLabelEntropy (certificate387.rho:ℝ) ≤ (certificate387.bound:ℝ) := rat_label_entropy_certificate_sound certificate387 valid387

def certificate388 : RatLabelEntropyCertificate := ⟨(11911931257275859/500000000000000000),⟨(500000000000000000/11911931257275859),5,9,(1868533786968634099/500000000000000000)⟩,⟨(500000000000000000/488088068742724141),0,4,(6028060029119331/250000000000000000)⟩,(4502767100483813/40000000000000000)⟩
theorem valid388 : certificate388.Valid := by decide +kernel
theorem sound388 : 0 ≤ cappedLabelEntropy (certificate388.rho:ℝ) ∧ cappedLabelEntropy (certificate388.rho:ℝ) ≤ (certificate388.bound:ℝ) := rat_label_entropy_certificate_sound certificate388 valid388

def certificate389 : RatLabelEntropyCertificate := ⟨(6039609813084243/250000000000000000),⟨(250000000000000000/6039609813084243),5,8,(3723121508484965133/1000000000000000000)⟩,⟨(250000000000000000/243960390186915757),0,3,(1528440065398191/62500000000000000)⟩,(22761810042928423/200000000000000000)⟩
theorem valid389 : certificate389.Valid := by decide +kernel
theorem sound389 : 0 ≤ cappedLabelEntropy (certificate389.rho:ℝ) ∧ cappedLabelEntropy (certificate389.rho:ℝ) ≤ (certificate389.bound:ℝ) := rat_label_entropy_certificate_sound certificate389 valid389

def certificate390 : RatLabelEntropyCertificate := ⟨(771004308279847/31250000000000000),⟨(31250000000000000/771004308279847),5,8,(1851040346852612989/500000000000000000)⟩,⟨(31250000000000000/30478995691720153),0,4,(499631913070679/20000000000000000)⟩,(57851745771883681/500000000000000000)⟩
theorem valid390 : certificate390.Valid := by decide +kernel
theorem sound390 : 0 ≤ cappedLabelEntropy (certificate390.rho:ℝ) ∧ cappedLabelEntropy (certificate390.rho:ℝ) ≤ (certificate390.bound:ℝ) := rat_label_entropy_certificate_sound certificate390 valid390

def certificate391 : RatLabelEntropyCertificate := ⟨(393662936930521/15625000000000000),⟨(15625000000000000/393662936930521),5,8,(3681132421471151987/1000000000000000000)⟩,⟨(15625000000000000/15231337063069479),0,3,(6379310291429247/250000000000000000)⟩,(5880918724419717/50000000000000000)⟩
theorem valid391 : certificate391.Valid := by decide +kernel
theorem sound391 : 0 ≤ cappedLabelEntropy (certificate391.rho:ℝ) ∧ cappedLabelEntropy (certificate391.rho:ℝ) ≤ (certificate391.bound:ℝ) := rat_label_entropy_certificate_sound certificate391 valid391

def certificate392 : RatLabelEntropyCertificate := ⟨(25544821643442893/1000000000000000000),⟨(1000000000000000000/25544821643442893),5,7,(916830164569317001/250000000000000000)⟩,⟨(1000000000000000000/974455178356557107),0,3,(12938377797788797/500000000000000000)⟩,(23779358122836799/200000000000000000)⟩
theorem valid392 : certificate392.Valid := by decide +kernel
theorem sound392 : 0 ≤ cappedLabelEntropy (certificate392.rho:ℝ) ∧ cappedLabelEntropy (certificate392.rho:ℝ) ≤ (certificate392.bound:ℝ) := rat_label_entropy_certificate_sound certificate392 valid392

def certificate393 : RatLabelEntropyCertificate := ⟨(13313693316077/500000000000000),⟨(500000000000000/13313693316077),5,7,(3625815020203514597/1000000000000000000)⟩,⟨(500000000000000/486686306683923),0,4,(1686769812647941/62500000000000000)⟩,(122815667050624143/1000000000000000000)⟩
theorem valid393 : certificate393.Valid := by decide +kernel
theorem sound393 : 0 ≤ cappedLabelEntropy (certificate393.rho:ℝ) ∧ cappedLabelEntropy (certificate393.rho:ℝ) ≤ (certificate393.bound:ℝ) := rat_label_entropy_certificate_sound certificate393 valid393

def certificate394 : RatLabelEntropyCertificate := ⟨(6882851312215891/250000000000000000),⟨(250000000000000000/6882851312215891),5,6,(718485583371264647/200000000000000000)⟩,⟨(250000000000000000/243117148687784109),0,4,(27917497326002819/1000000000000000000)⟩,(31513369549972187/250000000000000000)⟩
theorem valid394 : certificate394.Valid := by decide +kernel
theorem sound394 : 0 ≤ cappedLabelEntropy (certificate394.rho:ℝ) ∧ cappedLabelEntropy (certificate394.rho:ℝ) ≤ (certificate394.bound:ℝ) := rat_label_entropy_certificate_sound certificate394 valid394

def certificate395 : RatLabelEntropyCertificate := ⟨(7019114590047393/250000000000000000),⟨(250000000000000000/7019114590047393),5,6,(3572823834553052737/1000000000000000000)⟩,⟨(250000000000000000/242980885409952607),0,4,(14239069240009291/500000000000000000)⟩,(511963251319721/4000000000000000)⟩
theorem valid395 : certificate395.Valid := by decide +kernel
theorem sound395 : 0 ≤ cappedLabelEntropy (certificate395.rho:ℝ) ∧ cappedLabelEntropy (certificate395.rho:ℝ) ≤ (certificate395.bound:ℝ) := rat_label_entropy_certificate_sound certificate395 valid395

def certificate396 : RatLabelEntropyCertificate := ⟨(28433971537209159/1000000000000000000),⟨(1000000000000000000/28433971537209159),5,6,(1780085333890840809/500000000000000000)⟩,⟨(1000000000000000000/971566028462790841),0,4,(901438968601567/31250000000000000)⟩,(16156953843917183/125000000000000000)⟩
theorem valid396 : certificate396.Valid := by decide +kernel
theorem sound396 : 0 ≤ cappedLabelEntropy (certificate396.rho:ℝ) ∧ cappedLabelEntropy (certificate396.rho:ℝ) ≤ (certificate396.bound:ℝ) := rat_label_entropy_certificate_sound certificate396 valid396

def certificate397 : RatLabelEntropyCertificate := ⟨(3624886649159447/125000000000000000),⟨(125000000000000000/3624886649159447),5,5,(3540490718681948501/1000000000000000000)⟩,⟨(125000000000000000/121375113350840553),0,4,(29427876801727697/1000000000000000000)⟩,(131245515360859209/1000000000000000000)⟩
theorem valid397 : certificate397.Valid := by decide +kernel
theorem sound397 : 0 ≤ cappedLabelEntropy (certificate397.rho:ℝ) ∧ cappedLabelEntropy (certificate397.rho:ℝ) ≤ (certificate397.bound:ℝ) := rat_label_entropy_certificate_sound certificate397 valid397

def certificate398 : RatLabelEntropyCertificate := ⟨(29573639683627821/1000000000000000000),⟨(1000000000000000000/29573639683627821),5,4,(3520871865657241667/1000000000000000000)⟩,⟨(1000000000000000000/970426360316372179),0,4,(30019757339160023/1000000000000000000)⟩,(133256959779391487/1000000000000000000)⟩
theorem valid398 : certificate398.Valid := by decide +kernel
theorem sound398 : 0 ≤ cappedLabelEntropy (certificate398.rho:ℝ) ∧ cappedLabelEntropy (certificate398.rho:ℝ) ≤ (certificate398.bound:ℝ) := rat_label_entropy_certificate_sound certificate398 valid398

def certificate399 : RatLabelEntropyCertificate := ⟨(29933198514104553/1000000000000000000),⟨(1000000000000000000/29933198514104553),5,4,(3508787096335379897/1000000000000000000)⟩,⟨(1000000000000000000/970066801485895447),0,4,(30390342344734311/1000000000000000000)⟩,(33627470723188301/250000000000000000)⟩
theorem valid399 : certificate399.Valid := by decide +kernel
theorem sound399 : 0 ≤ cappedLabelEntropy (certificate399.rho:ℝ) ∧ cappedLabelEntropy (certificate399.rho:ℝ) ≤ (certificate399.bound:ℝ) := rat_label_entropy_certificate_sound certificate399 valid399

end Cycle12.CutLabelCertificates.Entropy019
