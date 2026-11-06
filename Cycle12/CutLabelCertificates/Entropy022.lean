import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy022

def certificate440 : RatLabelEntropyCertificate := ⟨(152229762109961/1000000000000000000),⟨(1000000000000000000/152229762109961),12,12,(4395059792797882229/500000000000000000)⟩,⟨(1000000000000000000/999847770237890039),0,1,(152241350236251/1000000000000000000)⟩,(745167994002537/500000000000000000)⟩
theorem valid440 : certificate440.Valid := by decide +kernel
theorem sound440 : 0 ≤ cappedLabelEntropy (certificate440.rho:ℝ) ∧ cappedLabelEntropy (certificate440.rho:ℝ) ≤ (certificate440.bound:ℝ) := rat_label_entropy_certificate_sound certificate440 valid440

def certificate441 : RatLabelEntropyCertificate := ⟨(120612383884489/1000000000000000000),⟨(1000000000000000000/120612383884489),13,3,(9022928593333633807/1000000000000000000)⟩,⟨(1000000000000000000/999879387616115511),0,1,(120619658142979/1000000000000000000)⟩,(302220509294989/250000000000000000)⟩
theorem valid441 : certificate441.Valid := by decide +kernel
theorem sound441 : 0 ≤ cappedLabelEntropy (certificate441.rho:ℝ) ∧ cappedLabelEntropy (certificate441.rho:ℝ) ≤ (certificate441.bound:ℝ) := rat_label_entropy_certificate_sound certificate441 valid441

def certificate442 : RatLabelEntropyCertificate := ⟨(20060575206299/62500000000000000),⟨(62500000000000000/20060575206299),11,11,(804416537930972927/100000000000000000)⟩,⟨(62500000000000000/62479939424793701),0,1,(160510362470193/500000000000000000)⟩,(725711760047713/250000000000000000)⟩
theorem valid442 : certificate442.Valid := by decide +kernel
theorem sound442 : 0 ≤ cappedLabelEntropy (certificate442.rho:ℝ) ∧ cappedLabelEntropy (certificate442.rho:ℝ) ≤ (certificate442.bound:ℝ) := rat_label_entropy_certificate_sound certificate442 valid442

def certificate443 : RatLabelEntropyCertificate := ⟨(22345626185063283/250000000000000000),⟨(250000000000000000/22345626185063283),3,9,(603707578092865331/250000000000000000)⟩,⟨(250000000000000000/227654373814936717),0,5,(93632343373700291/1000000000000000000)⟩,(30110683184070861/100000000000000000)⟩
theorem valid443 : certificate443.Valid := by decide +kernel
theorem sound443 : 0 ≤ cappedLabelEntropy (certificate443.rho:ℝ) ∧ cappedLabelEntropy (certificate443.rho:ℝ) ≤ (certificate443.bound:ℝ) := rat_label_entropy_certificate_sound certificate443 valid443

def certificate444 : RatLabelEntropyCertificate := ⟨(184840772540153/1000000000000000000),⟨(1000000000000000000/184840772540153),12,8,(8596015792463514543/1000000000000000000)⟩,⟨(1000000000000000000/999815159227459847),0,1,(184857857701139/1000000000000000000)⟩,(1773717888278223/1000000000000000000)⟩
theorem valid444 : certificate444.Valid := by decide +kernel
theorem sound444 : 0 ≤ cappedLabelEntropy (certificate444.rho:ℝ) ∧ cappedLabelEntropy (certificate444.rho:ℝ) ≤ (certificate444.bound:ℝ) := rat_label_entropy_certificate_sound certificate444 valid444

def certificate445 : RatLabelEntropyCertificate := ⟨(7317159305781/50000000000000000),⟨(50000000000000000/7317159305781),12,12,(8829556104737606833/1000000000000000000)⟩,⟨(50000000000000000/49992682840694219),0,1,(36588473831127/250000000000000000)⟩,(1438477849783091/1000000000000000000)⟩
theorem valid445 : certificate445.Valid := by decide +kernel
theorem sound445 : 0 ≤ cappedLabelEntropy (certificate445.rho:ℝ) ∧ cappedLabelEntropy (certificate445.rho:ℝ) ≤ (certificate445.bound:ℝ) := rat_label_entropy_certificate_sound certificate445 valid445

def certificate446 : RatLabelEntropyCertificate := ⟨(70405841320511/200000000000000000),⟨(200000000000000000/70405841320511),11,9,(7951796412505558027/1000000000000000000)⟩,⟨(200000000000000000/199929594158679489),0,1,(70418236685847/200000000000000000)⟩,(196951988700541/62500000000000000)⟩
theorem valid446 : certificate446.Valid := by decide +kernel
theorem sound446 : 0 ≤ cappedLabelEntropy (certificate446.rho:ℝ) ∧ cappedLabelEntropy (certificate446.rho:ℝ) ≤ (certificate446.bound:ℝ) := rat_label_entropy_certificate_sound certificate446 valid446

def certificate447 : RatLabelEntropyCertificate := ⟨(89261420339759423/1000000000000000000),⟨(1000000000000000000/89261420339759423),3,9,(483237181503908121/200000000000000000)⟩,⟨(1000000000000000000/910738579660240577),0,5,(93499382661251561/1000000000000000000)⟩,(150412840437061187/500000000000000000)⟩
theorem valid447 : certificate447.Valid := by decide +kernel
theorem sound447 : 0 ≤ cappedLabelEntropy (certificate447.rho:ℝ) ∧ cappedLabelEntropy (certificate447.rho:ℝ) ≤ (certificate447.bound:ℝ) := rat_label_entropy_certificate_sound certificate447 valid447

def certificate448 : RatLabelEntropyCertificate := ⟨(219212044929871/1000000000000000000),⟨(1000000000000000000/219212044929871),12,6,(131647985232851489/15625000000000000)⟩,⟨(1000000000000000000/999780787955070129),0,1,(219236075402103/1000000000000000000)⟩,(1033076377828153/500000000000000000)⟩
theorem valid448 : certificate448.Valid := by decide +kernel
theorem sound448 : 0 ≤ cappedLabelEntropy (certificate448.rho:ℝ) ∧ cappedLabelEntropy (certificate448.rho:ℝ) ≤ (certificate448.bound:ℝ) := rat_label_entropy_certificate_sound certificate448 valid448

def certificate449 : RatLabelEntropyCertificate := ⟨(34928861901559/200000000000000000),⟨(200000000000000000/34928861901559),12,10,(8652759169505086549/1000000000000000000)⟩,⟨(200000000000000000/199965071138098441),0,1,(174659561601037/1000000000000000000)⟩,(42144605219949/25000000000000000)⟩
theorem valid449 : certificate449.Valid := by decide +kernel
theorem sound449 : 0 ≤ cappedLabelEntropy (certificate449.rho:ℝ) ∧ cappedLabelEntropy (certificate449.rho:ℝ) ≤ (certificate449.bound:ℝ) := rat_label_entropy_certificate_sound certificate449 valid449

def certificate450 : RatLabelEntropyCertificate := ⟨(193231398549207/500000000000000000),⟨(500000000000000000/193231398549207),11,8,(314338998018398171/40000000000000000)⟩,⟨(500000000000000000/499806768601450793),0,1,(19326874654531/50000000000000000)⟩,(213962270063277/62500000000000000)⟩
theorem valid450 : certificate450.Valid := by decide +kernel
theorem sound450 : 0 ≤ cappedLabelEntropy (certificate450.rho:ℝ) ∧ cappedLabelEntropy (certificate450.rho:ℝ) ≤ (certificate450.bound:ℝ) := rat_label_entropy_certificate_sound certificate450 valid450

def certificate451 : RatLabelEntropyCertificate := ⟨(44570929579311873/500000000000000000),⟨(500000000000000000/44570929579311873),3,10,(2417526255066642501/1000000000000000000)⟩,⟨(500000000000000000/455429070420688127),0,5,(46684055957021/500000000000000)⟩,(300547889773319601/1000000000000000000)⟩
theorem valid451 : certificate451.Valid := by decide +kernel
theorem sound451 : 0 ≤ cappedLabelEntropy (certificate451.rho:ℝ) ∧ cappedLabelEntropy (certificate451.rho:ℝ) ≤ (certificate451.bound:ℝ) := rat_label_entropy_certificate_sound certificate451 valid451

def certificate452 : RatLabelEntropyCertificate := ⟨(259673852371707/1000000000000000000),⟨(1000000000000000000/259673852371707),11,14,(4128042064169743581/500000000000000000)⟩,⟨(1000000000000000000/999740326147628293),0,1,(129853786732147/500000000000000000)⟩,(75110290790907/31250000000000000)⟩
theorem valid452 : certificate452.Valid := by decide +kernel
theorem sound452 : 0 ≤ cappedLabelEntropy (certificate452.rho:ℝ) ∧ cappedLabelEntropy (certificate452.rho:ℝ) ≤ (certificate452.bound:ℝ) := rat_label_entropy_certificate_sound certificate452 valid452

def certificate453 : RatLabelEntropyCertificate := ⟨(207010054402851/1000000000000000000),⟨(1000000000000000000/207010054402851),12,7,(4241371596942018441/500000000000000000)⟩,⟨(1000000000000000000/999792989945597149),0,1,(103515741970817/500000000000000000)⟩,(1963001756394229/1000000000000000000)⟩
theorem valid453 : certificate453.Valid := by decide +kernel
theorem sound453 : 0 ≤ cappedLabelEntropy (certificate453.rho:ℝ) ∧ cappedLabelEntropy (certificate453.rho:ℝ) ≤ (certificate453.bound:ℝ) := rat_label_entropy_certificate_sound certificate453 valid453

def certificate454 : RatLabelEntropyCertificate := ⟨(403030375809821/1000000000000000000),⟨(1000000000000000000/403030375809821),11,8,(7816498624640166639/1000000000000000000)⟩,⟨(1000000000000000000/999596969624190179),0,2,(25194475898763/62500000000000000)⟩,(3553235526360447/1000000000000000000)⟩
theorem valid454 : certificate454.Valid := by decide +kernel
theorem sound454 : 0 ≤ cappedLabelEntropy (certificate454.rho:ℝ) ∧ cappedLabelEntropy (certificate454.rho:ℝ) ≤ (certificate454.bound:ℝ) := rat_label_entropy_certificate_sound certificate454 valid454

def certificate455 : RatLabelEntropyCertificate := ⟨(7062642543839969/1000000000000000000),⟨(1000000000000000000/7062642543839969),7,5,(1238233999878669013/250000000000000000)⟩,⟨(1000000000000000000/992937357456160031),0,3,(3543850529810703/500000000000000000)⟩,(10504614916917149/250000000000000000)⟩
theorem valid455 : certificate455.Valid := by decide +kernel
theorem sound455 : 0 ≤ cappedLabelEntropy (certificate455.rho:ℝ) ∧ cappedLabelEntropy (certificate455.rho:ℝ) ≤ (certificate455.bound:ℝ) := rat_label_entropy_certificate_sound certificate455 valid455

def certificate456 : RatLabelEntropyCertificate := ⟨(92443239604212619/1000000000000000000),⟨(1000000000000000000/92443239604212619),3,9,(1190580224354793757/500000000000000000)⟩,⟨(1000000000000000000/907556760395787381),0,5,(6062448056773067/62500000000000000)⟩,(308154437391698051/1000000000000000000)⟩
theorem valid456 : certificate456.Valid := by decide +kernel
theorem sound456 : 0 ≤ cappedLabelEntropy (certificate456.rho:ℝ) ∧ cappedLabelEntropy (certificate456.rho:ℝ) ≤ (certificate456.bound:ℝ) := rat_label_entropy_certificate_sound certificate456 valid456

def certificate457 : RatLabelEntropyCertificate := ⟨(149379404738687/500000000000000000),⟨(500000000000000000/149379404738687),11,12,(2028968491840734201/250000000000000000)⟩,⟨(500000000000000000/499850620595261313),0,1,(298803446781241/1000000000000000000)⟩,(170212688811061/62500000000000000)⟩
theorem valid457 : certificate457.Valid := by decide +kernel
theorem sound457 : 0 ≤ cappedLabelEntropy (certificate457.rho:ℝ) ∧ cappedLabelEntropy (certificate457.rho:ℝ) ≤ (certificate457.bound:ℝ) := rat_label_entropy_certificate_sound certificate457 valid457

def certificate458 : RatLabelEntropyCertificate := ⟨(240759325551751/1000000000000000000),⟨(1000000000000000000/240759325551751),12,3,(8331712772618786441/1000000000000000000)⟩,⟨(1000000000000000000/999759240674448249),0,1,(240788312730887/1000000000000000000)⟩,(1123333944262861/500000000000000000)⟩
theorem valid458 : certificate458.Valid := by decide +kernel
theorem sound458 : 0 ≤ cappedLabelEntropy (certificate458.rho:ℝ) ∧ cappedLabelEntropy (certificate458.rho:ℝ) ≤ (certificate458.bound:ℝ) := rat_label_entropy_certificate_sound certificate458 valid458

def certificate459 : RatLabelEntropyCertificate := ⟨(44577308027827/100000000000000000),⟨(100000000000000000/44577308027827),11,5,(1543140104806960119/200000000000000000)⟩,⟨(100000000000000000/99955422691972173),0,1,(11146811665869/25000000000000000)⟩,(3885125297795553/1000000000000000000)⟩
theorem valid459 : certificate459.Valid := by decide +kernel
theorem sound459 : 0 ≤ cappedLabelEntropy (certificate459.rho:ℝ) ∧ cappedLabelEntropy (certificate459.rho:ℝ) ≤ (certificate459.bound:ℝ) := rat_label_entropy_certificate_sound certificate459 valid459

end Cycle12.CutLabelCertificates.Entropy022
