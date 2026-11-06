import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy014

def certificate280 : RatLabelEntropyCertificate := ⟨(9415455929374787/200000000000000000),⟨(200000000000000000/9415455929374787),4,9,(3055964779761729261/1000000000000000000)⟩,⟨(200000000000000000/190584544070625213),0,4,(3013841846006307/62500000000000000)⟩,(94908921228803561/500000000000000000)⟩
theorem valid280 : certificate280.Valid := by decide +kernel
theorem sound280 : 0 ≤ cappedLabelEntropy (certificate280.rho:ℝ) ∧ cappedLabelEntropy (certificate280.rho:ℝ) ≤ (certificate280.bound:ℝ) := rat_label_entropy_certificate_sound certificate280 valid280

def certificate281 : RatLabelEntropyCertificate := ⟨(49681576696995347/1000000000000000000),⟨(1000000000000000000/49681576696995347),4,8,(1501060552401725633/500000000000000000)⟩,⟨(1000000000000000000/950318423303004653),0,5,(2547908406220737/50000000000000000)⟩,(49394148977091079/250000000000000000)⟩
theorem valid281 : certificate281.Valid := by decide +kernel
theorem sound281 : 0 ≤ cappedLabelEntropy (certificate281.rho:ℝ) ∧ cappedLabelEntropy (certificate281.rho:ℝ) ≤ (certificate281.bound:ℝ) := rat_label_entropy_certificate_sound certificate281 valid281

def certificate282 : RatLabelEntropyCertificate := ⟨(26019902489636641/500000000000000000),⟨(500000000000000000/26019902489636641),4,7,(591149274572148137/200000000000000000)⟩,⟨(500000000000000000/473980097510363359),0,4,(26721382991706289/500000000000000000)⟩,(51119519918987541/250000000000000000)⟩
theorem valid282 : certificate282.Valid := by decide +kernel
theorem sound282 : 0 ≤ cappedLabelEntropy (certificate282.rho:ℝ) ∧ cappedLabelEntropy (certificate282.rho:ℝ) ≤ (certificate282.bound:ℝ) := rat_label_entropy_certificate_sound certificate282 valid282

def certificate283 : RatLabelEntropyCertificate := ⟨(5484730426157351/100000000000000000),⟨(100000000000000000/5484730426157351),4,6,(1451601120466574833/500000000000000000)⟩,⟨(100000000000000000/94515269573842649),0,5,(56408781749501843/1000000000000000000)⟩,(8501909151008189/40000000000000000)⟩
theorem valid283 : certificate283.Valid := by decide +kernel
theorem sound283 : 0 ≤ cappedLabelEntropy (certificate283.rho:ℝ) ∧ cappedLabelEntropy (certificate283.rho:ℝ) ≤ (certificate283.bound:ℝ) := rat_label_entropy_certificate_sound certificate283 valid283

def certificate284 : RatLabelEntropyCertificate := ⟨(57320774346407921/1000000000000000000),⟨(1000000000000000000/57320774346407921),4,5,(2859092166929744909/1000000000000000000)⟩,⟨(1000000000000000000/942679225653592079),0,5,(3689326118337667/62500000000000000)⟩,(54882748587713087/250000000000000000)⟩
theorem valid284 : certificate284.Valid := by decide +kernel
theorem sound284 : 0 ≤ cappedLabelEntropy (certificate284.rho:ℝ) ∧ cappedLabelEntropy (certificate284.rho:ℝ) ≤ (certificate284.bound:ℝ) := rat_label_entropy_certificate_sound certificate284 valid284

def certificate285 : RatLabelEntropyCertificate := ⟨(59875833746068471/1000000000000000000),⟨(1000000000000000000/59875833746068471),4,4,(703870574642561261/250000000000000000)⟩,⟨(1000000000000000000/940124166253931529),0,5,(6174332068193413/100000000000000000)⟩,(56656434475510789/250000000000000000)⟩
theorem valid285 : certificate285.Valid := by decide +kernel
theorem sound285 : 0 ≤ cappedLabelEntropy (certificate285.rho:ℝ) ∧ cappedLabelEntropy (certificate285.rho:ℝ) ≤ (certificate285.bound:ℝ) := rat_label_entropy_certificate_sound certificate285 valid285

def certificate286 : RatLabelEntropyCertificate := ⟨(62839649500036041/1000000000000000000),⟨(1000000000000000000/62839649500036041),3,17,(2767169043267241261/1000000000000000000)⟩,⟨(1000000000000000000/937160350499963959),0,5,(64900879581501447/1000000000000000000)⟩,(117355231921309679/500000000000000000)⟩
theorem valid286 : certificate286.Valid := by decide +kernel
theorem sound286 : 0 ≤ cappedLabelEntropy (certificate286.rho:ℝ) ∧ cappedLabelEntropy (certificate286.rho:ℝ) ≤ (certificate286.bound:ℝ) := rat_label_entropy_certificate_sound certificate286 valid286

def certificate287 : RatLabelEntropyCertificate := ⟨(65404959426181037/1000000000000000000),⟨(1000000000000000000/65404959426181037),3,15,(2727157191189497301/1000000000000000000)⟩,⟨(1000000000000000000/934595040573818963),0,5,(33820977599581/500000000000000)⟩,(120793720651210083/500000000000000000)⟩
theorem valid287 : certificate287.Valid := by decide +kernel
theorem sound287 : 0 ≤ cappedLabelEntropy (certificate287.rho:ℝ) ∧ cappedLabelEntropy (certificate287.rho:ℝ) ≤ (certificate287.bound:ℝ) := rat_label_entropy_certificate_sound certificate287 valid287

def certificate288 : RatLabelEntropyCertificate := ⟨(536129640116737/7812500000000000),⟨(7812500000000000/536129640116737),3,14,(669776074082314757/250000000000000000)⟩,⟨(7812500000000000/7276370359883263),0,5,(14218570824769397/200000000000000000)⟩,(250066580322876719/1000000000000000000)⟩
theorem valid288 : certificate288.Valid := by decide +kernel
theorem sound288 : 0 ≤ cappedLabelEntropy (certificate288.rho:ℝ) ∧ cappedLabelEntropy (certificate288.rho:ℝ) ≤ (certificate288.bound:ℝ) := rat_label_entropy_certificate_sound certificate288 valid288

def certificate289 : RatLabelEntropyCertificate := ⟨(35643703776955837/500000000000000000),⟨(500000000000000000/35643703776955837),3,13,(330129447413343741/125000000000000000)⟩,⟨(500000000000000000/464356296223044163),0,5,(36977980536871291/500000000000000000)⟩,(256956412042058967/1000000000000000000)⟩
theorem valid289 : certificate289.Valid := by decide +kernel
theorem sound289 : 0 ≤ cappedLabelEntropy (certificate289.rho:ℝ) ∧ cappedLabelEntropy (certificate289.rho:ℝ) ≤ (certificate289.bound:ℝ) := rat_label_entropy_certificate_sound certificate289 valid289

def certificate290 : RatLabelEntropyCertificate := ⟨(582870173971899/7812500000000000),⟨(7812500000000000/582870173971899),3,12,(648878954661738749/250000000000000000)⟩,⟨(7812500000000000/7229629826028101),0,5,(77537179922085051/1000000000000000000)⟩,(132698487382552309/500000000000000000)⟩
theorem valid290 : certificate290.Valid := by decide +kernel
theorem sound290 : 0 ≤ cappedLabelEntropy (certificate290.rho:ℝ) ∧ cappedLabelEntropy (certificate290.rho:ℝ) ≤ (certificate290.bound:ℝ) := rat_label_entropy_certificate_sound certificate290 valid290

def certificate291 : RatLabelEntropyCertificate := ⟨(18910589108701557/250000000000000000),⟨(250000000000000000/18910589108701557),3,12,(2581738882387786671/1000000000000000000)⟩,⟨(250000000000000000/231089410891298443),0,5,(39328111046706221/500000000000000000)⟩,(267995292869182493/1000000000000000000)⟩
theorem valid291 : certificate291.Valid := by decide +kernel
theorem sound291 : 0 ≤ cappedLabelEntropy (certificate291.rho:ℝ) ∧ cappedLabelEntropy (certificate291.rho:ℝ) ≤ (certificate291.bound:ℝ) := rat_label_entropy_certificate_sound certificate291 valid291

def certificate292 : RatLabelEntropyCertificate := ⟨(77375146218873251/1000000000000000000),⟨(1000000000000000000/77375146218873251),3,12,(1279544829118025479/500000000000000000)⟩,⟨(1000000000000000000/922624853781126749),0,5,(40266284686651197/500000000000000000)⟩,(136155643267941193/500000000000000000)⟩
theorem valid292 : certificate292.Valid := by decide +kernel
theorem sound292 : 0 ≤ cappedLabelEntropy (certificate292.rho:ℝ) ∧ cappedLabelEntropy (certificate292.rho:ℝ) ≤ (certificate292.bound:ℝ) := rat_label_entropy_certificate_sound certificate292 valid292

def certificate293 : RatLabelEntropyCertificate := ⟨(19776658756296413/250000000000000000),⟨(250000000000000000/19776658756296413),3,11,(634239631561224057/250000000000000000)⟩,⟨(250000000000000000/230223341243703587),0,5,(2060275780409057/25000000000000000)⟩,(276582024057568209/1000000000000000000)⟩
theorem valid293 : certificate293.Valid := by decide +kernel
theorem sound293 : 0 ≤ cappedLabelEntropy (certificate293.rho:ℝ) ∧ cappedLabelEntropy (certificate293.rho:ℝ) ≤ (certificate293.bound:ℝ) := rat_label_entropy_certificate_sound certificate293 valid293

def certificate294 : RatLabelEntropyCertificate := ⟨(31421714616237/390625000000000),⟨(390625000000000/31421714616237),3,12,(2520248818297988247/1000000000000000000)⟩,⟨(390625000000000/359203285383763),0,5,(83859537713127007/1000000000000000000)⟩,(139920845552367003/500000000000000000)⟩
theorem valid294 : certificate294.Valid := by decide +kernel
theorem sound294 : 0 ≤ cappedLabelEntropy (certificate294.rho:ℝ) ∧ cappedLabelEntropy (certificate294.rho:ℝ) ≤ (certificate294.bound:ℝ) := rat_label_entropy_certificate_sound certificate294 valid294

def certificate295 : RatLabelEntropyCertificate := ⟨(16396294497761351/200000000000000000),⟨(200000000000000000/16396294497761351),3,11,(2501262002505813637/1000000000000000000)⟩,⟨(200000000000000000/183603705502238649),0,6,(42768853045621631/500000000000000000)⟩,(141791170519148209/500000000000000000)⟩
theorem valid295 : certificate295.Valid := by decide +kernel
theorem sound295 : 0 ≤ cappedLabelEntropy (certificate295.rho:ℝ) ∧ cappedLabelEntropy (certificate295.rho:ℝ) ≤ (certificate295.bound:ℝ) := rat_label_entropy_certificate_sound certificate295 valid295

def certificate296 : RatLabelEntropyCertificate := ⟨(10470152176800223/125000000000000000),⟨(125000000000000000/10470152176800223),3,11,(2479785177969586047/1000000000000000000)⟩,⟨(125000000000000000/114529847823199777),0,5,(2733695893764061/31250000000000000)⟩,(57572161551618749/200000000000000000)⟩
theorem valid296 : certificate296.Valid := by decide +kernel
theorem sound296 : 0 ≤ cappedLabelEntropy (certificate296.rho:ℝ) ∧ cappedLabelEntropy (certificate296.rho:ℝ) ≤ (certificate296.bound:ℝ) := rat_label_entropy_certificate_sound certificate296 valid296

def certificate297 : RatLabelEntropyCertificate := ⟨(87434773479867019/1000000000000000000),⟨(1000000000000000000/87434773479867019),3,10,(1218431104772964669/500000000000000000)⟩,⟨(1000000000000000000/912565226520132981),0,5,(18299142992437981/200000000000000000)⟩,(296562303143388921/1000000000000000000)⟩
theorem valid297 : certificate297.Valid := by decide +kernel
theorem sound297 : 0 ≤ cappedLabelEntropy (certificate297.rho:ℝ) ∧ cappedLabelEntropy (certificate297.rho:ℝ) ≤ (certificate297.bound:ℝ) := rat_label_entropy_certificate_sound certificate297 valid297

def certificate298 : RatLabelEntropyCertificate := ⟨(22090894744377449/250000000000000000),⟨(250000000000000000/22090894744377449),3,9,(303286924593969113/125000000000000000)⟩,⟨(250000000000000000/227909105255622551),0,5,(92514029553842097/1000000000000000000)⟩,(298735303710475479/1000000000000000000)⟩
theorem valid298 : certificate298.Valid := by decide +kernel
theorem sound298 : 0 ≤ cappedLabelEntropy (certificate298.rho:ℝ) ∧ cappedLabelEntropy (certificate298.rho:ℝ) ≤ (certificate298.bound:ℝ) := rat_label_entropy_certificate_sound certificate298 valid298

def certificate299 : RatLabelEntropyCertificate := ⟨(90387268344052403/1000000000000000000),⟨(1000000000000000000/90387268344052403),3,10,(2403651858404529187/1000000000000000000)⟩,⟨(1000000000000000000/909612731655947597),0,5,(47368169830267939/500000000000000000)⟩,(151716453118498079/500000000000000000)⟩
theorem valid299 : certificate299.Valid := by decide +kernel
theorem sound299 : 0 ≤ cappedLabelEntropy (certificate299.rho:ℝ) ∧ cappedLabelEntropy (certificate299.rho:ℝ) ≤ (certificate299.bound:ℝ) := rat_label_entropy_certificate_sound certificate299 valid299

end Cycle12.CutLabelCertificates.Entropy014
