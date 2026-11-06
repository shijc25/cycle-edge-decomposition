import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy011

def certificate220 : RatLabelEntropyCertificate := ⟨(219160427910609281/1000000000000000000),⟨(1000000000000000000/219160427910609281),2,6,(758975634905295923/500000000000000000)⟩,⟨(1000000000000000000/780839572089390719),0,8,(49477112740114279/200000000000000000)⟩,(525843287540188911/1000000000000000000)⟩
theorem valid220 : certificate220.Valid := by decide +kernel
theorem sound220 : 0 ≤ cappedLabelEntropy (certificate220.rho:ℝ) ∧ cappedLabelEntropy (certificate220.rho:ℝ) ≤ (certificate220.bound:ℝ) := rat_label_entropy_certificate_sound certificate220 valid220

def certificate221 : RatLabelEntropyCertificate := ⟨(27737274475923557/125000000000000000),⟨(125000000000000000/27737274475923557),2,6,(60221463189313849/40000000000000000)⟩,⟨(125000000000000000/97262725524076443),0,8,(250897909646336729/1000000000000000000)⟩,(529299966928714459/1000000000000000000)⟩
theorem valid221 : certificate221.Valid := by decide +kernel
theorem sound221 : 0 ≤ cappedLabelEntropy (certificate221.rho:ℝ) ∧ cappedLabelEntropy (certificate221.rho:ℝ) ≤ (certificate221.bound:ℝ) := rat_label_entropy_certificate_sound certificate221 valid221

def certificate222 : RatLabelEntropyCertificate := ⟨(28823749839926329/125000000000000000),⟨(125000000000000000/28823749839926329),2,5,(1467114042775438799/1000000000000000000)⟩,⟨(125000000000000000/96176250160073671),0,8,(262131289943396967/1000000000000000000)⟩,(33749266335990587/62500000000000000)⟩
theorem valid222 : certificate222.Valid := by decide +kernel
theorem sound222 : 0 ≤ cappedLabelEntropy (certificate222.rho:ℝ) ∧ cappedLabelEntropy (certificate222.rho:ℝ) ≤ (certificate222.bound:ℝ) := rat_label_entropy_certificate_sound certificate222 valid222

def certificate223 : RatLabelEntropyCertificate := ⟨(9586859399530847/40000000000000000),⟨(40000000000000000/9586859399530847),2,4,(1428486105868682297/1000000000000000000)⟩,⟨(40000000000000000/30413140600469153),0,8,(274004682503348903/1000000000000000000)⟩,(110140191926538269/200000000000000000)⟩
theorem valid223 : certificate223.Valid := by decide +kernel
theorem sound223 : 0 ≤ cappedLabelEntropy (certificate223.rho:ℝ) ∧ cappedLabelEntropy (certificate223.rho:ℝ) ≤ (certificate223.bound:ℝ) := rat_label_entropy_certificate_sound certificate223 valid223

def certificate224 : RatLabelEntropyCertificate := ⟨(49362214008355409/200000000000000000),⟨(200000000000000000/49362214008355409),2,3,(699566066827326201/500000000000000000)⟩,⟨(200000000000000000/150637785991644591),0,9,(70859794913542217/250000000000000000)⟩,(111760910293819869/200000000000000000)⟩
theorem valid224 : certificate224.Valid := by decide +kernel
theorem sound224 : 0 ≤ cappedLabelEntropy (certificate224.rho:ℝ) ∧ cappedLabelEntropy (certificate224.rho:ℝ) ≤ (certificate224.bound:ℝ) := rat_label_entropy_certificate_sound certificate224 valid224

def certificate225 : RatLabelEntropyCertificate := ⟨(7850750751799163/31250000000000000),⟨(31250000000000000/7850750751799163),1,16,(276282042357833661/200000000000000000)⟩,⟨(31250000000000000/23399249248200837),0,9,(289315437743659017/1000000000000000000)⟩,(140918970382904507/250000000000000000)⟩
theorem valid225 : certificate225.Valid := by decide +kernel
theorem sound225 : 0 ≤ cappedLabelEntropy (certificate225.rho:ℝ) ∧ cappedLabelEntropy (certificate225.rho:ℝ) ≤ (certificate225.bound:ℝ) := rat_label_entropy_certificate_sound certificate225 valid225

def certificate226 : RatLabelEntropyCertificate := ⟨(127948212791773477/500000000000000000),⟨(500000000000000000/127948212791773477),1,15,(340745625983618841/250000000000000000)⟩,⟨(500000000000000000/372051787208226523),0,9,(29557504091292513/100000000000000000)⟩,(568720795341341907/1000000000000000000)⟩
theorem valid226 : certificate226.Valid := by decide +kernel
theorem sound226 : 0 ≤ cappedLabelEntropy (certificate226.rho:ℝ) ∧ cappedLabelEntropy (certificate226.rho:ℝ) ≤ (certificate226.bound:ℝ) := rat_label_entropy_certificate_sound certificate226 valid226

def certificate227 : RatLabelEntropyCertificate := ⟨(261232106247669603/1000000000000000000),⟨(1000000000000000000/261232106247669603),1,15,(1342345970880744101/1000000000000000000)⟩,⟨(1000000000000000000/738767893752330397),0,9,(151385744446903929/500000000000000000)⟩,(574341720424585277/1000000000000000000)⟩
theorem valid227 : certificate227.Valid := by decide +kernel
theorem sound227 : 0 ≤ cappedLabelEntropy (certificate227.rho:ℝ) ∧ cappedLabelEntropy (certificate227.rho:ℝ) ≤ (certificate227.bound:ℝ) := rat_label_entropy_certificate_sound certificate227 valid227

def certificate228 : RatLabelEntropyCertificate := ⟨(52805461933532023/200000000000000000),⟨(200000000000000000/52805461933532023),1,15,(665851367737562851/500000000000000000)⟩,⟨(200000000000000000/147194538066467977),0,9,(306562266468400013/1000000000000000000)⟩,(577227346531689103/1000000000000000000)⟩
theorem valid228 : certificate228.Valid := by decide +kernel
theorem sound228 : 0 ≤ cappedLabelEntropy (certificate228.rho:ℝ) ∧ cappedLabelEntropy (certificate228.rho:ℝ) ≤ (certificate228.bound:ℝ) := rat_label_entropy_certificate_sound certificate228 valid228

def certificate229 : RatLabelEntropyCertificate := ⟨(268694550271329367/1000000000000000000),⟨(1000000000000000000/268694550271329367),1,14,(657090022699952427/500000000000000000)⟩,⟨(1000000000000000000/731305449728670633),0,9,(156462027311070071/500000000000000000)⟩,(36372255173165371/62500000000000000)⟩
theorem valid229 : certificate229.Valid := by decide +kernel
theorem sound229 : 0 ≤ cappedLabelEntropy (certificate229.rho:ℝ) ∧ cappedLabelEntropy (certificate229.rho:ℝ) ≤ (certificate229.bound:ℝ) := rat_label_entropy_certificate_sound certificate229 valid229

def certificate230 : RatLabelEntropyCertificate := ⟨(273464507125149633/1000000000000000000),⟨(1000000000000000000/273464507125149633),1,14,(648291719196349331/500000000000000000)⟩,⟨(1000000000000000000/726535492874850367),0,9,(63893588510840743/200000000000000000)⟩,(293337175014011967/500000000000000000)⟩
theorem valid230 : certificate230.Valid := by decide +kernel
theorem sound230 : 0 ≤ cappedLabelEntropy (certificate230.rho:ℝ) ∧ cappedLabelEntropy (certificate230.rho:ℝ) ≤ (certificate230.bound:ℝ) := rat_label_entropy_certificate_sound certificate230 valid230

def certificate231 : RatLabelEntropyCertificate := ⟨(55689654726456393/200000000000000000),⟨(200000000000000000/55689654726456393),1,14,(1278522968885657601/1000000000000000000)⟩,⟨(200000000000000000/144310345273543607),0,10,(163175605260334341/500000000000000000)⟩,(591481792838814181/1000000000000000000)⟩
theorem valid231 : certificate231.Valid := by decide +kernel
theorem sound231 : 0 ≤ cappedLabelEntropy (certificate231.rho:ℝ) ∧ cappedLabelEntropy (certificate231.rho:ℝ) ≤ (certificate231.bound:ℝ) := rat_label_entropy_certificate_sound certificate231 valid231

def certificate232 : RatLabelEntropyCertificate := ⟨(283423558185177187/1000000000000000000),⟨(1000000000000000000/283423558185177187),1,14,(315203207050945447/250000000000000000)⟩,⟨(1000000000000000000/716576441814822813),0,10,(333270349596104559/1000000000000000000)⟩,(596157739250991033/1000000000000000000)⟩
theorem valid232 : certificate232.Valid := by decide +kernel
theorem sound232 : 0 ≤ cappedLabelEntropy (certificate232.rho:ℝ) ∧ cappedLabelEntropy (certificate232.rho:ℝ) ≤ (certificate232.bound:ℝ) := rat_label_entropy_certificate_sound certificate232 valid232

def certificate233 : RatLabelEntropyCertificate := ⟨(289791979338231029/1000000000000000000),⟨(1000000000000000000/289791979338231029),1,13,(1238591926020203457/1000000000000000000)⟩,⟨(1000000000000000000/710208020661768971),0,9,(42774670626434853/125000000000000000)⟩,(601965319114221827/1000000000000000000)⟩
theorem valid233 : certificate233.Valid := by decide +kernel
theorem sound233 : 0 ≤ cappedLabelEntropy (certificate233.rho:ℝ) ∧ cappedLabelEntropy (certificate233.rho:ℝ) ≤ (certificate233.bound:ℝ) := rat_label_entropy_certificate_sound certificate233 valid233

def certificate234 : RatLabelEntropyCertificate := ⟨(146860297374126651/500000000000000000),⟨(500000000000000000/146860297374126651),1,13,(245025264303815221/200000000000000000)⟩,⟨(500000000000000000/353139702625873349),0,10,(347744361633544739/1000000000000000000)⟩,(605449512712511133/1000000000000000000)⟩
theorem valid234 : certificate234.Valid := by decide +kernel
theorem sound234 : 0 ≤ cappedLabelEntropy (certificate234.rho:ℝ) ∧ cappedLabelEntropy (certificate234.rho:ℝ) ≤ (certificate234.bound:ℝ) := rat_label_entropy_certificate_sound certificate234 valid234

def certificate235 : RatLabelEntropyCertificate := ⟨(74059361890696991/250000000000000000),⟨(250000000000000000/74059361890696991),1,13,(1216593958526550743/1000000000000000000)⟩,⟨(250000000000000000/175940638109303009),0,10,(87828565796706621/250000000000000000)⟩,(121528502312434639/200000000000000000)⟩
theorem valid235 : certificate235.Valid := by decide +kernel
theorem sound235 : 0 ≤ cappedLabelEntropy (certificate235.rho:ℝ) ∧ cappedLabelEntropy (certificate235.rho:ℝ) ≤ (certificate235.bound:ℝ) := rat_label_entropy_certificate_sound certificate235 valid235

def certificate236 : RatLabelEntropyCertificate := ⟨(305725468467787949/1000000000000000000),⟨(1000000000000000000/305725468467787949),1,12,(1185067741590311209/1000000000000000000)⟩,⟨(1000000000000000000/694274531532212051),0,10,(364887818119235711/1000000000000000000)⟩,(615637709450304737/1000000000000000000)⟩
theorem valid236 : certificate236.Valid := by decide +kernel
theorem sound236 : 0 ≤ cappedLabelEntropy (certificate236.rho:ℝ) ∧ cappedLabelEntropy (certificate236.rho:ℝ) ≤ (certificate236.bound:ℝ) := rat_label_entropy_certificate_sound certificate236 valid236

def certificate237 : RatLabelEntropyCertificate := ⟨(61887996807147177/200000000000000000),⟨(200000000000000000/61887996807147177),1,14,(58649555915401569/50000000000000000)⟩,⟨(200000000000000000/138112003192852823),0,10,(370252393234569827/1000000000000000000)⟩,(154662962876542187/250000000000000000)⟩
theorem valid237 : certificate237.Valid := by decide +kernel
theorem sound237 : 0 ≤ cappedLabelEntropy (certificate237.rho:ℝ) ∧ cappedLabelEntropy (certificate237.rho:ℝ) ≤ (certificate237.bound:ℝ) := rat_label_entropy_certificate_sound certificate237 valid237

def certificate238 : RatLabelEntropyCertificate := ⟨(311843590259886733/1000000000000000000),⟨(1000000000000000000/311843590259886733),1,12,(7282834563385983/6250000000000000)⟩,⟨(1000000000000000000/688156409740113267),0,12,(93434781787004783/250000000000000000)⟩,(155141955079999319/250000000000000000)⟩
theorem valid238 : certificate238.Valid := by decide +kernel
theorem sound238 : 0 ≤ cappedLabelEntropy (certificate238.rho:ℝ) ∧ cappedLabelEntropy (certificate238.rho:ℝ) ≤ (certificate238.bound:ℝ) := rat_label_entropy_certificate_sound certificate238 valid238

def certificate239 : RatLabelEntropyCertificate := ⟨(317156706968692181/1000000000000000000),⟨(1000000000000000000/317156706968692181),1,12,(287089820875664177/250000000000000000)⟩,⟨(1000000000000000000/682843293031307819),0,10,(15259595397174387/40000000000000000)⟩,(156176914513982013/250000000000000000)⟩
theorem valid239 : certificate239.Valid := by decide +kernel
theorem sound239 : 0 ≤ cappedLabelEntropy (certificate239.rho:ℝ) ∧ cappedLabelEntropy (certificate239.rho:ℝ) ≤ (certificate239.bound:ℝ) := rat_label_entropy_certificate_sound certificate239 valid239

end Cycle12.CutLabelCertificates.Entropy011
