import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy013

def certificate260 : RatLabelEntropyCertificate := ⟨(5561778223314971/500000000000000000),⟨(500000000000000000/5561778223314971),6,10,(2249345108477688501/500000000000000000)⟩,⟨(500000000000000000/494438221776685029),0,3,(5592942924034267/500000000000000000)⟩,(61102893579637021/1000000000000000000)⟩
theorem valid260 : certificate260.Valid := by decide +kernel
theorem sound260 : 0 ≤ cappedLabelEntropy (certificate260.rho:ℝ) ∧ cappedLabelEntropy (certificate260.rho:ℝ) ≤ (certificate260.bound:ℝ) := rat_label_entropy_certificate_sound certificate260 valid260

def certificate261 : RatLabelEntropyCertificate := ⟨(2473408530228587/200000000000000000),⟨(200000000000000000/2473408530228587),6,8,(2196360097720820341/500000000000000000)⟩,⟨(200000000000000000/197526591469771413),0,3,(6222075458393/500000000000000)⟩,(16653802895801137/250000000000000000)⟩
theorem valid261 : certificate261.Valid := by decide +kernel
theorem sound261 : 0 ≤ cappedLabelEntropy (certificate261.rho:ℝ) ∧ cappedLabelEntropy (certificate261.rho:ℝ) ≤ (certificate261.bound:ℝ) := rat_label_entropy_certificate_sound certificate261 valid261

def certificate262 : RatLabelEntropyCertificate := ⟨(13573807576887401/1000000000000000000),⟨(1000000000000000000/13573807576887401),6,6,(859922651332047097/200000000000000000)⟩,⟨(1000000000000000000/986426192423112599),0,3,(427086685410313/31250000000000000)⟩,(71843386774505107/1000000000000000000)⟩
theorem valid262 : certificate262.Valid := by decide +kernel
theorem sound262 : 0 ≤ cappedLabelEntropy (certificate262.rho:ℝ) ∧ cappedLabelEntropy (certificate262.rho:ℝ) ≤ (certificate262.bound:ℝ) := rat_label_entropy_certificate_sound certificate262 valid262

def certificate263 : RatLabelEntropyCertificate := ⟨(7475185015199797/500000000000000000),⟨(500000000000000000/7475185015199797),6,4,(4203019228254450191/1000000000000000000)⟩,⟨(500000000000000000/492524814984800203),0,3,(15063253323428237/1000000000000000000)⟩,(38837372409834951/500000000000000000)⟩
theorem valid263 : certificate263.Valid := by decide +kernel
theorem sound263 : 0 ≤ cappedLabelEntropy (certificate263.rho:ℝ) ∧ cappedLabelEntropy (certificate263.rho:ℝ) ≤ (certificate263.bound:ℝ) := rat_label_entropy_certificate_sound certificate263 valid263

def certificate264 : RatLabelEntropyCertificate := ⟨(8149384047522589/500000000000000000),⟨(500000000000000000/8149384047522589),5,15,(514583218877074809/125000000000000000)⟩,⟨(500000000000000000/491850615952477411),0,3,(8216527073237529/500000000000000000)⟩,(83261796008482873/1000000000000000000)⟩
theorem valid264 : certificate264.Valid := by decide +kernel
theorem sound264 : 0 ≤ cappedLabelEntropy (certificate264.rho:ℝ) ∧ cappedLabelEntropy (certificate264.rho:ℝ) ≤ (certificate264.bound:ℝ) := rat_label_entropy_certificate_sound certificate264 valid264

def certificate265 : RatLabelEntropyCertificate := ⟨(8898959667178359/500000000000000000),⟨(500000000000000000/8898959667178359),5,13,(4028673719844695603/1000000000000000000)⟩,⟨(500000000000000000/491101040332821641),0,3,(17958207006559649/1000000000000000000)⟩,(89340598177105929/1000000000000000000)⟩
theorem valid265 : certificate265.Valid := by decide +kernel
theorem sound265 : 0 ≤ cappedLabelEntropy (certificate265.rho:ℝ) ∧ cappedLabelEntropy (certificate265.rho:ℝ) ≤ (certificate265.bound:ℝ) := rat_label_entropy_certificate_sound certificate265 valid265

def certificate266 : RatLabelEntropyCertificate := ⟨(9692147915489623/500000000000000000),⟨(500000000000000000/9692147915489623),5,12,(1971646016988964451/500000000000000000)⟩,⟨(500000000000000000/490307852084510377),0,3,(19574635035989201/1000000000000000000)⟩,(47816566927120087/500000000000000000)⟩
theorem valid266 : certificate266.Valid := by decide +kernel
theorem sound266 : 0 ≤ cappedLabelEntropy (certificate266.rho:ℝ) ∧ cappedLabelEntropy (certificate266.rho:ℝ) ≤ (certificate266.bound:ℝ) := rat_label_entropy_certificate_sound certificate266 valid266

def certificate267 : RatLabelEntropyCertificate := ⟨(40775596252183/1953125000000000),⟨(1953125000000000/40775596252183),5,11,(1934551080770174243/500000000000000000)⟩,⟨(1953125000000000/1912349403747817),0,3,(21098113462875437/1000000000000000000)⟩,(101433299096755923/1000000000000000000)⟩
theorem valid267 : certificate267.Valid := by decide +kernel
theorem sound267 : 0 ≤ cappedLabelEntropy (certificate267.rho:ℝ) ∧ cappedLabelEntropy (certificate267.rho:ℝ) ≤ (certificate267.bound:ℝ) := rat_label_entropy_certificate_sound certificate267 valid267

def certificate268 : RatLabelEntropyCertificate := ⟨(11312910010429673/500000000000000000),⟨(500000000000000000/11312910010429673),5,9,(947165886509265753/250000000000000000)⟩,⟨(500000000000000000/488687089989570327),0,3,(5721427885280037/250000000000000000)⟩,(21617904612593361/200000000000000000)⟩
theorem valid268 : certificate268.Valid := by decide +kernel
theorem sound268 : 0 ≤ cappedLabelEntropy (certificate268.rho:ℝ) ∧ cappedLabelEntropy (certificate268.rho:ℝ) ≤ (certificate268.bound:ℝ) := rat_label_entropy_certificate_sound certificate268 valid268

def certificate269 : RatLabelEntropyCertificate := ⟨(24228504709270111/1000000000000000000),⟨(1000000000000000000/24228504709270111),5,8,(3720225458428187/1000000000000000)⟩,⟨(1000000000000000000/975771495290729889),0,3,(24526843657802103/1000000000000000000)⟩,(570340474749047/5000000000000000)⟩
theorem valid269 : certificate269.Valid := by decide +kernel
theorem sound269 : 0 ≤ cappedLabelEntropy (certificate269.rho:ℝ) ∧ cappedLabelEntropy (certificate269.rho:ℝ) ≤ (certificate269.bound:ℝ) := rat_label_entropy_certificate_sound certificate269 valid269

def certificate270 : RatLabelEntropyCertificate := ⟨(260931091563677/10000000000000000),⟨(10000000000000000/260931091563677),5,7,(911521004127379641/250000000000000000)⟩,⟨(10000000000000000/9739068908436323),0,4,(26439574525452449/1000000000000000000)⟩,(120887352057382339/1000000000000000000)⟩
theorem valid270 : certificate270.Valid := by decide +kernel
theorem sound270 : 0 ≤ cappedLabelEntropy (certificate270.rho:ℝ) ∧ cappedLabelEntropy (certificate270.rho:ℝ) ≤ (certificate270.bound:ℝ) := rat_label_entropy_certificate_sound certificate270 valid270

def certificate271 : RatLabelEntropyCertificate := ⟨(222714104610229/8000000000000000),⟨(8000000000000000/222714104610229),5,6,(111915872307109689/31250000000000000)⟩,⟨(8000000000000000/7777285895389771),0,4,(28234120987872427/1000000000000000000)⟩,(127149077036166199/1000000000000000000)⟩
theorem valid271 : certificate271.Valid := by decide +kernel
theorem sound271 : 0 ≤ cappedLabelEntropy (certificate271.rho:ℝ) ∧ cappedLabelEntropy (certificate271.rho:ℝ) ≤ (certificate271.bound:ℝ) := rat_label_entropy_certificate_sound certificate271 valid271

def certificate272 : RatLabelEntropyCertificate := ⟨(2984452207860627/100000000000000000),⟨(100000000000000000/2984452207860627),5,4,(3511753970939019459/1000000000000000000)⟩,⟨(100000000000000000/97015547792139373),0,4,(7574733453079757/250000000000000000)⟩,(134201295533521851/1000000000000000000)⟩
theorem valid272 : certificate272.Valid := by decide +kernel
theorem sound272 : 0 ≤ cappedLabelEntropy (certificate272.rho:ℝ) ∧ cappedLabelEntropy (certificate272.rho:ℝ) ≤ (certificate272.bound:ℝ) := rat_label_entropy_certificate_sound certificate272 valid272

def certificate273 : RatLabelEntropyCertificate := ⟨(31670672145636623/1000000000000000000),⟨(1000000000000000000/31670672145636623),4,15,(3452364195239163297/1000000000000000000)⟩,⟨(1000000000000000000/968329327854363377),0,4,(8045758709971241/250000000000000000)⟩,(35125617762393383/250000000000000000)⟩
theorem valid273 : certificate273.Valid := by decide +kernel
theorem sound273 : 0 ≤ cappedLabelEntropy (certificate273.rho:ℝ) ∧ cappedLabelEntropy (certificate273.rho:ℝ) ≤ (certificate273.bound:ℝ) := rat_label_entropy_certificate_sound certificate273 valid273

def certificate274 : RatLabelEntropyCertificate := ⟨(33818659020504217/1000000000000000000),⟨(1000000000000000000/33818659020504217),4,15,(423342823348194561/125000000000000000)⟩,⟨(1000000000000000000/966181340979495783),0,4,(34403738806227137/1000000000000000000)⟩,(147775343227229999/1000000000000000000)⟩
theorem valid274 : certificate274.Valid := by decide +kernel
theorem sound274 : 0 ≤ cappedLabelEntropy (certificate274.rho:ℝ) ∧ cappedLabelEntropy (certificate274.rho:ℝ) ≤ (certificate274.bound:ℝ) := rat_label_entropy_certificate_sound certificate274 valid274

def certificate275 : RatLabelEntropyCertificate := ⟨(35793638544097477/1000000000000000000),⟨(1000000000000000000/35793638544097477),4,13,(133199403826557521/40000000000000000)⟩,⟨(1000000000000000000/964206361455902523),0,4,(36449939380541223/1000000000000000000)⟩,(154337546296826723/1000000000000000000)⟩
theorem valid275 : certificate275.Valid := by decide +kernel
theorem sound275 : 0 ≤ cappedLabelEntropy (certificate275.rho:ℝ) ∧ cappedLabelEntropy (certificate275.rho:ℝ) ≤ (certificate275.bound:ℝ) := rat_label_entropy_certificate_sound certificate275 valid275

def certificate276 : RatLabelEntropyCertificate := ⟨(9521273035897943/250000000000000000),⟨(250000000000000000/9521273035897943),4,12,(816983088935202347/250000000000000000)⟩,⟨(250000000000000000/240478726964102057),0,4,(38829285600377767/1000000000000000000)⟩,(161809973567831191/1000000000000000000)⟩
theorem valid276 : certificate276.Valid := by decide +kernel
theorem sound276 : 0 ≤ cappedLabelEntropy (certificate276.rho:ℝ) ∧ cappedLabelEntropy (certificate276.rho:ℝ) ≤ (certificate276.bound:ℝ) := rat_label_entropy_certificate_sound certificate276 valid276

def certificate277 : RatLabelEntropyCertificate := ⟨(1004369840473803/25000000000000000),⟨(25000000000000000/1004369840473803),4,11,(321451550442335173/100000000000000000)⟩,⟨(25000000000000000/23995630159526197),0,4,(20502043892317897/500000000000000000)⟩,(84249626997742291/500000000000000000)⟩
theorem valid277 : certificate277.Valid := by decide +kernel
theorem sound277 : 0 ≤ cappedLabelEntropy (certificate277.rho:ℝ) ∧ cappedLabelEntropy (certificate277.rho:ℝ) ≤ (certificate277.bound:ℝ) := rat_label_entropy_certificate_sound certificate277 valid277

def certificate278 : RatLabelEntropyCertificate := ⟨(42618862931454637/1000000000000000000),⟨(1000000000000000000/42618862931454637),4,10,(9860807287162489/3125000000000000)⟩,⟨(1000000000000000000/957381137068545363),0,4,(21776852232502463/500000000000000000)⟩,(17617954123707529/100000000000000000)⟩
theorem valid278 : certificate278.Valid := by decide +kernel
theorem sound278 : 0 ≤ cappedLabelEntropy (certificate278.rho:ℝ) ∧ cappedLabelEntropy (certificate278.rho:ℝ) ≤ (certificate278.bound:ℝ) := rat_label_entropy_certificate_sound certificate278 valid278

def certificate279 : RatLabelEntropyCertificate := ⟨(44816898014988791/1000000000000000000),⟨(1000000000000000000/44816898014988791),4,9,(3105170022844075093/1000000000000000000)⟩,⟨(1000000000000000000/955183101985011209),0,4,(45852227051984251/1000000000000000000)⟩,(182961360701438691/1000000000000000000)⟩
theorem valid279 : certificate279.Valid := by decide +kernel
theorem sound279 : 0 ≤ cappedLabelEntropy (certificate279.rho:ℝ) ∧ cappedLabelEntropy (certificate279.rho:ℝ) ≤ (certificate279.bound:ℝ) := rat_label_entropy_certificate_sound certificate279 valid279

end Cycle12.CutLabelCertificates.Entropy013
