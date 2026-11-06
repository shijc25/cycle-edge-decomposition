import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy002

def certificate40 : RatLabelEntropyCertificate := ⟨(5481734931488071/31250000000000000),⟨(31250000000000000/5481734931488071),2,10,(435149432997585671/250000000000000000)⟩,⟨(31250000000000000/25768265068511929),0,7,(192875677474352839/1000000000000000000)⟩,(232185071544772997/500000000000000000)⟩
theorem valid40 : certificate40.Valid := by decide +kernel
theorem sound40 : 0 ≤ cappedLabelEntropy (certificate40.rho:ℝ) ∧ cappedLabelEntropy (certificate40.rho:ℝ) ≤ (certificate40.bound:ℝ) := rat_label_entropy_certificate_sound certificate40 valid40

def certificate41 : RatLabelEntropyCertificate := ⟨(92927449319207087/500000000000000000),⟨(500000000000000000/92927449319207087),2,9,(841394512282052701/500000000000000000)⟩,⟨(500000000000000000/407072550680792913),0,7,(205616671664558389/1000000000000000000)⟩,(480156389584171471/1000000000000000000)⟩
theorem valid41 : certificate41.Valid := by decide +kernel
theorem sound41 : 0 ≤ cappedLabelEntropy (certificate41.rho:ℝ) ∧ cappedLabelEntropy (certificate41.rho:ℝ) ≤ (certificate41.bound:ℝ) := rat_label_entropy_certificate_sound certificate41 valid41

def certificate42 : RatLabelEntropyCertificate := ⟨(18962959627375679/100000000000000000),⟨(100000000000000000/18962959627375679),2,9,(831341301426519403/500000000000000000)⟩,⟨(100000000000000000/81037040372624321),0,7,(105131923644640211/500000000000000000)⟩,(485685429527268173/1000000000000000000)⟩
theorem valid42 : certificate42.Valid := by decide +kernel
theorem sound42 : 0 ≤ cappedLabelEntropy (certificate42.rho:ℝ) ∧ cappedLabelEntropy (certificate42.rho:ℝ) ≤ (certificate42.bound:ℝ) := rat_label_entropy_certificate_sound certificate42 valid42

def certificate43 : RatLabelEntropyCertificate := ⟨(194962494405438691/1000000000000000000),⟨(1000000000000000000/194962494405438691),2,8,(1634948075299769989/1000000000000000000)⟩,⟨(1000000000000000000/805037505594561309),0,8,(105891802660251/488281250000000)⟩,(123334787556331779/250000000000000000)⟩
theorem valid43 : certificate43.Valid := by decide +kernel
theorem sound43 : 0 ≤ cappedLabelEntropy (certificate43.rho:ℝ) ∧ cappedLabelEntropy (certificate43.rho:ℝ) ≤ (certificate43.bound:ℝ) := rat_label_entropy_certificate_sound certificate43 valid43

def certificate44 : RatLabelEntropyCertificate := ⟨(49846020181123377/250000000000000000),⟨(250000000000000000/49846020181123377),2,8,(201565282565830129/125000000000000000)⟩,⟨(250000000000000000/200153979818876623),0,8,(111186974220052171/500000000000000000)⟩,(7805427995565387/15625000000000000)⟩
theorem valid44 : certificate44.Valid := by decide +kernel
theorem sound44 : 0 ≤ cappedLabelEntropy (certificate44.rho:ℝ) ∧ cappedLabelEntropy (certificate44.rho:ℝ) ≤ (certificate44.bound:ℝ) := rat_label_entropy_certificate_sound certificate44 valid44

def certificate45 : RatLabelEntropyCertificate := ⟨(101675436300490267/500000000000000000),⟨(500000000000000000/101675436300490267),2,7,(199102794438701261/125000000000000000)⟩,⟨(500000000000000000/398324563699509733),0,8,(227340938784172429/1000000000000000000)⟩,(505012776395713313/1000000000000000000)⟩
theorem valid45 : certificate45.Valid := by decide +kernel
theorem sound45 : 0 ≤ cappedLabelEntropy (certificate45.rho:ℝ) ∧ cappedLabelEntropy (certificate45.rho:ℝ) ≤ (certificate45.bound:ℝ) := rat_label_entropy_certificate_sound certificate45 valid45

def certificate46 : RatLabelEntropyCertificate := ⟨(208788148593487429/1000000000000000000),⟨(1000000000000000000/208788148593487429),2,7,(783217592097137769/500000000000000000)⟩,⟨(1000000000000000000/791211851406512571),0,8,(234189519758376623/1000000000000000000)⟩,(512346625507648477/1000000000000000000)⟩
theorem valid46 : certificate46.Valid := by decide +kernel
theorem sound46 : 0 ≤ cappedLabelEntropy (certificate46.rho:ℝ) ∧ cappedLabelEntropy (certificate46.rho:ℝ) ≤ (certificate46.bound:ℝ) := rat_label_entropy_certificate_sound certificate46 valid46

def certificate47 : RatLabelEntropyCertificate := ⟨(214375821931108661/1000000000000000000),⟨(1000000000000000000/214375821931108661),2,6,(308004925397661883/200000000000000000)⟩,⟨(1000000000000000000/785624178068891339),0,8,(48255349170239721/200000000000000000)⟩,(10393937807025051/20000000000000000)⟩
theorem valid47 : certificate47.Valid := by decide +kernel
theorem sound47 : 0 ≤ cappedLabelEntropy (certificate47.rho:ℝ) ∧ cappedLabelEntropy (certificate47.rho:ℝ) ≤ (certificate47.bound:ℝ) := rat_label_entropy_certificate_sound certificate47 valid47

def certificate48 : RatLabelEntropyCertificate := ⟨(218417281169139707/1000000000000000000),⟨(1000000000000000000/218417281169139707),2,6,(304269582401875521/200000000000000000)⟩,⟨(1000000000000000000/781582718830860293),0,8,(61608572122304071/250000000000000000)⟩,(262448727931993043/500000000000000000)⟩
theorem valid48 : certificate48.Valid := by decide +kernel
theorem sound48 : 0 ≤ cappedLabelEntropy (certificate48.rho:ℝ) ∧ cappedLabelEntropy (certificate48.rho:ℝ) ≤ (certificate48.bound:ℝ) := rat_label_entropy_certificate_sound certificate48 valid48

def certificate49 : RatLabelEntropyCertificate := ⟨(112045210325723831/500000000000000000),⟨(500000000000000000/112045210325723831),2,6,(1495705644954804811/1000000000000000000)⟩,⟨(500000000000000000/387954789674276169),0,8,(253719287046121899/1000000000000000000)⟩,(133009133108309521/250000000000000000)⟩
theorem valid49 : certificate49.Valid := by decide +kernel
theorem sound49 : 0 ≤ cappedLabelEntropy (certificate49.rho:ℝ) ∧ cappedLabelEntropy (certificate49.rho:ℝ) ≤ (certificate49.bound:ℝ) := rat_label_entropy_certificate_sound certificate49 valid49

def certificate50 : RatLabelEntropyCertificate := ⟨(114966216696431771/500000000000000000),⟨(500000000000000000/114966216696431771),2,5,(146996978107428619/100000000000000000)⟩,⟨(500000000000000000/385033783303568229),0,8,(261277019143674857/1000000000000000000)⟩,(269597343559360709/500000000000000000)⟩
theorem valid50 : certificate50.Valid := by decide +kernel
theorem sound50 : 0 ≤ cappedLabelEntropy (certificate50.rho:ℝ) ∧ cappedLabelEntropy (certificate50.rho:ℝ) ≤ (certificate50.bound:ℝ) := rat_label_entropy_certificate_sound certificate50 valid50

def certificate51 : RatLabelEntropyCertificate := ⟨(117009073818992553/500000000000000000),⟨(500000000000000000/117009073818992553),2,5,(181544576577888613/125000000000000000)⟩,⟨(500000000000000000/382990926181007447),0,8,(66649200238898279/250000000000000000)⟩,(13602152890639781/25000000000000000)⟩
theorem valid51 : certificate51.Valid := by decide +kernel
theorem sound51 : 0 ≤ cappedLabelEntropy (certificate51.rho:ℝ) ∧ cappedLabelEntropy (certificate51.rho:ℝ) ≤ (certificate51.bound:ℝ) := rat_label_entropy_certificate_sound certificate51 valid51

def certificate52 : RatLabelEntropyCertificate := ⟨(236896973495266683/1000000000000000000),⟨(1000000000000000000/236896973495266683),2,4,(1440129943351656311/1000000000000000000)⟩,⟨(1000000000000000000/763103026504733317),0,9,(270362228628717453/1000000000000000000)⟩,(547476659939056179/1000000000000000000)⟩
theorem valid52 : certificate52.Valid := by decide +kernel
theorem sound52 : 0 ≤ cappedLabelEntropy (certificate52.rho:ℝ) ∧ cappedLabelEntropy (certificate52.rho:ℝ) ≤ (certificate52.bound:ℝ) := rat_label_entropy_certificate_sound certificate52 valid52

def certificate53 : RatLabelEntropyCertificate := ⟨(119945851177609947/500000000000000000),⟨(500000000000000000/119945851177609947),2,4,(1427567697666219717/1000000000000000000)⟩,⟨(500000000000000000/380054148822390053),0,8,(54858871790490571/200000000000000000)⟩,(34434691466086657/62500000000000000)⟩
theorem valid53 : certificate53.Valid := by decide +kernel
theorem sound53 : 0 ≤ cappedLabelEntropy (certificate53.rho:ℝ) ∧ cappedLabelEntropy (certificate53.rho:ℝ) ≤ (certificate53.bound:ℝ) := rat_label_entropy_certificate_sound certificate53 valid53

def certificate54 : RatLabelEntropyCertificate := ⟨(244211148755382263/1000000000000000000),⟨(1000000000000000000/244211148755382263),2,3,(352430516037177351/250000000000000000)⟩,⟨(1000000000000000000/755788851244617737),0,9,(27999323910883677/100000000000000000)⟩,(555885613253892329/1000000000000000000)⟩
theorem valid54 : certificate54.Valid := by decide +kernel
theorem sound54 : 0 ≤ cappedLabelEntropy (certificate54.rho:ℝ) ∧ cappedLabelEntropy (certificate54.rho:ℝ) ≤ (certificate54.bound:ℝ) := rat_label_entropy_certificate_sound certificate54 valid54

def certificate55 : RatLabelEntropyCertificate := ⟨(250084233648277827/1000000000000000000),⟨(1000000000000000000/250084233648277827),1,16,(173244685409561549/125000000000000000)⟩,⟨(1000000000000000000/749915766351722173),0,9,(2877943902902303/10000000000000000)⟩,(562427665820522119/1000000000000000000)⟩
theorem valid55 : certificate55.Valid := by decide +kernel
theorem sound55 : 0 ≤ cappedLabelEntropy (certificate55.rho:ℝ) ∧ cappedLabelEntropy (certificate55.rho:ℝ) ≤ (certificate55.bound:ℝ) := rat_label_entropy_certificate_sound certificate55 valid55

def certificate56 : RatLabelEntropyCertificate := ⟨(126550740543443809/500000000000000000),⟨(500000000000000000/126550740543443809),1,15,(686982379831384471/500000000000000000)⟩,⟨(500000000000000000/373449259456556191),0,9,(291825954599911489/1000000000000000000)⟩,(35357305556432217/62500000000000000)⟩
theorem valid56 : certificate56.Valid := by decide +kernel
theorem sound56 : 0 ≤ cappedLabelEntropy (certificate56.rho:ℝ) ∧ cappedLabelEntropy (certificate56.rho:ℝ) ≤ (certificate56.bound:ℝ) := rat_label_entropy_certificate_sound certificate56 valid56

def certificate57 : RatLabelEntropyCertificate := ⟨(256147827412317399/1000000000000000000),⟨(1000000000000000000/256147827412317399),1,15,(1362000550333784133/1000000000000000000)⟩,⟨(1000000000000000000/743852172587682601),0,9,(295912956649557561/1000000000000000000)⟩,(284494488801498793/500000000000000000)⟩
theorem valid57 : certificate57.Valid := by decide +kernel
theorem sound57 : 0 ≤ cappedLabelEntropy (certificate57.rho:ℝ) ∧ cappedLabelEntropy (certificate57.rho:ℝ) ≤ (certificate57.bound:ℝ) := rat_label_entropy_certificate_sound certificate57 valid57

def certificate58 : RatLabelEntropyCertificate := ⟨(131260235222638649/500000000000000000),⟨(500000000000000000/131260235222638649),1,15,(1337426217342271873/1000000000000000000)⟩,⟨(500000000000000000/368739764777361351),0,9,(304516947689351153/1000000000000000000)⟩,(287838387542961843/500000000000000000)⟩
theorem valid58 : certificate58.Valid := by decide +kernel
theorem sound58 : 0 ≤ cappedLabelEntropy (certificate58.rho:ℝ) ∧ cappedLabelEntropy (certificate58.rho:ℝ) ≤ (certificate58.bound:ℝ) := rat_label_entropy_certificate_sound certificate58 valid58

def certificate59 : RatLabelEntropyCertificate := ⟨(10625698352646607/40000000000000000),⟨(40000000000000000/10625698352646607),1,15,(662802007077742341/500000000000000000)⟩,⟨(40000000000000000/29374301647353393),0,9,(15437962781966543/50000000000000000)⟩,(23155055901035667/40000000000000000)⟩
theorem valid59 : certificate59.Valid := by decide +kernel
theorem sound59 : 0 ≤ cappedLabelEntropy (certificate59.rho:ℝ) ∧ cappedLabelEntropy (certificate59.rho:ℝ) ≤ (certificate59.bound:ℝ) := rat_label_entropy_certificate_sound certificate59 valid59

end Cycle12.CutLabelCertificates.Entropy002
