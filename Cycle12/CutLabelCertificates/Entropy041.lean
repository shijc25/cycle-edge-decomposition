import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy041

def certificate820 : RatLabelEntropyCertificate := ⟨(12581320507309647/1000000000000000000),⟨(1000000000000000000/12581320507309647),6,8,(875108412886825863/200000000000000000)⟩,⟨(1000000000000000000/987418679492690353),0,3,(12661135478617613/1000000000000000000)⟩,(16887984695258939/250000000000000000)⟩
theorem valid820 : certificate820.Valid := by decide +kernel
theorem sound820 : 0 ≤ cappedLabelEntropy (certificate820.rho:ℝ) ∧ cappedLabelEntropy (certificate820.rho:ℝ) ≤ (certificate820.bound:ℝ) := rat_label_entropy_certificate_sound certificate820 valid820

def certificate821 : RatLabelEntropyCertificate := ⟨(21598216473371901/250000000000000000),⟨(250000000000000000/21598216473371901),3,10,(489770035451699991/200000000000000000)⟩,⟨(250000000000000000/228401783526628099),0,5,(45177315662646283/500000000000000000)⟩,(147055910367743993/500000000000000000)⟩
theorem valid821 : certificate821.Valid := by decide +kernel
theorem sound821 : 0 ≤ cappedLabelEntropy (certificate821.rho:ℝ) ∧ cappedLabelEntropy (certificate821.rho:ℝ) ≤ (certificate821.bound:ℝ) := rat_label_entropy_certificate_sound certificate821 valid821

def certificate822 : RatLabelEntropyCertificate := ⟨(94128260905867/1000000000000000),⟨(1000000000000000/94128260905867),3,9,(2363096949043941701/1000000000000000000)⟩,⟨(1000000000000000/905871739094133),0,5,(49428775644835477/500000000000000000)⟩,(155993234037414059/500000000000000000)⟩
theorem valid822 : certificate822.Valid := by decide +kernel
theorem sound822 : 0 ≤ cappedLabelEntropy (certificate822.rho:ℝ) ∧ cappedLabelEntropy (certificate822.rho:ℝ) ≤ (certificate822.bound:ℝ) := rat_label_entropy_certificate_sound certificate822 valid822

def certificate823 : RatLabelEntropyCertificate := ⟨(2133188033172489/250000000000000000),⟨(250000000000000000/2133188033172489),6,15,(4763843327934679673/1000000000000000000)⟩,⟨(250000000000000000/247866811966827511),0,3,(8569364480330797/1000000000000000000)⟩,(49144938533520913/1000000000000000000)⟩
theorem valid823 : certificate823.Valid := by decide +kernel
theorem sound823 : 0 ≤ cappedLabelEntropy (certificate823.rho:ℝ) ∧ cappedLabelEntropy (certificate823.rho:ℝ) ≤ (certificate823.bound:ℝ) := rat_label_entropy_certificate_sound certificate823 valid823

def certificate824 : RatLabelEntropyCertificate := ⟨(55890214435069/8000000000000000),⟨(8000000000000000/55890214435069),7,6,(992761502130724749/200000000000000000)⟩,⟨(8000000000000000/7944109785564931),0,3,(1752698774324093/250000000000000000)⟩,(260252181345203/6250000000000000)⟩
theorem valid824 : certificate824.Valid := by decide +kernel
theorem sound824 : 0 ≤ cappedLabelEntropy (certificate824.rho:ℝ) ∧ cappedLabelEntropy (certificate824.rho:ℝ) ≤ (certificate824.bound:ℝ) := rat_label_entropy_certificate_sound certificate824 valid824

def certificate825 : RatLabelEntropyCertificate := ⟨(1475784027706743/200000000000000000),⟨(200000000000000000/1475784027706743),7,4,(1227281993441968483/250000000000000000)⟩,⟨(200000000000000000/198524215972293257),0,3,(925784879864843/125000000000000000)⟩,(43575691965641843/1000000000000000000)⟩
theorem valid825 : certificate825.Valid := by decide +kernel
theorem sound825 : 0 ≤ cappedLabelEntropy (certificate825.rho:ℝ) ∧ cappedLabelEntropy (certificate825.rho:ℝ) ≤ (certificate825.bound:ℝ) := rat_label_entropy_certificate_sound certificate825 valid825

def certificate826 : RatLabelEntropyCertificate := ⟨(1295812521452677/100000000000000000),⟨(100000000000000000/1295812521452677),6,7,(4346032257895119093/1000000000000000000)⟩,⟨(100000000000000000/98704187478547323),0,3,(1630351765111611/125000000000000000)⟩,(69190233886542013/1000000000000000000)⟩
theorem valid826 : certificate826.Valid := by decide +kernel
theorem sound826 : 0 ≤ cappedLabelEntropy (certificate826.rho:ℝ) ∧ cappedLabelEntropy (certificate826.rho:ℝ) ≤ (certificate826.bound:ℝ) := rat_label_entropy_certificate_sound certificate826 valid826

def certificate827 : RatLabelEntropyCertificate := ⟨(88124705263538319/1000000000000000000),⟨(1000000000000000000/88124705263538319),3,10,(2429002362382522021/1000000000000000000)⟩,⟨(1000000000000000000/911875294736461681),0,5,(1845040729697867/20000000000000000)⟩,(29817747022909899/100000000000000000)⟩
theorem valid827 : certificate827.Valid := by decide +kernel
theorem sound827 : 0 ≤ cappedLabelEntropy (certificate827.rho:ℝ) ∧ cappedLabelEntropy (certificate827.rho:ℝ) ≤ (certificate827.bound:ℝ) := rat_label_entropy_certificate_sound certificate827 valid827

def certificate828 : RatLabelEntropyCertificate := ⟨(4701825306294211/50000000000000000),⟨(50000000000000000/4701825306294211),3,9,(1182036104532109111/500000000000000000)⟩,⟨(50000000000000000/45298174693705789),0,5,(98756267488151209/1000000000000000000)⟩,(62355732781046443/200000000000000000)⟩
theorem valid828 : certificate828.Valid := by decide +kernel
theorem sound828 : 0 ≤ cappedLabelEntropy (certificate828.rho:ℝ) ∧ cappedLabelEntropy (certificate828.rho:ℝ) ≤ (certificate828.bound:ℝ) := rat_label_entropy_certificate_sound certificate828 valid828

end Cycle12.CutLabelCertificates.Entropy041
