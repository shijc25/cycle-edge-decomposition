import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy027

def certificate540 : RatLabelEntropyCertificate := ⟨(6868658993238117/500000000000000000),⟨(500000000000000000/6868658993238117),6,6,(85752784174645123/20000000000000000)⟩,⟨(500000000000000000/493131341006761883),0,3,(13832548082396187/1000000000000000000)⟩,(72543189192463439/1000000000000000000)⟩
theorem valid540 : certificate540.Valid := by decide +kernel
theorem sound540 : 0 ≤ cappedLabelEntropy (certificate540.rho:ℝ) ∧ cappedLabelEntropy (certificate540.rho:ℝ) ≤ (certificate540.bound:ℝ) := rat_label_entropy_certificate_sound certificate540 valid540

def certificate541 : RatLabelEntropyCertificate := ⟨(23706258068564657/250000000000000000),⟨(250000000000000000/23706258068564657),3,8,(2355721851051222553/1000000000000000000)⟩,⟨(250000000000000000/226293741931435343),0,5,(49813509732667979/500000000000000000)⟩,(313561284684255739/1000000000000000000)⟩
theorem valid541 : certificate541.Valid := by decide +kernel
theorem sound541 : 0 ≤ cappedLabelEntropy (certificate541.rho:ℝ) ∧ cappedLabelEntropy (certificate541.rho:ℝ) ≤ (certificate541.bound:ℝ) := rat_label_entropy_certificate_sound certificate541 valid541

def certificate542 : RatLabelEntropyCertificate := ⟨(778383660805789/500000000000000000),⟨(500000000000000000/778383660805789),9,8,(6465143837495662101/1000000000000000000)⟩,⟨(500000000000000000/499221616339194211),0,2,(1557980342949841/1000000000000000000)⟩,(2324055917159189/200000000000000000)⟩
theorem valid542 : certificate542.Valid := by decide +kernel
theorem sound542 : 0 ≤ cappedLabelEntropy (certificate542.rho:ℝ) ∧ cappedLabelEntropy (certificate542.rho:ℝ) ≤ (certificate542.bound:ℝ) := rat_label_entropy_certificate_sound certificate542 valid542

def certificate543 : RatLabelEntropyCertificate := ⟨(1256245801955697/1000000000000000000),⟨(1000000000000000000/1256245801955697),9,11,(6679627527889280163/1000000000000000000)⟩,⟨(1000000000000000000/998743754198044303),0,2,(157129442523251/125000000000000000)⟩,(9646710435104359/1000000000000000000)⟩
theorem valid543 : certificate543.Valid := by decide +kernel
theorem sound543 : 0 ≤ cappedLabelEntropy (certificate543.rho:ℝ) ∧ cappedLabelEntropy (certificate543.rho:ℝ) ≤ (certificate543.bound:ℝ) := rat_label_entropy_certificate_sound certificate543 valid543

def certificate544 : RatLabelEntropyCertificate := ⟨(1476570799130407/1000000000000000000),⟨(1000000000000000000/1476570799130407),9,9,(6518032907282816757/1000000000000000000)⟩,⟨(1000000000000000000/998523429200869593),0,2,(738831002043011/500000000000000000)⟩,(11099817190184683/1000000000000000000)⟩
theorem valid544 : certificate544.Valid := by decide +kernel
theorem sound544 : 0 ≤ cappedLabelEntropy (certificate544.rho:ℝ) ∧ cappedLabelEntropy (certificate544.rho:ℝ) ≤ (certificate544.bound:ℝ) := rat_label_entropy_certificate_sound certificate544 valid544

def certificate545 : RatLabelEntropyCertificate := ⟨(5576751526577801/500000000000000000),⟨(500000000000000000/5576751526577801),6,9,(179840066209911509/40000000000000000)⟩,⟨(500000000000000000/494423248473422199),0,3,(11216169772995223/1000000000000000000)⟩,(48989790702389/800000000000000)⟩
theorem valid545 : certificate545.Valid := by decide +kernel
theorem sound545 : 0 ≤ cappedLabelEntropy (certificate545.rho:ℝ) ∧ cappedLabelEntropy (certificate545.rho:ℝ) ≤ (certificate545.bound:ℝ) := rat_label_entropy_certificate_sound certificate545 valid545

def certificate546 : RatLabelEntropyCertificate := ⟨(47874865154940087/500000000000000000),⟨(500000000000000000/47874865154940087),3,8,(1173008733766171949/500000000000000000)⟩,⟨(500000000000000000/452125134845059913),0,5,(50324554951337763/500000000000000000)⟩,(6312850491841097/20000000000000000)⟩
theorem valid546 : certificate546.Valid := by decide +kernel
theorem sound546 : 0 ≤ cappedLabelEntropy (certificate546.rho:ℝ) ∧ cappedLabelEntropy (certificate546.rho:ℝ) ≤ (certificate546.bound:ℝ) := rat_label_entropy_certificate_sound certificate546 valid546

def certificate547 : RatLabelEntropyCertificate := ⟨(1674602434999671/1000000000000000000),⟨(1000000000000000000/1674602434999671),9,7,(3196089747058305161/500000000000000000)⟩,⟨(1000000000000000000/998325397565000329),0,2,(838003074492391/500000000000000000)⟩,(12377558850809259/1000000000000000000)⟩
theorem valid547 : certificate547.Valid := by decide +kernel
theorem sound547 : 0 ≤ cappedLabelEntropy (certificate547.rho:ℝ) ∧ cappedLabelEntropy (certificate547.rho:ℝ) ≤ (certificate547.bound:ℝ) := rat_label_entropy_certificate_sound certificate547 valid547

def certificate548 : RatLabelEntropyCertificate := ⟨(671415429916989/500000000000000000),⟨(500000000000000000/671415429916989),9,10,(413310956963568391/62500000000000000)⟩,⟨(500000000000000000/499328584570083011),0,2,(20995832267739/15625000000000000)⟩,(2555509045532643/250000000000000000)⟩
theorem valid548 : certificate548.Valid := by decide +kernel
theorem sound548 : 0 ≤ cappedLabelEntropy (certificate548.rho:ℝ) ∧ cappedLabelEntropy (certificate548.rho:ℝ) ≤ (certificate548.bound:ℝ) := rat_label_entropy_certificate_sound certificate548 valid548

def certificate549 : RatLabelEntropyCertificate := ⟨(786098266797591/500000000000000000),⟨(500000000000000000/786098266797591),9,7,(6455281571418661621/1000000000000000000)⟩,⟨(500000000000000000/499213901733202409),0,2,(1573433731480829/1000000000000000000)⟩,(11719931294387633/1000000000000000000)⟩
theorem valid549 : certificate549.Valid := by decide +kernel
theorem sound549 : 0 ≤ cappedLabelEntropy (certificate549.rho:ℝ) ∧ cappedLabelEntropy (certificate549.rho:ℝ) ≤ (certificate549.bound:ℝ) := rat_label_entropy_certificate_sound certificate549 valid549

def certificate550 : RatLabelEntropyCertificate := ⟨(56123123137611/5000000000000000),⟨(5000000000000000/56123123137611),6,9,(4489645286668234163/1000000000000000000)⟩,⟨(5000000000000000/4943876876862389),0,3,(705506008503789/62500000000000000)⟩,(61555974547749189/1000000000000000000)⟩
theorem valid550 : certificate550.Valid := by decide +kernel
theorem sound550 : 0 ≤ cappedLabelEntropy (certificate550.rho:ℝ) ∧ cappedLabelEntropy (certificate550.rho:ℝ) ≤ (certificate550.bound:ℝ) := rat_label_entropy_certificate_sound certificate550 valid550

def certificate551 : RatLabelEntropyCertificate := ⟨(95562584397392487/1000000000000000000),⟨(1000000000000000000/95562584397392487),3,8,(2347973912128903407/1000000000000000000)⟩,⟨(1000000000000000000/904437415602607513),0,6,(6277635549919797/62500000000000000)⟩,(19701381919157899/62500000000000000)⟩
theorem valid551 : certificate551.Valid := by decide +kernel
theorem sound551 : 0 ≤ cappedLabelEntropy (certificate551.rho:ℝ) ∧ cappedLabelEntropy (certificate551.rho:ℝ) ≤ (certificate551.bound:ℝ) := rat_label_entropy_certificate_sound certificate551 valid551

def certificate552 : RatLabelEntropyCertificate := ⟨(447318813969649/250000000000000000),⟨(250000000000000000/447318813969649),9,5,(1265188925220310877/200000000000000000)⟩,⟨(250000000000000000/249552681186030351),0,2,(223859740109223/125000000000000000)⟩,(6553264868432677/500000000000000000)⟩
theorem valid552 : certificate552.Valid := by decide +kernel
theorem sound552 : 0 ≤ cappedLabelEntropy (certificate552.rho:ℝ) ∧ cappedLabelEntropy (certificate552.rho:ℝ) ≤ (certificate552.bound:ℝ) := rat_label_entropy_certificate_sound certificate552 valid552

def certificate553 : RatLabelEntropyCertificate := ⟨(1432630696914647/1000000000000000000),⟨(1000000000000000000/1432630696914647),9,9,(6548242876598544271/1000000000000000000)⟩,⟨(1000000000000000000/998567369303085353),0,2,(716828946725463/500000000000000000)⟩,(270320443675291/25000000000000000)⟩
theorem valid553 : certificate553.Valid := by decide +kernel
theorem sound553 : 0 ≤ cappedLabelEntropy (certificate553.rho:ℝ) ∧ cappedLabelEntropy (certificate553.rho:ℝ) ≤ (certificate553.bound:ℝ) := rat_label_entropy_certificate_sound certificate553 valid553

def certificate554 : RatLabelEntropyCertificate := ⟨(835425712667223/500000000000000000),⟨(500000000000000000/835425712667223),9,6,(1278884389389168241/200000000000000000)⟩,⟨(500000000000000000/499164574287332777),0,2,(1672248854391703/1000000000000000000)⟩,(12353583799254151/1000000000000000000)⟩
theorem valid554 : certificate554.Valid := by decide +kernel
theorem sound554 : 0 ≤ cappedLabelEntropy (certificate554.rho:ℝ) ∧ cappedLabelEntropy (certificate554.rho:ℝ) ≤ (certificate554.bound:ℝ) := rat_label_entropy_certificate_sound certificate554 valid554

def certificate555 : RatLabelEntropyCertificate := ⟨(5640095335605051/500000000000000000),⟨(500000000000000000/5640095335605051),6,9,(1121176782394753371/250000000000000000)⟩,⟨(500000000000000000/494359904664394949),0,3,(2836073636798619/250000000000000000)⟩,(7725585033482297/125000000000000000)⟩
theorem valid555 : certificate555.Valid := by decide +kernel
theorem sound555 : 0 ≤ cappedLabelEntropy (certificate555.rho:ℝ) ∧ cappedLabelEntropy (certificate555.rho:ℝ) ≤ (certificate555.bound:ℝ) := rat_label_entropy_certificate_sound certificate555 valid555

def certificate556 : RatLabelEntropyCertificate := ⟨(95404759144127827/1000000000000000000),⟨(1000000000000000000/95404759144127827),3,8,(587406703891345251/250000000000000000)⟩,⟨(1000000000000000000/904595240855872173),0,5,(100267683000351949/1000000000000000000)⟩,(157433624635681421/500000000000000000)⟩
theorem valid556 : certificate556.Valid := by decide +kernel
theorem sound556 : 0 ≤ cappedLabelEntropy (certificate556.rho:ℝ) ∧ cappedLabelEntropy (certificate556.rho:ℝ) ≤ (certificate556.bound:ℝ) := rat_label_entropy_certificate_sound certificate556 valid556

def certificate557 : RatLabelEntropyCertificate := ⟨(59186233958649/31250000000000000),⟨(31250000000000000/59186233958649),9,4,(1567271418699300661/250000000000000000)⟩,⟨(31250000000000000/31190813766041351),0,2,(1895755295763361/1000000000000000000)⟩,(6882779549304061/500000000000000000)⟩
theorem valid557 : certificate557.Valid := by decide +kernel
theorem sound557 : 0 ≤ cappedLabelEntropy (certificate557.rho:ℝ) ∧ cappedLabelEntropy (certificate557.rho:ℝ) ≤ (certificate557.bound:ℝ) := rat_label_entropy_certificate_sound certificate557 valid557

def certificate558 : RatLabelEntropyCertificate := ⟨(762838951224891/500000000000000000),⟨(500000000000000000/762838951224891),9,8,(6485316441498683243/1000000000000000000)⟩,⟨(500000000000000000/499237161048775109),0,2,(305368586821389/200000000000000000)⟩,(5709508724385331/500000000000000000)⟩
theorem valid558 : certificate558.Valid := by decide +kernel
theorem sound558 : 0 ≤ cappedLabelEntropy (certificate558.rho:ℝ) ∧ cappedLabelEntropy (certificate558.rho:ℝ) ≤ (certificate558.bound:ℝ) := rat_label_entropy_certificate_sound certificate558 valid558

def certificate559 : RatLabelEntropyCertificate := ⟨(88623425748273/50000000000000000),⟨(50000000000000000/88623425748273),9,5,(395961378923861731/62500000000000000)⟩,⟨(50000000000000000/49911376574251727),0,2,(44351029897753/25000000000000000)⟩,(6500081000151883/500000000000000000)⟩
theorem valid559 : certificate559.Valid := by decide +kernel
theorem sound559 : 0 ≤ cappedLabelEntropy (certificate559.rho:ℝ) ∧ cappedLabelEntropy (certificate559.rho:ℝ) ≤ (certificate559.bound:ℝ) := rat_label_entropy_certificate_sound certificate559 valid559

end Cycle12.CutLabelCertificates.Entropy027
