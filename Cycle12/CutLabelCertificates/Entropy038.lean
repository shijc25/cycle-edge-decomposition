import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy038

def certificate760 : RatLabelEntropyCertificate := ⟨(10461242095398061/1000000000000000000),⟨(1000000000000000000/10461242095398061),6,10,(285004880014078787/62500000000000000)⟩,⟨(1000000000000000000/989538757904601939),0,3,(10516345525606509/1000000000000000000)⟩,(14527603065064689/250000000000000000)⟩
theorem valid760 : certificate760.Valid := by decide +kernel
theorem sound760 : 0 ≤ cappedLabelEntropy (certificate760.rho:ℝ) ∧ cappedLabelEntropy (certificate760.rho:ℝ) ≤ (certificate760.bound:ℝ) := rat_label_entropy_certificate_sound certificate760 valid760

def certificate761 : RatLabelEntropyCertificate := ⟨(17402087165732341/200000000000000000),⟨(200000000000000000/17402087165732341),3,10,(2441727215467642839/1000000000000000000)⟩,⟨(200000000000000000/182597912834267659),0,5,(2275770717847459/25000000000000000)⟩,(295565945826201981/1000000000000000000)⟩
theorem valid761 : certificate761.Valid := by decide +kernel
theorem sound761 : 0 ≤ cappedLabelEntropy (certificate761.rho:ℝ) ∧ cappedLabelEntropy (certificate761.rho:ℝ) ≤ (certificate761.bound:ℝ) := rat_label_entropy_certificate_sound certificate761 valid761

def certificate762 : RatLabelEntropyCertificate := ⟨(23791333835364873/250000000000000000),⟨(250000000000000000/23791333835364873),3,9,(2352139528058764881/1000000000000000000)⟩,⟨(250000000000000000/226208666164635127),0,6,(100003042957279827/1000000000000000000)⟩,(157164183398349271/500000000000000000)⟩
theorem valid762 : certificate762.Valid := by decide +kernel
theorem sound762 : 0 ≤ cappedLabelEntropy (certificate762.rho:ℝ) ∧ cappedLabelEntropy (certificate762.rho:ℝ) ≤ (certificate762.bound:ℝ) := rat_label_entropy_certificate_sound certificate762 valid762

def certificate763 : RatLabelEntropyCertificate := ⟨(2982327233625441/500000000000000000),⟨(500000000000000000/2982327233625441),7,9,(320119009487957949/62500000000000000)⟩,⟨(500000000000000000/497017672766374559),0,2,(1495628517924927/250000000000000000)⟩,(36497218922324967/1000000000000000000)⟩
theorem valid763 : certificate763.Valid := by decide +kernel
theorem sound763 : 0 ≤ cappedLabelEntropy (certificate763.rho:ℝ) ∧ cappedLabelEntropy (certificate763.rho:ℝ) ≤ (certificate763.bound:ℝ) := rat_label_entropy_certificate_sound certificate763 valid763

def certificate764 : RatLabelEntropyCertificate := ⟨(608557521614357/125000000000000000),⟨(125000000000000000/608557521614357),7,12,(1064995515628967301/200000000000000000)⟩,⟨(125000000000000000/124391442478385643),0,2,(2440174865031369/500000000000000000)⟩,(15390515601317387/500000000000000000)⟩
theorem valid764 : certificate764.Valid := by decide +kernel
theorem sound764 : 0 ≤ cappedLabelEntropy (certificate764.rho:ℝ) ∧ cappedLabelEntropy (certificate764.rho:ℝ) ≤ (certificate764.bound:ℝ) := rat_label_entropy_certificate_sound certificate764 valid764

def certificate765 : RatLabelEntropyCertificate := ⟨(1039636694331053/200000000000000000),⟨(200000000000000000/1039636694331053),7,11,(2629723023399755201/500000000000000000)⟩,⟨(200000000000000000/198960363305668947),0,2,(5211741030886823/1000000000000000000)⟩,(16262107477668679/500000000000000000)⟩
theorem valid765 : certificate765.Valid := by decide +kernel
theorem sound765 : 0 ≤ cappedLabelEntropy (certificate765.rho:ℝ) ∧ cappedLabelEntropy (certificate765.rho:ℝ) ≤ (certificate765.bound:ℝ) := rat_label_entropy_certificate_sound certificate765 valid765

def certificate766 : RatLabelEntropyCertificate := ⟨(260947045753167/25000000000000000),⟨(25000000000000000/260947045753167),6,11,(4562313606947180443/1000000000000000000)⟩,⟨(25000000000000000/24739052954246833),0,3,(10492738578073041/1000000000000000000)⟩,(29002053457007197/500000000000000000)⟩
theorem valid766 : certificate766.Valid := by decide +kernel
theorem sound766 : 0 ≤ cappedLabelEntropy (certificate766.rho:ℝ) ∧ cappedLabelEntropy (certificate766.rho:ℝ) ≤ (certificate766.bound:ℝ) := rat_label_entropy_certificate_sound certificate766 valid766

def certificate767 : RatLabelEntropyCertificate := ⟨(42487848343593693/500000000000000000),⟨(500000000000000000/42487848343593693),3,11,(123269499235116181/50000000000000000)⟩,⟨(500000000000000000/457512151656406307),0,5,(710437224493947/8000000000000000)⟩,(58151329470890393/200000000000000000)⟩
theorem valid767 : certificate767.Valid := by decide +kernel
theorem sound767 : 0 ≤ cappedLabelEntropy (certificate767.rho:ℝ) ∧ cappedLabelEntropy (certificate767.rho:ℝ) ≤ (certificate767.bound:ℝ) := rat_label_entropy_certificate_sound certificate767 valid767

def certificate768 : RatLabelEntropyCertificate := ⟨(95050515833734117/1000000000000000000),⟨(1000000000000000000/95050515833734117),3,9,(588336695772486493/250000000000000000)⟩,⟨(1000000000000000000/904949484166265883),0,6,(49938077720469091/500000000000000000)⟩,(78517425253786239/250000000000000000)⟩
theorem valid768 : certificate768.Valid := by decide +kernel
theorem sound768 : 0 ≤ cappedLabelEntropy (certificate768.rho:ℝ) ∧ cappedLabelEntropy (certificate768.rho:ℝ) ≤ (certificate768.bound:ℝ) := rat_label_entropy_certificate_sound certificate768 valid768

def certificate769 : RatLabelEntropyCertificate := ⟨(3079912030804319/500000000000000000),⟨(500000000000000000/3079912030804319),7,8,(5089707063271763127/1000000000000000000)⟩,⟨(500000000000000000/496920087969195681),0,2,(772359255980237/125000000000000000)⟩,(9373128326422299/250000000000000000)⟩
theorem valid769 : certificate769.Valid := by decide +kernel
theorem sound769 : 0 ≤ cappedLabelEntropy (certificate769.rho:ℝ) ∧ cappedLabelEntropy (certificate769.rho:ℝ) ≤ (certificate769.bound:ℝ) := rat_label_entropy_certificate_sound certificate769 valid769

def certificate770 : RatLabelEntropyCertificate := ⟨(1011634115013803/200000000000000000),⟨(200000000000000000/1011634115013803),7,11,(2643375203742739513/500000000000000000)⟩,⟨(200000000000000000/198988365884986197),0,2,(633875802760277/125000000000000000)⟩,(31786641755489229/1000000000000000000)⟩
theorem valid770 : certificate770.Valid := by decide +kernel
theorem sound770 : 0 ≤ cappedLabelEntropy (certificate770.rho:ℝ) ∧ cappedLabelEntropy (certificate770.rho:ℝ) ≤ (certificate770.bound:ℝ) := rat_label_entropy_certificate_sound certificate770 valid770

def certificate771 : RatLabelEntropyCertificate := ⟨(5402547044365051/1000000000000000000),⟨(1000000000000000000/5402547044365051),7,10,(2610442380866561127/500000000000000000)⟩,⟨(1000000000000000000/994597452955634949),0,2,(1083438715571521/200000000000000000)⟩,(33594002473176611/1000000000000000000)⟩
theorem valid771 : certificate771.Valid := by decide +kernel
theorem sound771 : 0 ≤ cappedLabelEntropy (certificate771.rho:ℝ) ∧ cappedLabelEntropy (certificate771.rho:ℝ) ≤ (certificate771.bound:ℝ) := rat_label_entropy_certificate_sound certificate771 valid771

def certificate772 : RatLabelEntropyCertificate := ⟨(1349540789733227/125000000000000000),⟨(125000000000000000/1349540789733227),6,10,(4528549358471219129/1000000000000000000)⟩,⟨(125000000000000000/123650459210266773),0,3,(10855029550694193/1000000000000000000)⟩,(59629531730092003/1000000000000000000)⟩
theorem valid772 : certificate772.Valid := by decide +kernel
theorem sound772 : 0 ≤ cappedLabelEntropy (certificate772.rho:ℝ) ∧ cappedLabelEntropy (certificate772.rho:ℝ) ≤ (certificate772.bound:ℝ) := rat_label_entropy_certificate_sound certificate772 valid772

def certificate773 : RatLabelEntropyCertificate := ⟨(4310093814873409/50000000000000000),⟨(50000000000000000/4310093814873409),3,10,(612765833689352143/250000000000000000)⟩,⟨(50000000000000000/45689906185126591),0,5,(22536400786560171/250000000000000000)⟩,(917691066859643/3125000000000000)⟩
theorem valid773 : certificate773.Valid := by decide +kernel
theorem sound773 : 0 ≤ cappedLabelEntropy (certificate773.rho:ℝ) ∧ cappedLabelEntropy (certificate773.rho:ℝ) ≤ (certificate773.bound:ℝ) := rat_label_entropy_certificate_sound certificate773 valid773

def certificate774 : RatLabelEntropyCertificate := ⟨(11867280899844057/125000000000000000),⟨(125000000000000000/11867280899844057),3,9,(2354528628229178119/1000000000000000000)⟩,⟨(125000000000000000/113132719100155943),0,6,(99752102470622117/1000000000000000000)⟩,(156908316825516071/500000000000000000)⟩
theorem valid774 : certificate774.Valid := by decide +kernel
theorem sound774 : 0 ≤ cappedLabelEntropy (certificate774.rho:ℝ) ∧ cappedLabelEntropy (certificate774.rho:ℝ) ≤ (certificate774.bound:ℝ) := rat_label_entropy_certificate_sound certificate774 valid774

def certificate775 : RatLabelEntropyCertificate := ⟨(1282050258673597/200000000000000000),⟨(200000000000000000/1282050258673597),7,7,(631232100685556247/125000000000000000)⟩,⟨(200000000000000000/198717949741326403),0,2,(6430885180389831/1000000000000000000)⟩,(38760512709024553/1000000000000000000)⟩
theorem valid775 : certificate775.Valid := by decide +kernel
theorem sound775 : 0 ≤ cappedLabelEntropy (certificate775.rho:ℝ) ∧ cappedLabelEntropy (certificate775.rho:ℝ) ≤ (certificate775.bound:ℝ) := rat_label_entropy_certificate_sound certificate775 valid775

def certificate776 : RatLabelEntropyCertificate := ⟨(5252481572942277/1000000000000000000),⟨(1000000000000000000/5252481572942277),7,10,(1312263658374109089/250000000000000000)⟩,⟨(1000000000000000000/994747518427057723),0,2,(5266324348170293/1000000000000000000)⟩,(32809225814381701/1000000000000000000)⟩
theorem valid776 : certificate776.Valid := by decide +kernel
theorem sound776 : 0 ≤ cappedLabelEntropy (certificate776.rho:ℝ) ∧ cappedLabelEntropy (certificate776.rho:ℝ) ≤ (certificate776.bound:ℝ) := rat_label_entropy_certificate_sound certificate776 valid776

def certificate777 : RatLabelEntropyCertificate := ⟨(279314943521017/50000000000000000),⟨(50000000000000000/279314943521017),7,10,(2593719154706901303/500000000000000000)⟩,⟨(50000000000000000/49720685056478983),0,2,(700245074070377/125000000000000000)⟩,(17274623567343083/500000000000000000)⟩
theorem valid777 : certificate777.Valid := by decide +kernel
theorem sound777 : 0 ≤ cappedLabelEntropy (certificate777.rho:ℝ) ∧ cappedLabelEntropy (certificate777.rho:ℝ) ≤ (certificate777.bound:ℝ) := rat_label_entropy_certificate_sound certificate777 valid777

def certificate778 : RatLabelEntropyCertificate := ⟨(2137832279384289/200000000000000000),⟨(200000000000000000/2137832279384289),6,10,(4538525004457194939/1000000000000000000)⟩,⟨(200000000000000000/197862167720615711),0,3,(10746700882510311/1000000000000000000)⟩,(29572426969449649/500000000000000000)⟩
theorem valid778 : certificate778.Valid := by decide +kernel
theorem sound778 : 0 ≤ cappedLabelEntropy (certificate778.rho:ℝ) ∧ cappedLabelEntropy (certificate778.rho:ℝ) ≤ (certificate778.bound:ℝ) := rat_label_entropy_certificate_sound certificate778 valid778

def certificate779 : RatLabelEntropyCertificate := ⟨(5206544115865729/62500000000000000),⟨(62500000000000000/5206544115865729),3,11,(497050047712328663/200000000000000000)⟩,⟨(62500000000000000/57293455884134271),0,5,(43490073749829499/500000000000000000)⟩,(286767331993667647/1000000000000000000)⟩
theorem valid779 : certificate779.Valid := by decide +kernel
theorem sound779 : 0 ≤ cappedLabelEntropy (certificate779.rho:ℝ) ∧ cappedLabelEntropy (certificate779.rho:ℝ) ≤ (certificate779.bound:ℝ) := rat_label_entropy_certificate_sound certificate779 valid779

end Cycle12.CutLabelCertificates.Entropy038
