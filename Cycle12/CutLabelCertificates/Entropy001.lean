import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy001

def certificate20 : RatLabelEntropyCertificate := ⟨(12645756995938561/200000000000000000),⟨(200000000000000000/12645756995938561),3,15,(2760995622979639711/1000000000000000000)⟩,⟨(200000000000000000/187354243004061439),0,5,(65316194091817729/1000000000000000000)⟩,(235760729075146927/1000000000000000000)⟩
theorem valid20 : certificate20.Valid := by decide +kernel
theorem sound20 : 0 ≤ cappedLabelEntropy (certificate20.rho:ℝ) ∧ cappedLabelEntropy (certificate20.rho:ℝ) ≤ (certificate20.bound:ℝ) := rat_label_entropy_certificate_sound certificate20 valid20

def certificate21 : RatLabelEntropyCertificate := ⟨(34578596283928039/500000000000000000),⟨(500000000000000000/34578596283928039),3,14,(667843303070994481/250000000000000000)⟩,⟨(500000000000000000/465421403716071961),0,5,(8958107334476389/125000000000000000)⟩,(251453389906555187/1000000000000000000)⟩
theorem valid21 : certificate21.Valid := by decide +kernel
theorem sound21 : 0 ≤ cappedLabelEntropy (certificate21.rho:ℝ) ∧ cappedLabelEntropy (certificate21.rho:ℝ) ≤ (certificate21.bound:ℝ) := rat_label_entropy_certificate_sound certificate21 valid21

def certificate22 : RatLabelEntropyCertificate := ⟨(75182358000219201/1000000000000000000),⟨(1000000000000000000/75182358000219201),3,13,(517567735322078281/200000000000000000)⟩,⟨(1000000000000000000/924817641999780799),0,5,(3126348187564913/40000000000000000)⟩,(8338823837627741/31250000000000000)⟩
theorem valid22 : certificate22.Valid := by decide +kernel
theorem sound22 : 0 ≤ cappedLabelEntropy (certificate22.rho:ℝ) ∧ cappedLabelEntropy (certificate22.rho:ℝ) ≤ (certificate22.bound:ℝ) := rat_label_entropy_certificate_sound certificate22 valid22

def certificate23 : RatLabelEntropyCertificate := ⟨(20373925261785973/250000000000000000),⟨(250000000000000000/20373925261785973),3,11,(2507205008014343791/1000000000000000000)⟩,⟨(250000000000000000/229626074738214027),0,5,(85008693931969539/1000000000000000000)⟩,(141203640310960281/500000000000000000)⟩
theorem valid23 : certificate23.Valid := by decide +kernel
theorem sound23 : 0 ≤ cappedLabelEntropy (certificate23.rho:ℝ) ∧ cappedLabelEntropy (certificate23.rho:ℝ) ≤ (certificate23.bound:ℝ) := rat_label_entropy_certificate_sound certificate23 valid23

def certificate24 : RatLabelEntropyCertificate := ⟨(22027643528860111/250000000000000000),⟨(250000000000000000/22027643528860111),3,10,(2429162729230498833/1000000000000000000)⟩,⟨(250000000000000000/227972356471139889),0,5,(46118269903015399/500000000000000000)⟩,(74536112005407301/250000000000000000)⟩
theorem valid24 : certificate24.Valid := by decide +kernel
theorem sound24 : 0 ≤ cappedLabelEntropy (certificate24.rho:ℝ) ∧ cappedLabelEntropy (certificate24.rho:ℝ) ≤ (certificate24.bound:ℝ) := rat_label_entropy_certificate_sound certificate24 valid24

def certificate25 : RatLabelEntropyCertificate := ⟨(94945537311997371/1000000000000000000),⟨(1000000000000000000/94945537311997371),3,8,(1177225921614316957/500000000000000000)⟩,⟨(1000000000000000000/905054462688002629),0,5,(99760157327191627/1000000000000000000)⟩,(313833070917997273/1000000000000000000)⟩
theorem valid25 : certificate25.Valid := by decide +kernel
theorem sound25 : 0 ≤ cappedLabelEntropy (certificate25.rho:ℝ) ∧ cappedLabelEntropy (certificate25.rho:ℝ) ≤ (certificate25.bound:ℝ) := rat_label_entropy_certificate_sound certificate25 valid25

def certificate26 : RatLabelEntropyCertificate := ⟨(102354284405087273/1000000000000000000),⟨(1000000000000000000/102354284405087273),3,7,(2279315107417911663/1000000000000000000)⟩,⟨(1000000000000000000/897645715594912727),0,6,(21595962917878387/200000000000000000)⟩,(3302252846903657/10000000000000000)⟩
theorem valid26 : certificate26.Valid := by decide +kernel
theorem sound26 : 0 ≤ cappedLabelEntropy (certificate26.rho:ℝ) ∧ cappedLabelEntropy (certificate26.rho:ℝ) ≤ (certificate26.bound:ℝ) := rat_label_entropy_certificate_sound certificate26 valid26

def certificate27 : RatLabelEntropyCertificate := ⟨(54817985672925693/500000000000000000),⟨(500000000000000000/54817985672925693),3,6,(221058975260561141/100000000000000000)⟩,⟨(500000000000000000/445182014327074307),0,6,(116124878922504243/1000000000000000000)⟩,(43219196224814703/125000000000000000)⟩
theorem valid27 : certificate27.Valid := by decide +kernel
theorem sound27 : 0 ≤ cappedLabelEntropy (certificate27.rho:ℝ) ∧ cappedLabelEntropy (certificate27.rho:ℝ) ≤ (certificate27.bound:ℝ) := rat_label_entropy_certificate_sound certificate27 valid27

def certificate28 : RatLabelEntropyCertificate := ⟨(116988125377074891/1000000000000000000),⟨(1000000000000000000/116988125377074891),3,5,(2145682841838727/1000000000000000)⟩,⟨(1000000000000000000/883011874622925109),0,6,(124416630424518377/1000000000000000000)⟩,(360880775385888979/1000000000000000000)⟩
theorem valid28 : certificate28.Valid := by decide +kernel
theorem sound28 : 0 ≤ cappedLabelEntropy (certificate28.rho:ℝ) ∧ cappedLabelEntropy (certificate28.rho:ℝ) ≤ (certificate28.bound:ℝ) := rat_label_entropy_certificate_sound certificate28 valid28

def certificate29 : RatLabelEntropyCertificate := ⟨(62224965631189079/500000000000000000),⟨(500000000000000000/62224965631189079),3,2,(1041925901249960367/500000000000000000)⟩,⟨(500000000000000000/437775034368810921),0,6,(66451470078148073/500000000000000000)⟩,(187849195985687547/500000000000000000)⟩
theorem valid29 : certificate29.Valid := by decide +kernel
theorem sound29 : 0 ≤ cappedLabelEntropy (certificate29.rho:ℝ) ∧ cappedLabelEntropy (certificate29.rho:ℝ) ≤ (certificate29.bound:ℝ) := rat_label_entropy_certificate_sound certificate29 valid29

def certificate30 : RatLabelEntropyCertificate := ⟨(66076682449900601/500000000000000000),⟨(500000000000000000/66076682449900601),2,15,(404758435105153753/200000000000000000)⟩,⟨(500000000000000000/433923317550099399),0,6,(141740267605474621/1000000000000000000)⟩,(78091952030646461/200000000000000000)⟩
theorem valid30 : certificate30.Valid := by decide +kernel
theorem sound30 : 0 ≤ cappedLabelEntropy (certificate30.rho:ℝ) ∧ cappedLabelEntropy (certificate30.rho:ℝ) ≤ (certificate30.bound:ℝ) := rat_label_entropy_certificate_sound certificate30 valid30

def certificate31 : RatLabelEntropyCertificate := ⟨(70168365037842959/500000000000000000),⟨(500000000000000000/70168365037842959),2,14,(1963710529445933107/1000000000000000000)⟩,⟨(500000000000000000/429831634962157041),0,7,(37803628252150829/250000000000000000)⟩,(202787138615312427/500000000000000000)⟩
theorem valid31 : certificate31.Valid := by decide +kernel
theorem sound31 : 0 ≤ cappedLabelEntropy (certificate31.rho:ℝ) ∧ cappedLabelEntropy (certificate31.rho:ℝ) ≤ (certificate31.bound:ℝ) := rat_label_entropy_certificate_sound certificate31 valid31

def certificate32 : RatLabelEntropyCertificate := ⟨(5792653962209363/40000000000000000),⟨(40000000000000000/5792653962209363),2,13,(1932288897564117151/1000000000000000000)⟩,⟨(40000000000000000/34207346037790637),0,6,(15643903668419961/100000000000000000)⟩,(413611130007074621/1000000000000000000)⟩
theorem valid32 : certificate32.Valid := by decide +kernel
theorem sound32 : 0 ≤ cappedLabelEntropy (certificate32.rho:ℝ) ∧ cappedLabelEntropy (certificate32.rho:ℝ) ≤ (certificate32.bound:ℝ) := rat_label_entropy_certificate_sound certificate32 valid32

def certificate33 : RatLabelEntropyCertificate := ⟨(148516600215273631/1000000000000000000),⟨(1000000000000000000/148516600215273631),2,13,(476764635256382287/250000000000000000)⟩,⟨(1000000000000000000/851483399784726369),0,7,(80387637165527049/500000000000000000)⟩,(420127328113339511/1000000000000000000)⟩
theorem valid33 : certificate33.Valid := by decide +kernel
theorem sound33 : 0 ≤ cappedLabelEntropy (certificate33.rho:ℝ) ∧ cappedLabelEntropy (certificate33.rho:ℝ) ≤ (certificate33.bound:ℝ) := rat_label_entropy_certificate_sound certificate33 valid33

def certificate34 : RatLabelEntropyCertificate := ⟨(153270367886940079/1000000000000000000),⟨(1000000000000000000/153270367886940079),2,12,(1875551806720139387/1000000000000000000)⟩,⟨(1000000000000000000/846729632113059921),0,7,(83186920882701077/500000000000000000)⟩,(107085044309566577/250000000000000000)⟩
theorem valid34 : certificate34.Valid := by decide +kernel
theorem sound34 : 0 ≤ cappedLabelEntropy (certificate34.rho:ℝ) ∧ cappedLabelEntropy (certificate34.rho:ℝ) ≤ (certificate34.bound:ℝ) := rat_label_entropy_certificate_sound certificate34 valid34

def certificate35 : RatLabelEntropyCertificate := ⟨(31404049739306821/200000000000000000),⟨(200000000000000000/31404049739306821),2,12,(46284512734017229/25000000000000000)⟩,⟨(200000000000000000/168595950260693179),0,7,(170812341074852037/1000000000000000000)⟩,(217347786405286481/500000000000000000)⟩
theorem valid35 : certificate35.Valid := by decide +kernel
theorem sound35 : 0 ≤ cappedLabelEntropy (certificate35.rho:ℝ) ∧ cappedLabelEntropy (certificate35.rho:ℝ) ≤ (certificate35.bound:ℝ) := rat_label_entropy_certificate_sound certificate35 valid35

def certificate36 : RatLabelEntropyCertificate := ⟨(32340093273335399/200000000000000000),⟨(200000000000000000/32340093273335399),2,11,(182200962825557273/100000000000000000)⟩,⟨(200000000000000000/167659906726664601),0,7,(176379803662799561/1000000000000000000)⟩,(221239456883181921/500000000000000000)⟩
theorem valid36 : certificate36.Valid := by decide +kernel
theorem sound36 : 0 ≤ cappedLabelEntropy (certificate36.rho:ℝ) ∧ cappedLabelEntropy (certificate36.rho:ℝ) ≤ (certificate36.bound:ℝ) := rat_label_entropy_certificate_sound certificate36 valid36

def certificate37 : RatLabelEntropyCertificate := ⟨(164129963818970093/1000000000000000000),⟨(1000000000000000000/164129963818970093),2,11,(180709670267961307/100000000000000000)⟩,⟨(1000000000000000000/835870036181029907),0,7,(179282137096056521/1000000000000000000)⟩,(446455282849278177/1000000000000000000)⟩
theorem valid37 : certificate37.Valid := by decide +kernel
theorem sound37 : 0 ≤ cappedLabelEntropy (certificate37.rho:ℝ) ∧ cappedLabelEntropy (certificate37.rho:ℝ) ≤ (certificate37.bound:ℝ) := rat_label_entropy_certificate_sound certificate37 valid37

def certificate38 : RatLabelEntropyCertificate := ⟨(82824367354056397/500000000000000000),⟨(500000000000000000/82824367354056397),2,11,(14383086308885069/8000000000000000)⟩,⟨(500000000000000000/417175632645943603),0,7,(11318798993140041/62500000000000000)⟩,(448919174217223923/1000000000000000000)⟩
theorem valid38 : certificate38.Valid := by decide +kernel
theorem sound38 : 0 ≤ cappedLabelEntropy (certificate38.rho:ℝ) ∧ cappedLabelEntropy (certificate38.rho:ℝ) ≤ (certificate38.bound:ℝ) := rat_label_entropy_certificate_sound certificate38 valid38

def certificate39 : RatLabelEntropyCertificate := ⟨(85160789914632243/500000000000000000),⟨(500000000000000000/85160789914632243),2,10,(1770066982786664331/1000000000000000000)⟩,⟨(500000000000000000/414839210085367757),0,7,(186717098845350917/1000000000000000000)⟩,(456395752500717989/1000000000000000000)⟩
theorem valid39 : certificate39.Valid := by decide +kernel
theorem sound39 : 0 ≤ cappedLabelEntropy (certificate39.rho:ℝ) ∧ cappedLabelEntropy (certificate39.rho:ℝ) ≤ (certificate39.bound:ℝ) := rat_label_entropy_certificate_sound certificate39 valid39

end Cycle12.CutLabelCertificates.Entropy001
