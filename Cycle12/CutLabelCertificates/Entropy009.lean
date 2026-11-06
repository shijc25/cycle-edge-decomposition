import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy009

def certificate180 : RatLabelEntropyCertificate := ⟨(19176652099368087/1000000000000000000),⟨(1000000000000000000/19176652099368087),5,12,(3954061776411970407/1000000000000000000)⟩,⟨(1000000000000000000/980823347900631913),0,3,(19362909127740617/1000000000000000000)⟩,(94817260421427977/1000000000000000000)⟩
theorem valid180 : certificate180.Valid := by decide +kernel
theorem sound180 : 0 ≤ cappedLabelEntropy (certificate180.rho:ℝ) ∧ cappedLabelEntropy (certificate180.rho:ℝ) ≤ (certificate180.bound:ℝ) := rat_label_entropy_certificate_sound certificate180 valid180

def certificate181 : RatLabelEntropyCertificate := ⟨(339271889621247/15625000000000000),⟨(15625000000000000/339271889621247),5,10,(3829825654400812767/1000000000000000000)⟩,⟨(15625000000000000/15285728110378753),0,3,(4390521159795943/200000000000000000)⟩,(10463448001574531/100000000000000000)⟩
theorem valid181 : certificate181.Valid := by decide +kernel
theorem sound181 : 0 ≤ cappedLabelEntropy (certificate181.rho:ℝ) ∧ cappedLabelEntropy (certificate181.rho:ℝ) ≤ (certificate181.bound:ℝ) := rat_label_entropy_certificate_sound certificate181 valid181

def certificate182 : RatLabelEntropyCertificate := ⟨(24217806477693433/1000000000000000000),⟨(1000000000000000000/24217806477693433),5,8,(930166777881953161/250000000000000000)⟩,⟨(1000000000000000000/975782193522306567),0,4,(24515879848158421/1000000000000000000)⟩,(890848086634879/7812500000000000)⟩
theorem valid182 : certificate182.Valid := by decide +kernel
theorem sound182 : 0 ≤ cappedLabelEntropy (certificate182.rho:ℝ) ∧ cappedLabelEntropy (certificate182.rho:ℝ) ≤ (certificate182.bound:ℝ) := rat_label_entropy_certificate_sound certificate182 valid182

def certificate183 : RatLabelEntropyCertificate := ⟨(2709807497312019/100000000000000000),⟨(100000000000000000/2709807497312019),5,6,(451036573477717159/125000000000000000)⟩,⟨(100000000000000000/97290192502687981),0,4,(13735999177232643/500000000000000000)⟩,(3890791973535683/31250000000000000)⟩
theorem valid183 : certificate183.Valid := by decide +kernel
theorem sound183 : 0 ≤ cappedLabelEntropy (certificate183.rho:ℝ) ∧ cappedLabelEntropy (certificate183.rho:ℝ) ≤ (certificate183.bound:ℝ) := rat_label_entropy_certificate_sound certificate183 valid183

def certificate184 : RatLabelEntropyCertificate := ⟨(14937287509219139/500000000000000000),⟨(500000000000000000/14937287509219139),5,4,(3510747494155884939/1000000000000000000)⟩,⟨(500000000000000000/485062712490780861),0,4,(30329911739060921/1000000000000000000)⟩,(134305907900463919/1000000000000000000)⟩
theorem valid184 : certificate184.Valid := by decide +kernel
theorem sound184 : 0 ≤ cappedLabelEntropy (certificate184.rho:ℝ) ∧ cappedLabelEntropy (certificate184.rho:ℝ) ≤ (certificate184.bound:ℝ) := rat_label_entropy_certificate_sound certificate184 valid184

def certificate185 : RatLabelEntropyCertificate := ⟨(513101226700353/15625000000000000),⟨(15625000000000000/513101226700353),4,15,(3416154325896818337/1000000000000000000)⟩,⟨(15625000000000000/15111898773299647),0,4,(1669488193871231/50000000000000000)⟩,(144474605247705149/1000000000000000000)⟩
theorem valid185 : certificate185.Valid := by decide +kernel
theorem sound185 : 0 ≤ cappedLabelEntropy (certificate185.rho:ℝ) ∧ cappedLabelEntropy (certificate185.rho:ℝ) ≤ (certificate185.bound:ℝ) := rat_label_entropy_certificate_sound certificate185 valid185

def certificate186 : RatLabelEntropyCertificate := ⟨(36126381730842419/1000000000000000000),⟨(1000000000000000000/36126381730842419),4,13,(3320731884676365611/1000000000000000000)⟩,⟨(1000000000000000000/963873618269157581),0,4,(7359018869334107/200000000000000000)⟩,(155431848414078523/1000000000000000000)⟩
theorem valid186 : certificate186.Valid := by decide +kernel
theorem sound186 : 0 ≤ cappedLabelEntropy (certificate186.rho:ℝ) ∧ cappedLabelEntropy (certificate186.rho:ℝ) ≤ (certificate186.bound:ℝ) := rat_label_entropy_certificate_sound certificate186 valid186

def certificate187 : RatLabelEntropyCertificate := ⟨(4911737147677521/125000000000000000),⟨(125000000000000000/4911737147677521),4,11,(3236686060169927931/1000000000000000000)⟩,⟨(125000000000000000/120088262852322479),0,4,(40086741115943627/1000000000000000000)⟩,(16569358608904861/100000000000000000)⟩
theorem valid187 : certificate187.Valid := by decide +kernel
theorem sound187 : 0 ≤ cappedLabelEntropy (certificate187.rho:ℝ) ∧ cappedLabelEntropy (certificate187.rho:ℝ) ≤ (certificate187.bound:ℝ) := rat_label_entropy_certificate_sound certificate187 valid187

def certificate188 : RatLabelEntropyCertificate := ⟨(42700553751522909/1000000000000000000),⟨(1000000000000000000/42700553751522909),4,11,(3153543390411907153/1000000000000000000)⟩,⟨(1000000000000000000/957299446248477091),0,4,(1745561419255777/40000000000000000)⟩,(176433673551199963/1000000000000000000)⟩
theorem valid188 : certificate188.Valid := by decide +kernel
theorem sound188 : 0 ≤ cappedLabelEntropy (certificate188.rho:ℝ) ∧ cappedLabelEntropy (certificate188.rho:ℝ) ≤ (certificate188.bound:ℝ) := rat_label_entropy_certificate_sound certificate188 valid188

def certificate189 : RatLabelEntropyCertificate := ⟨(23205464231252837/500000000000000000),⟨(500000000000000000/23205464231252837),4,9,(23986096252132283/7812500000000000)⟩,⟨(500000000000000000/476794535768747163),0,4,(47522442953274291/1000000000000000000)⟩,(11738041118832793/62500000000000000)⟩
theorem valid189 : certificate189.Valid := by decide +kernel
theorem sound189 : 0 ≤ cappedLabelEntropy (certificate189.rho:ℝ) ∧ cappedLabelEntropy (certificate189.rho:ℝ) ≤ (certificate189.bound:ℝ) := rat_label_entropy_certificate_sound certificate189 valid189

def certificate190 : RatLabelEntropyCertificate := ⟨(9992585831274823/200000000000000000),⟨(200000000000000000/9992585831274823),4,8,(2996473965411925741/1000000000000000000)⟩,⟨(200000000000000000/190007414168725177),0,4,(12813568302056957/250000000000000000)⟩,(49601519009939791/250000000000000000)⟩
theorem valid190 : certificate190.Valid := by decide +kernel
theorem sound190 : 0 ≤ cappedLabelEntropy (certificate190.rho:ℝ) ∧ cappedLabelEntropy (certificate190.rho:ℝ) ≤ (certificate190.bound:ℝ) := rat_label_entropy_certificate_sound certificate190 valid190

def certificate191 : RatLabelEntropyCertificate := ⟨(13449036219553173/250000000000000000),⟨(250000000000000000/13449036219553173),4,6,(1461276735460324147/500000000000000000)⟩,⟨(250000000000000000/236550963780446827),0,5,(6912155184146813/125000000000000000)⟩,(209544572995488657/1000000000000000000)⟩
theorem valid191 : certificate191.Valid := by decide +kernel
theorem sound191 : 0 ≤ cappedLabelEntropy (certificate191.rho:ℝ) ∧ cappedLabelEntropy (certificate191.rho:ℝ) ≤ (certificate191.bound:ℝ) := rat_label_entropy_certificate_sound certificate191 valid191

def certificate192 : RatLabelEntropyCertificate := ⟨(57940391888539363/1000000000000000000),⟨(1000000000000000000/57940391888539363),4,5,(712085130741981273/250000000000000000)⟩,⟨(1000000000000000000/942059608111460637),0,4,(29843364078899893/500000000000000000)⟩,(55315605467640221/250000000000000000)⟩
theorem valid192 : certificate192.Valid := by decide +kernel
theorem sound192 : 0 ≤ cappedLabelEntropy (certificate192.rho:ℝ) ∧ cappedLabelEntropy (certificate192.rho:ℝ) ≤ (certificate192.bound:ℝ) := rat_label_entropy_certificate_sound certificate192 valid192

def certificate193 : RatLabelEntropyCertificate := ⟨(967686528648681/15625000000000000),⟨(15625000000000000/967686528648681),4,3,(278171927381420971/100000000000000000)⟩,⟨(15625000000000000/14657313471351319),0,5,(63932771663251079/1000000000000000000)⟩,(232250556359232017/1000000000000000000)⟩
theorem valid193 : certificate193.Valid := by decide +kernel
theorem sound193 : 0 ≤ cappedLabelEntropy (certificate193.rho:ℝ) ∧ cappedLabelEntropy (certificate193.rho:ℝ) ≤ (certificate193.bound:ℝ) := rat_label_entropy_certificate_sound certificate193 valid193

def certificate194 : RatLabelEntropyCertificate := ⟨(32998607749077457/500000000000000000),⟨(500000000000000000/32998607749077457),3,16,(1359071363633802721/500000000000000000)⟩,⟨(500000000000000000/467001392250922543),0,5,(6827585949237963/100000000000000000)⟩,(121579847103180991/500000000000000000)⟩
theorem valid194 : certificate194.Valid := by decide +kernel
theorem sound194 : 0 ≤ cappedLabelEntropy (certificate194.rho:ℝ) ∧ cappedLabelEntropy (certificate194.rho:ℝ) ≤ (certificate194.bound:ℝ) := rat_label_entropy_certificate_sound certificate194 valid194

def certificate195 : RatLabelEntropyCertificate := ⟨(70681559087333923/1000000000000000000),⟨(1000000000000000000/70681559087333923),3,13,(2649570573379273351/1000000000000000000)⟩,⟨(1000000000000000000/929318440912666077),0,5,(73303820741130177/1000000000000000000)⟩,(127699185721228491/500000000000000000)⟩
theorem valid195 : certificate195.Valid := by decide +kernel
theorem sound195 : 0 ≤ cappedLabelEntropy (certificate195.rho:ℝ) ∧ cappedLabelEntropy (certificate195.rho:ℝ) ≤ (certificate195.bound:ℝ) := rat_label_entropy_certificate_sound certificate195 valid195

def certificate196 : RatLabelEntropyCertificate := ⟨(37513201436160917/500000000000000000),⟨(500000000000000000/37513201436160917),3,13,(2589915189099144679/1000000000000000000)⟩,⟨(500000000000000000/462486798563839083),0,5,(38995042761421401/500000000000000000)⟩,(133225395164428589/500000000000000000)⟩
theorem valid196 : certificate196.Valid := by decide +kernel
theorem sound196 : 0 ≤ cappedLabelEntropy (certificate196.rho:ℝ) ∧ cappedLabelEntropy (certificate196.rho:ℝ) ≤ (certificate196.bound:ℝ) := rat_label_entropy_certificate_sound certificate196 valid196

def certificate197 : RatLabelEntropyCertificate := ⟨(39710308556658193/500000000000000000),⟨(500000000000000000/39710308556658193),3,11,(2532997283058446961/1000000000000000000)⟩,⟨(500000000000000000/460289691443341807),0,5,(41376021574961309/500000000000000000)⟩,(277352032182423581/1000000000000000000)⟩
theorem valid197 : certificate197.Valid := by decide +kernel
theorem sound197 : 0 ≤ cappedLabelEntropy (certificate197.rho:ℝ) ∧ cappedLabelEntropy (certificate197.rho:ℝ) ≤ (certificate197.bound:ℝ) := rat_label_entropy_certificate_sound certificate197 valid197

def certificate198 : RatLabelEntropyCertificate := ⟨(84103450378641463/1000000000000000000),⟨(1000000000000000000/84103450378641463),3,11,(2475707685750394091/1000000000000000000)⟩,⟨(1000000000000000000/915896549621358537),0,5,(43925928890233703/500000000000000000)⟩,(288678771919485961/1000000000000000000)⟩
theorem valid198 : certificate198.Valid := by decide +kernel
theorem sound198 : 0 ≤ cappedLabelEntropy (certificate198.rho:ℝ) ∧ cappedLabelEntropy (certificate198.rho:ℝ) ≤ (certificate198.bound:ℝ) := rat_label_entropy_certificate_sound certificate198 valid198

def certificate199 : RatLabelEntropyCertificate := ⟨(89314123107793603/1000000000000000000),⟨(1000000000000000000/89314123107793603),3,10,(483119130020380507/200000000000000000)⟩,⟨(1000000000000000000/910685876892206397),0,5,(18711450499616193/200000000000000000)⟩,(75237018950673119/250000000000000000)⟩
theorem valid199 : certificate199.Valid := by decide +kernel
theorem sound199 : 0 ≤ cappedLabelEntropy (certificate199.rho:ℝ) ∧ cappedLabelEntropy (certificate199.rho:ℝ) ≤ (certificate199.bound:ℝ) := rat_label_entropy_certificate_sound certificate199 valid199

end Cycle12.CutLabelCertificates.Entropy009
