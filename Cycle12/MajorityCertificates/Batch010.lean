import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch010

def certificate400 : RatMajorityCertificate := ⟨0,(1007155399278960521/1000000000000000000),(2333934031/1956060000),(880416899422157387/2000000000000000000),(44020844971107869351/100000000000000000000),(180316827439910943/250000000000000000),false⟩
theorem valid400 : certificate400.Valid := by decide +kernel
theorem bound400 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate400.a certificate400.b certificate400.c x ≤ (certificate400.bound:ℝ) :=
  rat_majority_certificate_sound certificate400 valid400 x hx0 hx1

def certificate401 : RatMajorityCertificate := ⟨(202277974618520173/1000000000000000000),(803430044986705394186228809290909867/1000000000000000000000000000000000000),(2333934031/1956060000),(7928881897568270617/20000000000000000000),(19822204743920676543/50000000000000000000),(180316827439910943/250000000000000000),false⟩
theorem valid401 : certificate401.Valid := by decide +kernel
theorem bound401 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate401.a certificate401.b certificate401.c x ≤ (certificate401.bound:ℝ) :=
  rat_majority_certificate_sound certificate401 valid401 x hx0 hx1

def certificate402 : RatMajorityCertificate := ⟨0,(1007155399278960521/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543429314248083431/1000000000000000000),false⟩
theorem valid402 : certificate402.Valid := by decide +kernel
theorem bound402 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate402.a certificate402.b certificate402.c x ≤ (certificate402.bound:ℝ) :=
  rat_majority_certificate_sound certificate402 valid402 x hx0 hx1

def certificate403 : RatMajorityCertificate := ⟨(64386730358823341/500000000000000000),(438730256516672769478248064847679339/500000000000000000000000000000000000),1,(18273080889559626571/50000000000000000000),(36546161779119253143/100000000000000000000),(543429314248083431/1000000000000000000),false⟩
theorem valid403 : certificate403.Valid := by decide +kernel
theorem bound403 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate403.a certificate403.b certificate403.c x ≤ (certificate403.bound:ℝ) :=
  rat_majority_certificate_sound certificate403 valid403 x hx0 hx1

def certificate404 : RatMajorityCertificate := ⟨0,(251786673365702731/250000000000000000),(31063427/26193200),(43856718099543698529/100000000000000000000),(4385671809954369853/10000000000000000000),(357099820529344571/500000000000000000),false⟩
theorem valid404 : certificate404.Valid := by decide +kernel
theorem bound404 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate404.a certificate404.b certificate404.c x ≤ (certificate404.bound:ℝ) :=
  rat_majority_certificate_sound certificate404 valid404 x hx0 hx1

def certificate405 : RatMajorityCertificate := ⟨(3938232145823043/20000000000000000),(4044139096375397525254583932169567/5000000000000000000000000000000000),(31063427/26193200),(396121280922483867/1000000000000000000),(39612128092248386701/100000000000000000000),(357099820529344571/500000000000000000),false⟩
theorem valid405 : certificate405.Valid := by decide +kernel
theorem bound405 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate405.a certificate405.b certificate405.c x ≤ (certificate405.bound:ℝ) :=
  rat_majority_certificate_sound certificate405 valid405 x hx0 hx1

def certificate406 : RatMajorityCertificate := ⟨0,(251786673365702731/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543214216519857657/1000000000000000000),false⟩
theorem valid406 : certificate406.Valid := by decide +kernel
theorem bound406 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate406.a certificate406.b certificate406.c x ≤ (certificate406.bound:ℝ) :=
  rat_majority_certificate_sound certificate406 valid406 x hx0 hx1

def certificate407 : RatMajorityCertificate := ⟨(15843703664807663/125000000000000000),(27484100731158927023949930051172347/31250000000000000000000000000000000),1,(18296603388160765683/50000000000000000000),(36593206776321531367/100000000000000000000),(543214216519857657/1000000000000000000),false⟩
theorem valid407 : certificate407.Valid := by decide +kernel
theorem bound407 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate407.a certificate407.b certificate407.c x ≤ (certificate407.bound:ℝ) :=
  rat_majority_certificate_sound certificate407 valid407 x hx0 hx1

def certificate408 : RatMajorityCertificate := ⟨0,(1007192387024942709/1000000000000000000),(2328158023/1963730000),(21924320775650958373/50000000000000000000),(43848641551301916747/100000000000000000000),(713904834251680939/1000000000000000000),false⟩
theorem valid408 : certificate408.Valid := by decide +kernel
theorem bound408 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate408.a certificate408.b certificate408.c x ≤ (certificate408.bound:ℝ) :=
  rat_majority_certificate_sound certificate408 valid408 x hx0 hx1

def certificate409 : RatMajorityCertificate := ⟨(12307716277109277/62500000000000000),(50553286053091485365471300942588607/62500000000000000000000000000000000),(2328158023/1963730000),(9900902754573176731/25000000000000000000),(1584144440731708277/4000000000000000000),(713904834251680939/1000000000000000000),false⟩
theorem valid409 : certificate409.Valid := by decide +kernel
theorem bound409 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate409.a certificate409.b certificate409.c x ≤ (certificate409.bound:ℝ) :=
  rat_majority_certificate_sound certificate409 valid409 x hx0 hx1

def certificate410 : RatMajorityCertificate := ⟨0,(1007192387024942709/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(108645599344552757/200000000000000000),false⟩
theorem valid410 : certificate410.Valid := by decide +kernel
theorem bound410 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate410.a certificate410.b certificate410.c x ≤ (certificate410.bound:ℝ) :=
  rat_majority_certificate_sound certificate410 valid410 x hx0 hx1

def certificate411 : RatMajorityCertificate := ⟨(126680221711093457/1000000000000000000),(879601032130897517757892854830244987/1000000000000000000000000000000000000),1,(3659493443716912257/10000000000000000000),(36594934437169122571/100000000000000000000),(108645599344552757/200000000000000000),false⟩
theorem valid411 : certificate411.Valid := by decide +kernel
theorem bound411 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate411.a certificate411.b certificate411.c x ≤ (certificate411.bound:ℝ) :=
  rat_majority_certificate_sound certificate411 valid411 x hx0 hx1

def certificate412 : RatMajorityCertificate := ⟨0,(503618998746617691/500000000000000000),(2326215387/1962980000),(1369888649925193043/3125000000000000000),(43836436797606177377/100000000000000000000),(713354287576641449/1000000000000000000),false⟩
theorem valid412 : certificate412.Valid := by decide +kernel
theorem bound412 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate412.a certificate412.b certificate412.c x ≤ (certificate412.bound:ℝ) :=
  rat_majority_certificate_sound certificate412 valid412 x hx0 hx1

def certificate413 : RatMajorityCertificate := ⟨(39192097142790547/200000000000000000),(80985915027491186921790118502233023/100000000000000000000000000000000000),(2326215387/1962980000),(3961583464450068201/10000000000000000000),(39615834644500682011/100000000000000000000),(713354287576641449/1000000000000000000),false⟩
theorem valid413 : certificate413.Valid := by decide +kernel
theorem bound413 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate413.a certificate413.b certificate413.c x ≤ (certificate413.bound:ℝ) :=
  rat_majority_certificate_sound certificate413 valid413 x hx0 hx1

def certificate414 : RatMajorityCertificate := ⟨0,(503618998746617691/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543227897614675109/1000000000000000000),false⟩
theorem valid414 : certificate414.Valid := by decide +kernel
theorem bound414 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate414.a certificate414.b certificate414.c x ≤ (certificate414.bound:ℝ) :=
  rat_majority_certificate_sound certificate414 valid414 x hx0 hx1

def certificate415 : RatMajorityCertificate := ⟨(126477597624040507/1000000000000000000),(439922477667320818251959804573190663/500000000000000000000000000000000000),1,(7319950536400204003/20000000000000000000),(2287484542625063751/6250000000000000000),(543227897614675109/1000000000000000000),false⟩
theorem valid415 : certificate415.Valid := by decide +kernel
theorem bound415 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate415.a certificate415.b certificate415.c x ≤ (certificate415.bound:ℝ) :=
  rat_majority_certificate_sound certificate415 valid415 x hx0 hx1

def certificate416 : RatMajorityCertificate := ⟨0,(503641760903407947/500000000000000000),(774707947/654080000),(43822351759886133287/100000000000000000000),(5477793969985766661/12500000000000000000),(356374217416025491/500000000000000000),false⟩
theorem valid416 : certificate416.Valid := by decide +kernel
theorem bound416 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate416.a certificate416.b certificate416.c x ≤ (certificate416.bound:ℝ) :=
  rat_majority_certificate_sound certificate416 valid416 x hx0 hx1

def certificate417 : RatMajorityCertificate := ⟨(195199943081267833/1000000000000000000),(405330917841713212722928892832331149/500000000000000000000000000000000000),(774707947/654080000),(7924175235098566599/20000000000000000000),(9905219043873208249/25000000000000000000),(356374217416025491/500000000000000000),false⟩
theorem valid417 : certificate417.Valid := by decide +kernel
theorem bound417 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate417.a certificate417.b certificate417.c x ≤ (certificate417.bound:ℝ) :=
  rat_majority_certificate_sound certificate417 valid417 x hx0 hx1

def certificate418 : RatMajorityCertificate := ⟨0,(503641760903407947/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(67902680577441123/125000000000000000),false⟩
theorem valid418 : certificate418.Valid := by decide +kernel
theorem bound418 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate418.a certificate418.b certificate418.c x ≤ (certificate418.bound:ℝ) :=
  rat_majority_certificate_sound certificate418 valid418 x hx0 hx1

def certificate419 : RatMajorityCertificate := ⟨(31553489105418193/250000000000000000),(110018785410152669678047603685420229/125000000000000000000000000000000000),1,(1464239344098034119/4000000000000000000),(2287873975153178311/6250000000000000000),(67902680577441123/125000000000000000),false⟩
theorem valid419 : certificate419.Valid := by decide +kernel
theorem bound419 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate419.a certificate419.b certificate419.c x ≤ (certificate419.bound:ℝ) :=
  rat_majority_certificate_sound certificate419 valid419 x hx0 hx1

def certificate420 : RatMajorityCertificate := ⟨0,(50366447845363727/50000000000000000),(2322423181/1961510000),(21906324205545999013/50000000000000000000),(43812648411091998027/100000000000000000000),(712354896962078953/1000000000000000000),false⟩
theorem valid420 : certificate420.Valid := by decide +kernel
theorem bound420 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate420.a certificate420.b certificate420.c x ≤ (certificate420.bound:ℝ) :=
  rat_majority_certificate_sound certificate420 valid420 x hx0 hx1

def certificate421 : RatMajorityCertificate := ⟨(12177766049312987/62500000000000000),(2534552171739469297371518520177451/3125000000000000000000000000000000),(2322423181/1961510000),(990502095968942847/2500000000000000000),(39620083838757713881/100000000000000000000),(712354896962078953/1000000000000000000),false⟩
theorem valid421 : certificate421.Valid := by decide +kernel
theorem bound421 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate421.a certificate421.b certificate421.c x ≤ (certificate421.bound:ℝ) :=
  rat_majority_certificate_sound certificate421 valid421 x hx0 hx1

def certificate422 : RatMajorityCertificate := ⟨0,(50366447845363727/50000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543239110852466509/1000000000000000000),false⟩
theorem valid422 : certificate422.Valid := by decide +kernel
theorem bound422 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate422.a certificate422.b certificate422.c x ≤ (certificate422.bound:ℝ) :=
  rat_majority_certificate_sound certificate422 valid422 x hx0 hx1

def certificate423 : RatMajorityCertificate := ⟨(246450899273557/1953125000000000),(85959112083271431422500261933061/97656250000000000000000000000000),1,(36606819992996432349/100000000000000000000),(732136399859928647/2000000000000000000),(543239110852466509/1000000000000000000),false⟩
theorem valid423 : certificate423.Valid := by decide +kernel
theorem bound423 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate423.a certificate423.b certificate423.c x ≤ (certificate423.bound:ℝ) :=
  rat_majority_certificate_sound certificate423 valid423 x hx0 hx1

def certificate424 : RatMajorityCertificate := ⟨0,(62958705116858597/62500000000000000),(2321112909/1961530000),(43797157883710480641/100000000000000000000),(21898578941855240321/50000000000000000000),(711622883322017541/1000000000000000000),false⟩
theorem valid424 : certificate424.Valid := by decide +kernel
theorem bound424 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate424.a certificate424.b certificate424.c x ≤ (certificate424.bound:ℝ) :=
  rat_majority_certificate_sound certificate424 valid424 x hx0 hx1

def certificate425 : RatMajorityCertificate := ⟨(193531595822817787/1000000000000000000),(50774206444654748916488617824535161/62500000000000000000000000000000000),(2321112909/1961530000),(1585503859892052323/4000000000000000000),(9909399124325327019/25000000000000000000),(711622883322017541/1000000000000000000),false⟩
theorem valid425 : certificate425.Valid := by decide +kernel
theorem bound425 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate425.a certificate425.b certificate425.c x ≤ (certificate425.bound:ℝ) :=
  rat_majority_certificate_sound certificate425 valid425 x hx0 hx1

def certificate426 : RatMajorityCertificate := ⟨0,(62958705116858597/62500000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(10864063381217783/20000000000000000),false⟩
theorem valid426 : certificate426.Valid := by decide +kernel
theorem bound426 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate426.a certificate426.b certificate426.c x ≤ (certificate426.bound:ℝ) :=
  rat_majority_certificate_sound certificate426 valid426 x hx0 hx1

def certificate427 : RatMajorityCertificate := ⟨(31447649253634677/250000000000000000),(13759773003236665272258869495231831/15625000000000000000000000000000000),1,(183079691453582311/500000000000000000),(36615938290716462201/100000000000000000000),(10864063381217783/20000000000000000),false⟩
theorem valid427 : certificate427.Valid := by decide +kernel
theorem bound427 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate427.a certificate427.b certificate427.c x ≤ (certificate427.bound:ℝ) :=
  rat_majority_certificate_sound certificate427 valid427 x hx0 hx1

def certificate428 : RatMajorityCertificate := ⟨0,(20147237862634103/20000000000000000),(2320351889/1961170000),(10948316272382004807/25000000000000000000),(43793265089528019229/100000000000000000000),(711493885803406667/1000000000000000000),false⟩
theorem valid428 : certificate428.Valid := by decide +kernel
theorem bound428 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate428.a certificate428.b certificate428.c x ≤ (certificate428.bound:ℝ) :=
  rat_majority_certificate_sound certificate428 valid428 x hx0 hx1

def certificate429 : RatMajorityCertificate := ⟨(24208743210364729/125000000000000000),(2030665425014616339365908696246913/2500000000000000000000000000000000),(2320351889/1961170000),(19815054517784031703/50000000000000000000),(39630109035568063407/100000000000000000000),(711493885803406667/1000000000000000000),false⟩
theorem valid429 : certificate429.Valid := by decide +kernel
theorem bound429 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate429.a certificate429.b certificate429.c x ≤ (certificate429.bound:ℝ) :=
  rat_majority_certificate_sound certificate429 valid429 x hx0 hx1

def certificate430 : RatMajorityCertificate := ⟨0,(20147237862634103/20000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543200919817270311/1000000000000000000),false⟩
theorem valid430 : certificate430.Valid := by decide +kernel
theorem bound430 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate430.a certificate430.b certificate430.c x ≤ (certificate430.bound:ℝ) :=
  rat_majority_certificate_sound certificate430 valid430 x hx0 hx1

def certificate431 : RatMajorityCertificate := ⟨(125668527511175287/1000000000000000000),(17615364147019476839334464822987439/20000000000000000000000000000000000),1,(366188235120753891/1000000000000000000),(36618823512075389101/100000000000000000000),(543200919817270311/1000000000000000000),false⟩
theorem valid431 : certificate431.Valid := by decide +kernel
theorem bound431 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate431.a certificate431.b certificate431.c x ≤ (certificate431.bound:ℝ) :=
  rat_majority_certificate_sound certificate431 valid431 x hx0 hx1

def certificate432 : RatMajorityCertificate := ⟨0,(1007419585320748907/1000000000000000000),(2319092819/1960070000),(21896878981838398789/50000000000000000000),(43793757963676797579/100000000000000000000),(177914851456653599/250000000000000000),false⟩
theorem valid432 : certificate432.Valid := by decide +kernel
theorem bound432 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate432.a certificate432.b certificate432.c x ≤ (certificate432.bound:ℝ) :=
  rat_majority_certificate_sound certificate432 valid432 x hx0 hx1

def certificate433 : RatMajorityCertificate := ⟨(48721829337767579/250000000000000000),(202771571222665113980235800215713847/250000000000000000000000000000000000),(2319092819/1960070000),(39599716030588990731/100000000000000000000),(9899929007647247683/25000000000000000000),(177914851456653599/250000000000000000),false⟩
theorem valid433 : certificate433.Valid := by decide +kernel
theorem bound433 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate433.a certificate433.b certificate433.c x ≤ (certificate433.bound:ℝ) :=
  rat_majority_certificate_sound certificate433 valid433 x hx0 hx1

def certificate434 : RatMajorityCertificate := ⟨0,(1007419585320748907/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543232607452270633/1000000000000000000),false⟩
theorem valid434 : certificate434.Valid := by decide +kernel
theorem bound434 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate434.a certificate434.b certificate434.c x ≤ (certificate434.bound:ℝ) :=
  rat_majority_certificate_sound certificate434 valid434 x hx0 hx1

def certificate435 : RatMajorityCertificate := ⟨(125718135335098743/1000000000000000000),(880768673554165940894107344445676099/1000000000000000000000000000000000000),1,(36617820126430657403/100000000000000000000),(9154455031607664351/25000000000000000000),(543232607452270633/1000000000000000000),false⟩
theorem valid435 : certificate435.Valid := by decide +kernel
theorem bound435 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate435.a certificate435.b certificate435.c x ≤ (certificate435.bound:ℝ) :=
  rat_majority_certificate_sound certificate435 valid435 x hx0 hx1

def certificate436 : RatMajorityCertificate := ⟨0,(7870818539260401/7812500000000000),(193059071/163280000),(21887897054328287711/50000000000000000000),(43775794108656575423/100000000000000000000),(710817685054558479/1000000000000000000),false⟩
theorem valid436 : certificate436.Valid := by decide +kernel
theorem bound436 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate436.a certificate436.b certificate436.c x ≤ (certificate436.bound:ℝ) :=
  rat_majority_certificate_sound certificate436 valid436 x hx0 hx1

def certificate437 : RatMajorityCertificate := ⟨(193237931703321211/1000000000000000000),(6349877843921565213935792724334389/7812500000000000000000000000000000),(193059071/163280000),(39623402289197457109/100000000000000000000),(3962340228919745711/10000000000000000000),(710817685054558479/1000000000000000000),false⟩
theorem valid437 : certificate437.Valid := by decide +kernel
theorem bound437 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate437.a certificate437.b certificate437.c x ≤ (certificate437.bound:ℝ) :=
  rat_majority_certificate_sound certificate437 valid437 x hx0 hx1

def certificate438 : RatMajorityCertificate := ⟨0,(7870818539260401/7812500000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543224810924872243/1000000000000000000),false⟩
theorem valid438 : certificate438.Valid := by decide +kernel
theorem bound438 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate438.a certificate438.b certificate438.c x ≤ (certificate438.bound:ℝ) :=
  rat_majority_certificate_sound certificate438 valid438 x hx0 hx1

def certificate439 : RatMajorityCertificate := ⟨(62721028400140759/500000000000000000),(3441743436496894485336843845215641/3906250000000000000000000000000000),1,(36624328014681068037/100000000000000000000),(18312164007340534019/50000000000000000000),(543224810924872243/1000000000000000000),false⟩
theorem valid439 : certificate439.Valid := by decide +kernel
theorem bound439 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate439.a certificate439.b certificate439.c x ≤ (certificate439.bound:ℝ) :=
  rat_majority_certificate_sound certificate439 valid439 x hx0 hx1

end Cycle12.MajorityCertificates.Batch010
