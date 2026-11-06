import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch005

def certificate200 : RatMajorityCertificate := ⟨0,(1004522118512091303/1000000000000000000),(303662277/252676250),(4421421047358400429/10000000000000000000),(44214210473584004291/100000000000000000000),(729200858313781183/1000000000000000000),false⟩
theorem valid200 : certificate200.Valid := by decide +kernel
theorem bound200 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate200.a certificate200.b certificate200.c x ≤ (certificate200.bound:ℝ) :=
  rat_majority_certificate_sound certificate200 valid200 x hx0 hx1

def certificate201 : RatMajorityCertificate := ⟨(109404481753331043/500000000000000000),(392361837470472115015387907599780971/500000000000000000000000000000000000),(303662277/252676250),(1969934815092410301/5000000000000000000),(39398696301848206021/100000000000000000000),(729200858313781183/1000000000000000000),false⟩
theorem valid201 : certificate201.Valid := by decide +kernel
theorem bound201 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate201.a certificate201.b certificate201.c x ≤ (certificate201.bound:ℝ) :=
  rat_majority_certificate_sound certificate201 valid201 x hx0 hx1

def certificate202 : RatMajorityCertificate := ⟨0,(1004522118512091303/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(108487366714690953/200000000000000000),false⟩
theorem valid202 : certificate202.Valid := by decide +kernel
theorem bound202 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate202.a certificate202.b certificate202.c x ≤ (certificate202.bound:ℝ) :=
  rat_majority_certificate_sound certificate202 valid202 x hx0 hx1

def certificate203 : RatMajorityCertificate := ⟨(130793022763385317/1000000000000000000),(873137634199215302066847946326401949/1000000000000000000000000000000000000),1,(9123013647028715081/25000000000000000000),(1459682183524594413/4000000000000000000),(108487366714690953/200000000000000000),false⟩
theorem valid203 : certificate203.Valid := by decide +kernel
theorem bound203 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate203.a certificate203.b certificate203.c x ≤ (certificate203.bound:ℝ) :=
  rat_majority_certificate_sound certificate203 valid203 x hx0 hx1

def certificate204 : RatMajorityCertificate := ⟨0,(125569327198973759/125000000000000000),(151739256/126296875),(44206710769533329713/100000000000000000000),(22103355384766664857/50000000000000000000),(22775413880068091/31250000000000000),false⟩
theorem valid204 : certificate204.Valid := by decide +kernel
theorem bound204 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate204.a certificate204.b certificate204.c x ≤ (certificate204.bound:ℝ) :=
  rat_majority_certificate_sound certificate204 valid204 x hx0 hx1

def certificate205 : RatMajorityCertificate := ⟨(43556569525819299/200000000000000000),(19644496309342298933261113523225059/25000000000000000000000000000000000),(151739256/126296875),(78837005535192229/200000000000000000),(39418502767596114501/100000000000000000000),(22775413880068091/31250000000000000),false⟩
theorem valid205 : certificate205.Valid := by decide +kernel
theorem bound205 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate205.a certificate205.b certificate205.c x ≤ (certificate205.bound:ℝ) :=
  rat_majority_certificate_sound certificate205 valid205 x hx0 hx1

def certificate206 : RatMajorityCertificate := ⟨0,(125569327198973759/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(54241352349893801/100000000000000000),false⟩
theorem valid206 : certificate206.Valid := by decide +kernel
theorem bound206 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate206.a certificate206.b certificate206.c x ≤ (certificate206.bound:ℝ) :=
  rat_majority_certificate_sound certificate206 valid206 x hx0 hx1

def certificate207 : RatMajorityCertificate := ⟨(130434655240474511/1000000000000000000),(109190735296997277836009640602643151/125000000000000000000000000000000000),1,(36500538486130324499/100000000000000000000),(73001076972260649/200000000000000000),(54241352349893801/100000000000000000),false⟩
theorem valid207 : certificate207.Valid := by decide +kernel
theorem bound207 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate207.a certificate207.b certificate207.c x ≤ (certificate207.bound:ℝ) :=
  rat_majority_certificate_sound certificate207 valid207 x hx0 hx1

def certificate208 : RatMajorityCertificate := ⟨0,(1004600026835485771/1000000000000000000),(2426409839/2019490000),(44207770363477750919/100000000000000000000),(1105194259086943773/2500000000000000000),(91109898120746829/125000000000000000),false⟩
theorem valid208 : certificate208.Valid := by decide +kernel
theorem bound208 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate208.a certificate208.b certificate208.c x ≤ (certificate208.bound:ℝ) :=
  rat_majority_certificate_sound certificate208 valid208 x hx0 hx1

def certificate209 : RatMajorityCertificate := ⟨(27220632624910651/125000000000000000),(98229155088971581896991844943153079/125000000000000000000000000000000000),(2426409839/2019490000),(394202937973577325704011/1000000000000000000000000),(98550734493394331426003/250000000000000000000000),(91109898120746829/125000000000000000),false⟩
theorem valid209 : certificate209.Valid := by decide +kernel
theorem bound209 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate209.a certificate209.b certificate209.c x ≤ (certificate209.bound:ℝ) :=
  rat_majority_certificate_sound certificate209 valid209 x hx0 hx1

def certificate210 : RatMajorityCertificate := ⟨0,(1004600026835485771/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271214459839055293/500000000000000000),false⟩
theorem valid210 : certificate210.Valid := by decide +kernel
theorem bound210 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate210.a certificate210.b certificate210.c x ≤ (certificate210.bound:ℝ) :=
  rat_majority_certificate_sound certificate210 valid210 x hx0 hx1

def certificate211 : RatMajorityCertificate := ⟨(26076824039515713/200000000000000000),(174723227237215428454905342057580277/200000000000000000000000000000000000),1,(1140682571683947951/3125000000000000000),(36501842293886334433/100000000000000000000),(271214459839055293/500000000000000000),false⟩
theorem valid211 : certificate211.Valid := by decide +kernel
theorem bound211 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate211.a certificate211.b certificate211.c x ≤ (certificate211.bound:ℝ) :=
  rat_majority_certificate_sound certificate211 valid211 x hx0 hx1

def certificate212 : RatMajorityCertificate := ⟨0,(251176131875265017/250000000000000000),(2423224117/2016400000),(22106810165123823219/50000000000000000000),(44213620330247646439/100000000000000000000),(145857954239871747/200000000000000000),false⟩
theorem valid212 : certificate212.Valid := by decide +kernel
theorem bound212 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate212.a certificate212.b certificate212.c x ≤ (certificate212.bound:ℝ) :=
  rat_majority_certificate_sound certificate212 valid212 x hx0 hx1

def certificate213 : RatMajorityCertificate := ⟨(21893232563209819/100000000000000000),(19618555718053865850746915198398077/25000000000000000000000000000000000),(2423224117/2016400000),(4924450171126502329/12500000000000000000),(39395601369012018633/100000000000000000000),(145857954239871747/200000000000000000),false⟩
theorem valid213 : certificate213.Valid := by decide +kernel
theorem bound213 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate213.a certificate213.b certificate213.c x ≤ (certificate213.bound:ℝ) :=
  rat_majority_certificate_sound certificate213 valid213 x hx0 hx1

def certificate214 : RatMajorityCertificate := ⟨0,(251176131875265017/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(542683718097899887/1000000000000000000),false⟩
theorem valid214 : certificate214.Valid := by decide +kernel
theorem bound214 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate214.a certificate214.b certificate214.c x ≤ (certificate214.bound:ℝ) :=
  rat_majority_certificate_sound certificate214 valid214 x hx0 hx1

def certificate215 : RatMajorityCertificate := ⟨(66162612197636471/500000000000000000),(108969596931066952479797605850364993/125000000000000000000000000000000000),1,(2278536123185974279/6250000000000000000),(7291315594195117693/20000000000000000000),(542683718097899887/1000000000000000000),false⟩
theorem valid215 : certificate215.Valid := by decide +kernel
theorem bound215 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate215.a certificate215.b certificate215.c x ≤ (certificate215.bound:ℝ) :=
  rat_majority_certificate_sound certificate215 valid215 x hx0 hx1

def certificate216 : RatMajorityCertificate := ⟨0,(1004796220582616627/1000000000000000000),(2419527359/2013950000),(22102627779765194687/50000000000000000000),(70728408895248623/160000000000000000),(728880909890272779/1000000000000000000),false⟩
theorem valid216 : certificate216.Valid := by decide +kernel
theorem bound216 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate216.a certificate216.b certificate216.c x ≤ (certificate216.bound:ℝ) :=
  rat_majority_certificate_sound certificate216 valid216 x hx0 hx1

def certificate217 : RatMajorityCertificate := ⟨(217716393963916477/1000000000000000000),(786035610768797343420822882460536921/1000000000000000000000000000000000000),(2419527359/2013950000),(615935253913863859/1562500000000000000),(39419856250487286977/100000000000000000000),(728880909890272779/1000000000000000000),false⟩
theorem valid217 : certificate217.Valid := by decide +kernel
theorem bound217 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate217.a certificate217.b certificate217.c x ≤ (certificate217.bound:ℝ) :=
  rat_majority_certificate_sound certificate217 valid217 x hx0 hx1

def certificate218 : RatMajorityCertificate := ⟨0,(1004796220582616627/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(33919769367404947/62500000000000000),false⟩
theorem valid218 : certificate218.Valid := by decide +kernel
theorem bound218 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate218.a certificate218.b certificate218.c x ≤ (certificate218.bound:ℝ) :=
  rat_majority_certificate_sound certificate218 valid218 x hx0 hx1

def certificate219 : RatMajorityCertificate := ⟨(132238530333727691/1000000000000000000),(871923445087887338071398368333081743/1000000000000000000000000000000000000),1,(36458861384928908171/100000000000000000000),(9114715346232227043/25000000000000000000),(33919769367404947/62500000000000000),false⟩
theorem valid219 : certificate219.Valid := by decide +kernel
theorem bound219 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate219.a certificate219.b certificate219.c x ≤ (certificate219.bound:ℝ) :=
  rat_majority_certificate_sound certificate219 valid219 x hx0 hx1

def certificate220 : RatMajorityCertificate := ⟨0,(1004828204316224421/1000000000000000000),(201490053/167780000),(4419482186326356351/10000000000000000000),(44194821863263563511/100000000000000000000),(364186077700955429/500000000000000000),false⟩
theorem valid220 : certificate220.Valid := by decide +kernel
theorem bound220 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate220.a certificate220.b certificate220.c x ≤ (certificate220.bound:ℝ) :=
  rat_majority_certificate_sound certificate220 valid220 x hx0 hx1

def certificate221 : RatMajorityCertificate := ⟨(43331766361268201/200000000000000000),(157424659880601579898359682313063379/200000000000000000000000000000000000),(201490053/167780000),(4929670961616205869/12500000000000000000),(39437367692929646953/100000000000000000000),(364186077700955429/500000000000000000),false⟩
theorem valid221 : certificate221.Valid := by decide +kernel
theorem bound221 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate221.a certificate221.b certificate221.c x ≤ (certificate221.bound:ℝ) :=
  rat_majority_certificate_sound certificate221 valid221 x hx0 hx1

def certificate222 : RatMajorityCertificate := ⟨0,(1004828204316224421/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(542689167848999299/1000000000000000000),false⟩
theorem valid222 : certificate222.Valid := by decide +kernel
theorem bound222 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate222.a certificate222.b certificate222.c x ≤ (certificate222.bound:ℝ) :=
  rat_majority_certificate_sound certificate222 valid222 x hx0 hx1

def certificate223 : RatMajorityCertificate := ⟨(16480937410864353/125000000000000000),(109043014795521139822100168863035387/125000000000000000000000000000000000),1,(36468131564020545863/100000000000000000000),(4558516445502568233/12500000000000000000),(542689167848999299/1000000000000000000),false⟩
theorem valid223 : certificate223.Valid := by decide +kernel
theorem bound223 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate223.a certificate223.b certificate223.c x ≤ (certificate223.bound:ℝ) :=
  rat_majority_certificate_sound certificate223 valid223 x hx0 hx1

def certificate224 : RatMajorityCertificate := ⟨0,(200974808071305427/200000000000000000),(2416329033/2012170000),(22096728924803770243/50000000000000000000),(44193457849607540487/100000000000000000000),(364169750270954151/500000000000000000),false⟩
theorem valid224 : certificate224.Valid := by decide +kernel
theorem bound224 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate224.a certificate224.b certificate224.c x ≤ (certificate224.bound:ℝ) :=
  rat_majority_certificate_sound certificate224 valid224 x hx0 hx1

def certificate225 : RatMajorityCertificate := ⟨(216629524154023317/1000000000000000000),(157437731031872367717792417613358641/200000000000000000000000000000000000),(2416329033/2012170000),(197184653867092574797251/500000000000000000000000),(394369307734185149594503/1000000000000000000000000),(364169750270954151/500000000000000000),false⟩
theorem valid225 : certificate225.Valid := by decide +kernel
theorem bound225 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate225.a certificate225.b certificate225.c x ≤ (certificate225.bound:ℝ) :=
  rat_majority_certificate_sound certificate225 valid225 x hx0 hx1

def certificate226 : RatMajorityCertificate := ⟨0,(200974808071305427/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(542706447161716783/1000000000000000000),false⟩
theorem valid226 : certificate226.Valid := by decide +kernel
theorem bound226 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate226.a certificate226.b certificate226.c x ≤ (certificate226.bound:ℝ) :=
  rat_majority_certificate_sound certificate226 valid226 x hx0 hx1

def certificate227 : RatMajorityCertificate := ⟨(131813234983373297/1000000000000000000),(174483668469264096438357253157017181/200000000000000000000000000000000000),1,(7293811718637331507/20000000000000000000),(142457260129635381/390625000000000000),(542706447161716783/1000000000000000000),false⟩
theorem valid227 : certificate227.Valid := by decide +kernel
theorem bound227 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate227.a certificate227.b certificate227.c x ≤ (certificate227.bound:ℝ) :=
  rat_majority_certificate_sound certificate227 valid227 x hx0 hx1

def certificate228 : RatMajorityCertificate := ⟨0,(125622555748978741/125000000000000000),(2413391677/2009170000),(44200874364018296223/100000000000000000000),(1381277323875571757/3125000000000000000),(29151107555377679/40000000000000000),false⟩
theorem valid228 : certificate228.Valid := by decide +kernel
theorem bound228 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate228.a certificate228.b certificate228.c x ≤ (certificate228.bound:ℝ) :=
  rat_majority_certificate_sound certificate228 valid228 x hx0 hx1

def certificate229 : RatMajorityCertificate := ⟨(217436648257391719/1000000000000000000),(98307608281393468564296861359554221/125000000000000000000000000000000000),(2413391677/2009170000),(7884718813178401349/20000000000000000000),(19711797032946003373/50000000000000000000),(29151107555377679/40000000000000000),false⟩
theorem valid229 : certificate229.Valid := by decide +kernel
theorem bound229 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate229.a certificate229.b certificate229.c x ≤ (certificate229.bound:ℝ) :=
  rat_majority_certificate_sound certificate229 valid229 x hx0 hx1

def certificate230 : RatMajorityCertificate := ⟨0,(125622555748978741/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(678490013188849/1250000000000000),false⟩
theorem valid230 : certificate230.Valid := by decide +kernel
theorem bound230 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate230.a certificate230.b certificate230.c x ≤ (certificate230.bound:ℝ) :=
  rat_majority_certificate_sound certificate230 valid230 x hx0 hx1

def certificate231 : RatMajorityCertificate := ⟨(33039956244169763/250000000000000000),(27255075192017650937742177317991617/31250000000000000000000000000000000),1,(36461204497506133033/100000000000000000000),(18230602248753066517/50000000000000000000),(678490013188849/1250000000000000),false⟩
theorem valid231 : certificate231.Valid := by decide +kernel
theorem bound231 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate231.a certificate231.b certificate231.c x ≤ (certificate231.bound:ℝ) :=
  rat_majority_certificate_sound certificate231 valid231 x hx0 hx1

def certificate232 : RatMajorityCertificate := ⟨0,(125626499988929919/125000000000000000),(482326223/401726000),(44188472862550589711/100000000000000000000),(2761779553909411857/6250000000000000000),(728199390497361457/1000000000000000000),false⟩
theorem valid232 : certificate232.Valid := by decide +kernel
theorem bound232 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate232.a certificate232.b certificate232.c x ≤ (certificate232.bound:ℝ) :=
  rat_majority_certificate_sound certificate232 valid232 x hx0 hx1

def certificate233 : RatMajorityCertificate := ⟨(216477226765484631/1000000000000000000),(98431223663072184438627782869425111/125000000000000000000000000000000000),(482326223/401726000),(9859101644298931659/25000000000000000000),(39436406577195726637/100000000000000000000),(728199390497361457/1000000000000000000),false⟩
theorem valid233 : certificate233.Valid := by decide +kernel
theorem bound233 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate233.a certificate233.b certificate233.c x ≤ (certificate233.bound:ℝ) :=
  rat_majority_certificate_sound certificate233 valid233 x hx0 hx1

def certificate234 : RatMajorityCertificate := ⟨0,(125626499988929919/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(542762842568877863/1000000000000000000),false⟩
theorem valid234 : certificate234.Valid := by decide +kernel
theorem bound234 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate234.a certificate234.b certificate234.c x ≤ (certificate234.bound:ℝ) :=
  rat_majority_certificate_sound certificate234 valid234 x hx0 hx1

def certificate235 : RatMajorityCertificate := ⟨(131751157858849909/1000000000000000000),(109075063157633606896352755059472629/125000000000000000000000000000000000),1,(36470884497371845051/100000000000000000000),(9117721124342961263/25000000000000000000),(542762842568877863/1000000000000000000),false⟩
theorem valid235 : certificate235.Valid := by decide +kernel
theorem bound235 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate235.a certificate235.b certificate235.c x ≤ (certificate235.bound:ℝ) :=
  rat_majority_certificate_sound certificate235 valid235 x hx0 hx1

def certificate236 : RatMajorityCertificate := ⟨0,(125632262888211321/125000000000000000),(481924913/401494000),(8836324012032206033/20000000000000000000),(22090810030080515083/50000000000000000000),(45491433205634829/62500000000000000),false⟩
theorem valid236 : certificate236.Valid := by decide +kernel
theorem bound236 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate236.a certificate236.b certificate236.c x ≤ (certificate236.bound:ℝ) :=
  rat_majority_certificate_sound certificate236 valid236 x hx0 hx1

def certificate237 : RatMajorityCertificate := ⟨(107808009164588369/500000000000000000),(49271967295285399169180180349274551/62500000000000000000000000000000000),(481924913/401494000),(1972621158078801743/5000000000000000000),(39452423161576034861/100000000000000000000),(45491433205634829/62500000000000000),false⟩
theorem valid237 : certificate237.Valid := by decide +kernel
theorem bound237 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate237.a certificate237.b certificate237.c x ≤ (certificate237.bound:ℝ) :=
  rat_majority_certificate_sound certificate237 valid237 x hx0 hx1

def certificate238 : RatMajorityCertificate := ⟨0,(125632262888211321/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271385983198156253/500000000000000000),false⟩
theorem valid238 : certificate238.Valid := by decide +kernel
theorem bound238 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate238.a certificate238.b certificate238.c x ≤ (certificate238.bound:ℝ) :=
  rat_majority_certificate_sound certificate238 valid238 x hx0 hx1

def certificate239 : RatMajorityCertificate := ⟨(131639122812999457/1000000000000000000),(109094142004595037043302782325747303/125000000000000000000000000000000000),1,(9118409217225653663/25000000000000000000),(36473636868902614653/100000000000000000000),(271385983198156253/500000000000000000),false⟩
theorem valid239 : certificate239.Valid := by decide +kernel
theorem bound239 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate239.a certificate239.b certificate239.c x ≤ (certificate239.bound:ℝ) :=
  rat_majority_certificate_sound certificate239 valid239 x hx0 hx1

end Cycle12.MajorityCertificates.Batch005
