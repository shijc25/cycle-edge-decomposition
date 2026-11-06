import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch004

def certificate160 : RatMajorityCertificate := ⟨0,(1003654701653779867/1000000000000000000),(1230030691/1023840000),(22102689783062515067/50000000000000000000),(8841075913225006027/20000000000000000000),(728417410899779319/1000000000000000000),false⟩
theorem valid160 : certificate160.Valid := by decide +kernel
theorem bound160 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate160.a certificate160.b certificate160.c x ≤ (certificate160.bound:ℝ) :=
  rat_majority_certificate_sound certificate160 valid160 x hx0 hx1

def certificate161 : RatMajorityCertificate := ⟨(54823984302581073/250000000000000000),(195889325804766449234174285337342709/250000000000000000000000000000000000),(1230030691/1023840000),(39372405961440674881/100000000000000000000),(19686202980720337441/50000000000000000000),(728417410899779319/1000000000000000000),false⟩
theorem valid161 : certificate161.Valid := by decide +kernel
theorem bound161 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate161.a certificate161.b certificate161.c x ≤ (certificate161.bound:ℝ) :=
  rat_majority_certificate_sound certificate161 valid161 x hx0 hx1

def certificate162 : RatMajorityCertificate := ⟨0,(1003654701653779867/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(542093716749528063/1000000000000000000),false⟩
theorem valid162 : certificate162.Valid := by decide +kernel
theorem bound162 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate162.a certificate162.b certificate162.c x ≤ (certificate162.bound:ℝ) :=
  rat_majority_certificate_sound certificate162 valid162 x hx0 hx1

def certificate163 : RatMajorityCertificate := ⟨(131292921982155601/1000000000000000000),(871881943212526490871334633804914933/1000000000000000000000000000000000000),1,(9119504560460773713/25000000000000000000),(36478018241843094853/100000000000000000000),(542093716749528063/1000000000000000000),false⟩
theorem valid163 : certificate163.Valid := by decide +kernel
theorem bound163 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate163.a certificate163.b certificate163.c x ≤ (certificate163.bound:ℝ) :=
  rat_majority_certificate_sound certificate163 valid163 x hx0 hx1

def certificate164 : RatMajorityCertificate := ⟨0,(50186080072063521/50000000000000000),(614229943/511467500),(44194792142598013849/100000000000000000000),(883895842851960277/2000000000000000000),(145576390117070903/200000000000000000),false⟩
theorem valid164 : certificate164.Valid := by decide +kernel
theorem bound164 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate164.a certificate164.b certificate164.c x ≤ (certificate164.bound:ℝ) :=
  rat_majority_certificate_sound certificate164 valid164 x hx0 hx1

def certificate165 : RatMajorityCertificate := ⟨(43571130475271541/200000000000000000),(7850551771550399545652249324444139/10000000000000000000000000000000000),(614229943/511467500),(19700148026207992193/50000000000000000000),(39400296052415984387/100000000000000000000),(145576390117070903/200000000000000000),false⟩
theorem valid165 : certificate165.Valid := by decide +kernel
theorem bound165 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate165.a certificate165.b certificate165.c x ≤ (certificate165.bound:ℝ) :=
  rat_majority_certificate_sound certificate165 valid165 x hx0 hx1

def certificate166 : RatMajorityCertificate := ⟨0,(50186080072063521/50000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(8469660354196163/15625000000000000),false⟩
theorem valid166 : certificate166.Valid := by decide +kernel
theorem bound166 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate166.a certificate166.b certificate166.c x ≤ (certificate166.bound:ℝ) :=
  rat_majority_certificate_sound certificate166 valid166 x hx0 hx1

def certificate167 : RatMajorityCertificate := ⟨(32669073091626067/250000000000000000),(10906987299959438686663709996598093/12500000000000000000000000000000000),1,(36492667292424174309/100000000000000000000),(3649266729242417431/10000000000000000000),(8469660354196163/15625000000000000),false⟩
theorem valid167 : certificate167.Valid := by decide +kernel
theorem bound167 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate167.a certificate167.b certificate167.c x ≤ (certificate167.bound:ℝ) :=
  rat_majority_certificate_sound certificate167 valid167 x hx0 hx1

def certificate168 : RatMajorityCertificate := ⟨0,(501904313016493929/500000000000000000),(2454000793/2042990000),(44200709096723275599/100000000000000000000),(110501772741808189/250000000000000000),(145631886685797881/200000000000000000),false⟩
theorem valid168 : certificate168.Valid := by decide +kernel
theorem bound168 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate168.a certificate168.b certificate168.c x ≤ (certificate168.bound:ℝ) :=
  rat_majority_certificate_sound certificate168 valid168 x hx0 hx1

def certificate169 : RatMajorityCertificate := ⟨(217769529972287431/1000000000000000000),(392604846679828221739683816145493601/500000000000000000000000000000000000),(2454000793/2042990000),(39409190482419534897/100000000000000000000),(19704595241209767449/50000000000000000000),(145631886685797881/200000000000000000),false⟩
theorem valid169 : certificate169.Valid := by decide +kernel
theorem bound169 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate169.a certificate169.b certificate169.c x ≤ (certificate169.bound:ℝ) :=
  rat_majority_certificate_sound certificate169 valid169 x hx0 hx1

def certificate170 : RatMajorityCertificate := ⟨0,(501904313016493929/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135525514984154667/250000000000000000),false⟩
theorem valid170 : certificate170.Valid := by decide +kernel
theorem bound170 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate170.a certificate170.b certificate170.c x ≤ (certificate170.bound:ℝ) :=
  rat_majority_certificate_sound certificate170 valid170 x hx0 hx1

def certificate171 : RatMajorityCertificate := ⟨(2614272913107071/20000000000000000),(8725971409839245782487365801528041/10000000000000000000000000000000000),1,(36492022233846328677/100000000000000000000),(18246011116923164339/50000000000000000000),(135525514984154667/250000000000000000),false⟩
theorem valid171 : certificate171.Valid := by decide +kernel
theorem bound171 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate171.a certificate171.b certificate171.c x ≤ (certificate171.bound:ℝ) :=
  rat_majority_certificate_sound certificate171 valid171 x hx0 hx1

def certificate172 : RatMajorityCertificate := ⟨0,(100389618324802041/100000000000000000),(2451898573/2040150000),(22107538196104938941/50000000000000000000),(44215076392209877883/100000000000000000000),(729070435054862411/1000000000000000000),false⟩
theorem valid172 : certificate172.Valid := by decide +kernel
theorem bound172 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate172.a certificate172.b certificate172.c x ≤ (certificate172.bound:ℝ) :=
  rat_majority_certificate_sound certificate172 valid172 x hx0 hx1

def certificate173 : RatMajorityCertificate := ⟨(220573625629742493/1000000000000000000),(78246316235314418894052053969171787/100000000000000000000000000000000000),(2451898573/2040150000),(19674639838010133677/50000000000000000000),(7869855935204053471/20000000000000000000),(729070435054862411/1000000000000000000),false⟩
theorem valid173 : certificate173.Valid := by decide +kernel
theorem bound173 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate173.a certificate173.b certificate173.c x ≤ (certificate173.bound:ℝ) :=
  rat_majority_certificate_sound certificate173 valid173 x hx0 hx1

def certificate174 : RatMajorityCertificate := ⟨0,(100389618324802041/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(4235543742142811/7812500000000000),false⟩
theorem valid174 : certificate174.Valid := by decide +kernel
theorem bound174 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate174.a certificate174.b certificate174.c x ≤ (certificate174.bound:ℝ) :=
  rat_majority_certificate_sound certificate174 valid174 x hx0 hx1

def certificate175 : RatMajorityCertificate := ⟨(65391872827251371/500000000000000000),(43630144007729261616230036279151789/50000000000000000000000000000000000),1,(36490610589332595611/100000000000000000000),(9122652647333148903/25000000000000000000),(4235543742142811/7812500000000000),false⟩
theorem valid175 : certificate175.Valid := by decide +kernel
theorem bound175 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate175.a certificate175.b certificate175.c x ≤ (certificate175.bound:ℝ) :=
  rat_majority_certificate_sound certificate175 valid175 x hx0 hx1

def certificate176 : RatMajorityCertificate := ⟨0,(501992115944308631/500000000000000000),(2448892973/2037360000),(22109446824252391701/50000000000000000000),(44218893648504783403/100000000000000000000),(364651939985643181/500000000000000000),false⟩
theorem valid176 : certificate176.Valid := by decide +kernel
theorem bound176 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate176.a certificate176.b certificate176.c x ≤ (certificate176.bound:ℝ) :=
  rat_majority_certificate_sound certificate176 valid176 x hx0 hx1

def certificate177 : RatMajorityCertificate := ⟨(110440731776539203/500000000000000000),(195555681341211557375073722297238907/250000000000000000000000000000000000),(2448892973/2037360000),(7869077227290008839/20000000000000000000),(9836346534112511049/25000000000000000000),(364651939985643181/500000000000000000),false⟩
theorem valid177 : certificate177.Valid := by decide +kernel
theorem bound177 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate177.a certificate177.b certificate177.c x ≤ (certificate177.bound:ℝ) :=
  rat_majority_certificate_sound certificate177 valid177 x hx0 hx1

def certificate178 : RatMajorityCertificate := ⟨0,(501992115944308631/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135547827467195379/250000000000000000),false⟩
theorem valid178 : certificate178.Valid := by decide +kernel
theorem bound178 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate178.a certificate178.b certificate178.c x ≤ (certificate178.bound:ℝ) :=
  rat_majority_certificate_sound certificate178 valid178 x hx0 hx1

def certificate179 : RatMajorityCertificate := ⟨(5231890807086153/40000000000000000),(17453316701133590662735394761513457/20000000000000000000000000000000000),1,(18245263616009401681/50000000000000000000),(36490527232018803363/100000000000000000000),(135547827467195379/250000000000000000),false⟩
theorem valid179 : certificate179.Valid := by decide +kernel
theorem bound179 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate179.a certificate179.b certificate179.c x ≤ (certificate179.bound:ℝ) :=
  rat_majority_certificate_sound certificate179 valid179 x hx0 hx1

def certificate180 : RatMajorityCertificate := ⟨0,(502036394485920073/500000000000000000),(489104363/406920000),(44218303451932074511/100000000000000000000),(2763643965745754657/6250000000000000000),(729250320145705837/1000000000000000000),false⟩
theorem valid180 : certificate180.Valid := by decide +kernel
theorem bound180 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate180.a certificate180.b certificate180.c x ≤ (certificate180.bound:ℝ) :=
  rat_majority_certificate_sound certificate180 valid180 x hx0 hx1

def certificate181 : RatMajorityCertificate := ⟨(22010959549603713/100000000000000000),(39153336677133528025325594657968951/50000000000000000000000000000000000),(489104363/406920000),(7873193584099163781/20000000000000000000),(19682983960247909453/50000000000000000000),(729250320145705837/1000000000000000000),false⟩
theorem valid181 : certificate181.Valid := by decide +kernel
theorem bound181 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate181.a certificate181.b certificate181.c x ≤ (certificate181.bound:ℝ) :=
  rat_majority_certificate_sound certificate181 valid181 x hx0 hx1

def certificate182 : RatMajorityCertificate := ⟨0,(502036394485920073/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(542233137317967521/1000000000000000000),false⟩
theorem valid182 : certificate182.Valid := by decide +kernel
theorem bound182 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate182.a certificate182.b certificate182.c x ≤ (certificate182.bound:ℝ) :=
  rat_majority_certificate_sound certificate182 valid182 x hx0 hx1

def certificate183 : RatMajorityCertificate := ⟨(26161944253206631/200000000000000000),(87273030731562520774531289380395937/100000000000000000000000000000000000),1,(36490470404081974567/100000000000000000000),(4561308800510246821/12500000000000000000),(542233137317967521/1000000000000000000),false⟩
theorem valid183 : certificate183.Valid := by decide +kernel
theorem bound183 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate183.a certificate183.b certificate183.c x ≤ (certificate183.bound:ℝ) :=
  rat_majority_certificate_sound certificate183 valid183 x hx0 hx1

def certificate184 : RatMajorityCertificate := ⟨0,(25104044821896923/25000000000000000),(348908201/290270000),(44219326904765348471/100000000000000000000),(5527415863095668559/12500000000000000000),(729331423813769287/1000000000000000000),false⟩
theorem valid184 : certificate184.Valid := by decide +kernel
theorem bound184 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate184.a certificate184.b certificate184.c x ≤ (certificate184.bound:ℝ) :=
  rat_majority_certificate_sound certificate184 valid184 x hx0 hx1

def certificate185 : RatMajorityCertificate := ⟨(220020429358793147/1000000000000000000),(19580642101540774163682581487213319/25000000000000000000000000000000000),(348908201/290270000),(196849241130166979295047/500000000000000000000000),(78739696452066791718019/200000000000000000000000),(729331423813769287/1000000000000000000),false⟩
theorem valid185 : certificate185.Valid := by decide +kernel
theorem bound185 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate185.a certificate185.b certificate185.c x ≤ (certificate185.bound:ℝ) :=
  rat_majority_certificate_sound certificate185 valid185 x hx0 hx1

def certificate186 : RatMajorityCertificate := ⟨0,(25104044821896923/25000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(542273280765621441/1000000000000000000),false⟩
theorem valid186 : certificate186.Valid := by decide +kernel
theorem bound186 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate186.a certificate186.b certificate186.c x ≤ (certificate186.bound:ℝ) :=
  rat_majority_certificate_sound certificate186 valid186 x hx0 hx1

def certificate187 : RatMajorityCertificate := ⟨(65402250207425993/500000000000000000),(10910161390288322042224772603080461/12500000000000000000000000000000000),1,(7298165835055377409/20000000000000000000),(18245414587638443523/50000000000000000000),(542273280765621441/1000000000000000000),false⟩
theorem valid187 : certificate187.Valid := by decide +kernel
theorem bound187 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate187.a certificate187.b certificate187.c x ≤ (certificate187.bound:ℝ) :=
  rat_majority_certificate_sound certificate187 valid187 x hx0 hx1

def certificate188 : RatMajorityCertificate := ⟨0,(1004251262146736551/1000000000000000000),(609764993/507302500),(44218488278316047423/100000000000000000000),(690913879348688241/1562500000000000000),(729303926947670141/1000000000000000000),false⟩
theorem valid188 : certificate188.Valid := by decide +kernel
theorem bound188 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate188.a certificate188.b certificate188.c x ≤ (certificate188.bound:ℝ) :=
  rat_majority_certificate_sound certificate188 valid188 x hx0 hx1

def certificate189 : RatMajorityCertificate := ⟨(857800819615257/3906250000000000),(3061408936991562721924100040841393/3906250000000000000000000000000000),(609764993/507302500),(1575230756014397051/4000000000000000000),(9845192225089981569/25000000000000000000),(729303926947670141/1000000000000000000),false⟩
theorem valid189 : certificate189.Valid := by decide +kernel
theorem bound189 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate189.a certificate189.b certificate189.c x ≤ (certificate189.bound:ℝ) :=
  rat_majority_certificate_sound certificate189 valid189 x hx0 hx1

def certificate190 : RatMajorityCertificate := ⟨0,(1004251262146736551/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271156934251933683/500000000000000000),false⟩
theorem valid190 : certificate190.Valid := by decide +kernel
theorem bound190 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate190.a certificate190.b certificate190.c x ≤ (certificate190.bound:ℝ) :=
  rat_majority_certificate_sound certificate190 valid190 x hx0 hx1

def certificate191 : RatMajorityCertificate := ⟨(130801443095618039/1000000000000000000),(872893747827347596038611027743756511/1000000000000000000000000000000000000),1,(57017403733777613/156250000000000000),(36491138389617672321/100000000000000000000),(271156934251933683/500000000000000000),false⟩
theorem valid191 : certificate191.Valid := by decide +kernel
theorem bound191 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate191.a certificate191.b certificate191.c x ≤ (certificate191.bound:ℝ) :=
  rat_majority_certificate_sound certificate191 valid191 x hx0 hx1

def certificate192 : RatMajorityCertificate := ⟨0,(1004341154464232573/1000000000000000000),(304484473/253321250),(44218367094561268049/100000000000000000000),(884367341891225361/2000000000000000000),(729337185801126103/1000000000000000000),false⟩
theorem valid192 : certificate192.Valid := by decide +kernel
theorem bound192 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate192.a certificate192.b certificate192.c x ≤ (certificate192.bound:ℝ) :=
  rat_majority_certificate_sound certificate192 valid192 x hx0 hx1

def certificate193 : RatMajorityCertificate := ⟨(10974279476725013/50000000000000000),(39195137204144494954613851601551551/50000000000000000000000000000000000),(304484473/253321250),(246150306168172687/625000000000000000),(39384048986907629921/100000000000000000000),(729337185801126103/1000000000000000000),false⟩
theorem valid193 : certificate193.Valid := by decide +kernel
theorem bound193 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate193.a certificate193.b certificate193.c x ≤ (certificate193.bound:ℝ) :=
  rat_majority_certificate_sound certificate193 valid193 x hx0 hx1

def certificate194 : RatMajorityCertificate := ⟨0,(1004341154464232573/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271176076625203987/500000000000000000),false⟩
theorem valid194 : certificate194.Valid := by decide +kernel
theorem bound194 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate194.a certificate194.b certificate194.c x ≤ (certificate194.bound:ℝ) :=
  rat_majority_certificate_sound certificate194 valid194 x hx0 hx1

def certificate195 : RatMajorityCertificate := ⟨(26154996351648269/200000000000000000),(174599691662024301057306285291133863/200000000000000000000000000000000000),1,(1824599869189642529/5000000000000000000),(36491997383792850581/100000000000000000000),(271176076625203987/500000000000000000),false⟩
theorem valid195 : certificate195.Valid := by decide +kernel
theorem bound195 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate195.a certificate195.b certificate195.c x ≤ (certificate195.bound:ℝ) :=
  rat_majority_certificate_sound certificate195 valid195 x hx0 hx1

def certificate196 : RatMajorityCertificate := ⟨0,(502215723717135781/500000000000000000),(1216402679/1011985000),(86365179440978627/195312500000000000),(1768758874951242281/4000000000000000000),(364705140663476863/500000000000000000),false⟩
theorem valid196 : certificate196.Valid := by decide +kernel
theorem bound196 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate196.a certificate196.b certificate196.c x ≤ (certificate196.bound:ℝ) :=
  rat_majority_certificate_sound certificate196 valid196 x hx0 hx1

def certificate197 : RatMajorityCertificate := ⟨(109738242303721149/500000000000000000),(195995591080558167964527967605667631/250000000000000000000000000000000000),(1216402679/1011985000),(19692670255989689561/50000000000000000000),(39385340511979379123/100000000000000000000),(364705140663476863/500000000000000000),false⟩
theorem valid197 : certificate197.Valid := by decide +kernel
theorem bound197 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate197.a certificate197.b certificate197.c x ≤ (certificate197.bound:ℝ) :=
  rat_majority_certificate_sound certificate197 valid197 x hx0 hx1

def certificate198 : RatMajorityCertificate := ⟨0,(502215723717135781/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(54239830508883339/100000000000000000),false⟩
theorem valid198 : certificate198.Valid := by decide +kernel
theorem bound198 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate198.a certificate198.b certificate198.c x ≤ (certificate198.bound:ℝ) :=
  rat_majority_certificate_sound certificate198 valid198 x hx0 hx1

def certificate199 : RatMajorityCertificate := ⟨(130820553780338919/1000000000000000000),(436515584623266387603260709878239261/500000000000000000000000000000000000),1,(9122792145500926213/25000000000000000000),(36491168582003704853/100000000000000000000),(54239830508883339/100000000000000000),false⟩
theorem valid199 : certificate199.Valid := by decide +kernel
theorem bound199 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate199.a certificate199.b certificate199.c x ≤ (certificate199.bound:ℝ) :=
  rat_majority_certificate_sound certificate199 valid199 x hx0 hx1

end Cycle12.MajorityCertificates.Batch004
