import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay005
import Cycle12.CutFailureCertificates.Decay006
import Cycle12.CutFailureCertificates.Decay007

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget002

def certificate40 : RatFailureBudget := ⟨(114167855278157797031/1000000000000000000),(75224544716211/15625000000000000),(70664757197/1000000000000000000),[(2,CutFailureCertificates.Decay005.certificate100),(2,CutFailureCertificates.Decay005.certificate101),(2,CutFailureCertificates.Decay005.certificate102)]⟩
theorem numericValid40 : certificate40.NumericValid := by decide +kernel
theorem sound40 : certificate40.Sound := rat_failure_budget_sound certificate40 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay005.sound100,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay005.sound101,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay005.sound102,List.forall_mem_nil _⟩⟩⟩) numericValid40

def certificate41 : RatFailureBudget := ⟨(114167855278157797031/1000000000000000000),(789827860602431/200000000000000000),(1/7812500000000000),[(2,CutFailureCertificates.Decay005.certificate103),(2,CutFailureCertificates.Decay005.certificate104)]⟩
theorem numericValid41 : certificate41.NumericValid := by decide +kernel
theorem sound41 : certificate41.Sound := rat_failure_budget_sound certificate41 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay005.sound103,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay005.sound104,List.forall_mem_nil _⟩⟩) numericValid41

def certificate42 : RatFailureBudget := ⟨(5197574803552414211/50000000000000000),(2615087909717737/500000000000000000),(84852618023/50000000000000000),[(2,CutFailureCertificates.Decay005.certificate105),(2,CutFailureCertificates.Decay005.certificate106),(2,CutFailureCertificates.Decay005.certificate107)]⟩
theorem numericValid42 : certificate42.NumericValid := by decide +kernel
theorem sound42 : certificate42.Sound := rat_failure_budget_sound certificate42 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay005.sound105,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay005.sound106,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay005.sound107,List.forall_mem_nil _⟩⟩⟩) numericValid42

def certificate43 : RatFailureBudget := ⟨(5197574803552414211/50000000000000000),(4310252836006449/1000000000000000000),(91/500000000000000000),[(2,CutFailureCertificates.Decay005.certificate108),(2,CutFailureCertificates.Decay005.certificate109)]⟩
theorem numericValid43 : certificate43.NumericValid := by decide +kernel
theorem sound43 : certificate43.Sound := rat_failure_budget_sound certificate43 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay005.sound108,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay005.sound109,List.forall_mem_nil _⟩⟩) numericValid43

def certificate44 : RatFailureBudget := ⟨(95005518140300851637/1000000000000000000),(5643432850945303/1000000000000000000),(9925819612913/1000000000000000000),[(2,CutFailureCertificates.Decay005.certificate110),(2,CutFailureCertificates.Decay005.certificate111),(2,CutFailureCertificates.Decay005.certificate112)]⟩
theorem numericValid44 : certificate44.NumericValid := by decide +kernel
theorem sound44 : certificate44.Sound := rat_failure_budget_sound certificate44 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay005.sound110,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay005.sound111,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay005.sound112,List.forall_mem_nil _⟩⟩⟩) numericValid44

def certificate45 : RatFailureBudget := ⟨(95005518140300851637/1000000000000000000),(4679072421606269/1000000000000000000),(57045229/1000000000000000000),[(2,CutFailureCertificates.Decay005.certificate113),(2,CutFailureCertificates.Decay005.certificate114)]⟩
theorem numericValid45 : certificate45.NumericValid := by decide +kernel
theorem sound45 : certificate45.Sound := rat_failure_budget_sound certificate45 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay005.sound113,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay005.sound114,List.forall_mem_nil _⟩⟩) numericValid45

def certificate46 : RatFailureBudget := ⟨(87129209707661412453/1000000000000000000),(3034260705243897/500000000000000000),(114315085627181/1000000000000000000),[(2,CutFailureCertificates.Decay005.certificate115),(2,CutFailureCertificates.Decay005.certificate116),(2,CutFailureCertificates.Decay005.certificate117)]⟩
theorem numericValid46 : certificate46.NumericValid := by decide +kernel
theorem sound46 : certificate46.Sound := rat_failure_budget_sound certificate46 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay005.sound115,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay005.sound116,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay005.sound117,List.forall_mem_nil _⟩⟩⟩) numericValid46

def certificate47 : RatFailureBudget := ⟨(87129209707661412453/1000000000000000000),(1266840691516533/250000000000000000),(32659943/1000000000000000000),[(2,CutFailureCertificates.Decay005.certificate118),(2,CutFailureCertificates.Decay005.certificate119)]⟩
theorem numericValid47 : certificate47.NumericValid := by decide +kernel
theorem sound47 : certificate47.Sound := rat_failure_budget_sound certificate47 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay005.sound118,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay005.sound119,List.forall_mem_nil _⟩⟩) numericValid47

def certificate48 : RatFailureBudget := ⟨(40079938802876286037/500000000000000000),(315639804933787/50000000000000000),(1099884470320859/1000000000000000000),[(2,CutFailureCertificates.Decay006.certificate120),(2,CutFailureCertificates.Decay006.certificate121),(2,CutFailureCertificates.Decay006.certificate122)]⟩
theorem numericValid48 : certificate48.NumericValid := by decide +kernel
theorem sound48 : certificate48.Sound := rat_failure_budget_sound certificate48 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay006.sound120,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay006.sound121,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay006.sound122,List.forall_mem_nil _⟩⟩⟩) numericValid48

def certificate49 : RatFailureBudget := ⟨(40079938802876286037/500000000000000000),(2736693390147867/500000000000000000),(21718051/1000000000000000000),[(2,CutFailureCertificates.Decay006.certificate123),(2,CutFailureCertificates.Decay006.certificate124)]⟩
theorem numericValid49 : certificate49.NumericValid := by decide +kernel
theorem sound49 : certificate49.Sound := rat_failure_budget_sound certificate49 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay006.sound123,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay006.sound124,List.forall_mem_nil _⟩⟩) numericValid49

def certificate50 : RatFailureBudget := ⟨(924556669586532241/12500000000000000),(1422456203235449/200000000000000000),(193017100048933/62500000000000000),[(2,CutFailureCertificates.Decay006.certificate125),(2,CutFailureCertificates.Decay006.certificate126),(2,CutFailureCertificates.Decay006.certificate127)]⟩
theorem numericValid50 : certificate50.NumericValid := by decide +kernel
theorem sound50 : certificate50.Sound := rat_failure_budget_sound certificate50 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay006.sound125,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay006.sound126,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay006.sound127,List.forall_mem_nil _⟩⟩⟩) numericValid50

def certificate51 : RatFailureBudget := ⟨(924556669586532241/12500000000000000),(5892665873330429/1000000000000000000),(16702439/1000000000000000000),[(2,CutFailureCertificates.Decay006.certificate128),(2,CutFailureCertificates.Decay006.certificate129)]⟩
theorem numericValid51 : certificate51.NumericValid := by decide +kernel
theorem sound51 : certificate51.Sound := rat_failure_budget_sound certificate51 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay006.sound128,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay006.sound129,List.forall_mem_nil _⟩⟩) numericValid51

def certificate52 : RatFailureBudget := ⟨(68433625112009156493/1000000000000000000),(375900511454869/50000000000000000),(8071001482285951/1000000000000000000),[(2,CutFailureCertificates.Decay006.certificate130),(2,CutFailureCertificates.Decay006.certificate131),(2,CutFailureCertificates.Decay006.certificate132)]⟩
theorem numericValid52 : certificate52.NumericValid := by decide +kernel
theorem sound52 : certificate52.Sound := rat_failure_budget_sound certificate52 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay006.sound130,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay006.sound131,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay006.sound132,List.forall_mem_nil _⟩⟩⟩) numericValid52

def certificate53 : RatFailureBudget := ⟨(68433625112009156493/1000000000000000000),(1581551426212033/250000000000000000),(14113223/1000000000000000000),[(2,CutFailureCertificates.Decay006.certificate133),(2,CutFailureCertificates.Decay006.certificate134)]⟩
theorem numericValid53 : certificate53.NumericValid := by decide +kernel
theorem sound53 : certificate53.Sound := rat_failure_budget_sound certificate53 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay006.sound133,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay006.sound134,List.forall_mem_nil _⟩⟩) numericValid53

def certificate54 : RatFailureBudget := ⟨(63476256200139309633/1000000000000000000),(8042065482993687/1000000000000000000),(1967558296486079/50000000000000000),[(2,CutFailureCertificates.Decay006.certificate135),(2,CutFailureCertificates.Decay006.certificate136),(2,CutFailureCertificates.Decay006.certificate137)]⟩
theorem numericValid54 : certificate54.NumericValid := by decide +kernel
theorem sound54 : certificate54.Sound := rat_failure_budget_sound certificate54 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay006.sound135,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay006.sound136,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay006.sound137,List.forall_mem_nil _⟩⟩⟩) numericValid54

def certificate55 : RatFailureBudget := ⟨(63476256200139309633/1000000000000000000),(3383068772662723/500000000000000000),(20287023551/500000000000000000),[(2,CutFailureCertificates.Decay006.certificate138),(2,CutFailureCertificates.Decay006.certificate139)]⟩
theorem numericValid55 : certificate55.NumericValid := by decide +kernel
theorem sound55 : certificate55.Sound := rat_failure_budget_sound certificate55 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay006.sound138,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay006.sound139,List.forall_mem_nil _⟩⟩) numericValid55

def certificate56 : RatFailureBudget := ⟨(29508253281651770749/500000000000000000),(8755955685373489/1000000000000000000),(40578846701895729/500000000000000000),[(2,CutFailureCertificates.Decay007.certificate140),(2,CutFailureCertificates.Decay007.certificate141),(2,CutFailureCertificates.Decay007.certificate142)]⟩
theorem numericValid56 : certificate56.NumericValid := by decide +kernel
theorem sound56 : certificate56.Sound := rat_failure_budget_sound certificate56 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay007.sound140,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay007.sound141,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay007.sound142,List.forall_mem_nil _⟩⟩⟩) numericValid56

def certificate57 : RatFailureBudget := ⟨(29508253281651770749/500000000000000000),(7228805146497797/1000000000000000000),(21751607591/1000000000000000000),[(2,CutFailureCertificates.Decay007.certificate143),(2,CutFailureCertificates.Decay007.certificate144)]⟩
theorem numericValid57 : certificate57.NumericValid := by decide +kernel
theorem sound57 : certificate57.Sound := rat_failure_budget_sound certificate57 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay007.sound143,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay007.sound144,List.forall_mem_nil _⟩⟩) numericValid57

def certificate58 : RatFailureBudget := ⟨(54990570427380060659/1000000000000000000),(9064221611448977/1000000000000000000),(12152033640579877/62500000000000000),[(2,CutFailureCertificates.Decay007.certificate145),(2,CutFailureCertificates.Decay007.certificate146),(2,CutFailureCertificates.Decay007.certificate147)]⟩
theorem numericValid58 : certificate58.NumericValid := by decide +kernel
theorem sound58 : certificate58.Sound := rat_failure_budget_sound certificate58 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay007.sound145,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay007.sound146,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay007.sound147,List.forall_mem_nil _⟩⟩⟩) numericValid58

def certificate59 : RatFailureBudget := ⟨(54990570427380060659/1000000000000000000),(3847019746748329/500000000000000000),(9562078111/500000000000000000),[(2,CutFailureCertificates.Decay007.certificate148),(2,CutFailureCertificates.Decay007.certificate149)]⟩
theorem numericValid59 : certificate59.NumericValid := by decide +kernel
theorem sound59 : certificate59.Sound := rat_failure_budget_sound certificate59 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay007.sound148,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay007.sound149,List.forall_mem_nil _⟩⟩) numericValid59

end Cycle12.CutFailureCertificates.Budget002
