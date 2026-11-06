import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch006

def certificate240 : RatMajorityCertificate := ⟨0,(251276064938497917/250000000000000000),(1204440619/1003160000),(44188736332704867217/100000000000000000000),(22094368166352433609/50000000000000000000),(72833062498620823/100000000000000000),false⟩
theorem valid240 : certificate240.Valid := by decide +kernel
theorem bound240 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate240.a certificate240.b certificate240.c x ≤ (certificate240.bound:ℝ) :=
  rat_majority_certificate_sound certificate240 valid240 x hx0 hx1

def certificate241 : RatMajorityCertificate := ⟨(217177293802218173/1000000000000000000),(196704609157884502166210162659954359/250000000000000000000000000000000000),(1204440619/1003160000),(2463649613005482857/6250000000000000000),(39418393808087725713/100000000000000000000),(72833062498620823/100000000000000000),false⟩
theorem valid241 : certificate241.Valid := by decide +kernel
theorem bound241 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate241.a certificate241.b certificate241.c x ≤ (certificate241.bound:ℝ) :=
  rat_majority_certificate_sound certificate241 valid241 x hx0 hx1

def certificate242 : RatMajorityCertificate := ⟨0,(251276064938497917/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(16962365378947727/31250000000000000),false⟩
theorem valid242 : certificate242.Valid := by decide +kernel
theorem bound242 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate242.a certificate242.b certificate242.c x ≤ (certificate242.bound:ℝ) :=
  rat_majority_certificate_sound certificate242 valid242 x hx0 hx1

def certificate243 : RatMajorityCertificate := ⟨(65831955562072261/500000000000000000),(109096037728405379905297914848019663/125000000000000000000000000000000000),1,(18236589196443519177/50000000000000000000),(7294635678577407671/20000000000000000000),(16962365378947727/31250000000000000),false⟩
theorem valid243 : certificate243.Valid := by decide +kernel
theorem bound243 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate243.a certificate243.b certificate243.c x ≤ (certificate243.bound:ℝ) :=
  rat_majority_certificate_sound certificate243 valid243 x hx0 hx1

def certificate244 : RatMajorityCertificate := ⟨0,(502575233457690119/500000000000000000),(1203203687/1002590000),(22088191472584365399/50000000000000000000),(44176382945168730799/100000000000000000000),(363831982379372727/500000000000000000),false⟩
theorem valid244 : certificate244.Valid := by decide +kernel
theorem bound244 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate244.a certificate244.b certificate244.c x ≤ (certificate244.bound:ℝ) :=
  rat_majority_certificate_sound certificate244 valid244 x hx0 hx1

def certificate245 : RatMajorityCertificate := ⟨(4304490604225097/20000000000000000),(7888174298818940653895232451283457/10000000000000000000000000000000000),(1203203687/1002590000),(9864448072478681691/25000000000000000000),(7891558457982945353/20000000000000000000),(363831982379372727/500000000000000000),false⟩
theorem valid245 : certificate245.Valid := by decide +kernel
theorem bound245 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate245.a certificate245.b certificate245.c x ≤ (certificate245.bound:ℝ) :=
  rat_majority_certificate_sound certificate245 valid245 x hx0 hx1

def certificate246 : RatMajorityCertificate := ⟨0,(502575233457690119/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271402343458869577/500000000000000000),false⟩
theorem valid246 : certificate246.Valid := by decide +kernel
theorem bound246 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate246.a certificate246.b certificate246.c x ≤ (certificate246.bound:ℝ) :=
  rat_majority_certificate_sound certificate246 valid246 x hx0 hx1

def certificate247 : RatMajorityCertificate := ⟨(131550117410178467/1000000000000000000),(436461402488883130483963634627532427/500000000000000000000000000000000000),1,(1823798577396025957/5000000000000000000),(36475971547920519141/100000000000000000000),(271402343458869577/500000000000000000),false⟩
theorem valid247 : certificate247.Valid := by decide +kernel
theorem bound247 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate247.a certificate247.b certificate247.c x ≤ (certificate247.bound:ℝ) :=
  rat_majority_certificate_sound certificate247 valid247 x hx0 hx1

def certificate248 : RatMajorityCertificate := ⟨0,(1005258584762215319/1000000000000000000),(1201675283/1001140000),(44181124219354691621/100000000000000000000),(22090562109677345811/50000000000000000000),(145602774753124663/200000000000000000),false⟩
theorem valid248 : certificate248.Valid := by decide +kernel
theorem bound248 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate248.a certificate248.b certificate248.c x ≤ (certificate248.bound:ℝ) :=
  rat_majority_certificate_sound certificate248 valid248 x hx0 hx1

def certificate249 : RatMajorityCertificate := ⟨(54056022291521539/250000000000000000),(196974365723904123974556023155744059/250000000000000000000000000000000000),(1201675283/1001140000),(19718294339333310207/50000000000000000000),(7887317735733324083/20000000000000000000),(145602774753124663/200000000000000000),false⟩
theorem valid249 : certificate249.Valid := by decide +kernel
theorem bound249 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate249.a certificate249.b certificate249.c x ≤ (certificate249.bound:ℝ) :=
  rat_majority_certificate_sound certificate249 valid249 x hx0 hx1

def certificate250 : RatMajorityCertificate := ⟨0,(1005258584762215319/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(54287187143138583/100000000000000000),false⟩
theorem valid250 : certificate250.Valid := by decide +kernel
theorem bound250 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate250.a certificate250.b certificate250.c x ≤ (certificate250.bound:ℝ) :=
  rat_majority_certificate_sound certificate250 valid250 x hx0 hx1

def certificate251 : RatMajorityCertificate := ⟨(131717288793084209/1000000000000000000),(872848649441363482772664138643202329/1000000000000000000000000000000000000),1,(36472337838783647251/100000000000000000000),(9118084459695911813/25000000000000000000),(54287187143138583/100000000000000000),false⟩
theorem valid251 : certificate251.Valid := by decide +kernel
theorem bound251 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate251.a certificate251.b certificate251.c x ≤ (certificate251.bound:ℝ) :=
  rat_majority_certificate_sound certificate251 valid251 x hx0 hx1

def certificate252 : RatMajorityCertificate := ⟨0,(1005289388498388519/1000000000000000000),(1200605009/1000905000),(8832693062155129859/20000000000000000000),(2760216581923478081/6250000000000000000),(727124142161518381/1000000000000000000),false⟩
theorem valid252 : certificate252.Valid := by decide +kernel
theorem bound252 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate252.a certificate252.b certificate252.c x ≤ (certificate252.bound:ℝ) :=
  rat_majority_certificate_sound certificate252 valid252 x hx0 hx1

def certificate253 : RatMajorityCertificate := ⟨(26781783351944799/125000000000000000),(98737730953525655937552363856637319/125000000000000000000000000000000000),(1200605009/1000905000),(7894144980654515781/20000000000000000000),(19735362451636289453/50000000000000000000),(727124142161518381/1000000000000000000),false⟩
theorem valid253 : certificate253.Valid := by decide +kernel
theorem bound253 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate253.a certificate253.b certificate253.c x ≤ (certificate253.bound:ℝ) :=
  rat_majority_certificate_sound certificate253 valid253 x hx0 hx1

def certificate254 : RatMajorityCertificate := ⟨0,(1005289388498388519/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(542840327415411983/1000000000000000000),false⟩
theorem valid254 : certificate254.Valid := by decide +kernel
theorem bound254 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate254.a certificate254.b certificate254.c x ≤ (certificate254.bound:ℝ) :=
  rat_majority_certificate_sound certificate254 valid254 x hx0 hx1

def certificate255 : RatMajorityCertificate := ⟨(32822091156345273/250000000000000000),(218326647176796424537243157936879313/250000000000000000000000000000000000),1,(4560310035290812657/12500000000000000000),(36482480282326501257/100000000000000000000),(542840327415411983/1000000000000000000),false⟩
theorem valid255 : certificate255.Valid := by decide +kernel
theorem bound255 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate255.a certificate255.b certificate255.c x ≤ (certificate255.bound:ℝ) :=
  rat_majority_certificate_sound certificate255 valid255 x hx0 hx1

def certificate256 : RatMajorityCertificate := ⟨0,(1005335795196675851/1000000000000000000),(799900441/666900000),(5520184756575137671/12500000000000000000),(44161478052601101369/100000000000000000000),(727058628596223211/1000000000000000000),false⟩
theorem valid256 : certificate256.Valid := by decide +kernel
theorem bound256 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate256.a certificate256.b certificate256.c x ≤ (certificate256.bound:ℝ) :=
  rat_majority_certificate_sound certificate256 valid256 x hx0 hx1

def certificate257 : RatMajorityCertificate := ⟨(4282842132076897/20000000000000000),(15801021403380163152347006885085653/20000000000000000000000000000000000),(799900441/666900000),(9867958834029029607/25000000000000000000),(39471835336116118429/100000000000000000000),(727058628596223211/1000000000000000000),false⟩
theorem valid257 : certificate257.Valid := by decide +kernel
theorem bound257 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate257.a certificate257.b certificate257.c x ≤ (certificate257.bound:ℝ) :=
  rat_majority_certificate_sound certificate257 valid257 x hx0 hx1

def certificate258 : RatMajorityCertificate := ⟨0,(1005335795196675851/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(33928015998581197/62500000000000000),false⟩
theorem valid258 : certificate258.Valid := by decide +kernel
theorem bound258 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate258.a certificate258.b certificate258.c x ≤ (certificate258.bound:ℝ) :=
  rat_majority_certificate_sound certificate258 valid258 x hx0 hx1

def certificate259 : RatMajorityCertificate := ⟨(26232673044430883/200000000000000000),(174694513824077844821624810275293567/200000000000000000000000000000000000),1,(18242766963481736403/50000000000000000000),(36485533926963472807/100000000000000000000),(33928015998581197/62500000000000000),false⟩
theorem valid259 : certificate259.Valid := by decide +kernel
theorem bound259 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate259.a certificate259.b certificate259.c x ≤ (certificate259.bound:ℝ) :=
  rat_majority_certificate_sound certificate259 valid259 x hx0 hx1

def certificate260 : RatMajorityCertificate := ⟨0,(251345552768229817/250000000000000000),(2397842313/1999610000),(44155288173528570553/100000000000000000000),(22077644086764285277/50000000000000000000),(726800361416719837/1000000000000000000),false⟩
theorem valid260 : certificate260.Valid := by decide +kernel
theorem bound260 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate260.a certificate260.b certificate260.c x ≤ (certificate260.bound:ℝ) :=
  rat_majority_certificate_sound certificate260 valid260 x hx0 hx1

def certificate261 : RatMajorityCertificate := ⟨(106895734786719793/500000000000000000),(98805008835580729085806983393332119/125000000000000000000000000000000000),(2397842313/1999610000),(19737443654779274667/50000000000000000000),(7894977461911709867/20000000000000000000),(726800361416719837/1000000000000000000),false⟩
theorem valid261 : certificate261.Valid := by decide +kernel
theorem bound261 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate261.a certificate261.b certificate261.c x ≤ (certificate261.bound:ℝ) :=
  rat_majority_certificate_sound certificate261 valid261 x hx0 hx1

def certificate262 : RatMajorityCertificate := ⟨0,(251345552768229817/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(108573851687884247/200000000000000000),false⟩
theorem valid262 : certificate262.Valid := by decide +kernel
theorem bound262 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate262.a certificate262.b certificate262.c x ≤ (certificate262.bound:ℝ) :=
  rat_majority_certificate_sound certificate262 valid262 x hx0 hx1

def certificate263 : RatMajorityCertificate := ⟨(16395168413186617/125000000000000000),(27297341428488115566375880835240911/31250000000000000000000000000000000),1,(18242852270877147161/50000000000000000000),(36485704541754294323/100000000000000000000),(108573851687884247/200000000000000000),false⟩
theorem valid263 : certificate263.Valid := by decide +kernel
theorem bound263 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate263.a certificate263.b certificate263.c x ≤ (certificate263.bound:ℝ) :=
  rat_majority_certificate_sound certificate263 valid263 x hx0 hx1

def certificate264 : RatMajorityCertificate := ⟨0,(502714343478728713/500000000000000000),(149770231/124907500),(44152912759427824553/100000000000000000000),(22076456379713912277/50000000000000000000),(72671677135094981/100000000000000000),false⟩
theorem valid264 : certificate264.Valid := by decide +kernel
theorem bound264 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate264.a certificate264.b certificate264.c x ≤ (certificate264.bound:ℝ) :=
  rat_majority_certificate_sound certificate264 valid264 x hx0 hx1

def certificate265 : RatMajorityCertificate := ⟨(53413408127455957/250000000000000000),(98826899469926764435508018741206659/125000000000000000000000000000000000),(149770231/124907500),(39476271051599723181/100000000000000000000),(19738135525799861591/50000000000000000000),(72671677135094981/100000000000000000),false⟩
theorem valid265 : certificate265.Valid := by decide +kernel
theorem bound265 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate265.a certificate265.b certificate265.c x ≤ (certificate265.bound:ℝ) :=
  rat_majority_certificate_sound certificate265 valid265 x hx0 hx1

def certificate266 : RatMajorityCertificate := ⟨0,(502714343478728713/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(542892842400020917/1000000000000000000),false⟩
theorem valid266 : certificate266.Valid := by decide +kernel
theorem bound266 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate266.a certificate266.b certificate266.c x ≤ (certificate266.bound:ℝ) :=
  rat_majority_certificate_sound certificate266 valid266 x hx0 hx1

def certificate267 : RatMajorityCertificate := ⟨(131183382393000921/1000000000000000000),(436766575523712235381101905881855327/500000000000000000000000000000000000),1,(36485311559232642919/100000000000000000000),(912132788980816073/2500000000000000000),(542892842400020917/1000000000000000000),false⟩
theorem valid267 : certificate267.Valid := by decide +kernel
theorem bound267 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate267.a certificate267.b certificate267.c x ≤ (certificate267.bound:ℝ) :=
  rat_majority_certificate_sound certificate267 valid267 x hx0 hx1

def certificate268 : RatMajorityCertificate := ⟨0,(502737596542916913/500000000000000000),(2394505591/1997440000),(44147034159893578859/100000000000000000000),(2207351707994678943/5000000000000000000),(18161914096003373/25000000000000000),false⟩
theorem valid268 : certificate268.Valid := by decide +kernel
theorem bound268 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate268.a certificate268.b certificate268.c x ≤ (certificate268.bound:ℝ) :=
  rat_majority_certificate_sound certificate268 valid268 x hx0 hx1

def certificate269 : RatMajorityCertificate := ⟨(53339296690852831/250000000000000000),(98868729316080314502276789656169297/125000000000000000000000000000000000),(2394505591/1997440000),(78956404249024221/200000000000000000),(39478202124512110501/100000000000000000000),(18161914096003373/25000000000000000),false⟩
theorem valid269 : certificate269.Valid := by decide +kernel
theorem bound269 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate269.a certificate269.b certificate269.c x ≤ (certificate269.bound:ℝ) :=
  rat_majority_certificate_sound certificate269 valid269 x hx0 hx1

def certificate270 : RatMajorityCertificate := ⟨0,(502737596542916913/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(67861537262191429/125000000000000000),false⟩
theorem valid270 : certificate270.Valid := by decide +kernel
theorem bound270 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate270.a certificate270.b certificate270.c x ≤ (certificate270.bound:ℝ) :=
  rat_majority_certificate_sound certificate270 valid270 x hx0 hx1

def certificate271 : RatMajorityCertificate := ⟨(32744489166544933/250000000000000000),(109222513352114848031536414099848171/125000000000000000000000000000000000),1,(3649024877708902523/10000000000000000000),(36490248777089025231/100000000000000000000),(67861537262191429/125000000000000000),false⟩
theorem valid271 : certificate271.Valid := by decide +kernel
theorem bound271 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate271.a certificate271.b certificate271.c x ≤ (certificate271.bound:ℝ) :=
  rat_majority_certificate_sound certificate271 valid271 x hx0 hx1

def certificate272 : RatMajorityCertificate := ⟨0,(502760863234007793/500000000000000000),(1196536993/998185000),(5518169965603392883/12500000000000000000),(8829071944965428613/20000000000000000000),(145286804276568761/200000000000000000),false⟩
theorem valid272 : certificate272.Valid := by decide +kernel
theorem bound272 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate272.a certificate272.b certificate272.c x ≤ (certificate272.bound:ℝ) :=
  rat_majority_certificate_sound certificate272 valid272 x hx0 hx1

def certificate273 : RatMajorityCertificate := ⟨(213348776961151609/1000000000000000000),(395497447959099416149393098239511063/500000000000000000000000000000000000),(1196536993/998185000),(39476881800780978711/100000000000000000000),(4934610225097622339/12500000000000000000),(145286804276568761/200000000000000000),false⟩
theorem valid273 : certificate273.Valid := by decide +kernel
theorem bound273 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate273.a certificate273.b certificate273.c x ≤ (certificate273.bound:ℝ) :=
  rat_majority_certificate_sound certificate273 valid273 x hx0 hx1

def certificate274 : RatMajorityCertificate := ⟨0,(502760863234007793/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135728999143799809/250000000000000000),false⟩
theorem valid274 : certificate274.Valid := by decide +kernel
theorem bound274 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate274.a certificate274.b certificate274.c x ≤ (certificate274.bound:ℝ) :=
  rat_majority_certificate_sound certificate274 valid274 x hx0 hx1

def certificate275 : RatMajorityCertificate := ⟨(65500399809673207/500000000000000000),(218449394066519955200623111778697849/250000000000000000000000000000000000),1,(7297967405272451497/20000000000000000000),(18244918513181128743/50000000000000000000),(135728999143799809/250000000000000000),false⟩
theorem valid275 : certificate275.Valid := by decide +kernel
theorem bound275 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate275.a certificate275.b certificate275.c x ≤ (certificate275.bound:ℝ) :=
  rat_majority_certificate_sound certificate275 valid275 x hx0 hx1

def certificate276 : RatMajorityCertificate := ⟨0,(502784142054231537/500000000000000000),(149449153/124706875),(8827683516349228441/20000000000000000000),(22069208790873071103/50000000000000000000),(145227175272897181/200000000000000000),false⟩
theorem valid276 : certificate276.Valid := by decide +kernel
theorem bound276 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate276.a certificate276.b certificate276.c x ≤ (certificate276.bound:ℝ) :=
  rat_majority_certificate_sound certificate276 valid276 x hx0 hx1

def certificate277 : RatMajorityCertificate := ⟨(212897160329287011/1000000000000000000),(395742825952288789475027777279334093/500000000000000000000000000000000000),(149449153/124706875),(394818110004299569/1000000000000000000),(39481811000429956901/100000000000000000000),(145227175272897181/200000000000000000),false⟩
theorem valid277 : certificate277.Valid := by decide +kernel
theorem bound277 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate277.a certificate277.b certificate277.c x ≤ (certificate277.bound:ℝ) :=
  rat_majority_certificate_sound certificate277 valid277 x hx0 hx1

def certificate278 : RatMajorityCertificate := ⟨0,(502784142054231537/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(54293390027115631/100000000000000000),false⟩
theorem valid278 : certificate278.Valid := by decide +kernel
theorem bound278 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate278.a certificate278.b certificate278.c x ≤ (certificate278.bound:ℝ) :=
  rat_majority_certificate_sound certificate278 valid278 x hx0 hx1

def certificate279 : RatMajorityCertificate := ⟨(130968908563479147/1000000000000000000),(436935051726363576330103189790741061/500000000000000000000000000000000000),1,(9122676901845357041/25000000000000000000),(7298141521476285633/20000000000000000000),(54293390027115631/100000000000000000),false⟩
theorem valid279 : certificate279.Valid := by decide +kernel
theorem bound279 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate279.a certificate279.b certificate279.c x ≤ (certificate279.bound:ℝ) :=
  rat_majority_certificate_sound certificate279 valid279 x hx0 hx1

end Cycle12.MajorityCertificates.Batch006
