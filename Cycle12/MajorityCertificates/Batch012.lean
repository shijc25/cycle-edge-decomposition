import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch012

def certificate480 : RatMajorityCertificate := ⟨0,(201598440031808861/200000000000000000),(2298915859/1943060000),(21896578343221209841/50000000000000000000),(43793156686442419683/100000000000000000000),(88979128890748239/125000000000000000),false⟩
theorem valid480 : certificate480.Valid := by decide +kernel
theorem bound480 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate480.a certificate480.b certificate480.c x ≤ (certificate480.bound:ℝ) :=
  rat_majority_certificate_sound certificate480 valid480 x hx0 hx1

def certificate481 : RatMajorityCertificate := ⟨(193601266561622897/1000000000000000000),(162568726704803285319036709334909683/200000000000000000000000000000000000),(2298915859/1943060000),(19817122129407364239/50000000000000000000),(39634244258814728479/100000000000000000000),(88979128890748239/125000000000000000),false⟩
theorem valid481 : certificate481.Valid := by decide +kernel
theorem bound481 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate481.a certificate481.b certificate481.c x ≤ (certificate481.bound:ℝ) :=
  rat_majority_certificate_sound certificate481 valid481 x hx0 hx1

def certificate482 : RatMajorityCertificate := ⟨0,(201598440031808861/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(33963155489013881/62500000000000000),false⟩
theorem valid482 : certificate482.Valid := by decide +kernel
theorem bound482 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate482.a certificate482.b certificate482.c x ≤ (certificate482.bound:ℝ) :=
  rat_majority_certificate_sound certificate482 valid482 x hx0 hx1

def certificate483 : RatMajorityCertificate := ⟨(12488857399701043/100000000000000000),(17642109833621443035751168081657977/20000000000000000000000000000000000),1,(7327691863398862969/20000000000000000000),(18319229658497157423/50000000000000000000),(33963155489013881/62500000000000000),false⟩
theorem valid483 : certificate483.Valid := by decide +kernel
theorem bound483 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate483.a certificate483.b certificate483.c x ≤ (certificate483.bound:ℝ) :=
  rat_majority_certificate_sound certificate483 valid483 x hx0 hx1

def certificate484 : RatMajorityCertificate := ⟨0,(1008036405239811669/1000000000000000000),(574062159/485605000),(1094268418625120293/2500000000000000000),(43770736745004811721/100000000000000000000),(710897510264681539/1000000000000000000),false⟩
theorem valid484 : certificate484.Valid := by decide +kernel
theorem bound484 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate484.a certificate484.b certificate484.c x ≤ (certificate484.bound:ℝ) :=
  rat_majority_certificate_sound certificate484 valid484 x hx0 hx1

def certificate485 : RatMajorityCertificate := ⟨(24105341693027779/125000000000000000),(101705488667659380493485227654646849/125000000000000000000000000000000000),(574062159/485605000),(39630485570839700677/100000000000000000000),(19815242785419850339/50000000000000000000),(710897510264681539/1000000000000000000),false⟩
theorem valid485 : certificate485.Valid := by decide +kernel
theorem bound485 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate485.a certificate485.b certificate485.c x ≤ (certificate485.bound:ℝ) :=
  rat_majority_certificate_sound certificate485 valid485 x hx0 hx1

def certificate486 : RatMajorityCertificate := ⟨0,(1008036405239811669/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(67927187736467961/125000000000000000),false⟩
theorem valid486 : certificate486.Valid := by decide +kernel
theorem bound486 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate486.a certificate486.b certificate486.c x ≤ (certificate486.bound:ℝ) :=
  rat_majority_certificate_sound certificate486 valid486 x hx0 hx1

def certificate487 : RatMajorityCertificate := ⟨(6237952015838181/50000000000000000),(44113737535886626728960626380465911/50000000000000000000000000000000000),1,(36641564313597652913/100000000000000000000),(18320782156798826457/50000000000000000000),(67927187736467961/125000000000000000),false⟩
theorem valid487 : certificate487.Valid := by decide +kernel
theorem bound487 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate487.a certificate487.b certificate487.c x ≤ (certificate487.bound:ℝ) :=
  rat_majority_certificate_sound certificate487 valid487 x hx0 hx1

def certificate488 : RatMajorityCertificate := ⟨0,(1008042464728441601/1000000000000000000),(573036133/487727500),(21802409906592619923/50000000000000000000),(43604819813185239847/100000000000000000000),(351845739950111871/500000000000000000),false⟩
theorem valid488 : certificate488.Valid := by decide +kernel
theorem bound488 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate488.a certificate488.b certificate488.c x ≤ (certificate488.bound:ℝ) :=
  rat_majority_certificate_sound certificate488 valid488 x hx0 hx1

def certificate489 : RatMajorityCertificate := ⟨(185750615147060811/1000000000000000000),(820797956810774223237261868390801589/1000000000000000000000000000000000000),(573036133/487727500),(39638084645375150111/100000000000000000000),(1238690145167973441/3125000000000000000),(351845739950111871/500000000000000000),false⟩
theorem valid489 : certificate489.Valid := by decide +kernel
theorem bound489 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate489.a certificate489.b certificate489.c x ≤ (certificate489.bound:ℝ) :=
  rat_majority_certificate_sound certificate489 valid489 x hx0 hx1

def certificate490 : RatMajorityCertificate := ⟨0,(1008042464728441601/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543226744548104253/1000000000000000000),false⟩
theorem valid490 : certificate490.Valid := by decide +kernel
theorem bound490 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate490.a certificate490.b certificate490.c x ≤ (certificate490.bound:ℝ) :=
  rat_majority_certificate_sound certificate490 valid490 x hx0 hx1

def certificate491 : RatMajorityCertificate := ⟨(122875681937871621/1000000000000000000),(884178559452601438776695869866294779/1000000000000000000000000000000000000),1,(36685035115809912597/100000000000000000000),(18342517557904956299/50000000000000000000),(543226744548104253/1000000000000000000),false⟩
theorem valid491 : certificate491.Valid := by decide +kernel
theorem bound491 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate491.a certificate491.b certificate491.c x ≤ (certificate491.bound:ℝ) :=
  rat_majority_certificate_sound certificate491 valid491 x hx0 hx1

def certificate492 : RatMajorityCertificate := ⟨0,(1008086050717773037/1000000000000000000),(458260487/390064000),(43603066041253535723/100000000000000000000),(10900766510313383931/25000000000000000000),(703888767887983901/1000000000000000000),false⟩
theorem valid492 : certificate492.Valid := by decide +kernel
theorem bound492 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate492.a certificate492.b certificate492.c x ≤ (certificate492.bound:ℝ) :=
  rat_majority_certificate_sound certificate492 valid492 x hx0 hx1

def certificate493 : RatMajorityCertificate := ⟨(37674774257858663/200000000000000000),(163637795750266249220696216341730469/200000000000000000000000000000000000),(458260487/390064000),(39570220215814499417/100000000000000000000),(19785110107907249709/50000000000000000000),(703888767887983901/1000000000000000000),false⟩
theorem valid493 : certificate493.Valid := by decide +kernel
theorem bound493 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate493.a certificate493.b certificate493.c x ≤ (certificate493.bound:ℝ) :=
  rat_majority_certificate_sound certificate493 valid493 x hx0 hx1

def certificate494 : RatMajorityCertificate := ⟨0,(1008086050717773037/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543240695215622333/1000000000000000000),false⟩
theorem valid494 : certificate494.Valid := by decide +kernel
theorem bound494 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate494.a certificate494.b certificate494.c x ≤ (certificate494.bound:ℝ) :=
  rat_majority_certificate_sound certificate494 valid494 x hx0 hx1

def certificate495 : RatMajorityCertificate := ⟨(61407722199796733/500000000000000000),(442138757202919311868524928171911879/500000000000000000000000000000000000),1,(18343264937450071573/50000000000000000000),(36686529874900143147/100000000000000000000),(543240695215622333/1000000000000000000),false⟩
theorem valid495 : certificate495.Valid := by decide +kernel
theorem bound495 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate495.a certificate495.b certificate495.c x ≤ (certificate495.bound:ℝ) :=
  rat_majority_certificate_sound certificate495 valid495 x hx0 hx1

def certificate496 : RatMajorityCertificate := ⟨0,(63005843518075071/62500000000000000),(572608151/487607500),(21795648111735463499/50000000000000000000),(43591296223470926999/100000000000000000000),(28136082759520533/40000000000000000),false⟩
theorem valid496 : certificate496.Valid := by decide +kernel
theorem bound496 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate496.a certificate496.b certificate496.c x ≤ (certificate496.bound:ℝ) :=
  rat_majority_certificate_sound certificate496 valid496 x hx0 hx1

def certificate497 : RatMajorityCertificate := ⟨(376142039745793/2000000000000000),(102312540539357134384114469573697/125000000000000000000000000000000),(572608151/487607500),(39565709664718548507/100000000000000000000),(9891427416179637127/25000000000000000000),(28136082759520533/40000000000000000),false⟩
theorem valid497 : certificate497.Valid := by decide +kernel
theorem bound497 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate497.a certificate497.b certificate497.c x ≤ (certificate497.bound:ℝ) :=
  rat_majority_certificate_sound certificate497 valid497 x hx0 hx1

def certificate498 : RatMajorityCertificate := ⟨0,(63005843518075071/62500000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(54318182652457681/100000000000000000),false⟩
theorem valid498 : certificate498.Valid := by decide +kernel
theorem bound498 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate498.a certificate498.b certificate498.c x ≤ (certificate498.bound:ℝ) :=
  rat_majority_certificate_sound certificate498 valid498 x hx0 hx1

def certificate499 : RatMajorityCertificate := ⟨(122206958174537523/1000000000000000000),(55306091034510214695285553379610867/62500000000000000000000000000000000),1,(36700554682625342739/100000000000000000000),(1835027734131267137/5000000000000000000),(54318182652457681/100000000000000000),false⟩
theorem valid499 : certificate499.Valid := by decide +kernel
theorem bound499 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate499.a certificate499.b certificate499.c x ≤ (certificate499.bound:ℝ) :=
  rat_majority_certificate_sound certificate499 valid499 x hx0 hx1

def certificate500 : RatMajorityCertificate := ⟨0,(50405757473966601/50000000000000000),(1144564021/975070000),(5447491525120550441/12500000000000000000),(43579932200964403529/100000000000000000000),(702869606123862459/1000000000000000000),false⟩
theorem valid500 : certificate500.Valid := by decide +kernel
theorem bound500 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate500.a certificate500.b certificate500.c x ≤ (certificate500.bound:ℝ) :=
  rat_majority_certificate_sound certificate500 valid500 x hx0 hx1

def certificate501 : RatMajorityCertificate := ⟨(187013770195056327/1000000000000000000),(40979186729222468180379506688265473/50000000000000000000000000000000000),(1144564021/975070000),(19790364074969265111/50000000000000000000),(39580728149938530223/100000000000000000000),(702869606123862459/1000000000000000000),false⟩
theorem valid501 : certificate501.Valid := by decide +kernel
theorem bound501 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate501.a certificate501.b certificate501.c x ≤ (certificate501.bound:ℝ) :=
  rat_majority_certificate_sound certificate501 valid501 x hx0 hx1

def certificate502 : RatMajorityCertificate := ⟨0,(50405757473966601/50000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271587521914008453/500000000000000000),false⟩
theorem valid502 : certificate502.Valid := by decide +kernel
theorem bound502 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate502.a certificate502.b certificate502.c x ≤ (certificate502.bound:ℝ) :=
  rat_majority_certificate_sound certificate502 valid502 x hx0 hx1

def certificate503 : RatMajorityCertificate := ⟨(122042821983149421/1000000000000000000),(44254096587645491678581892653511979/50000000000000000000000000000000000),1,(36704383189037770213/100000000000000000000),(18352191594518885107/50000000000000000000),(271587521914008453/500000000000000000),false⟩
theorem valid503 : certificate503.Valid := by decide +kernel
theorem bound503 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate503.a certificate503.b certificate503.c x ≤ (certificate503.bound:ℝ) :=
  rat_majority_certificate_sound certificate503 valid503 x hx0 hx1

def certificate504 : RatMajorityCertificate := ⟨0,(100817287768269059/100000000000000000),(1143592029/974575000),(43570706350497688109/100000000000000000000),(4357070635049768811/10000000000000000000),(1756264745220661/2500000000000000),false⟩
theorem valid504 : certificate504.Valid := by decide +kernel
theorem bound504 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate504.a certificate504.b certificate504.c x ≤ (certificate504.bound:ℝ) :=
  rat_majority_certificate_sound certificate504 valid504 x hx0 hx1

def certificate505 : RatMajorityCertificate := ⟨(186654167910882499/1000000000000000000),(81999320808850805735718093633701559/100000000000000000000000000000000000),(1143592029/974575000),(39580461587562819509/100000000000000000000),(3958046158756281951/10000000000000000000),(1756264745220661/2500000000000000),false⟩
theorem valid505 : certificate505.Valid := by decide +kernel
theorem bound505 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate505.a certificate505.b certificate505.c x ≤ (certificate505.bound:ℝ) :=
  rat_majority_certificate_sound certificate505 valid505 x hx0 hx1

def certificate506 : RatMajorityCertificate := ⟨0,(100817287768269059/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543222007346310511/1000000000000000000),false⟩
theorem valid506 : certificate506.Valid := by decide +kernel
theorem bound506 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate506.a certificate506.b certificate506.c x ≤ (certificate506.bound:ℝ) :=
  rat_majority_certificate_sound certificate506 valid506 x hx0 hx1

def certificate507 : RatMajorityCertificate := ⟨(15280147146657757/125000000000000000),(11061657979007541927010451034559337/12500000000000000000000000000000000),1,(4587495223952496689/12500000000000000000),(36699961791619973513/100000000000000000000),(543222007346310511/1000000000000000000),false⟩
theorem valid507 : certificate507.Valid := by decide +kernel
theorem bound507 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate507.a certificate507.b certificate507.c x ≤ (certificate507.bound:ℝ) :=
  rat_majority_certificate_sound certificate507 valid507 x hx0 hx1

def certificate508 : RatMajorityCertificate := ⟨0,(504089955402502797/500000000000000000),(71456341/60915000),(43562046618008078789/100000000000000000000),(4356204661800807879/10000000000000000000),(351105533180546337/500000000000000000),false⟩
theorem valid508 : certificate508.Valid := by decide +kernel
theorem bound508 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate508.a certificate508.b certificate508.c x ≤ (certificate508.bound:ℝ) :=
  rat_majority_certificate_sound certificate508 valid508 x hx0 hx1

def certificate509 : RatMajorityCertificate := ⟨(93550340169145161/500000000000000000),(204887190897498048324659864598484683/250000000000000000000000000000000000),(71456341/60915000),(39560246512904031929/100000000000000000000),(3956024651290403193/10000000000000000000),(351105533180546337/500000000000000000),false⟩
theorem valid509 : certificate509.Valid := by decide +kernel
theorem bound509 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate509.a certificate509.b certificate509.c x ≤ (certificate509.bound:ℝ) :=
  rat_majority_certificate_sound certificate509 valid509 x hx0 hx1

def certificate510 : RatMajorityCertificate := ⟨0,(504089955402502797/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271592065079843011/500000000000000000),false⟩
theorem valid510 : certificate510.Valid := by decide +kernel
theorem bound510 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate510.a certificate510.b certificate510.c x ≤ (certificate510.bound:ℝ) :=
  rat_majority_certificate_sound certificate510 valid510 x hx0 hx1

def certificate511 : RatMajorityCertificate := ⟨(121838858244523903/1000000000000000000),(442672210783728882513598254109143309/500000000000000000000000000000000000),1,(36709231279601191007/100000000000000000000),(1147163477487537219/3125000000000000000),(271592065079843011/500000000000000000),false⟩
theorem valid511 : certificate511.Valid := by decide +kernel
theorem bound511 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate511.a certificate511.b certificate511.c x ≤ (certificate511.bound:ℝ) :=
  rat_majority_certificate_sound certificate511 valid511 x hx0 hx1

def certificate512 : RatMajorityCertificate := ⟨0,(201640283316484777/200000000000000000),(571292137/487250000),(10887246455341113193/25000000000000000000),(43548985821364452773/100000000000000000000),(701734456392772893/1000000000000000000),false⟩
theorem valid512 : certificate512.Valid := by decide +kernel
theorem bound512 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate512.a certificate512.b certificate512.c x ≤ (certificate512.bound:ℝ) :=
  rat_majority_certificate_sound certificate512 valid512 x hx0 hx1

def certificate513 : RatMajorityCertificate := ⟨(37471909574802923/200000000000000000),(32772210200223995391507123095396829/40000000000000000000000000000000000),(571292137/487250000),(39540256474146990803/100000000000000000000),(9885064118536747701/25000000000000000000),(701734456392772893/1000000000000000000),false⟩
theorem valid513 : certificate513.Valid := by decide +kernel
theorem bound513 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate513.a certificate513.b certificate513.c x ≤ (certificate513.bound:ℝ) :=
  rat_majority_certificate_sound certificate513 valid513 x hx0 hx1

def certificate514 : RatMajorityCertificate := ⟨0,(201640283316484777/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271590879055425407/500000000000000000),false⟩
theorem valid514 : certificate514.Valid := by decide +kernel
theorem bound514 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate514.a certificate514.b certificate514.c x ≤ (certificate514.bound:ℝ) :=
  rat_majority_certificate_sound certificate514 valid514 x hx0 hx1

def certificate515 : RatMajorityCertificate := ⟨(121718303871911271/1000000000000000000),(177096970038950602306950231833778433/200000000000000000000000000000000000),1,(36712054828454450349/100000000000000000000),(734241096569089007/2000000000000000000),(271590879055425407/500000000000000000),false⟩
theorem valid515 : certificate515.Valid := by decide +kernel
theorem bound515 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate515.a certificate515.b certificate515.c x ≤ (certificate515.bound:ℝ) :=
  rat_majority_certificate_sound certificate515 valid515 x hx0 hx1

def certificate516 : RatMajorityCertificate := ⟨0,(31506965474555557/31250000000000000),(571042377/487180000),(43541059724421322781/100000000000000000000),(21770529862210661391/50000000000000000000),(1402513578780353/2000000000000000),false⟩
theorem valid516 : certificate516.Valid := by decide +kernel
theorem bound516 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate516.a certificate516.b certificate516.c x ≤ (certificate516.bound:ℝ) :=
  rat_majority_certificate_sound certificate516 valid516 x hx0 hx1

def certificate517 : RatMajorityCertificate := ⟨(74170734466413/400000000000000),(10265891419766520525647280992959/12500000000000000000000000000000),(571042377/487180000),(39580863080355611243/100000000000000000000),(9895215770088902811/25000000000000000000),(1402513578780353/2000000000000000),false⟩
theorem valid517 : certificate517.Valid := by decide +kernel
theorem bound517 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate517.a certificate517.b certificate517.c x ≤ (certificate517.bound:ℝ) :=
  rat_majority_certificate_sound certificate517 valid517 x hx0 hx1

def certificate518 : RatMajorityCertificate := ⟨0,(31506965474555557/31250000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(21732616492704143/40000000000000000),false⟩
theorem valid518 : certificate518.Valid := by decide +kernel
theorem bound518 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate518.a certificate518.b certificate518.c x ≤ (certificate518.bound:ℝ) :=
  rat_majority_certificate_sound certificate518 valid518 x hx0 hx1

def certificate519 : RatMajorityCertificate := ⟨(24585603009661711/200000000000000000),(5526775349714570679251995354821973/6250000000000000000000000000000000),1,(7336854815192543939/20000000000000000000),(2292767129747669981/6250000000000000000),(21732616492704143/40000000000000000),false⟩
theorem valid519 : certificate519.Valid := by decide +kernel
theorem bound519 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate519.a certificate519.b certificate519.c x ≤ (certificate519.bound:ℝ) :=
  rat_majority_certificate_sound certificate519 valid519 x hx0 hx1

end Cycle12.MajorityCertificates.Batch012
