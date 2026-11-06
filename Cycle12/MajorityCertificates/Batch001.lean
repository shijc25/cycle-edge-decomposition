import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch001

def certificate40 : RatMajorityCertificate := ⟨0,(1000432357558111133/1000000000000000000),(105605419/90210800),(21753396424690904307/50000000000000000000),(8701358569876361723/20000000000000000000),(87269456259513071/125000000000000000),false⟩
theorem valid40 : certificate40.Valid := by decide +kernel
theorem bound40 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate40.a certificate40.b certificate40.c x ≤ (certificate40.bound:ℝ) :=
  rat_majority_certificate_sound certificate40 valid40 x hx0 hx1

def certificate41 : RatMajorityCertificate := ⟨(210308516076638651/1000000000000000000),(790032913005011610555688080658798417/1000000000000000000000000000000000000),(105605419/90210800),(1554766526966247479/4000000000000000000),(1214661349192380843/3125000000000000000),(87269456259513071/125000000000000000),false⟩
theorem valid41 : certificate41.Valid := by decide +kernel
theorem bound41 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate41.a certificate41.b certificate41.c x ≤ (certificate41.bound:ℝ) :=
  rat_majority_certificate_sound certificate41 valid41 x hx0 hx1

def certificate42 : RatMajorityCertificate := ⟨0,(1000432357558111133/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(539893397233443771/1000000000000000000),false⟩
theorem valid42 : certificate42.Valid := by decide +kernel
theorem bound42 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate42.a certificate42.b certificate42.c x ≤ (certificate42.bound:ℝ) :=
  rat_majority_certificate_sound certificate42 valid42 x hx0 hx1

def certificate43 : RatMajorityCertificate := ⟨(15570118557768357/125000000000000000),(109477194278556397062252127323181519/125000000000000000000000000000000000),1,(36626996306331042341/100000000000000000000),(18313498153165521171/50000000000000000000),(539893397233443771/1000000000000000000),false⟩
theorem valid43 : certificate43.Valid := by decide +kernel
theorem bound43 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate43.a certificate43.b certificate43.c x ≤ (certificate43.bound:ℝ) :=
  rat_majority_certificate_sound certificate43 valid43 x hx0 hx1

def certificate44 : RatMajorityCertificate := ⟨0,(1000505966523029923/1000000000000000000),(2631083451/2244130000),(43547755857202762171/100000000000000000000),(10886938964300690543/25000000000000000000),(87478547183972471/125000000000000000),false⟩
theorem valid44 : certificate44.Valid := by decide +kernel
theorem bound44 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate44.a certificate44.b certificate44.c x ≤ (certificate44.bound:ℝ) :=
  rat_majority_certificate_sound certificate44 valid44 x hx0 hx1

def certificate45 : RatMajorityCertificate := ⟨(105371049240832781/500000000000000000),(394828619797269781530266576097694137/500000000000000000000000000000000000),(2631083451/2244130000),(607821780472968519/1562500000000000000),(38900593950269985217/100000000000000000000),(87478547183972471/125000000000000000),false⟩
theorem valid45 : certificate45.Valid := by decide +kernel
theorem bound45 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate45.a certificate45.b certificate45.c x ≤ (certificate45.bound:ℝ) :=
  rat_majority_certificate_sound certificate45 valid45 x hx0 hx1

def certificate46 : RatMajorityCertificate := ⟨0,(1000505966523029923/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(134970245846570637/250000000000000000),false⟩
theorem valid46 : certificate46.Valid := by decide +kernel
theorem bound46 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate46.a certificate46.b certificate46.c x ≤ (certificate46.bound:ℝ) :=
  rat_majority_certificate_sound certificate46 valid46 x hx0 hx1

def certificate47 : RatMajorityCertificate := ⟨(62064162013579821/500000000000000000),(438157418859676363693265735268016217/500000000000000000000000000000000000),1,(18318622870692299899/50000000000000000000),(36637245741384599799/100000000000000000000),(134970245846570637/250000000000000000),false⟩
theorem valid47 : certificate47.Valid := by decide +kernel
theorem bound47 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate47.a certificate47.b certificate47.c x ≤ (certificate47.bound:ℝ) :=
  rat_majority_certificate_sound certificate47 valid47 x hx0 hx1

def certificate48 : RatMajorityCertificate := ⟨0,(100058502530151069/100000000000000000),(874133637/744430000),(5448654250148910353/12500000000000000000),(1743569360047651313/4000000000000000000),(70154299302723541/100000000000000000),false⟩
theorem valid48 : certificate48.Valid := by decide +kernel
theorem bound48 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate48.a certificate48.b certificate48.c x ≤ (certificate48.bound:ℝ) :=
  rat_majority_certificate_sound certificate48 valid48 x hx0 hx1

def certificate49 : RatMajorityCertificate := ⟨(211321492454374833/1000000000000000000),(78913990442729704736157582558353523/100000000000000000000000000000000000),(874133637/744430000),(38928705046272173781/100000000000000000000),(19464352523136086891/50000000000000000000),(70154299302723541/100000000000000000),false⟩
theorem valid49 : certificate49.Valid := by decide +kernel
theorem bound49 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate49.a certificate49.b certificate49.c x ≤ (certificate49.bound:ℝ) :=
  rat_majority_certificate_sound certificate49 valid49 x hx0 hx1

def certificate50 : RatMajorityCertificate := ⟨0,(100058502530151069/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(539967533218585479/1000000000000000000),false⟩
theorem valid50 : certificate50.Valid := by decide +kernel
theorem bound50 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate50.a certificate50.b certificate50.c x ≤ (certificate50.bound:ℝ) :=
  rat_majority_certificate_sound certificate50 valid50 x hx0 hx1

def certificate51 : RatMajorityCertificate := ⟨(31149091128802371/250000000000000000),(21897894219014588993378764324615401/25000000000000000000000000000000000),1,(36626559428436073211/100000000000000000000),(9156639857109018303/25000000000000000000),(539967533218585479/1000000000000000000),false⟩
theorem valid51 : certificate51.Valid := by decide +kernel
theorem bound51 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate51.a certificate51.b certificate51.c x ≤ (certificate51.bound:ℝ) :=
  rat_majority_certificate_sound certificate51 valid51 x hx0 hx1

def certificate52 : RatMajorityCertificate := ⟨0,(50033472211476713/50000000000000000),(65348939/55568500),(2181499623818840947/5000000000000000000),(43629992476376818941/100000000000000000000),(703217464914007971/1000000000000000000),false⟩
theorem valid52 : certificate52.Valid := by decide +kernel
theorem bound52 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate52.a certificate52.b certificate52.c x ≤ (certificate52.bound:ℝ) :=
  rat_majority_certificate_sound certificate52 valid52 x hx0 hx1

def certificate53 : RatMajorityCertificate := ⟨(211725112991211811/1000000000000000000),(39440129654159149653327136322942757/50000000000000000000000000000000000),(65348939/55568500),(38960782721359404291/100000000000000000000),(9740195680339851073/25000000000000000000),(703217464914007971/1000000000000000000),false⟩
theorem valid53 : certificate53.Valid := by decide +kernel
theorem bound53 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate53.a certificate53.b certificate53.c x ≤ (certificate53.bound:ℝ) :=
  rat_majority_certificate_sound certificate53 valid53 x hx0 hx1

def certificate54 : RatMajorityCertificate := ⟨0,(50033472211476713/50000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540055501411442719/1000000000000000000),false⟩
theorem valid54 : certificate54.Valid := by decide +kernel
theorem bound54 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate54.a certificate54.b certificate54.c x ≤ (certificate54.bound:ℝ) :=
  rat_majority_certificate_sound certificate54 valid54 x hx0 hx1

def certificate55 : RatMajorityCertificate := ⟨(25010890088602851/200000000000000000),(8755312768062933510229318308091237/10000000000000000000000000000000000),1,(18308055527839009769/50000000000000000000),(36616111055678019539/100000000000000000000),(540055501411442719/1000000000000000000),false⟩
theorem valid55 : certificate55.Valid := by decide +kernel
theorem bound55 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate55.a certificate55.b certificate55.c x ≤ (certificate55.bound:ℝ) :=
  rat_majority_certificate_sound certificate55 valid55 x hx0 hx1

def certificate56 : RatMajorityCertificate := ⟨0,(100075913284494947/100000000000000000),(1302928639/1106230000),(2183566443344244063/5000000000000000000),(43671328866884881261/100000000000000000000),(704937359199490487/1000000000000000000),false⟩
theorem valid56 : certificate56.Valid := by decide +kernel
theorem bound56 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate56.a certificate56.b certificate56.c x ≤ (certificate56.bound:ℝ) :=
  rat_majority_certificate_sound certificate56 valid56 x hx0 hx1

def certificate57 : RatMajorityCertificate := ⟨(212285133241444099/1000000000000000000),(78831284698636731623700035851532247/100000000000000000000000000000000000),(1302928639/1106230000),(4873664973045569017/12500000000000000000),(38989319784364552137/100000000000000000000),(704937359199490487/1000000000000000000),false⟩
theorem valid57 : certificate57.Valid := by decide +kernel
theorem bound57 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate57.a certificate57.b certificate57.c x ≤ (certificate57.bound:ℝ) :=
  rat_majority_certificate_sound certificate57 valid57 x hx0 hx1

def certificate58 : RatMajorityCertificate := ⟨0,(100075913284494947/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135036220564240059/250000000000000000),false⟩
theorem valid58 : certificate58.Valid := by decide +kernel
theorem bound58 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate58.a certificate58.b certificate58.c x ≤ (certificate58.bound:ℝ) :=
  rat_majority_certificate_sound certificate58 valid58 x hx0 hx1

def certificate59 : RatMajorityCertificate := ⟨(62751487575939947/500000000000000000),(43758044213124645338715195303052191/50000000000000000000000000000000000),1,(36605891884612940981/100000000000000000000),(18302945942306470491/50000000000000000000),(135036220564240059/250000000000000000),false⟩
theorem valid59 : certificate59.Valid := by decide +kernel
theorem bound59 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate59.a certificate59.b certificate59.c x ≤ (certificate59.bound:ℝ) :=
  rat_majority_certificate_sound certificate59 valid59 x hx0 hx1

def certificate60 : RatMajorityCertificate := ⟨0,(1000853990733387327/1000000000000000000),(866139389/734150000),(273228351036018459/625000000000000000),(43716536165762953441/100000000000000000000),(706919710432712773/1000000000000000000),false⟩
theorem valid60 : certificate60.Valid := by decide +kernel
theorem bound60 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate60.a certificate60.b certificate60.c x ≤ (certificate60.bound:ℝ) :=
  rat_majority_certificate_sound certificate60 valid60 x hx0 hx1

def certificate61 : RatMajorityCertificate := ⟨(213837807538064457/1000000000000000000),(786833567689237500252485027127063561/1000000000000000000000000000000000000),(866139389/734150000),(7799075379564627461/20000000000000000000),(19497688448911568653/50000000000000000000),(706919710432712773/1000000000000000000),false⟩
theorem valid61 : certificate61.Valid := by decide +kernel
theorem bound61 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate61.a certificate61.b certificate61.c x ≤ (certificate61.bound:ℝ) :=
  rat_majority_certificate_sound certificate61 valid61 x hx0 hx1

def certificate62 : RatMajorityCertificate := ⟨0,(1000853990733387327/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135058895415743427/250000000000000000),false⟩
theorem valid62 : certificate62.Valid := by decide +kernel
theorem bound62 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate62.a certificate62.b certificate62.c x ≤ (certificate62.bound:ℝ) :=
  rat_majority_certificate_sound certificate62 valid62 x hx0 hx1

def certificate63 : RatMajorityCertificate := ⟨(125941547026419479/1000000000000000000),(874804890792858821497178209915457367/1000000000000000000000000000000000000),1,(36595911408082062013/100000000000000000000),(18297955704041031007/50000000000000000000),(135058895415743427/250000000000000000),false⟩
theorem valid63 : certificate63.Valid := by decide +kernel
theorem bound63 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate63.a certificate63.b certificate63.c x ≤ (certificate63.bound:ℝ) :=
  rat_majority_certificate_sound certificate63 valid63 x hx0 hx1

def certificate64 : RatMajorityCertificate := ⟨0,(1000953916378391959/1000000000000000000),(1295224883/1096350000),(43753361800136254921/100000000000000000000),(21876680900068127461/50000000000000000000),(70835647780368939/100000000000000000),false⟩
theorem valid64 : certificate64.Valid := by decide +kernel
theorem bound64 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate64.a certificate64.b certificate64.c x ≤ (certificate64.bound:ℝ) :=
  rat_majority_certificate_sound certificate64 valid64 x hx0 hx1

def certificate65 : RatMajorityCertificate := ⟨(53316267928555369/250000000000000000),(196871351904830837858570057884122129/250000000000000000000000000000000000),(1295224883/1096350000),(39049552094190672307/100000000000000000000),(9762388023547668077/25000000000000000000),(70835647780368939/100000000000000000),false⟩
theorem valid65 : certificate65.Valid := by decide +kernel
theorem bound65 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate65.a certificate65.b certificate65.c x ≤ (certificate65.bound:ℝ) :=
  rat_majority_certificate_sound certificate65 valid65 x hx0 hx1

def certificate66 : RatMajorityCertificate := ⟨0,(1000953916378391959/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135081890931862863/250000000000000000),false⟩
theorem valid66 : certificate66.Valid := by decide +kernel
theorem bound66 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate66.a certificate66.b certificate66.c x ≤ (certificate66.bound:ℝ) :=
  rat_majority_certificate_sound certificate66 valid66 x hx0 hx1

def certificate67 : RatMajorityCertificate := ⟨(126370318881676237/1000000000000000000),(874463050779791876409613747477821717/1000000000000000000000000000000000000),1,(4573270802000572781/12500000000000000000),(36586166416004582249/100000000000000000000),(135081890931862863/250000000000000000),false⟩
theorem valid67 : certificate67.Valid := by decide +kernel
theorem bound67 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate67.a certificate67.b certificate67.c x ≤ (certificate67.bound:ℝ) :=
  rat_majority_certificate_sound certificate67 valid67 x hx0 hx1

def certificate68 : RatMajorityCertificate := ⟨0,(250264701200693601/250000000000000000),(2583171993/2183200000),(10948645165858557537/25000000000000000000),(43794580663434230149/100000000000000000000),(355045165899116331/500000000000000000),false⟩
theorem valid68 : certificate68.Valid := by decide +kernel
theorem bound68 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate68.a certificate68.b certificate68.c x ≤ (certificate68.bound:ℝ) :=
  rat_majority_certificate_sound certificate68 valid68 x hx0 hx1

def certificate69 : RatMajorityCertificate := ⟨(3340947346667793/15625000000000000),(3074264766819772200395952272107407/3906250000000000000000000000000000),(2583171993/2183200000),(7815633720875087833/20000000000000000000),(19539084302187719583/50000000000000000000),(355045165899116331/500000000000000000),false⟩
theorem valid69 : certificate69.Valid := by decide +kernel
theorem bound69 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate69.a certificate69.b certificate69.c x ≤ (certificate69.bound:ℝ) :=
  rat_majority_certificate_sound certificate69 valid69 x hx0 hx1

def certificate70 : RatMajorityCertificate := ⟨0,(250264701200693601/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540386929123939477/1000000000000000000),false⟩
theorem valid70 : certificate70.Valid := by decide +kernel
theorem bound70 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate70.a certificate70.b certificate70.c x ≤ (certificate70.bound:ℝ) :=
  rat_majority_certificate_sound certificate70 valid70 x hx0 hx1

def certificate71 : RatMajorityCertificate := ⟨(126474129655153707/1000000000000000000),(218612690932928776894769707333671093/250000000000000000000000000000000000),1,(36584014000688467577/100000000000000000000),(18292007000344233789/50000000000000000000),(540386929123939477/1000000000000000000),false⟩
theorem valid71 : certificate71.Valid := by decide +kernel
theorem bound71 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate71.a certificate71.b certificate71.c x ≤ (certificate71.bound:ℝ) :=
  rat_majority_certificate_sound certificate71 valid71 x hx0 hx1

def certificate72 : RatMajorityCertificate := ⟨0,(100116855321462273/100000000000000000),(644020801/543482500),(547940160013217037/1250000000000000000),(43835212801057362961/100000000000000000000),(355895548683991427/500000000000000000),false⟩
theorem valid72 : certificate72.Valid := by decide +kernel
theorem bound72 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate72.a certificate72.b certificate72.c x ≤ (certificate72.bound:ℝ) :=
  rat_majority_certificate_sound certificate72 valid72 x hx0 hx1

def certificate73 : RatMajorityCertificate := ⟨(13388795525741923/62500000000000000),(4916859353012046547650606421029021/6250000000000000000000000000000000),(644020801/543482500),(9777589714680680637/25000000000000000000),(39110358858722722549/100000000000000000000),(355895548683991427/500000000000000000),false⟩
theorem valid73 : certificate73.Valid := by decide +kernel
theorem bound73 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate73.a certificate73.b certificate73.c x ≤ (certificate73.bound:ℝ) :=
  rat_majority_certificate_sound certificate73 valid73 x hx0 hx1

def certificate74 : RatMajorityCertificate := ⟨0,(100116855321462273/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270239752158407211/500000000000000000),false⟩
theorem valid74 : certificate74.Valid := by decide +kernel
theorem bound74 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate74.a certificate74.b certificate74.c x ≤ (certificate74.bound:ℝ) :=
  rat_majority_certificate_sound certificate74 valid74 x hx0 hx1

def certificate75 : RatMajorityCertificate := ⟨(63433281524305277/500000000000000000),(43707686991796679244204085909685379/50000000000000000000000000000000000),1,(36575136400191212197/100000000000000000000),(18287568200095606099/50000000000000000000),(270239752158407211/500000000000000000),false⟩
theorem valid75 : certificate75.Valid := by decide +kernel
theorem bound75 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate75.a certificate75.b certificate75.c x ≤ (certificate75.bound:ℝ) :=
  rat_majority_certificate_sound certificate75 valid75 x hx0 hx1

def certificate76 : RatMajorityCertificate := ⟨0,(500642455880708803/500000000000000000),(512869787/432350000),(8772719510842413113/20000000000000000000),(21931798777106032783/50000000000000000000),(17825734327130617/25000000000000000),false⟩
theorem valid76 : certificate76.Valid := by decide +kernel
theorem bound76 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate76.a certificate76.b certificate76.c x ≤ (certificate76.bound:ℝ) :=
  rat_majority_certificate_sound certificate76 valid76 x hx0 hx1

def certificate77 : RatMajorityCertificate := ⟨(214754216469374157/1000000000000000000),(393127377536743963800019165029395929/500000000000000000000000000000000000),(512869787/432350000),(39126231991905160397/100000000000000000000),(19563115995952580199/50000000000000000000),(17825734327130617/25000000000000000),false⟩
theorem valid77 : certificate77.Valid := by decide +kernel
theorem bound77 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate77.a certificate77.b certificate77.c x ≤ (certificate77.bound:ℝ) :=
  rat_majority_certificate_sound certificate77 valid77 x hx0 hx1

def certificate78 : RatMajorityCertificate := ⟨0,(500642455880708803/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540579536149986187/1000000000000000000),false⟩
theorem valid78 : certificate78.Valid := by decide +kernel
theorem bound78 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate78.a certificate78.b certificate78.c x ≤ (certificate78.bound:ℝ) :=
  rat_majority_certificate_sound certificate78 valid78 x hx0 hx1

def certificate79 : RatMajorityCertificate := ⟨(127300205841610377/1000000000000000000),(436910568194045230796826182279951269/500000000000000000000000000000000000),1,(18282654234005447249/50000000000000000000),(36565308468010894499/100000000000000000000),(540579536149986187/1000000000000000000),false⟩
theorem valid79 : certificate79.Valid := by decide +kernel
theorem bound79 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate79.a certificate79.b certificate79.c x ≤ (certificate79.bound:ℝ) :=
  rat_majority_certificate_sound certificate79 valid79 x hx0 hx1

end Cycle12.MajorityCertificates.Batch001
