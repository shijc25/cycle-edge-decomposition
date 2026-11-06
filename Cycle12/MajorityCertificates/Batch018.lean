import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch018

def certificate720 : RatMajorityCertificate := ⟨0,(200083062065142663/200000000000000000),(2656717367/2263640000),(871516232540514377/2000000000000000000),(43575811627025718851/100000000000000000000),(700156289567224529/1000000000000000000),false⟩
theorem valid720 : certificate720.Valid := by decide +kernel
theorem bound720 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate720.a certificate720.b certificate720.c x ≤ (certificate720.bound:ℝ) :=
  rat_majority_certificate_sound certificate720 valid720 x hx0 hx1

def certificate721 : RatMajorityCertificate := ⟨(159319750196833/781250000000000),(124437708771556743329787524213721/156250000000000000000000000000000),(2656717367/2263640000),(9777422448268837737/25000000000000000000),(39109689793075350949/100000000000000000000),(700156289567224529/1000000000000000000),false⟩
theorem valid721 : certificate721.Valid := by decide +kernel
theorem bound721 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate721.a certificate721.b certificate721.c x ≤ (certificate721.bound:ℝ) :=
  rat_majority_certificate_sound certificate721 valid721 x hx0 hx1

def certificate722 : RatMajorityCertificate := ⟨0,(200083062065142663/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(2163887162281563/4000000000000000),false⟩
theorem valid722 : certificate722.Valid := by decide +kernel
theorem bound722 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate722.a certificate722.b certificate722.c x ≤ (certificate722.bound:ℝ) :=
  rat_majority_certificate_sound certificate722 valid722 x hx0 hx1

def certificate723 : RatMajorityCertificate := ⟨(6728434342238749/50000000000000000),(8657907357157740184156476508351413/10000000000000000000000000000000000),1,(36391963545653892637/100000000000000000000),(18195981772826946319/50000000000000000000),(2163887162281563/4000000000000000),false⟩
theorem valid723 : certificate723.Valid := by decide +kernel
theorem bound723 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate723.a certificate723.b certificate723.c x ≤ (certificate723.bound:ℝ) :=
  rat_majority_certificate_sound certificate723 valid723 x hx0 hx1

def certificate724 : RatMajorityCertificate := ⟨0,(250115827766672933/250000000000000000),(2651372087/2256420000),(21803838413116451573/50000000000000000000),(43607676826232903147/100000000000000000000),(701417651176898647/1000000000000000000),false⟩
theorem valid724 : certificate724.Valid := by decide +kernel
theorem bound724 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate724.a certificate724.b certificate724.c x ≤ (certificate724.bound:ℝ) :=
  rat_majority_certificate_sound certificate724 valid724 x hx0 hx1

def certificate725 : RatMajorityCertificate := ⟨(101938598389954021/500000000000000000),(99561456965658683832074505984786407/125000000000000000000000000000000000),(2651372087/2256420000),(19572204597004466471/50000000000000000000),(39144409194008932943/100000000000000000000),(701417651176898647/1000000000000000000),false⟩
theorem valid725 : certificate725.Valid := by decide +kernel
theorem bound725 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate725.a certificate725.b certificate725.c x ≤ (certificate725.bound:ℝ) :=
  rat_majority_certificate_sound certificate725 valid725 x hx0 hx1

def certificate726 : RatMajorityCertificate := ⟨0,(250115827766672933/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540869008393896019/1000000000000000000),false⟩
theorem valid726 : certificate726.Valid := by decide +kernel
theorem bound726 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate726.a certificate726.b certificate726.c x ≤ (certificate726.bound:ℝ) :=
  rat_majority_certificate_sound certificate726 valid726 x hx0 hx1

def certificate727 : RatMajorityCertificate := ⟨(66716366358750857/500000000000000000),(108371094685932884939120211247546419/125000000000000000000000000000000000),1,(18209490568132786447/50000000000000000000),(7283796227253114579/20000000000000000000),(540869008393896019/1000000000000000000),false⟩
theorem valid727 : certificate727.Valid := by decide +kernel
theorem bound727 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate727.a certificate727.b certificate727.c x ≤ (certificate727.bound:ℝ) :=
  rat_majority_certificate_sound certificate727 valid727 x hx0 hx1

def certificate728 : RatMajorityCertificate := ⟨0,(1000513609320040983/1000000000000000000),(165384781/140585625),(43638986940211868573/100000000000000000000),(21819493470105934287/50000000000000000000),(702647177541326503/1000000000000000000),false⟩
theorem valid728 : certificate728.Valid := by decide +kernel
theorem bound728 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate728.a certificate728.b certificate728.c x ≤ (certificate728.bound:ℝ) :=
  rat_majority_certificate_sound certificate728 valid728 x hx0 hx1

def certificate729 : RatMajorityCertificate := ⟨(203691846584134489/1000000000000000000),(796717144705084524459367604936237313/1000000000000000000000000000000000000),(165384781/140585625),(19591031885733852857/50000000000000000000),(7836412754293541143/20000000000000000000),(702647177541326503/1000000000000000000),false⟩
theorem valid729 : certificate729.Valid := by decide +kernel
theorem bound729 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate729.a certificate729.b certificate729.c x ≤ (certificate729.bound:ℝ) :=
  rat_majority_certificate_sound certificate729 valid729 x hx0 hx1

def certificate730 : RatMajorityCertificate := ⟨0,(1000513609320040983/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270448197820992961/500000000000000000),false⟩
theorem valid730 : certificate730.Valid := by decide +kernel
theorem bound730 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate730.a certificate730.b certificate730.c x ≤ (certificate730.bound:ℝ) :=
  rat_majority_certificate_sound certificate730 valid730 x hx0 hx1

def certificate731 : RatMajorityCertificate := ⟨(66736726022444599/500000000000000000),(433485802033101743353527359472999183/500000000000000000000000000000000000),1,(4552269480699410203/12500000000000000000),(291345246764762253/800000000000000000),(270448197820992961/500000000000000000),false⟩
theorem valid731 : certificate731.Valid := by decide +kernel
theorem bound731 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate731.a certificate731.b certificate731.c x ≤ (certificate731.bound:ℝ) :=
  rat_majority_certificate_sound certificate731 valid731 x hx0 hx1

def certificate732 : RatMajorityCertificate := ⟨0,(1000566148272280889/1000000000000000000),(165072021/140155000),(43670687416480081737/100000000000000000000),(21835343708240040869/50000000000000000000),(351953748669375053/500000000000000000),false⟩
theorem valid732 : certificate732.Valid := by decide +kernel
theorem bound732 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate732.a certificate732.b certificate732.c x ≤ (certificate732.bound:ℝ) :=
  rat_majority_certificate_sound certificate732 valid732 x hx0 hx1

def certificate733 : RatMajorityCertificate := ⟨(20362334361585649/100000000000000000),(79682752365224022405902160040638039/100000000000000000000000000000000000),(165072021/140155000),(39217067815683127687/100000000000000000000),(4902133476960390961/12500000000000000000),(351953748669375053/500000000000000000),false⟩
theorem valid733 : certificate733.Valid := by decide +kernel
theorem bound733 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate733.a certificate733.b certificate733.c x ≤ (certificate733.bound:ℝ) :=
  rat_majority_certificate_sound certificate733 valid733 x hx0 hx1

def certificate734 : RatMajorityCertificate := ⟨0,(1000566148272280889/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540917796337272989/1000000000000000000),false⟩
theorem valid734 : certificate734.Valid := by decide +kernel
theorem bound734 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate734.a certificate734.b certificate734.c x ≤ (certificate734.bound:ℝ) :=
  rat_majority_certificate_sound certificate734 valid734 x hx0 hx1

def certificate735 : RatMajorityCertificate := ⟨(133450199261574153/1000000000000000000),(867040396410959255424258802081737983/1000000000000000000000000000000000000),1,(36418849185240286399/100000000000000000000),(22761780740775179/62500000000000000),(540917796337272989/1000000000000000000),false⟩
theorem valid735 : certificate735.Valid := by decide +kernel
theorem bound735 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate735.a certificate735.b certificate735.c x ≤ (certificate735.bound:ℝ) :=
  rat_majority_certificate_sound certificate735 valid735 x hx0 hx1

def certificate736 : RatMajorityCertificate := ⟨0,(1000620864890410821/1000000000000000000),(2637198737/2235760000),(874224752586461223/2000000000000000000),(43711237629323061151/100000000000000000000),(352879258801965617/500000000000000000),false⟩
theorem valid736 : certificate736.Valid := by decide +kernel
theorem bound736 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate736.a certificate736.b certificate736.c x ≤ (certificate736.bound:ℝ) :=
  rat_majority_certificate_sound certificate736 valid736 x hx0 hx1

def certificate737 : RatMajorityCertificate := ⟨(205896882426059029/1000000000000000000),(794596148319008407164691252193647191/1000000000000000000000000000000000000),(2637198737/2235760000),(39199722697282552821/100000000000000000000),(19599861348641276411/50000000000000000000),(352879258801965617/500000000000000000),false⟩
theorem valid737 : certificate737.Valid := by decide +kernel
theorem bound737 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate737.a certificate737.b certificate737.c x ≤ (certificate737.bound:ℝ) :=
  rat_majority_certificate_sound certificate737 valid737 x hx0 hx1

def certificate738 : RatMajorityCertificate := ⟨0,(1000620864890410821/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(108187704300413353/200000000000000000),false⟩
theorem valid738 : certificate738.Valid := by decide +kernel
theorem bound738 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate738.a certificate738.b certificate738.c x ≤ (certificate738.bound:ℝ) :=
  rat_majority_certificate_sound certificate738 valid738 x hx0 hx1

def certificate739 : RatMajorityCertificate := ⟨(66705846931639547/500000000000000000),(433563170195220890112389892079661913/500000000000000000000000000000000000),1,(1820995447032346469/5000000000000000000),(36419908940646929381/100000000000000000000),(108187704300413353/200000000000000000),false⟩
theorem valid739 : certificate739.Valid := by decide +kernel
theorem bound739 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate739.a certificate739.b certificate739.c x ≤ (certificate739.bound:ℝ) :=
  rat_majority_certificate_sound certificate739 valid739 x hx0 hx1

def certificate740 : RatMajorityCertificate := ⟨0,(500338849790443061/500000000000000000),(657902569/557300000),(2733329824091570249/6250000000000000000),(8746655437093024797/20000000000000000000),(706390327959591827/1000000000000000000),false⟩
theorem valid740 : certificate740.Valid := by decide +kernel
theorem bound740 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate740.a certificate740.b certificate740.c x ≤ (certificate740.bound:ℝ) :=
  rat_majority_certificate_sound certificate740 valid740 x hx0 hx1

def certificate741 : RatMajorityCertificate := ⟨(203325049802571093/1000000000000000000),(398607428238640088343786302578964327/500000000000000000000000000000000000),(657902569/557300000),(39290496939802639761/100000000000000000000),(19645248469901319881/50000000000000000000),(706390327959591827/1000000000000000000),false⟩
theorem valid741 : certificate741.Valid := by decide +kernel
theorem bound741 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate741.a certificate741.b certificate741.c x ≤ (certificate741.bound:ℝ) :=
  rat_majority_certificate_sound certificate741 valid741 x hx0 hx1

def certificate742 : RatMajorityCertificate := ⟨0,(500338849790443061/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(10816849762381749/20000000000000000),false⟩
theorem valid742 : certificate742.Valid := by decide +kernel
theorem bound742 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate742.a certificate742.b certificate742.c x ≤ (certificate742.bound:ℝ) :=
  rat_majority_certificate_sound certificate742 valid742 x hx0 hx1

def certificate743 : RatMajorityCertificate := ⟨(26459173788949337/200000000000000000),(86829217378120261684838805087799443/100000000000000000000000000000000000),1,(7289282611181944017/20000000000000000000),(18223206527954860043/50000000000000000000),(10816849762381749/20000000000000000),false⟩
theorem valid743 : certificate743.Valid := by decide +kernel
theorem bound743 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate743.a certificate743.b certificate743.c x ≤ (certificate743.bound:ℝ) :=
  rat_majority_certificate_sound certificate743 valid743 x hx0 hx1

def certificate744 : RatMajorityCertificate := ⟨0,(1000736592209693337/1000000000000000000),(54731267/46308125),(43764684808388218967/100000000000000000000),(5470585601048527371/12500000000000000000),(70764672354015013/100000000000000000),false⟩
theorem valid744 : certificate744.Valid := by decide +kernel
theorem bound744 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate744.a certificate744.b certificate744.c x ≤ (certificate744.bound:ℝ) :=
  rat_majority_certificate_sound certificate744 valid744 x hx0 hx1

def certificate745 : RatMajorityCertificate := ⟨(25403574157866251/125000000000000000),(99669787793522364870553469028130413/125000000000000000000000000000000000),(54731267/46308125),(39325963127107787193/100000000000000000000),(19662981563553893597/50000000000000000000),(70764672354015013/100000000000000000),false⟩
theorem valid745 : certificate745.Valid := by decide +kernel
theorem bound745 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate745.a certificate745.b certificate745.c x ≤ (certificate745.bound:ℝ) :=
  rat_majority_certificate_sound certificate745 valid745 x hx0 hx1

def certificate746 : RatMajorityCertificate := ⟨0,(1000736592209693337/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(67607787251007919/125000000000000000),false⟩
theorem valid746 : certificate746.Valid := by decide +kernel
theorem bound746 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate746.a certificate746.b certificate746.c x ≤ (certificate746.bound:ℝ) :=
  rat_majority_certificate_sound certificate746 valid746 x hx0 hx1

def certificate747 : RatMajorityCertificate := ⟨(3305776052815777/25000000000000000),(21710203743539061534298387474622151/25000000000000000000000000000000000),1,(455601268949060997/1250000000000000000),(36448101515924879761/100000000000000000000),(67607787251007919/125000000000000000),false⟩
theorem valid747 : certificate747.Valid := by decide +kernel
theorem bound747 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate747.a certificate747.b certificate747.c x ≤ (certificate747.bound:ℝ) :=
  rat_majority_certificate_sound certificate747 valid747 x hx0 hx1

def certificate748 : RatMajorityCertificate := ⟨0,(500398741114046147/500000000000000000),(327685583/277065000),(43783148418558741897/100000000000000000000),(21891574209279370949/50000000000000000000),(354274883702549447/500000000000000000),false⟩
theorem valid748 : certificate748.Valid := by decide +kernel
theorem bound748 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate748.a certificate748.b certificate748.c x ≤ (certificate748.bound:ℝ) :=
  rat_majority_certificate_sound certificate748 valid748 x hx0 hx1

def certificate749 : RatMajorityCertificate := ⟨(51159246270905249/250000000000000000),(99499662848207090299487629149474397/125000000000000000000000000000000000),(327685583/277065000),(7861700118289095341/20000000000000000000),(19654250295722738353/50000000000000000000),(354274883702549447/500000000000000000),false⟩
theorem valid749 : certificate749.Valid := by decide +kernel
theorem bound749 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate749.a certificate749.b certificate749.c x ≤ (certificate749.bound:ℝ) :=
  rat_majority_certificate_sound certificate749 valid749 x hx0 hx1

def certificate750 : RatMajorityCertificate := ⟨0,(500398741114046147/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(108172070574812269/200000000000000000),false⟩
theorem valid750 : certificate750.Valid := by decide +kernel
theorem bound750 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate750.a certificate750.b certificate750.c x ≤ (certificate750.bound:ℝ) :=
  rat_majority_certificate_sound certificate750 valid750 x hx0 hx1

def certificate751 : RatMajorityCertificate := ⟨(26391642788865519/200000000000000000),(86873403395329329701017974056894707/100000000000000000000000000000000000),1,(9113674789679745011/25000000000000000000),(7290939831743796009/20000000000000000000),(108172070574812269/200000000000000000),false⟩
theorem valid751 : certificate751.Valid := by decide +kernel
theorem bound751 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate751.a certificate751.b certificate751.c x ≤ (certificate751.bound:ℝ) :=
  rat_majority_certificate_sound certificate751 valid751 x hx0 hx1

def certificate752 : RatMajorityCertificate := ⟨0,(500430148555839663/500000000000000000),(2616471959/2210410000),(21902984816241433367/50000000000000000000),(8761193926496573347/20000000000000000000),(35462488002484803/50000000000000000),false⟩
theorem valid752 : certificate752.Valid := by decide +kernel
theorem bound752 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate752.a certificate752.b certificate752.c x ≤ (certificate752.bound:ℝ) :=
  rat_majority_certificate_sound certificate752 valid752 x hx0 hx1

def certificate753 : RatMajorityCertificate := ⟨(202336098130386937/1000000000000000000),(399175064910241176222294118878317769/500000000000000000000000000000000000),(2616471959/2210410000),(39392812088628320761/100000000000000000000),(19696406044314160381/50000000000000000000),(35462488002484803/50000000000000000),false⟩
theorem valid753 : certificate753.Valid := by decide +kernel
theorem bound753 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate753.a certificate753.b certificate753.c x ≤ (certificate753.bound:ℝ) :=
  rat_majority_certificate_sound certificate753 valid753 x hx0 hx1

def certificate754 : RatMajorityCertificate := ⟨0,(500430148555839663/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135200262102132739/250000000000000000),false⟩
theorem valid754 : certificate754.Valid := by decide +kernel
theorem bound754 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate754.a certificate754.b certificate754.c x ≤ (certificate754.bound:ℝ) :=
  rat_majority_certificate_sound certificate754 valid754 x hx0 hx1

def certificate755 : RatMajorityCertificate := ⟨(5245988122725837/40000000000000000),(17391955326655725476428192120527069/20000000000000000000000000000000000),1,(7294782544678923049/20000000000000000000),(18236956361697307623/50000000000000000000),(135200262102132739/250000000000000000),false⟩
theorem valid755 : certificate755.Valid := by decide +kernel
theorem bound755 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate755.a certificate755.b certificate755.c x ≤ (certificate755.bound:ℝ) :=
  rat_majority_certificate_sound certificate755 valid755 x hx0 hx1

def certificate756 : RatMajorityCertificate := ⟨0,(1000924981506722401/1000000000000000000),(2610387209/2204430000),(43816235860666815089/100000000000000000000),(4381623586066681509/10000000000000000000),(22175746524567637/31250000000000000),false⟩
theorem valid756 : certificate756.Valid := by decide +kernel
theorem bound756 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate756.a certificate756.b certificate756.c x ≤ (certificate756.bound:ℝ) :=
  rat_majority_certificate_sound certificate756 valid756 x hx0 hx1

def certificate757 : RatMajorityCertificate := ⟨(5041949831034121/25000000000000000),(19976510996282410328620144893955479/25000000000000000000000000000000000),(2610387209/2204430000),(1576838347361514541/4000000000000000000),(19710479342018931763/50000000000000000000),(22175746524567637/31250000000000000),false⟩
theorem valid757 : certificate757.Valid := by decide +kernel
theorem bound757 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate757.a certificate757.b certificate757.c x ≤ (certificate757.bound:ℝ) :=
  rat_majority_certificate_sound certificate757 valid757 x hx0 hx1

def certificate758 : RatMajorityCertificate := ⟨0,(1000924981506722401/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540831520732436853/1000000000000000000),false⟩
theorem valid758 : certificate758.Valid := by decide +kernel
theorem bound758 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate758.a certificate758.b certificate758.c x ≤ (certificate758.bound:ℝ) :=
  rat_majority_certificate_sound certificate758 valid758 x hx0 hx1

def certificate759 : RatMajorityCertificate := ⟨(16394754324271677/125000000000000000),(108705703519511414709936786254263523/125000000000000000000000000000000000),1,(9118472489935233101/25000000000000000000),(7294777991948186481/20000000000000000000),(540831520732436853/1000000000000000000),false⟩
theorem valid759 : certificate759.Valid := by decide +kernel
theorem bound759 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate759.a certificate759.b certificate759.c x ≤ (certificate759.bound:ℝ) :=
  rat_majority_certificate_sound certificate759 valid759 x hx0 hx1

end Cycle12.MajorityCertificates.Batch018
