import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch017

def certificate680 : RatMajorityCertificate := ⟨0,(1000073440193184911/1000000000000000000),(2717847551/2347080000),(21606255344935168881/50000000000000000000),(43212510689870337763/100000000000000000000),(685877942554350021/1000000000000000000),false⟩
theorem valid680 : certificate680.Valid := by decide +kernel
theorem bound680 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate680.a certificate680.b certificate680.c x ≤ (certificate680.bound:ℝ) :=
  rat_majority_certificate_sound certificate680 valid680 x hx0 hx1

def certificate681 : RatMajorityCertificate := ⟨(40590735604130361/200000000000000000),(159420971443042336221179704977817129/200000000000000000000000000000000000),(2717847551/2347080000),(19378176932960587171/50000000000000000000),(38756353865921174343/100000000000000000000),(685877942554350021/1000000000000000000),false⟩
theorem valid681 : certificate681.Valid := by decide +kernel
theorem bound681 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate681.a certificate681.b certificate681.c x ≤ (certificate681.bound:ℝ) :=
  rat_majority_certificate_sound certificate681 valid681 x hx0 hx1

def certificate682 : RatMajorityCertificate := ⟨0,(1000073440193184911/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540933025443764317/1000000000000000000),false⟩
theorem valid682 : certificate682.Valid := by decide +kernel
theorem bound682 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate682.a certificate682.b certificate682.c x ≤ (certificate682.bound:ℝ) :=
  rat_majority_certificate_sound certificate682 valid682 x hx0 hx1

def certificate683 : RatMajorityCertificate := ⟨(6781435213167403/50000000000000000),(43221738766579716577815669223343867/50000000000000000000000000000000000),1,(18182936657955094609/50000000000000000000),(36365873315910189219/100000000000000000000),(540933025443764317/1000000000000000000),false⟩
theorem valid683 : certificate683.Valid := by decide +kernel
theorem bound683 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate683.a certificate683.b certificate683.c x ≤ (certificate683.bound:ℝ) :=
  rat_majority_certificate_sound certificate683 valid683 x hx0 hx1

def certificate684 : RatMajorityCertificate := ⟨0,(1000095581909658037/1000000000000000000),(2710212041/2337640000),(4324540262830116391/10000000000000000000),(43245402628301163911/100000000000000000000),(343573639948479363/500000000000000000),false⟩
theorem valid684 : certificate684.Valid := by decide +kernel
theorem bound684 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate684.a certificate684.b certificate684.c x ≤ (certificate684.bound:ℝ) :=
  rat_majority_certificate_sound certificate684 valid684 x hx0 hx1

def certificate685 : RatMajorityCertificate := ⟨(40594797873687707/200000000000000000),(159420438379940951309086699499348841/200000000000000000000000000000000000),(2710212041/2337640000),(303047392131663099/781250000000000000),(38790066192852876673/100000000000000000000),(343573639948479363/500000000000000000),false⟩
theorem valid685 : certificate685.Valid := by decide +kernel
theorem bound685 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate685.a certificate685.b certificate685.c x ≤ (certificate685.bound:ℝ) :=
  rat_majority_certificate_sound certificate685 valid685 x hx0 hx1

def certificate686 : RatMajorityCertificate := ⟨0,(1000095581909658037/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(10819172669111307/20000000000000000),false⟩
theorem valid686 : certificate686.Valid := by decide +kernel
theorem bound686 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate686.a certificate686.b certificate686.c x ≤ (certificate686.bound:ℝ) :=
  rat_majority_certificate_sound certificate686 valid686 x hx0 hx1

def certificate687 : RatMajorityCertificate := ⟨(135769506220830663/1000000000000000000),(864313098580149458271099687586011469/1000000000000000000000000000000000000),1,(36362591119664586131/100000000000000000000),(9090647779916146533/25000000000000000000),(10819172669111307/20000000000000000),false⟩
theorem valid687 : certificate687.Valid := by decide +kernel
theorem bound687 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate687.a certificate687.b certificate687.c x ≤ (certificate687.bound:ℝ) :=
  rat_majority_certificate_sound certificate687 valid687 x hx0 hx1

def certificate688 : RatMajorityCertificate := ⟨0,(500060261379084793/500000000000000000),(2704848773/2328490000),(43297863138524667873/100000000000000000000),(21648931569262333937/50000000000000000000),(137846464708761689/200000000000000000),false⟩
theorem valid688 : certificate688.Valid := by decide +kernel
theorem bound688 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate688.a certificate688.b certificate688.c x ≤ (certificate688.bound:ℝ) :=
  rat_majority_certificate_sound certificate688 valid688 x hx0 hx1

def certificate689 : RatMajorityCertificate := ⟨(50896879561876173/250000000000000000),(99563558447679600476879087266662811/125000000000000000000000000000000000),(2704848773/2328490000),(9707127309229997901/25000000000000000000),(7765701847383998321/20000000000000000000),(137846464708761689/200000000000000000),false⟩
theorem valid689 : certificate689.Valid := by decide +kernel
theorem bound689 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate689.a certificate689.b certificate689.c x ≤ (certificate689.bound:ℝ) :=
  rat_majority_certificate_sound certificate689 valid689 x hx0 hx1

def certificate690 : RatMajorityCertificate := ⟨0,(500060261379084793/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270504230096160467/500000000000000000),false⟩
theorem valid690 : certificate690.Valid := by decide +kernel
theorem bound690 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate690.a certificate690.b certificate690.c x ≤ (certificate690.bound:ℝ) :=
  rat_majority_certificate_sound certificate690 valid690 x hx0 hx1

def certificate691 : RatMajorityCertificate := ⟨(68059015442104227/500000000000000000),(215996521638360588576522868623279989/250000000000000000000000000000000000),1,(36354380227557516611/100000000000000000000),(9088595056889379153/25000000000000000000),(270504230096160467/500000000000000000),false⟩
theorem valid691 : certificate691.Valid := by decide +kernel
theorem bound691 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate691.a certificate691.b certificate691.c x ≤ (certificate691.bound:ℝ) :=
  rat_majority_certificate_sound certificate691 valid691 x hx0 hx1

def certificate692 : RatMajorityCertificate := ⟨0,(20002964403968943/20000000000000000),(179853121/154640000),(21665343448648496817/50000000000000000000),(8666137379459398727/20000000000000000000),(172627738406148649/250000000000000000),false⟩
theorem valid692 : certificate692.Valid := by decide +kernel
theorem bound692 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate692.a certificate692.b certificate692.c x ≤ (certificate692.bound:ℝ) :=
  rat_majority_certificate_sound certificate692 valid692 x hx0 hx1

def certificate693 : RatMajorityCertificate := ⟨(20363781700677337/100000000000000000),(1592960439908051383267765788055209/2000000000000000000000000000000000),(179853121/154640000),(19430701118022235111/50000000000000000000),(38861402236044470223/100000000000000000000),(172627738406148649/250000000000000000),false⟩
theorem valid693 : certificate693.Valid := by decide +kernel
theorem bound693 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate693.a certificate693.b certificate693.c x ≤ (certificate693.bound:ℝ) :=
  rat_majority_certificate_sound certificate693 valid693 x hx0 hx1

def certificate694 : RatMajorityCertificate := ⟨0,(20002964403968943/20000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(4225741961460787/7812500000000000),false⟩
theorem valid694 : certificate694.Valid := by decide +kernel
theorem bound694 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate694.a certificate694.b certificate694.c x ≤ (certificate694.bound:ℝ) :=
  rat_majority_certificate_sound certificate694 valid694 x hx0 hx1

def certificate695 : RatMajorityCertificate := ⟨(134975183759938933/1000000000000000000),(17303060607799717566269291491442181/20000000000000000000000000000000000),1,(1136924676710537647/3125000000000000000),(7276317930947440941/20000000000000000000),(4225741961460787/7812500000000000),false⟩
theorem valid695 : certificate695.Valid := by decide +kernel
theorem bound695 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate695.a certificate695.b certificate695.c x ≤ (certificate695.bound:ℝ) :=
  rat_majority_certificate_sound certificate695 valid695 x hx0 hx1

def certificate696 : RatMajorityCertificate := ⟨0,(200035725817865169/200000000000000000),(1345496651/1155480000),(43363290026509424729/100000000000000000000),(4336329002650942473/10000000000000000000),(345890917910679707/500000000000000000),false⟩
theorem valid696 : certificate696.Valid := by decide +kernel
theorem bound696 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate696.a certificate696.b certificate696.c x ≤ (certificate696.bound:ℝ) :=
  rat_majority_certificate_sound certificate696 valid696 x hx0 hx1

def certificate697 : RatMajorityCertificate := ⟨(12728723075055563/62500000000000000),(9956033504563224853577307282614853/12500000000000000000000000000000000),(1345496651/1155480000),(19447417222035128057/50000000000000000000),(7778966888814051223/20000000000000000000),(345890917910679707/500000000000000000),false⟩
theorem valid697 : certificate697.Valid := by decide +kernel
theorem bound697 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate697.a certificate697.b certificate697.c x ≤ (certificate697.bound:ℝ) :=
  rat_majority_certificate_sound certificate697 valid697 x hx0 hx1

def certificate698 : RatMajorityCertificate := ⟨0,(200035725817865169/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(6761667651999731/12500000000000000),false⟩
theorem valid698 : certificate698.Valid := by decide +kernel
theorem bound698 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate698.a certificate698.b certificate698.c x ≤ (certificate698.bound:ℝ) :=
  rat_majority_certificate_sound certificate698 valid698 x hx0 hx1

def certificate699 : RatMajorityCertificate := ⟨(135198529579225899/1000000000000000000),(172991189823976603111893136225188069/200000000000000000000000000000000000),1,(36376376006168190147/100000000000000000000),(9094094001542047537/25000000000000000000),(6761667651999731/12500000000000000),false⟩
theorem valid699 : certificate699.Valid := by decide +kernel
theorem bound699 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate699.a certificate699.b certificate699.c x ≤ (certificate699.bound:ℝ) :=
  rat_majority_certificate_sound certificate699 valid699 x hx0 hx1

def certificate700 : RatMajorityCertificate := ⟨0,(200042340488878737/200000000000000000),(99496377/85280000),(43415533129569232479/100000000000000000000),(271347082059807703/625000000000000000),(173467192281189761/250000000000000000),false⟩
theorem valid700 : certificate700.Valid := by decide +kernel
theorem bound700 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate700.a certificate700.b certificate700.c x ≤ (certificate700.bound:ℝ) :=
  rat_majority_certificate_sound certificate700 valid700 x hx0 hx1

def certificate701 : RatMajorityCertificate := ⟨(204210463931084109/1000000000000000000),(159191601331784919410012485751309667/200000000000000000000000000000000000),(99496377/85280000),(1946738332262166687/5000000000000000000),(38934766645243333741/100000000000000000000),(173467192281189761/250000000000000000),false⟩
theorem valid701 : certificate701.Valid := by decide +kernel
theorem bound701 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate701.a certificate701.b certificate701.c x ≤ (certificate701.bound:ℝ) :=
  rat_majority_certificate_sound certificate701 valid701 x hx0 hx1

def certificate702 : RatMajorityCertificate := ⟨0,(200042340488878737/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(67622540466099439/125000000000000000),false⟩
theorem valid702 : certificate702.Valid := by decide +kernel
theorem bound702 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate702.a certificate702.b certificate702.c x ≤ (certificate702.bound:ℝ) :=
  rat_majority_certificate_sound certificate702 valid702 x hx0 hx1

def certificate703 : RatMajorityCertificate := ⟨(67743829116076827/500000000000000000),(86469536114380710789333354421272501/100000000000000000000000000000000000),1,(36369606539259873029/100000000000000000000),(3636960653925987303/10000000000000000000),(67622540466099439/125000000000000000),false⟩
theorem valid703 : certificate703.Valid := by decide +kernel
theorem bound703 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate703.a certificate703.b certificate703.c x ≤ (certificate703.bound:ℝ) :=
  rat_majority_certificate_sound certificate703 valid703 x hx0 hx1

def certificate704 : RatMajorityCertificate := ⟨0,(100024739372033897/100000000000000000),(89334449/76479000),(868953331288155523/2000000000000000000),(43447666564407776151/100000000000000000000),(695119763554619681/1000000000000000000),false⟩
theorem valid704 : certificate704.Valid := by decide +kernel
theorem bound704 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate704.a certificate704.b certificate704.c x ≤ (certificate704.bound:ℝ) :=
  rat_majority_certificate_sound certificate704 valid704 x hx0 hx1

def certificate705 : RatMajorityCertificate := ⟨(20413292783677837/100000000000000000),(7960639646790993729076813308359211/10000000000000000000000000000000000),(89334449/76479000),(9742590984129330359/25000000000000000000),(38970363936517321437/100000000000000000000),(695119763554619681/1000000000000000000),false⟩
theorem valid705 : certificate705.Valid := by decide +kernel
theorem bound705 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate705.a certificate705.b certificate705.c x ≤ (certificate705.bound:ℝ) :=
  rat_majority_certificate_sound certificate705 valid705 x hx0 hx1

def certificate706 : RatMajorityCertificate := ⟨0,(100024739372033897/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135250714090014519/250000000000000000),false⟩
theorem valid706 : certificate706.Valid := by decide +kernel
theorem bound706 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate706.a certificate706.b certificate706.c x ≤ (certificate706.bound:ℝ) :=
  rat_majority_certificate_sound certificate706 valid706 x hx0 hx1

def certificate707 : RatMajorityCertificate := ⟨(6777242200900139/50000000000000000),(4323345083795509054547543379988317/5000000000000000000000000000000000),1,(36368348316295723043/100000000000000000000),(9092087079073930761/25000000000000000000),(135250714090014519/250000000000000000),false⟩
theorem valid707 : certificate707.Valid := by decide +kernel
theorem bound707 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate707.a certificate707.b certificate707.c x ≤ (certificate707.bound:ℝ) :=
  rat_majority_certificate_sound certificate707 valid707 x hx0 hx1

def certificate708 : RatMajorityCertificate := ⟨0,(8002285209306379/8000000000000000),(2673920307/2286400000),(43479969483931007049/100000000000000000000),(869599389678620141/2000000000000000000),(696388439195317673/1000000000000000000),false⟩
theorem valid708 : certificate708.Valid := by decide +kernel
theorem bound708 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate708.a certificate708.b certificate708.c x ≤ (certificate708.bound:ℝ) :=
  rat_majority_certificate_sound certificate708 valid708 x hx0 hx1

def certificate709 : RatMajorityCertificate := ⟨(102063371679849341/500000000000000000),(3184402395047591561415402169753761/4000000000000000000000000000000000),(2673920307/2286400000),(39004274081878078729/100000000000000000000),(3900427408187807873/10000000000000000000),(696388439195317673/1000000000000000000),false⟩
theorem valid709 : certificate709.Valid := by decide +kernel
theorem bound709 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate709.a certificate709.b certificate709.c x ≤ (certificate709.bound:ℝ) :=
  rat_majority_certificate_sound certificate709 valid709 x hx0 hx1

def certificate710 : RatMajorityCertificate := ⟨0,(8002285209306379/8000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(108181153972638807/200000000000000000),false⟩
theorem valid710 : certificate710.Valid := by decide +kernel
theorem bound710 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate710.a certificate710.b certificate710.c x ≤ (certificate710.bound:ℝ) :=
  rat_majority_certificate_sound certificate710 valid710 x hx0 hx1

def certificate711 : RatMajorityCertificate := ⟨(134505012672367387/1000000000000000000),(6925937735820726384718373869338327/8000000000000000000000000000000000),1,(1137284831408966423/3125000000000000000),(36393114605086925537/100000000000000000000),(108181153972638807/200000000000000000),false⟩
theorem valid711 : certificate711.Valid := by decide +kernel
theorem bound711 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate711.a certificate711.b certificate711.c x ≤ (certificate711.bound:ℝ) :=
  rat_majority_certificate_sound certificate711 valid711 x hx0 hx1

def certificate712 : RatMajorityCertificate := ⟨0,(1000326425982197787/1000000000000000000),(111166757/94942500),(2719511060598076771/6250000000000000000),(43512176969569228337/100000000000000000000),(697655974021238117/1000000000000000000),false⟩
theorem valid712 : certificate712.Valid := by decide +kernel
theorem bound712 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate712.a certificate712.b certificate712.c x ≤ (certificate712.bound:ℝ) :=
  rat_majority_certificate_sound certificate712 valid712 x hx0 hx1

def certificate713 : RatMajorityCertificate := ⟨(25513758889760573/125000000000000000),(99518716004209002760384063239548049/125000000000000000000000000000000000),(111166757/94942500),(1951918817420196597/5000000000000000000),(39038376348403931941/100000000000000000000),(697655974021238117/1000000000000000000),false⟩
theorem valid713 : certificate713.Valid := by decide +kernel
theorem bound713 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate713.a certificate713.b certificate713.c x ≤ (certificate713.bound:ℝ) :=
  rat_majority_certificate_sound certificate713 valid713 x hx0 hx1

def certificate714 : RatMajorityCertificate := ⟨0,(1000326425982197787/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540928306998872201/1000000000000000000),false⟩
theorem valid714 : certificate714.Valid := by decide +kernel
theorem bound714 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate714.a certificate714.b certificate714.c x ≤ (certificate714.bound:ℝ) :=
  rat_majority_certificate_sound certificate714 valid714 x hx0 hx1

def certificate715 : RatMajorityCertificate := ⟨(67270587876952003/500000000000000000),(432870666246426133899489439348182639/500000000000000000000000000000000000),1,(36392370225186634811/100000000000000000000),(9098092556296658703/25000000000000000000),(540928306998872201/1000000000000000000),false⟩
theorem valid715 : certificate715.Valid := by decide +kernel
theorem bound715 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate715.a certificate715.b certificate715.c x ≤ (certificate715.bound:ℝ) :=
  rat_majority_certificate_sound certificate715 valid715 x hx0 hx1

def certificate716 : RatMajorityCertificate := ⟨0,(1000369663119474637/1000000000000000000),(28321723/24160000),(5442973211106708361/12500000000000000000),(43543785688853666889/100000000000000000000),(349444846088226261/500000000000000000),false⟩
theorem valid716 : certificate716.Valid := by decide +kernel
theorem bound716 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate716.a certificate716.b certificate716.c x ≤ (certificate716.bound:ℝ) :=
  rat_majority_certificate_sound certificate716 valid716 x hx0 hx1

def certificate717 : RatMajorityCertificate := ⟨(407913354499063/2000000000000000),(1592675181216786786918003131234869/2000000000000000000000000000000000),(28321723/24160000),(39075466009637103927/100000000000000000000),(4884433251204637991/12500000000000000000),(349444846088226261/500000000000000000),false⟩
theorem valid717 : certificate717.Valid := by decide +kernel
theorem bound717 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate717.a certificate717.b certificate717.c x ≤ (certificate717.bound:ℝ) :=
  rat_majority_certificate_sound certificate717 valid717 x hx0 hx1

def certificate718 : RatMajorityCertificate := ⟨0,(1000369663119474637/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540953988497993133/1000000000000000000),false⟩
theorem valid718 : certificate718.Valid := by decide +kernel
theorem bound718 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate718.a certificate718.b certificate718.c x ≤ (certificate718.bound:ℝ) :=
  rat_majority_certificate_sound certificate718 valid718 x hx0 hx1

def certificate719 : RatMajorityCertificate := ⟨(134595758613555007/1000000000000000000),(865724149417922488013353251259142541/1000000000000000000000000000000000000),1,(36391196188624387617/100000000000000000000),(18195598094312193809/50000000000000000000),(540953988497993133/1000000000000000000),false⟩
theorem valid719 : certificate719.Valid := by decide +kernel
theorem bound719 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate719.a certificate719.b certificate719.c x ≤ (certificate719.bound:ℝ) :=
  rat_majority_certificate_sound certificate719 valid719 x hx0 hx1

end Cycle12.MajorityCertificates.Batch017
