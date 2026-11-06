import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch020

def certificate800 : RatMajorityCertificate := ⟨0,(40069592795729869/40000000000000000),(106387241/89475000),(43926654356386885107/100000000000000000000),(10981663589096721277/25000000000000000000),(2231197120607523/3125000000000000),false⟩
theorem valid800 : certificate800.Valid := by decide +kernel
theorem bound800 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate800.a certificate800.b certificate800.c x ≤ (certificate800.bound:ℝ) :=
  rat_majority_certificate_sound certificate800 valid800 x hx0 hx1

def certificate801 : RatMajorityCertificate := ⟨(24623161137364649/125000000000000000),(4022059059348391398145728845999019/5000000000000000000000000000000000),(106387241/89475000),(2478814379772990533/6250000000000000000),(39661030076367848529/100000000000000000000),(2231197120607523/3125000000000000),false⟩
theorem valid801 : certificate801.Valid := by decide +kernel
theorem bound801 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate801.a certificate801.b certificate801.c x ≤ (certificate801.bound:ℝ) :=
  rat_majority_certificate_sound certificate801 valid801 x hx0 hx1

def certificate802 : RatMajorityCertificate := ⟨0,(40069592795729869/40000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540914527404130911/1000000000000000000),false⟩
theorem valid802 : certificate802.Valid := by decide +kernel
theorem bound802 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate802.a certificate802.b certificate802.c x ≤ (certificate802.bound:ℝ) :=
  rat_majority_certificate_sound certificate802 valid802 x hx0 hx1

def certificate803 : RatMajorityCertificate := ⟨(64237344315756969/500000000000000000),(17460832168853460003728164421792939/20000000000000000000000000000000000),1,(1461561093120096411/4000000000000000000),(9134756832000602569/25000000000000000000),(540914527404130911/1000000000000000000),false⟩
theorem valid803 : certificate803.Valid := by decide +kernel
theorem bound803 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate803.a certificate803.b certificate803.c x ≤ (certificate803.bound:ℝ) :=
  rat_majority_certificate_sound certificate803 valid803 x hx0 hx1

def certificate804 : RatMajorityCertificate := ⟨0,(1001821411410478177/1000000000000000000),(509679523/428590000),(21965415261199160687/50000000000000000000),(351446644179186571/800000000000000000),(714029338025499367/1000000000000000000),false⟩
theorem valid804 : certificate804.Valid := by decide +kernel
theorem bound804 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate804.a certificate804.b certificate804.c x ≤ (certificate804.bound:ℝ) :=
  rat_majority_certificate_sound certificate804 valid804 x hx0 hx1

def certificate805 : RatMajorityCertificate := ⟨(48821690353999233/250000000000000000),(201544738114730704698454147178761759/250000000000000000000000000000000000),(509679523/428590000),(39709477057756219163/100000000000000000000),(9927369264439054791/25000000000000000000),(714029338025499367/1000000000000000000),false⟩
theorem valid805 : certificate805.Valid := by decide +kernel
theorem bound805 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate805.a certificate805.b certificate805.c x ≤ (certificate805.bound:ℝ) :=
  rat_majority_certificate_sound certificate805 valid805 x hx0 hx1

def certificate806 : RatMajorityCertificate := ⟨0,(1001821411410478177/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540965230213923089/1000000000000000000),false⟩
theorem valid806 : certificate806.Valid := by decide +kernel
theorem bound806 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate806.a certificate806.b certificate806.c x ≤ (certificate806.bound:ℝ) :=
  rat_majority_certificate_sound certificate806 valid806 x hx0 hx1

def certificate807 : RatMajorityCertificate := ⟨(128598305336813593/1000000000000000000),(872988875652955955076815662356540039/1000000000000000000000000000000000000),1,(36536347400399540887/100000000000000000000),(4567043425049942611/12500000000000000000),(540965230213923089/1000000000000000000),false⟩
theorem valid807 : certificate807.Valid := by decide +kernel
theorem bound807 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate807.a certificate807.b certificate807.c x ≤ (certificate807.bound:ℝ) :=
  rat_majority_certificate_sound certificate807 valid807 x hx0 hx1

def certificate808 : RatMajorityCertificate := ⟨0,(500951962487318747/500000000000000000),(2541858211/2138620000),(8783219624654436859/20000000000000000000),(5489512265409023037/12500000000000000000),(178334223447618519/250000000000000000),false⟩
theorem valid808 : certificate808.Valid := by decide +kernel
theorem bound808 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate808.a certificate808.b certificate808.c x ≤ (certificate808.bound:ℝ) :=
  rat_majority_certificate_sound certificate808 valid808 x hx0 hx1

def certificate809 : RatMajorityCertificate := ⟨(6053467136287067/31250000000000000),(12622252585953215215013454277254951/15625000000000000000000000000000000),(2541858211/2138620000),(19867485292092410709/50000000000000000000),(39734970584184821419/100000000000000000000),(178334223447618519/250000000000000000),false⟩
theorem valid809 : certificate809.Valid := by decide +kernel
theorem bound809 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate809.a certificate809.b certificate809.c x ≤ (certificate809.bound:ℝ) :=
  rat_majority_certificate_sound certificate809 valid809 x hx0 hx1

def certificate810 : RatMajorityCertificate := ⟨0,(500951962487318747/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135247328283856173/250000000000000000),false⟩
theorem valid810 : certificate810.Valid := by decide +kernel
theorem bound810 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate810.a certificate810.b certificate810.c x ≤ (certificate810.bound:ℝ) :=
  rat_majority_certificate_sound certificate810 valid810 x hx0 hx1

def certificate811 : RatMajorityCertificate := ⟨(128470308382327213/1000000000000000000),(436594509381840893814078799616837889/500000000000000000000000000000000000),1,(18269779539023786753/50000000000000000000),(36539559078047573507/100000000000000000000),(135247328283856173/250000000000000000),false⟩
theorem valid811 : certificate811.Valid := by decide +kernel
theorem bound811 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate811.a certificate811.b certificate811.c x ≤ (certificate811.bound:ℝ) :=
  rat_majority_certificate_sound certificate811 valid811 x hx0 hx1

def certificate812 : RatMajorityCertificate := ⟨0,(250496822533032477/250000000000000000),(2538236991/2134400000),(8786181054688621169/20000000000000000000),(21965452636721552923/50000000000000000000),(714100394012666137/1000000000000000000),false⟩
theorem valid812 : certificate812.Valid := by decide +kernel
theorem bound812 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate812.a certificate812.b certificate812.c x ≤ (certificate812.bound:ℝ) :=
  rat_majority_certificate_sound certificate812 valid812 x hx0 hx1

def certificate813 : RatMajorityCertificate := ⟨(195033480150275579/1000000000000000000),(201641555467829183013858337893020817/250000000000000000000000000000000000),(2538236991/2134400000),(992918437494009867/2500000000000000000),(39716737499760394681/100000000000000000000),(714100394012666137/1000000000000000000),false⟩
theorem valid813 : certificate813.Valid := by decide +kernel
theorem bound813 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate813.a certificate813.b certificate813.c x ≤ (certificate813.bound:ℝ) :=
  rat_majority_certificate_sound certificate813 valid813 x hx0 hx1

def certificate814 : RatMajorityCertificate := ⟨0,(250496822533032477/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540950588196208237/1000000000000000000),false⟩
theorem valid814 : certificate814.Valid := by decide +kernel
theorem bound814 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate814.a certificate814.b certificate814.c x ≤ (certificate814.bound:ℝ) :=
  rat_majority_certificate_sound certificate814 valid814 x hx0 hx1

def certificate815 : RatMajorityCertificate := ⟨(127752924749981533/1000000000000000000),(218495120813860500501334611760752759/250000000000000000000000000000000000),1,(18278276337724230095083/50000000000000000000000),(365565526754484601901661/1000000000000000000000000),(540950588196208237/1000000000000000000),false⟩
theorem valid815 : certificate815.Valid := by decide +kernel
theorem bound815 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate815.a certificate815.b certificate815.c x ≤ (certificate815.bound:ℝ) :=
  rat_majority_certificate_sound certificate815 valid815 x hx0 hx1

def certificate816 : RatMajorityCertificate := ⟨0,(200414285506902387/200000000000000000),(253157291/213029000),(5489000491079491073/12500000000000000000),(8782400785727185717/20000000000000000000),(178288592127591351/250000000000000000),false⟩
theorem valid816 : certificate816.Valid := by decide +kernel
theorem bound816 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate816.a certificate816.b certificate816.c x ≤ (certificate816.bound:ℝ) :=
  rat_majority_certificate_sound certificate816 valid816 x hx0 hx1

def certificate817 : RatMajorityCertificate := ⟨(192533887685291499/1000000000000000000),(161827743970588498965272619366091887/200000000000000000000000000000000000),(253157291/213029000),(39761535588633482697/100000000000000000000),(19880767794316741349/50000000000000000000),(178288592127591351/250000000000000000),false⟩
theorem valid817 : certificate817.Valid := by decide +kernel
theorem bound817 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate817.a certificate817.b certificate817.c x ≤ (certificate817.bound:ℝ) :=
  rat_majority_certificate_sound certificate817 valid817 x hx0 hx1

def certificate818 : RatMajorityCertificate := ⟨0,(200414285506902387/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(13524555306926011/25000000000000000),false⟩
theorem valid818 : certificate818.Valid := by decide +kernel
theorem bound818 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate818.a certificate818.b certificate818.c x ≤ (certificate818.bound:ℝ) :=
  rat_majority_certificate_sound certificate818 valid818 x hx0 hx1

def certificate819 : RatMajorityCertificate := ⟨(63843817078529759/500000000000000000),(87411929769624279726494583712365267/100000000000000000000000000000000000),1,(18279148457749433959/50000000000000000000),(36558296915498867919/100000000000000000000),(13524555306926011/25000000000000000),false⟩
theorem valid819 : certificate819.Valid := by decide +kernel
theorem bound819 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate819.a certificate819.b certificate819.c x ≤ (certificate819.bound:ℝ) :=
  rat_majority_certificate_sound certificate819 valid819 x hx0 hx1

def certificate820 : RatMajorityCertificate := ⟨0,(501078123468610191/500000000000000000),(2526565631/2126300000),(21954585236517991201/50000000000000000000),(43909170473035982403/100000000000000000000),(178299788474999831/250000000000000000),false⟩
theorem valid820 : certificate820.Valid := by decide +kernel
theorem bound820 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate820.a certificate820.b certificate820.c x ≤ (certificate820.bound:ℝ) :=
  rat_majority_certificate_sound certificate820 valid820 x hx0 hx1

def certificate821 : RatMajorityCertificate := ⟨(38735370097797813/200000000000000000),(80806178133255394448470279170687717/100000000000000000000000000000000000),(2526565631/2126300000),(39729653003201769129/100000000000000000000),(3972965300320176913/10000000000000000000),(178299788474999831/250000000000000000),false⟩
theorem valid821 : certificate821.Valid := by decide +kernel
theorem bound821 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate821.a certificate821.b certificate821.c x ≤ (certificate821.bound:ℝ) :=
  rat_majority_certificate_sound certificate821 valid821 x hx0 hx1

def certificate822 : RatMajorityCertificate := ⟨0,(501078123468610191/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(13523201093237193/25000000000000000),false⟩
theorem valid822 : certificate822.Valid := by decide +kernel
theorem bound822 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate822.a certificate822.b certificate822.c x ≤ (certificate822.bound:ℝ) :=
  rat_majority_certificate_sound certificate822 valid822 x hx0 hx1

def certificate823 : RatMajorityCertificate := ⟨(126817092383025429/1000000000000000000),(437532852793578430091736041558453061/500000000000000000000000000000000000),1,(1143088741171018133/3125000000000000000),(36578839717472580257/100000000000000000000),(13523201093237193/25000000000000000),false⟩
theorem valid823 : certificate823.Valid := by decide +kernel
theorem bound823 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate823.a certificate823.b certificate823.c x ≤ (certificate823.bound:ℝ) :=
  rat_majority_certificate_sound certificate823 valid823 x hx0 hx1

def certificate824 : RatMajorityCertificate := ⟨0,(200448337490945489/200000000000000000),(1259774491/1061205000),(43883572645037435491/100000000000000000000),(10970893161259358873/25000000000000000000),(71190065542749527/100000000000000000),false⟩
theorem valid824 : certificate824.Valid := by decide +kernel
theorem bound824 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate824.a certificate824.b certificate824.c x ≤ (certificate824.bound:ℝ) :=
  rat_majority_certificate_sound certificate824 valid824 x hx0 hx1

def certificate825 : RatMajorityCertificate := ⟨(38049825912783881/200000000000000000),(32462643152151671424027549191137191/40000000000000000000000000000000000),(1259774491/1061205000),(39791001182274913153/100000000000000000000),(19895500591137456577/50000000000000000000),(71190065542749527/100000000000000000),false⟩
theorem valid825 : certificate825.Valid := by decide +kernel
theorem bound825 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate825.a certificate825.b certificate825.c x ≤ (certificate825.bound:ℝ) :=
  rat_majority_certificate_sound certificate825 valid825 x hx0 hx1

def certificate826 : RatMajorityCertificate := ⟨0,(200448337490945489/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(67619121494694227/125000000000000000),false⟩
theorem valid826 : certificate826.Valid := by decide +kernel
theorem bound826 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate826.a certificate826.b certificate826.c x ≤ (certificate826.bound:ℝ) :=
  rat_majority_certificate_sound certificate826 valid826 x hx0 hx1

def certificate827 : RatMajorityCertificate := ⟨(126682851280074399/1000000000000000000),(175054970563241880114565135226563889/200000000000000000000000000000000000),1,(36582190667222899851/100000000000000000000),(9145547666805724963/25000000000000000000),(67619121494694227/125000000000000000),false⟩
theorem valid827 : certificate827.Valid := by decide +kernel
theorem bound827 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate827.a certificate827.b certificate827.c x ≤ (certificate827.bound:ℝ) :=
  rat_majority_certificate_sound certificate827 valid827 x hx0 hx1

def certificate828 : RatMajorityCertificate := ⟨0,(200465531585209837/200000000000000000),(2511683399/2118630000),(4384734419921244539/10000000000000000000),(43847344199212445391/100000000000000000000),(710346401013864993/1000000000000000000),false⟩
theorem valid828 : certificate828.Valid := by decide +kernel
theorem bound828 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate828.a certificate828.b certificate828.c x ≤ (certificate828.bound:ℝ) :=
  rat_majority_certificate_sound certificate828 valid828 x hx0 hx1

def certificate829 : RatMajorityCertificate := ⟨(188526866391891363/1000000000000000000),(162672393095865504070571724337062169/200000000000000000000000000000000000),(2511683399/2118630000),(19898763226911977697/50000000000000000000),(7959505290764791079/20000000000000000000),(710346401013864993/1000000000000000000),false⟩
theorem valid829 : certificate829.Valid := by decide +kernel
theorem bound829 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate829.a certificate829.b certificate829.c x ≤ (certificate829.bound:ℝ) :=
  rat_majority_certificate_sound certificate829 valid829 x hx0 hx1

def certificate830 : RatMajorityCertificate := ⟨0,(200465531585209837/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135219986996993463/250000000000000000),false⟩
theorem valid830 : certificate830.Valid := by decide +kernel
theorem bound830 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate830.a certificate830.b certificate830.c x ≤ (certificate830.bound:ℝ) :=
  rat_majority_certificate_sound certificate830 valid830 x hx0 hx1

def certificate831 : RatMajorityCertificate := ⟨(25125356105431043/200000000000000000),(35056338449099035830094911511230009/40000000000000000000000000000000000),1,(36607013205033463037/100000000000000000000),(18303506602516731519/50000000000000000000),(135219986996993463/250000000000000000),false⟩
theorem valid831 : certificate831.Valid := by decide +kernel
theorem bound831 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate831.a certificate831.b certificate831.c x ≤ (certificate831.bound:ℝ) :=
  rat_majority_certificate_sound certificate831 valid831 x hx0 hx1

def certificate832 : RatMajorityCertificate := ⟨0,(501207038168743901/500000000000000000),(1252975767/1057480000),(5479061591716459187/12500000000000000000),(43832492733731673497/100000000000000000000),(141939845344312997/200000000000000000),false⟩
theorem valid832 : certificate832.Valid := by decide +kernel
theorem bound832 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate832.a certificate832.b certificate832.c x ≤ (certificate832.bound:ℝ) :=
  rat_majority_certificate_sound certificate832 valid832 x hx0 hx1

def certificate833 : RatMajorityCertificate := ⟨(93702037227379821/500000000000000000),(203639398535259530622224506995778279/250000000000000000000000000000000000),(1252975767/1057480000),(39810928986123842911/100000000000000000000),(1244091530816370091/3125000000000000000),(141939845344312997/200000000000000000),false⟩
theorem valid833 : certificate833.Valid := by decide +kernel
theorem bound833 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate833.a certificate833.b certificate833.c x ≤ (certificate833.bound:ℝ) :=
  rat_majority_certificate_sound certificate833 valid833 x hx0 hx1

def certificate834 : RatMajorityCertificate := ⟨0,(501207038168743901/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540907924348005823/1000000000000000000),false⟩
theorem valid834 : certificate834.Valid := by decide +kernel
theorem bound834 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate834.a certificate834.b certificate834.c x ≤ (certificate834.bound:ℝ) :=
  rat_majority_certificate_sound certificate834 valid834 x hx0 hx1

def certificate835 : RatMajorityCertificate := ⟨(62757959409421053/500000000000000000),(219148788127261772341483621365252247/250000000000000000000000000000000000),1,(3660981322230287271/10000000000000000000),(36609813222302872711/100000000000000000000),(540907924348005823/1000000000000000000),false⟩
theorem valid835 : certificate835.Valid := by decide +kernel
theorem bound835 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate835.a certificate835.b certificate835.c x ≤ (certificate835.bound:ℝ) :=
  rat_majority_certificate_sound certificate835 valid835 x hx0 hx1

def certificate836 : RatMajorityCertificate := ⟨0,(62656303758582349/62500000000000000),(1250163589/1055700000),(43817334906997457037/100000000000000000000),(21908667453498728519/50000000000000000000),(709037284312705153/1000000000000000000),false⟩
theorem valid836 : certificate836.Valid := by decide +kernel
theorem bound836 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate836.a certificate836.b certificate836.c x ≤ (certificate836.bound:ℝ) :=
  rat_majority_certificate_sound certificate836 valid836 x hx0 hx1

def certificate837 : RatMajorityCertificate := ⟨(186244043963479649/1000000000000000000),(50986940366779802820846690647884499/62500000000000000000000000000000000),(1250163589/1055700000),(19912449038157382381/50000000000000000000),(39824898076314764763/100000000000000000000),(709037284312705153/1000000000000000000),false⟩
theorem valid837 : certificate837.Valid := by decide +kernel
theorem bound837 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate837.a certificate837.b certificate837.c x ≤ (certificate837.bound:ℝ) :=
  rat_majority_certificate_sound certificate837 valid837 x hx0 hx1

def certificate838 : RatMajorityCertificate := ⟨0,(62656303758582349/62500000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(108171308697398573/200000000000000000),false⟩
theorem valid838 : certificate838.Valid := by decide +kernel
theorem bound838 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate838.a certificate838.b certificate838.c x ≤ (certificate838.bound:ℝ) :=
  rat_majority_certificate_sound certificate838 valid838 x hx0 hx1

def certificate839 : RatMajorityCertificate := ⟨(62327923432380643/500000000000000000),(27422914576070270355229720170929593/31250000000000000000000000000000000),1,(36630028194530099327/100000000000000000000),(286172095269766401/781250000000000000),(108171308697398573/200000000000000000),false⟩
theorem valid839 : certificate839.Valid := by decide +kernel
theorem bound839 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate839.a certificate839.b certificate839.c x ≤ (certificate839.bound:ℝ) :=
  rat_majority_certificate_sound certificate839 valid839 x hx0 hx1

end Cycle12.MajorityCertificates.Batch020
