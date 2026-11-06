import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch052

def certificate2080 : RatMajorityCertificate := ⟨0,(500032608536034437/500000000000000000),(718486179/587500000),(44683282164781674421/100000000000000000000),(22341641082390837211/50000000000000000000),(740753409564183597/1000000000000000000),false⟩
theorem valid2080 : certificate2080.Valid := by decide +kernel
theorem bound2080 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2080.a certificate2080.b certificate2080.c x ≤ (certificate2080.bound:ℝ) :=
  rat_majority_certificate_sound certificate2080 valid2080 x hx0 hx1

def certificate2081 : RatMajorityCertificate := ⟨(6520551430410119/40000000000000000),(16740816000600035051910215182731997/20000000000000000000000000000000000),(718486179/587500000),(41286650654286372977/100000000000000000000),(20643325327143186489/50000000000000000000),(740753409564183597/1000000000000000000),false⟩
theorem valid2081 : certificate2081.Valid := by decide +kernel
theorem bound2081 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2081.a certificate2081.b certificate2081.c x ≤ (certificate2081.bound:ℝ) :=
  rat_majority_certificate_sound certificate2081 valid2081 x hx0 hx1

def certificate2082 : RatMajorityCertificate := ⟨0,(500032608536034437/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(276387233521628491/500000000000000000),false⟩
theorem valid2082 : certificate2082.Valid := by decide +kernel
theorem bound2082 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2082.a certificate2082.b certificate2082.c x ≤ (certificate2082.bound:ℝ) :=
  rat_majority_certificate_sound certificate2082 valid2082 x hx0 hx1

def certificate2083 : RatMajorityCertificate := ⟨(230558322212976323/1000000000000000000),(384745929260188354324962258606364849/500000000000000000000000000000000000),1,(4237293240071865321/12500000000000000000),(33898345920574922569/100000000000000000000),(276387233521628491/500000000000000000),false⟩
theorem valid2083 : certificate2083.Valid := by decide +kernel
theorem bound2083 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2083.a certificate2083.b certificate2083.c x ≤ (certificate2083.bound:ℝ) :=
  rat_majority_certificate_sound certificate2083 valid2083 x hx0 hx1

def certificate2084 : RatMajorityCertificate := ⟨0,(500032608536034437/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271719433573326303/500000000000000000),false⟩
theorem valid2084 : certificate2084.Valid := by decide +kernel
theorem bound2084 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2084.a certificate2084.b certificate2084.c x ≤ (certificate2084.bound:ℝ) :=
  rat_majority_certificate_sound certificate2084 valid2084 x hx0 hx1

def certificate2085 : RatMajorityCertificate := ⟨(3943543321843629/25000000000000000),(10528914959304532723636008526948127/12500000000000000000000000000000000),1,(8957505585764619361/25000000000000000000),(7166004468611695489/20000000000000000000),(271719433573326303/500000000000000000),false⟩
theorem valid2085 : certificate2085.Valid := by decide +kernel
theorem bound2085 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2085.a certificate2085.b certificate2085.c x ≤ (certificate2085.bound:ℝ) :=
  rat_majority_certificate_sound certificate2085 valid2085 x hx0 hx1

def certificate2086 : RatMajorityCertificate := ⟨0,(50003329846474459/50000000000000000),(2866425781/2350000000),(22306504168631333881/50000000000000000000),(44613008337262667763/100000000000000000000),(737537586632587207/1000000000000000000),false⟩
theorem valid2086 : certificate2086.Valid := by decide +kernel
theorem bound2086 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2086.a certificate2086.b certificate2086.c x ≤ (certificate2086.bound:ℝ) :=
  rat_majority_certificate_sound certificate2086 valid2086 x hx0 hx1

def certificate2087 : RatMajorityCertificate := ⟨(159487037320999963/1000000000000000000),(42028446913075515607316919980554983/50000000000000000000000000000000000),(2866425781/2350000000),(41298440143362536179/100000000000000000000),(2064922007168126809/5000000000000000000),(737537586632587207/1000000000000000000),false⟩
theorem valid2087 : certificate2087.Valid := by decide +kernel
theorem bound2087 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2087.a certificate2087.b certificate2087.c x ≤ (certificate2087.bound:ℝ) :=
  rat_majority_certificate_sound certificate2087 valid2087 x hx0 hx1

def certificate2088 : RatMajorityCertificate := ⟨0,(50003329846474459/50000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(138183409460672139/250000000000000000),false⟩
theorem valid2088 : certificate2088.Valid := by decide +kernel
theorem bound2088 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2088.a certificate2088.b certificate2088.c x ≤ (certificate2088.bound:ℝ) :=
  rat_majority_certificate_sound certificate2088 valid2088 x hx0 hx1

def certificate2089 : RatMajorityCertificate := ⟨(230264044311637787/1000000000000000000),(38489360886976423871961453845217767/50000000000000000000000000000000000),1,(33906728807738550653/100000000000000000000),(16953364403869275327/50000000000000000000),(138183409460672139/250000000000000000),false⟩
theorem valid2089 : certificate2089.Valid := by decide +kernel
theorem bound2089 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2089.a certificate2089.b certificate2089.c x ≤ (certificate2089.bound:ℝ) :=
  rat_majority_certificate_sound certificate2089 valid2089 x hx0 hx1

def certificate2090 : RatMajorityCertificate := ⟨0,(50003329846474459/50000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271604334164752961/500000000000000000),false⟩
theorem valid2090 : certificate2090.Valid := by decide +kernel
theorem bound2090 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2090.a certificate2090.b certificate2090.c x ≤ (certificate2090.bound:ℝ) :=
  rat_majority_certificate_sound certificate2090 valid2090 x hx0 hx1

def certificate2091 : RatMajorityCertificate := ⟨(38939591475554559/250000000000000000),(10553723224979495050922031945491419/12500000000000000000000000000000000),1,(17939490024856263823/50000000000000000000),(35878980049712527647/100000000000000000000),(271604334164752961/500000000000000000),false⟩
theorem valid2091 : certificate2091.Valid := by decide +kernel
theorem bound2091 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2091.a certificate2091.b certificate2091.c x ≤ (certificate2091.bound:ℝ) :=
  rat_majority_certificate_sound certificate2091 valid2091 x hx0 hx1

def certificate2092 : RatMajorityCertificate := ⟨0,(1000067960477214149/1000000000000000000),(2901765303/2350000000),(44941409232715494829/100000000000000000000),(4494140923271549483/10000000000000000000),(187973965410387853/250000000000000000),false⟩
theorem valid2092 : certificate2092.Valid := by decide +kernel
theorem bound2092 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2092.a certificate2092.b certificate2092.c x ≤ (certificate2092.bound:ℝ) :=
  rat_majority_certificate_sound certificate2092 valid2092 x hx0 hx1

def certificate2093 : RatMajorityCertificate := ⟨(83335949476821393/500000000000000000),(416692367210890142507443403714510443/500000000000000000000000000000000000),(2901765303/2350000000),(20733054415146160001/50000000000000000000),(41466108830292320003/100000000000000000000),(187973965410387853/250000000000000000),false⟩
theorem valid2093 : certificate2093.Valid := by decide +kernel
theorem bound2093 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2093.a certificate2093.b certificate2093.c x ≤ (certificate2093.bound:ℝ) :=
  rat_majority_certificate_sound certificate2093 valid2093 x hx0 hx1

def certificate2094 : RatMajorityCertificate := ⟨0,(1000067960477214149/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(553149470068864423/1000000000000000000),false⟩
theorem valid2094 : certificate2094.Valid := by decide +kernel
theorem bound2094 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2094.a certificate2094.b certificate2094.c x ≤ (certificate2094.bound:ℝ) :=
  rat_majority_certificate_sound certificate2094 valid2094 x hx0 hx1

def certificate2095 : RatMajorityCertificate := ⟨(116603505229445543/500000000000000000),(383422550579301295862410815455412093/500000000000000000000000000000000000),1,(33822746174284191569/100000000000000000000),(3382274617428419157/10000000000000000000),(553149470068864423/1000000000000000000),false⟩
theorem valid2095 : certificate2095.Valid := by decide +kernel
theorem bound2095 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2095.a certificate2095.b certificate2095.c x ≤ (certificate2095.bound:ℝ) :=
  rat_majority_certificate_sound certificate2095 valid2095 x hx0 hx1

def certificate2096 : RatMajorityCertificate := ⟨0,(1000067960477214149/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(542953550726642647/1000000000000000000),false⟩
theorem valid2096 : certificate2096.Valid := by decide +kernel
theorem bound2096 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2096.a certificate2096.b certificate2096.c x ≤ (certificate2096.bound:ℝ) :=
  rat_majority_certificate_sound certificate2096 valid2096 x hx0 hx1

def certificate2097 : RatMajorityCertificate := ⟨(153549293853609923/1000000000000000000),(846508231340318039073731530017599473/1000000000000000000000000000000000000),1,(35933297401226623573/100000000000000000000),(17966648700613311787/50000000000000000000),(542953550726642647/1000000000000000000),false⟩
theorem valid2097 : certificate2097.Valid := by decide +kernel
theorem bound2097 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2097.a certificate2097.b certificate2097.c x ≤ (certificate2097.bound:ℝ) :=
  rat_majority_certificate_sound certificate2097 valid2097 x hx0 hx1

def certificate2098 : RatMajorityCertificate := ⟨0,(250017326644675869/250000000000000000),(1452058739/1175000000),(8992619479733687809/20000000000000000000),(22481548699334219523/50000000000000000000),(94091515247740323/125000000000000000),false⟩
theorem valid2098 : certificate2098.Valid := by decide +kernel
theorem bound2098 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2098.a certificate2098.b certificate2098.c x ≤ (certificate2098.bound:ℝ) :=
  rat_majority_certificate_sound certificate2098 valid2098 x hx0 hx1

def certificate2099 : RatMajorityCertificate := ⟨(165662412499411661/1000000000000000000),(208598853146065429204866839456091591/250000000000000000000000000000000000),(1452058739/1175000000),(41512964667126259401/100000000000000000000),(20756482333563129701/50000000000000000000),(94091515247740323/125000000000000000),false⟩
theorem valid2099 : certificate2099.Valid := by decide +kernel
theorem bound2099 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2099.a certificate2099.b certificate2099.c x ≤ (certificate2099.bound:ℝ) :=
  rat_majority_certificate_sound certificate2099 valid2099 x hx0 hx1

def certificate2100 : RatMajorityCertificate := ⟨0,(250017326644675869/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(110667113109517851/200000000000000000),false⟩
theorem valid2100 : certificate2100.Valid := by decide +kernel
theorem bound2100 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2100.a certificate2100.b certificate2100.c x ≤ (certificate2100.bound:ℝ) :=
  rat_majority_certificate_sound certificate2100 valid2100 x hx0 hx1

def certificate2101 : RatMajorityCertificate := ⟨(117257329463804417/500000000000000000),(95692299280303569605973641424486627/125000000000000000000000000000000000),1,(6757054566167636511/20000000000000000000),(8446318207709545639/25000000000000000000),(110667113109517851/200000000000000000),false⟩
theorem valid2101 : certificate2101.Valid := by decide +kernel
theorem bound2101 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2101.a certificate2101.b certificate2101.c x ≤ (certificate2101.bound:ℝ) :=
  rat_majority_certificate_sound certificate2101 valid2101 x hx0 hx1

def certificate2102 : RatMajorityCertificate := ⟨0,(250017326644675869/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(542715032704142183/1000000000000000000),false⟩
theorem valid2102 : certificate2102.Valid := by decide +kernel
theorem bound2102 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2102.a certificate2102.b certificate2102.c x ≤ (certificate2102.bound:ℝ) :=
  rat_majority_certificate_sound certificate2102 valid2102 x hx0 hx1

def certificate2103 : RatMajorityCertificate := ⟨(75736255739937403/500000000000000000),(106073287132161297110605238715371793/125000000000000000000000000000000000),1,(17992080268594667659/50000000000000000000),(35984160537189335319/100000000000000000000),(542715032704142183/1000000000000000000),false⟩
theorem valid2103 : certificate2103.Valid := by decide +kernel
theorem bound2103 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2103.a certificate2103.b certificate2103.c x ≤ (certificate2103.bound:ℝ) :=
  rat_majority_certificate_sound certificate2103 valid2103 x hx0 hx1

def certificate2104 : RatMajorityCertificate := ⟨0,(1000070634112331131/1000000000000000000),(363308693/293750000),(11246190859108918467/25000000000000000000),(44984763436435673869/100000000000000000000),(753568181897019577/1000000000000000000),false⟩
theorem valid2104 : certificate2104.Valid := by decide +kernel
theorem bound2104 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2104.a certificate2104.b certificate2104.c x ≤ (certificate2104.bound:ℝ) :=
  rat_majority_certificate_sound certificate2104 valid2104 x hx0 hx1

def certificate2105 : RatMajorityCertificate := ⟨(82320038563733781/500000000000000000),(417709463889580770692285014797363689/500000000000000000000000000000000000),(363308693/293750000),(5195006329484343303/12500000000000000000),(1662402025434989857/4000000000000000000),(753568181897019577/1000000000000000000),false⟩
theorem valid2105 : certificate2105.Valid := by decide +kernel
theorem bound2105 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2105.a certificate2105.b certificate2105.c x ≤ (certificate2105.bound:ℝ) :=
  rat_majority_certificate_sound certificate2105 valid2105 x hx0 hx1

def certificate2106 : RatMajorityCertificate := ⟨0,(1000070634112331131/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(69395687189971451/125000000000000000),false⟩
theorem valid2106 : certificate2106.Valid := by decide +kernel
theorem bound2106 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2106.a certificate2106.b certificate2106.c x ≤ (certificate2106.bound:ℝ) :=
  rat_majority_certificate_sound certificate2106 valid2106 x hx0 hx1

def certificate2107 : RatMajorityCertificate := ⟨(9886810088723357/40000000000000000),(30115316929715484795153156962073233/40000000000000000000000000000000000),1,(33417319577860981571/100000000000000000000),(8354329894465245393/25000000000000000000),(69395687189971451/125000000000000000),false⟩
theorem valid2107 : certificate2107.Valid := by decide +kernel
theorem bound2107 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2107.a certificate2107.b certificate2107.c x ≤ (certificate2107.bound:ℝ) :=
  rat_majority_certificate_sound certificate2107 valid2107 x hx0 hx1

def certificate2108 : RatMajorityCertificate := ⟨0,(1000070634112331131/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(542479414035274693/1000000000000000000),false⟩
theorem valid2108 : certificate2108.Valid := by decide +kernel
theorem bound2108 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2108.a certificate2108.b certificate2108.c x ≤ (certificate2108.bound:ℝ) :=
  rat_majority_certificate_sound certificate2108 valid2108 x hx0 hx1

def certificate2109 : RatMajorityCertificate := ⟨(29882055587409499/200000000000000000),(170129960542585681016709055617186631/200000000000000000000000000000000000),1,(2252154698121962227/6250000000000000000),(36034475169951395633/100000000000000000000),(542479414035274693/1000000000000000000),false⟩
theorem valid2109 : certificate2109.Valid := by decide +kernel
theorem bound2109 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2109.a certificate2109.b certificate2109.c x ≤ (certificate2109.bound:ℝ) :=
  rat_majority_certificate_sound certificate2109 valid2109 x hx0 hx1

def certificate2110 : RatMajorityCertificate := ⟨0,(500035970986149839/500000000000000000),(2908665087/2350000000),(45004968616978881133/100000000000000000000),(22502484308489440567/50000000000000000000),(754311185387832931/1000000000000000000),false⟩
theorem valid2110 : certificate2110.Valid := by decide +kernel
theorem bound2110 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2110.a certificate2110.b certificate2110.c x ≤ (certificate2110.bound:ℝ) :=
  rat_majority_certificate_sound certificate2110 valid2110 x hx0 hx1

def certificate2111 : RatMajorityCertificate := ⟨(32641999434682951/200000000000000000),(83685020314978924267101846855305111/100000000000000000000000000000000000),(2908665087/2350000000),(20807671352862978033/50000000000000000000),(41615342705725956067/100000000000000000000),(754311185387832931/1000000000000000000),false⟩
theorem valid2111 : certificate2111.Valid := by decide +kernel
theorem bound2111 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2111.a certificate2111.b certificate2111.c x ≤ (certificate2111.bound:ℝ) :=
  rat_majority_certificate_sound certificate2111 valid2111 x hx0 hx1

def certificate2112 : RatMajorityCertificate := ⟨0,(500035970986149839/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(138395004018506783/250000000000000000),false⟩
theorem valid2112 : certificate2112.Valid := by decide +kernel
theorem bound2112 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2112.a certificate2112.b certificate2112.c x ≤ (certificate2112.bound:ℝ) :=
  rat_majority_certificate_sound certificate2112 valid2112 x hx0 hx1

def certificate2113 : RatMajorityCertificate := ⟨(4724462791647421/20000000000000000),(7638318080313642500922035236084781/10000000000000000000000000000000000),1,(8434041769165071419/25000000000000000000),(33736167076660285677/100000000000000000000),(138395004018506783/250000000000000000),false⟩
theorem valid2113 : certificate2113.Valid := by decide +kernel
theorem bound2113 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2113.a certificate2113.b certificate2113.c x ≤ (certificate2113.bound:ℝ) :=
  rat_majority_certificate_sound certificate2113 valid2113 x hx0 hx1

def certificate2114 : RatMajorityCertificate := ⟨0,(500035970986149839/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(33890421103119571/62500000000000000),false⟩
theorem valid2114 : certificate2114.Valid := by decide +kernel
theorem bound2114 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2114.a certificate2114.b certificate2114.c x ≤ (certificate2114.bound:ℝ) :=
  rat_majority_certificate_sound certificate2114 valid2114 x hx0 hx1

def certificate2115 : RatMajorityCertificate := ⟨(29472654084644381/200000000000000000),(85269806994475899561140681304595341/100000000000000000000000000000000000),1,(36084230080638335919/100000000000000000000),(451052876007979199/1250000000000000000),(33890421103119571/62500000000000000),false⟩
theorem valid2115 : certificate2115.Valid := by decide +kernel
theorem bound2115 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2115.a certificate2115.b certificate2115.c x ≤ (certificate2115.bound:ℝ) :=
  rat_majority_certificate_sound certificate2115 valid2115 x hx0 hx1

def certificate2116 : RatMajorityCertificate := ⟨0,(250018307267395363/250000000000000000),(90982861/73437500),(45030585483206446121/100000000000000000000),(22515292741603223061/50000000000000000000),(188852413399840623/250000000000000000),false⟩
theorem valid2116 : certificate2116.Valid := by decide +kernel
theorem bound2116 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2116.a certificate2116.b certificate2116.c x ≤ (certificate2116.bound:ℝ) :=
  rat_majority_certificate_sound certificate2116 valid2116 x hx0 hx1

def certificate2117 : RatMajorityCertificate := ⟨(163320257654068289/1000000000000000000),(209185252906250338141170158436056093/250000000000000000000000000000000000),(90982861/73437500),(10409817601007593977/25000000000000000000),(41639270404030375909/100000000000000000000),(188852413399840623/250000000000000000),false⟩
theorem valid2117 : certificate2117.Valid := by decide +kernel
theorem bound2117 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2117.a certificate2117.b certificate2117.c x ≤ (certificate2117.bound:ℝ) :=
  rat_majority_certificate_sound certificate2117 valid2117 x hx0 hx1

def certificate2118 : RatMajorityCertificate := ⟨0,(250018307267395363/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(55365338819621439/100000000000000000),false⟩
theorem valid2118 : certificate2118.Valid := by decide +kernel
theorem bound2118 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2118.a certificate2118.b certificate2118.c x ≤ (certificate2118.bound:ℝ) :=
  rat_majority_certificate_sound certificate2118 valid2118 x hx0 hx1

def certificate2119 : RatMajorityCertificate := ⟨(47346614573689007/200000000000000000),(38166141022923555134596188724125459/50000000000000000000000000000000000),1,(33721479892644088249/100000000000000000000),(134885919570576353/400000000000000000),(55365338819621439/100000000000000000),false⟩
theorem valid2119 : certificate2119.Valid := by decide +kernel
theorem bound2119 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2119.a certificate2119.b certificate2119.c x ≤ (certificate2119.bound:ℝ) :=
  rat_majority_certificate_sound certificate2119 valid2119 x hx0 hx1

end Cycle12.MajorityCertificates.Batch052
