import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch026

def certificate1040 : RatMajorityCertificate := ⟨0,(1000220047326507061/1000000000000000000),(271753399/230720000),(43672232352410209439/100000000000000000000),(272951452202563809/625000000000000000),(703307198543795087/1000000000000000000),false⟩
theorem valid1040 : certificate1040.Valid := by decide +kernel
theorem bound1040 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1040.a certificate1040.b certificate1040.c x ≤ (certificate1040.bound:ℝ) :=
  rat_majority_certificate_sound certificate1040 valid1040 x hx0 hx1

def certificate1041 : RatMajorityCertificate := ⟨(99496971074419867/500000000000000000),(400591158546353187027615407945819113/500000000000000000000000000000000000),(271753399/230720000),(3933816882125878091/10000000000000000000),(39338168821258780911/100000000000000000000),(703307198543795087/1000000000000000000),false⟩
theorem valid1041 : certificate1041.Valid := by decide +kernel
theorem bound1041 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1041.a certificate1041.b certificate1041.c x ≤ (certificate1041.bound:ℝ) :=
  rat_majority_certificate_sound certificate1041 valid1041 x hx0 hx1

def certificate1042 : RatMajorityCertificate := ⟨0,(1000220047326507061/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(16985717989147731/31250000000000000),false⟩
theorem valid1042 : certificate1042.Valid := by decide +kernel
theorem bound1042 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1042.a certificate1042.b certificate1042.c x ≤ (certificate1042.bound:ℝ) :=
  rat_majority_certificate_sound certificate1042 valid1042 x hx0 hx1

def certificate1043 : RatMajorityCertificate := ⟨(79023688109202221/500000000000000000),(421068946602752151724959348766617519/500000000000000000000000000000000000),1,(8955743028564129361/25000000000000000000),(7164594422851303489/20000000000000000000),(16985717989147731/31250000000000000),false⟩
theorem valid1043 : certificate1043.Valid := by decide +kernel
theorem bound1043 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1043.a certificate1043.b certificate1043.c x ≤ (certificate1043.bound:ℝ) :=
  rat_majority_certificate_sound certificate1043 valid1043 x hx0 hx1

def certificate1044 : RatMajorityCertificate := ⟨0,(31257532802705789/31250000000000000),(542950437/460550000),(43696685996617734443/100000000000000000000),(10924171499154433611/25000000000000000000),(70422448435773053/100000000000000000),false⟩
theorem valid1044 : certificate1044.Valid := by decide +kernel
theorem bound1044 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1044.a certificate1044.b certificate1044.c x ≤ (certificate1044.bound:ℝ) :=
  rat_majority_certificate_sound certificate1044 valid1044 x hx0 hx1

def certificate1045 : RatMajorityCertificate := ⟨(39695876408605973/200000000000000000),(5010711401567001730944820052922303/6250000000000000000000000000000000),(542950437/460550000),(9844262859360868609/25000000000000000000),(39377051437443474437/100000000000000000000),(70422448435773053/100000000000000000),false⟩
theorem valid1045 : certificate1045.Valid := by decide +kernel
theorem bound1045 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1045.a certificate1045.b certificate1045.c x ≤ (certificate1045.bound:ℝ) :=
  rat_majority_certificate_sound certificate1045 valid1045 x hx0 hx1

def certificate1046 : RatMajorityCertificate := ⟨0,(31257532802705789/31250000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543557703468385061/1000000000000000000),false⟩
theorem valid1046 : certificate1046.Valid := by decide +kernel
theorem bound1046 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1046.a certificate1046.b certificate1046.c x ≤ (certificate1046.bound:ℝ) :=
  rat_majority_certificate_sound certificate1046 valid1046 x hx0 hx1

def certificate1047 : RatMajorityCertificate := ⟨(31618809022745529/200000000000000000),(5263180600330199655582303197832619/6250000000000000000000000000000000),1,(35821886724210764793/100000000000000000000),(17910943362105382397/50000000000000000000),(543557703468385061/1000000000000000000),false⟩
theorem valid1047 : certificate1047.Valid := by decide +kernel
theorem bound1047 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1047.a certificate1047.b certificate1047.c x ≤ (certificate1047.bound:ℝ) :=
  rat_majority_certificate_sound certificate1047 valid1047 x hx0 hx1

def certificate1048 : RatMajorityCertificate := ⟨0,(200052566583222279/200000000000000000),(84752333/71825000),(21860536320788449553/50000000000000000000),(43721072641576899107/100000000000000000000),(705140944145013817/1000000000000000000),false⟩
theorem valid1048 : certificate1048.Valid := by decide +kernel
theorem bound1048 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1048.a certificate1048.b certificate1048.c x ≤ (certificate1048.bound:ℝ) :=
  rat_majority_certificate_sound certificate1048 valid1048 x hx0 hx1

def certificate1049 : RatMajorityCertificate := ⟨(197962445841726861/1000000000000000000),(160449671205492681765598660832063781/200000000000000000000000000000000000),(84752333/71825000),(39415912420247119749/100000000000000000000),(157663649680988479/400000000000000000),(705140944145013817/1000000000000000000),false⟩
theorem valid1049 : certificate1049.Valid := by decide +kernel
theorem bound1049 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1049.a certificate1049.b certificate1049.c x ≤ (certificate1049.bound:ℝ) :=
  rat_majority_certificate_sound certificate1049 valid1049 x hx0 hx1

def certificate1050 : RatMajorityCertificate := ⟨0,(200052566583222279/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543572347129910561/1000000000000000000),false⟩
theorem valid1050 : certificate1050.Valid := by decide +kernel
theorem bound1050 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1050.a certificate1050.b certificate1050.c x ≤ (certificate1050.bound:ℝ) :=
  rat_majority_certificate_sound certificate1050 valid1050 x hx0 hx1

def certificate1051 : RatMajorityCertificate := ⟨(39534259648860213/250000000000000000),(42104211535083564153057448821714573/50000000000000000000000000000000000),1,(4477611847632414011/12500000000000000000),(35820894781059312089/100000000000000000000),(543572347129910561/1000000000000000000),false⟩
theorem valid1051 : certificate1051.Valid := by decide +kernel
theorem bound1051 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1051.a certificate1051.b certificate1051.c x ≤ (certificate1051.bound:ℝ) :=
  rat_majority_certificate_sound certificate1051 valid1051 x hx0 hx1

def certificate1052 : RatMajorityCertificate := ⟨0,(1000285371395657569/1000000000000000000),(2709787481/2294150000),(21874118200503118287/50000000000000000000),(1749929456040249463/4000000000000000000),(706244781084128461/1000000000000000000),false⟩
theorem valid1052 : certificate1052.Valid := by decide +kernel
theorem bound1052 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1052.a certificate1052.b certificate1052.c x ≤ (certificate1052.bound:ℝ) :=
  rat_majority_certificate_sound certificate1052 valid1052 x hx0 hx1

def certificate1053 : RatMajorityCertificate := ⟨(198204592959136217/1000000000000000000),(802024216515202862923772141041923527/1000000000000000000000000000000000000),(2709787481/2294150000),(197189807730354248734501/500000000000000000000000),(394379615460708497469003/1000000000000000000000000),(706244781084128461/1000000000000000000),false⟩
theorem valid1053 : certificate1053.Valid := by decide +kernel
theorem bound1053 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1053.a certificate1053.b certificate1053.c x ≤ (certificate1053.bound:ℝ) :=
  rat_majority_certificate_sound certificate1053 valid1053 x hx0 hx1

def certificate1054 : RatMajorityCertificate := ⟨0,(1000285371395657569/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543485886944379273/1000000000000000000),false⟩
theorem valid1054 : certificate1054.Valid := by decide +kernel
theorem bound1054 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1054.a certificate1054.b certificate1054.c x ≤ (certificate1054.bound:ℝ) :=
  rat_majority_certificate_sound certificate1054 valid1054 x hx0 hx1

def certificate1055 : RatMajorityCertificate := ⟨(157309629121744631/1000000000000000000),(842930850605500091174305813259737961/1000000000000000000000000000000000000),1,(179207118392022240133559/500000000000000000000000),(358414236784044480267119/1000000000000000000000000),(543485886944379273/1000000000000000000),false⟩
theorem valid1055 : certificate1055.Valid := by decide +kernel
theorem bound1055 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1055.a certificate1055.b certificate1055.c x ≤ (certificate1055.bound:ℝ) :=
  rat_majority_certificate_sound certificate1055 valid1055 x hx0 hx1

def certificate1056 : RatMajorityCertificate := ⟨0,(1000308640495644903/1000000000000000000),(1354492409/1144995000),(21894595332746817873/50000000000000000000),(43789190665493635747/100000000000000000000),(176945466750944377/250000000000000000),false⟩
theorem valid1056 : certificate1056.Valid := by decide +kernel
theorem bound1056 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1056.a certificate1056.b certificate1056.c x ≤ (certificate1056.bound:ℝ) :=
  rat_majority_certificate_sound certificate1056 valid1056 x hx0 hx1

def certificate1057 : RatMajorityCertificate := ⟨(98664250619506193/500000000000000000),(401459617845102621180719643062615721/500000000000000000000000000000000000),(1354492409/1144995000),(39503349512437124633/100000000000000000000),(19751674756218562317/50000000000000000000),(176945466750944377/250000000000000000),false⟩
theorem valid1057 : certificate1057.Valid := by decide +kernel
theorem bound1057 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1057.a certificate1057.b certificate1057.c x ≤ (certificate1057.bound:ℝ) :=
  rat_majority_certificate_sound certificate1057 valid1057 x hx0 hx1

def certificate1058 : RatMajorityCertificate := ⟨0,(1000308640495644903/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543524446433821179/1000000000000000000),false⟩
theorem valid1058 : certificate1058.Valid := by decide +kernel
theorem bound1058 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1058.a certificate1058.b certificate1058.c x ≤ (certificate1058.bound:ℝ) :=
  rat_majority_certificate_sound certificate1058 valid1058 x hx0 hx1

def certificate1059 : RatMajorityCertificate := ⟨(157552377853716119/1000000000000000000),(842707635597937980018307366008708543/1000000000000000000000000000000000000),1,(35835502157305953653/100000000000000000000),(17917751078652976827/50000000000000000000),(543524446433821179/1000000000000000000),false⟩
theorem valid1059 : certificate1059.Valid := by decide +kernel
theorem bound1059 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1059.a certificate1059.b certificate1059.c x ≤ (certificate1059.bound:ℝ) :=
  rat_majority_certificate_sound certificate1059 valid1059 x hx0 hx1

def certificate1060 : RatMajorityCertificate := ⟨0,(1000332615665066053/1000000000000000000),(902195317/761970000),(21906692474918041663/50000000000000000000),(43813384949836083327/100000000000000000000),(708695257926969091/1000000000000000000),false⟩
theorem valid1060 : certificate1060.Valid := by decide +kernel
theorem bound1060 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1060.a certificate1060.b certificate1060.c x ≤ (certificate1060.bound:ℝ) :=
  rat_majority_certificate_sound certificate1060 valid1060 x hx0 hx1

def certificate1061 : RatMajorityCertificate := ⟨(196786305042569403/1000000000000000000),(803480856414769024598905525168223641/1000000000000000000000000000000000000),(902195317/761970000),(39542634575699369871/100000000000000000000),(2471414660981210617/6250000000000000000),(708695257926969091/1000000000000000000),false⟩
theorem valid1061 : certificate1061.Valid := by decide +kernel
theorem bound1061 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1061.a certificate1061.b certificate1061.c x ≤ (certificate1061.bound:ℝ) :=
  rat_majority_certificate_sound certificate1061 valid1061 x hx0 hx1

def certificate1062 : RatMajorityCertificate := ⟨0,(1000332615665066053/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(33964954429565341/62500000000000000),false⟩
theorem valid1062 : certificate1062.Valid := by decide +kernel
theorem bound1062 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1062.a certificate1062.b certificate1062.c x ≤ (certificate1062.bound:ℝ) :=
  rat_majority_certificate_sound certificate1062 valid1062 x hx0 hx1

def certificate1063 : RatMajorityCertificate := ⟨(78364540057372053/500000000000000000),(421775702501552195343474580158783191/500000000000000000000000000000000000),1,(3585591094783529703/10000000000000000000),(35855910947835297031/100000000000000000000),(33964954429565341/62500000000000000),false⟩
theorem valid1063 : certificate1063.Valid := by decide +kernel
theorem bound1063 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1063.a certificate1063.b certificate1063.c x ≤ (certificate1063.bound:ℝ) :=
  rat_majority_certificate_sound certificate1063 valid1063 x hx0 hx1

def certificate1064 : RatMajorityCertificate := ⟨0,(125044658471771523/125000000000000000),(2704283719/2281930000),(43837422877878008733/100000000000000000000),(21918711438939004367/50000000000000000000),(709602307098842301/1000000000000000000),false⟩
theorem valid1064 : certificate1064.Valid := by decide +kernel
theorem bound1064 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1064.a certificate1064.b certificate1064.c x ≤ (certificate1064.bound:ℝ) :=
  rat_majority_certificate_sound certificate1064 valid1064 x hx0 hx1

def certificate1065 : RatMajorityCertificate := ⟨(196222279158775719/1000000000000000000),(100508110589809802033674118231949963/125000000000000000000000000000000000),(2704283719/2281930000),(39582304954272556987/100000000000000000000),(9895576238568139247/25000000000000000000),(709602307098842301/1000000000000000000),false⟩
theorem valid1065 : certificate1065.Valid := by decide +kernel
theorem bound1065 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1065.a certificate1065.b certificate1065.c x ≤ (certificate1065.bound:ℝ) :=
  rat_majority_certificate_sound certificate1065 valid1065 x hx0 hx1

def certificate1066 : RatMajorityCertificate := ⟨0,(125044658471771523/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271726876677877947/500000000000000000),false⟩
theorem valid1066 : certificate1066.Valid := by decide +kernel
theorem bound1066 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1066.a certificate1066.b certificate1066.c x ≤ (certificate1066.bound:ℝ) :=
  rat_majority_certificate_sound certificate1066 valid1066 x hx0 hx1

def certificate1067 : RatMajorityCertificate := ⟨(78379889971271379/500000000000000000),(52721342663373102023437493282859783/62500000000000000000000000000000000),1,(35855233798164238491/100000000000000000000),(8963808449541059623/25000000000000000000),(271726876677877947/500000000000000000),false⟩
theorem valid1067 : certificate1067.Valid := by decide +kernel
theorem bound1067 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1067.a certificate1067.b certificate1067.c x ≤ (certificate1067.bound:ℝ) :=
  rat_majority_certificate_sound certificate1067 valid1067 x hx0 hx1

def certificate1068 : RatMajorityCertificate := ⟨0,(500191285762795833/500000000000000000),(2702076873/2278040000),(43861406879614616909/100000000000000000000),(4386140687961461691/10000000000000000000),(355254663034096621/500000000000000000),false⟩
theorem valid1068 : certificate1068.Valid := by decide +kernel
theorem bound1068 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1068.a certificate1068.b certificate1068.c x ≤ (certificate1068.bound:ℝ) :=
  rat_majority_certificate_sound certificate1068 valid1068 x hx0 hx1

def certificate1069 : RatMajorityCertificate := ⟨(19565939591192733/100000000000000000),(40232416095003698309176554767718411/50000000000000000000000000000000000),(2702076873/2278040000),(19810936104160773149/50000000000000000000),(39621872208321546299/100000000000000000000),(355254663034096621/500000000000000000),false⟩
theorem valid1069 : certificate1069.Valid := by decide +kernel
theorem bound1069 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1069.a certificate1069.b certificate1069.c x ≤ (certificate1069.bound:ℝ) :=
  rat_majority_certificate_sound certificate1069 valid1069 x hx0 hx1

def certificate1070 : RatMajorityCertificate := ⟨0,(500191285762795833/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(108673757482605831/200000000000000000),false⟩
theorem valid1070 : certificate1070.Valid := by decide +kernel
theorem bound1070 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1070.a certificate1070.b certificate1070.c x ≤ (certificate1070.bound:ℝ) :=
  rat_majority_certificate_sound certificate1070 valid1070 x hx0 hx1

def certificate1071 : RatMajorityCertificate := ⟨(38982819511812517/250000000000000000),(105548954826426450410483972755158339/125000000000000000000000000000000000),1,(35875743927363205947/100000000000000000000),(8968935981840801487/25000000000000000000),(108673757482605831/200000000000000000),false⟩
theorem valid1071 : certificate1071.Valid := by decide +kernel
theorem bound1071 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1071.a certificate1071.b certificate1071.c x ≤ (certificate1071.bound:ℝ) :=
  rat_majority_certificate_sound certificate1071 valid1071 x hx0 hx1

def certificate1072 : RatMajorityCertificate := ⟨0,(500204250881156363/500000000000000000),(2699908977/2274230000),(43884889234536636639/100000000000000000000),(274280557715853979/625000000000000000),(44461636423311999/62500000000000000),false⟩
theorem valid1072 : certificate1072.Valid := by decide +kernel
theorem bound1072 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1072.a certificate1072.b certificate1072.c x ≤ (certificate1072.bound:ℝ) :=
  rat_majority_certificate_sound certificate1072 valid1072 x hx0 hx1

def certificate1073 : RatMajorityCertificate := ⟨(97485955041036847/500000000000000000),(201339236327842256636458706148492539/250000000000000000000000000000000000),(2699908977/2274230000),(9916027431465446881/25000000000000000000),(1586564389034471501/4000000000000000000),(44461636423311999/62500000000000000),false⟩
theorem valid1073 : certificate1073.Valid := by decide +kernel
theorem bound1073 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1073.a certificate1073.b certificate1073.c x ≤ (certificate1073.bound:ℝ) :=
  rat_majority_certificate_sound certificate1073 valid1073 x hx0 hx1

def certificate1074 : RatMajorityCertificate := ⟨0,(500204250881156363/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271698444377718167/500000000000000000),false⟩
theorem valid1074 : certificate1074.Valid := by decide +kernel
theorem bound1074 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1074.a certificate1074.b certificate1074.c x ≤ (certificate1074.bound:ℝ) :=
  rat_majority_certificate_sound certificate1074 valid1074 x hx0 hx1

def certificate1075 : RatMajorityCertificate := ⟨(156074505589251837/1000000000000000000),(422135119731237796110244429418011169/500000000000000000000000000000000000),1,(35872298868211624527/100000000000000000000),(2242018679263226533/6250000000000000000),(271698444377718167/500000000000000000),false⟩
theorem valid1075 : certificate1075.Valid := by decide +kernel
theorem bound1075 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1075.a certificate1075.b certificate1075.c x ≤ (certificate1075.bound:ℝ) :=
  rat_majority_certificate_sound certificate1075 valid1075 x hx0 hx1

def certificate1076 : RatMajorityCertificate := ⟨0,(1000435031589761769/1000000000000000000),(107833739/90820000),(8777702995944900773/20000000000000000000),(21944257489862251933/50000000000000000000),(142287128031453429/200000000000000000),false⟩
theorem valid1076 : certificate1076.Valid := by decide +kernel
theorem bound1076 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1076.a certificate1076.b certificate1076.c x ≤ (certificate1076.bound:ℝ) :=
  rat_majority_certificate_sound certificate1076 valid1076 x hx0 hx1

def certificate1077 : RatMajorityCertificate := ⟨(96930037944715651/500000000000000000),(403245310221662475258117192464253381/500000000000000000000000000000000000),(107833739/90820000),(4962073457934208037/12500000000000000000),(39696587663473664297/100000000000000000000),(142287128031453429/200000000000000000),false⟩
theorem valid1077 : certificate1077.Valid := by decide +kernel
theorem bound1077 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1077.a certificate1077.b certificate1077.c x ≤ (certificate1077.bound:ℝ) :=
  rat_majority_certificate_sound certificate1077 valid1077 x hx0 hx1

def certificate1078 : RatMajorityCertificate := ⟨0,(1000435031589761769/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(21731055565535257/40000000000000000),false⟩
theorem valid1078 : certificate1078.Valid := by decide +kernel
theorem bound1078 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1078.a certificate1078.b certificate1078.c x ≤ (certificate1078.bound:ℝ) :=
  rat_majority_certificate_sound certificate1078 valid1078 x hx0 hx1

def certificate1079 : RatMajorityCertificate := ⟨(154932405032362509/1000000000000000000),(845435226066932417038036605442881579/1000000000000000000000000000000000000),1,(8975124869356262117/25000000000000000000),(35900499477425048469/100000000000000000000),(21731055565535257/40000000000000000),false⟩
theorem valid1079 : certificate1079.Valid := by decide +kernel
theorem bound1079 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1079.a certificate1079.b certificate1079.c x ≤ (certificate1079.bound:ℝ) :=
  rat_majority_certificate_sound certificate1079 valid1079 x hx0 hx1

end Cycle12.MajorityCertificates.Batch026
