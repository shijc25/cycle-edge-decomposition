import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch025

def certificate1000 : RatMajorityCertificate := ⟨0,(1000070194472483901/1000000000000000000),(2737749073/2352150000),(8670274557121934007/20000000000000000000),(10837843196402417509/25000000000000000000),(21592060841138727/31250000000000000),false⟩
theorem valid1000 : certificate1000.Valid := by decide +kernel
theorem bound1000 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1000.a certificate1000.b certificate1000.c x ≤ (certificate1000.bound:ℝ) :=
  rat_majority_certificate_sound certificate1000 valid1000 x hx0 hx1

def certificate1001 : RatMajorityCertificate := ⟨(200605687136333003/1000000000000000000),(799450425925765092620227281907515297/1000000000000000000000000000000000000),(2737749073/2352150000),(38962136577178655539/100000000000000000000),(1948106828858932777/5000000000000000000),(21592060841138727/31250000000000000),false⟩
theorem valid1001 : certificate1001.Valid := by decide +kernel
theorem bound1001 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1001.a certificate1001.b certificate1001.c x ≤ (certificate1001.bound:ℝ) :=
  rat_majority_certificate_sound certificate1001 valid1001 x hx0 hx1

def certificate1002 : RatMajorityCertificate := ⟨0,(1000070194472483901/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543682109588577781/1000000000000000000),false⟩
theorem valid1002 : certificate1002.Valid := by decide +kernel
theorem bound1002 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1002.a certificate1002.b certificate1002.c x ≤ (certificate1002.bound:ℝ) :=
  rat_majority_certificate_sound certificate1002 valid1002 x hx0 hx1

def certificate1003 : RatMajorityCertificate := ⟨(159802551284290093/1000000000000000000),(840256425932404825720658014843707207/1000000000000000000000000000000000000),1,(357789829863016341/1000000000000000000),(35778982986301634101/100000000000000000000),(543682109588577781/1000000000000000000),false⟩
theorem valid1003 : certificate1003.Valid := by decide +kernel
theorem bound1003 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1003.a certificate1003.b certificate1003.c x ≤ (certificate1003.bound:ℝ) :=
  rat_majority_certificate_sound certificate1003 valid1003 x hx0 hx1

def certificate1004 : RatMajorityCertificate := ⟨0,(1000076200349844867/1000000000000000000),(2736801107/2349780000),(8673850488775144937/20000000000000000000),(21684626221937862343/50000000000000000000),(345769600454738933/500000000000000000),false⟩
theorem valid1004 : certificate1004.Valid := by decide +kernel
theorem bound1004 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1004.a certificate1004.b certificate1004.c x ≤ (certificate1004.bound:ℝ) :=
  rat_majority_certificate_sound certificate1004 valid1004 x hx0 hx1

def certificate1005 : RatMajorityCertificate := ⟨(199667126531443943/1000000000000000000),(800393859113506708645878222443209419/1000000000000000000000000000000000000),(2736801107/2349780000),(9751315004014041397/25000000000000000000),(39005260016056165589/100000000000000000000),(345769600454738933/500000000000000000),false⟩
theorem valid1005 : certificate1005.Valid := by decide +kernel
theorem bound1005 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1005.a certificate1005.b certificate1005.c x ≤ (certificate1005.bound:ℝ) :=
  rat_majority_certificate_sound certificate1005 valid1005 x hx0 hx1

def certificate1006 : RatMajorityCertificate := ⟨0,(1000076200349844867/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543687358735687069/1000000000000000000),false⟩
theorem valid1006 : certificate1006.Valid := by decide +kernel
theorem bound1006 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1006.a certificate1006.b certificate1006.c x ≤ (certificate1006.bound:ℝ) :=
  rat_majority_certificate_sound certificate1006 valid1006 x hx0 hx1

def certificate1007 : RatMajorityCertificate := ⟨(1278597810225211/8000000000000000),(6721914362973097894057069817658063/8000000000000000000000000000000000),1,(35778452566658364017/100000000000000000000),(17889226283329182009/50000000000000000000),(543687358735687069/1000000000000000000),false⟩
theorem valid1007 : certificate1007.Valid := by decide +kernel
theorem bound1007 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1007.a certificate1007.b certificate1007.c x ≤ (certificate1007.bound:ℝ) :=
  rat_majority_certificate_sound certificate1007 valid1007 x hx0 hx1

def certificate1008 : RatMajorityCertificate := ⟨0,(1000082741165258953/1000000000000000000),(2735883743/2347060000),(43391485299334998101/100000000000000000000),(21695742649667499051/50000000000000000000),(346202269934224719/500000000000000000),false⟩
theorem valid1008 : certificate1008.Valid := by decide +kernel
theorem bound1008 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1008.a certificate1008.b certificate1008.c x ≤ (certificate1008.bound:ℝ) :=
  rat_majority_certificate_sound certificate1008 valid1008 x hx0 hx1

def certificate1009 : RatMajorityCertificate := ⟨(99860867230959163/500000000000000000),(400172240747151854343633896536863661/500000000000000000000000000000000000),(2735883743/2347060000),(3902694663168721611/10000000000000000000),(39026946631687216111/100000000000000000000),(346202269934224719/500000000000000000),false⟩
theorem valid1009 : certificate1009.Valid := by decide +kernel
theorem bound1009 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1009.a certificate1009.b certificate1009.c x ≤ (certificate1009.bound:ℝ) :=
  rat_majority_certificate_sound certificate1009 valid1009 x hx0 hx1

def certificate1010 : RatMajorityCertificate := ⟨0,(1000082741165258953/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135898046252602857/250000000000000000),false⟩
theorem valid1010 : certificate1010.Valid := by decide +kernel
theorem bound1010 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1010.a certificate1010.b certificate1010.c x ≤ (certificate1010.bound:ℝ) :=
  rat_majority_certificate_sound certificate1010 valid1010 x hx0 hx1

def certificate1011 : RatMajorityCertificate := ⟨(19873456120678127/125000000000000000),(105135242172062094545099184081978969/125000000000000000000000000000000000),1,(3579923669455375103/10000000000000000000),(35799236694553751031/100000000000000000000),(135898046252602857/250000000000000000),false⟩
theorem valid1011 : certificate1011.Valid := by decide +kernel
theorem bound1011 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1011.a certificate1011.b certificate1011.c x ≤ (certificate1011.bound:ℝ) :=
  rat_majority_certificate_sound certificate1011 valid1011 x hx0 hx1

def certificate1012 : RatMajorityCertificate := ⟨0,(500048480874086511/500000000000000000),(2732148311/2341320000),(2713795091460392311/6250000000000000000),(43420721463366276977/100000000000000000000),(693592506080164839/1000000000000000000),false⟩
theorem valid1012 : certificate1012.Valid := by decide +kernel
theorem bound1012 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1012.a certificate1012.b certificate1012.c x ≤ (certificate1012.bound:ℝ) :=
  rat_majority_certificate_sound certificate1012 valid1012 x hx0 hx1

def certificate1013 : RatMajorityCertificate := ⟨(200232336673332119/1000000000000000000),(399922605098718143806700661359053191/500000000000000000000000000000000000),(2732148311/2341320000),(4880503859122446789/12500000000000000000),(39044030872979574313/100000000000000000000),(693592506080164839/1000000000000000000),false⟩
theorem valid1013 : certificate1013.Valid := by decide +kernel
theorem bound1013 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1013.a certificate1013.b certificate1013.c x ≤ (certificate1013.bound:ℝ) :=
  rat_majority_certificate_sound certificate1013 valid1013 x hx0 hx1

def certificate1014 : RatMajorityCertificate := ⟨0,(500048480874086511/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543635578243001341/1000000000000000000),false⟩
theorem valid1014 : certificate1014.Valid := by decide +kernel
theorem bound1014 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1014.a certificate1014.b certificate1014.c x ≤ (certificate1014.bound:ℝ) :=
  rat_majority_certificate_sound certificate1014 valid1014 x hx0 hx1

def certificate1015 : RatMajorityCertificate := ⟨(39826178019397577/250000000000000000),(105097100400900933864026921598216153/125000000000000000000000000000000000),1,(35791423487735201739/100000000000000000000),(1789571174386760087/5000000000000000000),(543635578243001341/1000000000000000000),false⟩
theorem valid1015 : certificate1015.Valid := by decide +kernel
theorem bound1015 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1015.a certificate1015.b certificate1015.c x ≤ (certificate1015.bound:ℝ) :=
  rat_majority_certificate_sound certificate1015 valid1015 x hx0 hx1

def certificate1016 : RatMajorityCertificate := ⟨0,(200022362889727213/200000000000000000),(2730549527/2336100000),(5433149286908348373/12500000000000000000),(8693038859053357397/20000000000000000000),(173832280814924241/250000000000000000),false⟩
theorem valid1016 : certificate1016.Valid := by decide +kernel
theorem bound1016 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1016.a certificate1016.b certificate1016.c x ≤ (certificate1016.bound:ℝ) :=
  rat_majority_certificate_sound certificate1016 valid1016 x hx0 hx1

def certificate1017 : RatMajorityCertificate := ⟨(4006637743218007/20000000000000000),(3199030109152914386153498980475509/4000000000000000000000000000000000),(2730549527/2336100000),(9771921990184812397/25000000000000000000),(39087687960739249589/100000000000000000000),(173832280814924241/250000000000000000),false⟩
theorem valid1017 : certificate1017.Valid := by decide +kernel
theorem bound1017 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1017.a certificate1017.b certificate1017.c x ≤ (certificate1017.bound:ℝ) :=
  rat_majority_certificate_sound certificate1017 valid1017 x hx0 hx1

def certificate1018 : RatMajorityCertificate := ⟨0,(200022362889727213/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(67960397724050811/125000000000000000),false⟩
theorem valid1018 : certificate1018.Valid := by decide +kernel
theorem bound1018 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1018.a certificate1018.b certificate1018.c x ≤ (certificate1018.bound:ℝ) :=
  rat_majority_certificate_sound certificate1018 valid1018 x hx0 hx1

def certificate1019 : RatMajorityCertificate := ⟨(39913777946144021/250000000000000000),(42021942545788192965078814099056527/50000000000000000000000000000000000),1,(8945695191786694111/25000000000000000000),(7156556153429355289/20000000000000000000),(67960397724050811/125000000000000000),false⟩
theorem valid1019 : certificate1019.Valid := by decide +kernel
theorem bound1019 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1019.a certificate1019.b certificate1019.c x ≤ (certificate1019.bound:ℝ) :=
  rat_majority_certificate_sound certificate1019 valid1019 x hx0 hx1

def certificate1020 : RatMajorityCertificate := ⟨0,(1000127616557169707/1000000000000000000),(2727400931/2331000000),(5436631909464940197/12500000000000000000),(43493055275719521577/100000000000000000000),(87056417665576471/125000000000000000),false⟩
theorem valid1020 : certificate1020.Valid := by decide +kernel
theorem bound1020 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1020.a certificate1020.b certificate1020.c x ≤ (certificate1020.bound:ℝ) :=
  rat_majority_certificate_sound certificate1020 valid1020 x hx0 hx1

def certificate1021 : RatMajorityCertificate := ⟨(100335893682786819/500000000000000000),(399715110074485691492485013114307967/500000000000000000000000000000000000),(2727400931/2331000000),(977695458677691517/2500000000000000000),(39107818347107660681/100000000000000000000),(87056417665576471/125000000000000000),false⟩
theorem valid1021 : certificate1021.Valid := by decide +kernel
theorem bound1021 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1021.a certificate1021.b certificate1021.c x ≤ (certificate1021.bound:ℝ) :=
  rat_majority_certificate_sound certificate1021 valid1021 x hx0 hx1

def certificate1022 : RatMajorityCertificate := ⟨0,(1000127616557169707/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543600651388389993/1000000000000000000),false⟩
theorem valid1022 : certificate1022.Valid := by decide +kernel
theorem bound1022 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1022.a certificate1022.b certificate1022.c x ≤ (certificate1022.bound:ℝ) :=
  rat_majority_certificate_sound certificate1022 valid1022 x hx0 hx1

def certificate1023 : RatMajorityCertificate := ⟨(158890663557772909/1000000000000000000),(841216675919947144792925146719932337/1000000000000000000000000000000000000),1,(35801788765619052903/100000000000000000000),(4475223595702381613/12500000000000000000),(543600651388389993/1000000000000000000),false⟩
theorem valid1023 : certificate1023.Valid := by decide +kernel
theorem bound1023 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1023.a certificate1023.b certificate1023.c x ≤ (certificate1023.bound:ℝ) :=
  rat_majority_certificate_sound certificate1023 valid1023 x hx0 hx1

def certificate1024 : RatMajorityCertificate := ⟨0,(125018043099631533/125000000000000000),(2725756103/2326020000),(8706902333237904299/20000000000000000000),(5441813958273690187/12500000000000000000),(697994874536660813/1000000000000000000),false⟩
theorem valid1024 : certificate1024.Valid := by decide +kernel
theorem bound1024 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1024.a certificate1024.b certificate1024.c x ≤ (certificate1024.bound:ℝ) :=
  rat_majority_certificate_sound certificate1024 valid1024 x hx0 hx1

def certificate1025 : RatMajorityCertificate := ⟨(49989390806989039/250000000000000000),(25004934960475403231932897930233213/31250000000000000000000000000000000),(2725756103/2326020000),(39169616330333788441/100000000000000000000),(19584808165166894221/50000000000000000000),(697994874536660813/1000000000000000000),false⟩
theorem valid1025 : certificate1025.Valid := by decide +kernel
theorem bound1025 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1025.a certificate1025.b certificate1025.c x ≤ (certificate1025.bound:ℝ) :=
  rat_majority_certificate_sound certificate1025 valid1025 x hx0 hx1

def certificate1026 : RatMajorityCertificate := ⟨0,(125018043099631533/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543636992198291603/1000000000000000000),false⟩
theorem valid1026 : certificate1026.Valid := by decide +kernel
theorem bound1026 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1026.a certificate1026.b certificate1026.c x ≤ (certificate1026.bound:ℝ) :=
  rat_majority_certificate_sound certificate1026 valid1026 x hx0 hx1

def certificate1027 : RatMajorityCertificate := ⟨(79569076571717029/500000000000000000),(52561451305574965306411200958524543/62500000000000000000000000000000000),1,(35795710398118437287/100000000000000000000),(4474463799764804661/12500000000000000000),(543636992198291603/1000000000000000000),false⟩
theorem valid1027 : certificate1027.Valid := by decide +kernel
theorem bound1027 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1027.a certificate1027.b certificate1027.c x ≤ (certificate1027.bound:ℝ) :=
  rat_majority_certificate_sound certificate1027 valid1027 x hx0 hx1

def certificate1028 : RatMajorityCertificate := ⟨0,(1000161976135265881/1000000000000000000),(680634763/580287500),(1088980286222678099/2500000000000000000),(43559211448907123961/100000000000000000000),(10920542083584767/15625000000000000),false⟩
theorem valid1028 : certificate1028.Valid := by decide +kernel
theorem bound1028 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1028.a certificate1028.b certificate1028.c x ≤ (certificate1028.bound:ℝ) :=
  rat_majority_certificate_sound certificate1028 valid1028 x hx0 hx1

def certificate1029 : RatMajorityCertificate := ⟨(3989460815626963/20000000000000000),(16013132509633644695100352282450597/20000000000000000000000000000000000),(680634763/580287500),(7841597967851396793/20000000000000000000),(19603994919628491983/50000000000000000000),(10920542083584767/15625000000000000),false⟩
theorem valid1029 : certificate1029.Valid := by decide +kernel
theorem bound1029 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1029.a certificate1029.b certificate1029.c x ≤ (certificate1029.bound:ℝ) :=
  rat_majority_certificate_sound certificate1029 valid1029 x hx0 hx1

def certificate1030 : RatMajorityCertificate := ⟨0,(1000161976135265881/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(33974645824764641/62500000000000000),false⟩
theorem valid1030 : certificate1030.Valid := by decide +kernel
theorem bound1030 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1030.a certificate1030.b certificate1030.c x ≤ (certificate1030.bound:ℝ) :=
  rat_majority_certificate_sound certificate1030 valid1030 x hx0 hx1

def certificate1031 : RatMajorityCertificate := ⟨(158706868430048851/1000000000000000000),(841429400980028580028368779296447269/1000000000000000000000000000000000000),1,(8951613947635188809/25000000000000000000),(35806455790540755237/100000000000000000000),(33974645824764641/62500000000000000),false⟩
theorem valid1031 : certificate1031.Valid := by decide +kernel
theorem bound1031 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1031.a certificate1031.b certificate1031.c x ≤ (certificate1031.bound:ℝ) :=
  rat_majority_certificate_sound certificate1031 valid1031 x hx0 hx1

def certificate1032 : RatMajorityCertificate := ⟨0,(125022560732308487/125000000000000000),(1360716893/1158200000),(21801771451303363411/50000000000000000000),(43603542902606726823/100000000000000000000),(700655726226355661/1000000000000000000),false⟩
theorem valid1032 : certificate1032.Valid := by decide +kernel
theorem bound1032 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1032.a certificate1032.b certificate1032.c x ≤ (certificate1032.bound:ℝ) :=
  rat_majority_certificate_sound certificate1032 valid1032 x hx0 hx1

def certificate1033 : RatMajorityCertificate := ⟨(99759555419766637/500000000000000000),(50039085290058374846427324165451781/62500000000000000000000000000000000),(1360716893/1158200000),(1962646811789407243/5000000000000000000),(39252936235788144861/100000000000000000000),(700655726226355661/1000000000000000000),false⟩
theorem valid1033 : certificate1033.Valid := by decide +kernel
theorem bound1033 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1033.a certificate1033.b certificate1033.c x ≤ (certificate1033.bound:ℝ) :=
  rat_majority_certificate_sound certificate1033 valid1033 x hx0 hx1

def certificate1034 : RatMajorityCertificate := ⟨0,(125022560732308487/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543589849613271307/1000000000000000000),false⟩
theorem valid1034 : certificate1034.Valid := by decide +kernel
theorem bound1034 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1034.a certificate1034.b certificate1034.c x ≤ (certificate1034.bound:ℝ) :=
  rat_majority_certificate_sound certificate1034 valid1034 x hx0 hx1

def certificate1035 : RatMajorityCertificate := ⟨(79299277175024103/500000000000000000),(52597081669511628393000784943537839/62500000000000000000000000000000000),1,(4476149943370369691/12500000000000000000),(35809199546962957529/100000000000000000000),(543589849613271307/1000000000000000000),false⟩
theorem valid1035 : certificate1035.Valid := by decide +kernel
theorem bound1035 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1035.a certificate1035.b certificate1035.c x ≤ (certificate1035.bound:ℝ) :=
  rat_majority_certificate_sound certificate1035 valid1035 x hx0 hx1

def certificate1036 : RatMajorityCertificate := ⟨0,(125024981386235339/125000000000000000),(135920921/115587500),(21813926604427624453/50000000000000000000),(43627853208855248907/100000000000000000000),(701556848750229649/1000000000000000000),false⟩
theorem valid1036 : certificate1036.Valid := by decide +kernel
theorem bound1036 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1036.a certificate1036.b certificate1036.c x ≤ (certificate1036.bound:ℝ) :=
  rat_majority_certificate_sound certificate1036 valid1036 x hx0 hx1

def certificate1037 : RatMajorityCertificate := ⟨(24868791231777543/125000000000000000),(12518902512428257453272490106807923/15625000000000000000000000000000000),(135920921/115587500),(19646545653064027537/50000000000000000000),(1571723652245122203/4000000000000000000),(701556848750229649/1000000000000000000),false⟩
theorem valid1037 : certificate1037.Valid := by decide +kernel
theorem bound1037 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1037.a certificate1037.b certificate1037.c x ≤ (certificate1037.bound:ℝ) :=
  rat_majority_certificate_sound certificate1037 valid1037 x hx0 hx1

def certificate1038 : RatMajorityCertificate := ⟨0,(125024981386235339/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543605040794362117/1000000000000000000),false⟩
theorem valid1038 : certificate1038.Valid := by decide +kernel
theorem bound1038 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1038.a certificate1038.b certificate1038.c x ≤ (certificate1038.bound:ℝ) :=
  rat_majority_certificate_sound certificate1038 valid1038 x hx0 hx1

def certificate1039 : RatMajorityCertificate := ⟨(158655358717666389/1000000000000000000),(105189098115732608092451907955679129/125000000000000000000000000000000000),1,(1790392839027426881/5000000000000000000),(35807856780548537621/100000000000000000000),(543605040794362117/1000000000000000000),false⟩
theorem valid1039 : certificate1039.Valid := by decide +kernel
theorem bound1039 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1039.a certificate1039.b certificate1039.c x ≤ (certificate1039.bound:ℝ) :=
  rat_majority_certificate_sound certificate1039 valid1039 x hx0 hx1

end Cycle12.MajorityCertificates.Batch025
