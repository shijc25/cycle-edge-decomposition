import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch029

def certificate1160 : RatMajorityCertificate := ⟨0,(1001058441422900177/1000000000000000000),(2614303031/2211780000),(21883450617426315537/50000000000000000000),(1750676049394105243/4000000000000000000),(176072777729745311/250000000000000000),false⟩
theorem valid1160 : certificate1160.Valid := by decide +kernel
theorem bound1160 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1160.a certificate1160.b certificate1160.c x ≤ (certificate1160.bound:ℝ) :=
  rat_majority_certificate_sound certificate1160 valid1160 x hx0 hx1

def certificate1161 : RatMajorityCertificate := ⟨(4132385862153463/25000000000000000),(20889701285047131138931819896137049/25000000000000000000000000000000000),(2614303031/2211780000),(20143530823669564497/50000000000000000000),(8057412329467825799/20000000000000000000),(176072777729745311/250000000000000000),false⟩
theorem valid1161 : certificate1161.Valid := by decide +kernel
theorem bound1161 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1161.a certificate1161.b certificate1161.c x ≤ (certificate1161.bound:ℝ) :=
  rat_majority_certificate_sound certificate1161 valid1161 x hx0 hx1

def certificate1162 : RatMajorityCertificate := ⟨0,(1001058441422900177/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270931957883717347/500000000000000000),false⟩
theorem valid1162 : certificate1162.Valid := by decide +kernel
theorem bound1162 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1162.a certificate1162.b certificate1162.c x ≤ (certificate1162.bound:ℝ) :=
  rat_majority_certificate_sound certificate1162 valid1162 x hx0 hx1

def certificate1163 : RatMajorityCertificate := ⟨(70001731238496887/500000000000000000),(430453396740935651085360070273751001/500000000000000000000000000000000000),1,(7252882734838614231/20000000000000000000),(9066103418548267789/25000000000000000000),(270931957883717347/500000000000000000),false⟩
theorem valid1163 : certificate1163.Valid := by decide +kernel
theorem bound1163 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1163.a certificate1163.b certificate1163.c x ≤ (certificate1163.bound:ℝ) :=
  rat_majority_certificate_sound certificate1163 valid1163 x hx0 hx1

def certificate1164 : RatMajorityCertificate := ⟨0,(1001074599661654149/1000000000000000000),(2611196259/2210710000),(43747883511979882147/100000000000000000000),(10936970877994970537/25000000000000000000),(703484329590074171/1000000000000000000),false⟩
theorem valid1164 : certificate1164.Valid := by decide +kernel
theorem bound1164 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1164.a certificate1164.b certificate1164.c x ≤ (certificate1164.bound:ℝ) :=
  rat_majority_certificate_sound certificate1164 valid1164 x hx0 hx1

def certificate1165 : RatMajorityCertificate := ⟨(41148370216171769/250000000000000000),(209076061674529850405086291144480419/250000000000000000000000000000000000),(2611196259/2210710000),(40284545636056454293/100000000000000000000),(20142272818028227147/50000000000000000000),(703484329590074171/1000000000000000000),false⟩
theorem valid1165 : certificate1165.Valid := by decide +kernel
theorem bound1165 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1165.a certificate1165.b certificate1165.c x ≤ (certificate1165.bound:ℝ) :=
  rat_majority_certificate_sound certificate1165 valid1165 x hx0 hx1

def certificate1166 : RatMajorityCertificate := ⟨0,(1001074599661654149/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(541851220863881377/1000000000000000000),false⟩
theorem valid1166 : certificate1166.Valid := by decide +kernel
theorem bound1166 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1166.a certificate1166.b certificate1166.c x ≤ (certificate1166.bound:ℝ) :=
  rat_majority_certificate_sound certificate1166 valid1166 x hx0 hx1

def certificate1167 : RatMajorityCertificate := ⟨(27964655969106741/200000000000000000),(172220213153381412017911049993481591/200000000000000000000000000000000000),1,(18134384029782706877/50000000000000000000),(7253753611913082751/20000000000000000000),(541851220863881377/1000000000000000000),false⟩
theorem valid1167 : certificate1167.Valid := by decide +kernel
theorem bound1167 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1167.a certificate1167.b certificate1167.c x ≤ (certificate1167.bound:ℝ) :=
  rat_majority_certificate_sound certificate1167 valid1167 x hx0 hx1

def certificate1168 : RatMajorityCertificate := ⟨0,(250272687928524241/250000000000000000),(2608086479/2209650000),(43728678945345649607/100000000000000000000),(5466084868168206201/12500000000000000000),(702656229126413793/1000000000000000000),false⟩
theorem valid1168 : certificate1168.Valid := by decide +kernel
theorem bound1168 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1168.a certificate1168.b certificate1168.c x ≤ (certificate1168.bound:ℝ) :=
  rat_majority_certificate_sound certificate1168 valid1168 x hx0 hx1

def certificate1169 : RatMajorityCertificate := ⟨(16372765439347007/100000000000000000),(20929612777523803530061479789703313/25000000000000000000000000000000000),(2608086479/2209650000),(402857971262650562225963/1000000000000000000000000),(100714492815662640556491/250000000000000000000000),(702656229126413793/1000000000000000000),false⟩
theorem valid1169 : certificate1169.Valid := by decide +kernel
theorem bound1169 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1169.a certificate1169.b certificate1169.c x ≤ (certificate1169.bound:ℝ) :=
  rat_majority_certificate_sound certificate1169 valid1169 x hx0 hx1

def certificate1170 : RatMajorityCertificate := ⟨0,(250272687928524241/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(541763499188655521/1000000000000000000),false⟩
theorem valid1170 : certificate1170.Valid := by decide +kernel
theorem bound1170 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1170.a certificate1170.b certificate1170.c x ≤ (certificate1170.bound:ℝ) :=
  rat_majority_certificate_sound certificate1170 valid1170 x hx0 hx1

def certificate1171 : RatMajorityCertificate := ⟨(69483015016537663/500000000000000000),(107746643030695226363667283015011217/125000000000000000000000000000000000),1,(18144645234841098669/50000000000000000000),(36289290469682197339/100000000000000000000),(541763499188655521/1000000000000000000),false⟩
theorem valid1171 : certificate1171.Valid := by decide +kernel
theorem bound1171 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1171.a certificate1171.b certificate1171.c x ≤ (certificate1171.bound:ℝ) :=
  rat_majority_certificate_sound certificate1171 valid1171 x hx0 hx1

def certificate1172 : RatMajorityCertificate := ⟨0,(20022137679862257/20000000000000000),(1303102279/1104310000),(43721785146955370557/100000000000000000000),(21860892573477685279/50000000000000000000),(70264293069667101/100000000000000000),false⟩
theorem valid1172 : certificate1172.Valid := by decide +kernel
theorem bound1172 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1172.a certificate1172.b certificate1172.c x ≤ (certificate1172.bound:ℝ) :=
  rat_majority_certificate_sound certificate1172 valid1172 x hx0 hx1

def certificate1173 : RatMajorityCertificate := ⟨(166509184678675083/1000000000000000000),(16688267859264213402813767301957669/20000000000000000000000000000000000),(1303102279/1104310000),(40211066001768308007/100000000000000000000),(5026383250221038501/12500000000000000000),(70264293069667101/100000000000000000),false⟩
theorem valid1173 : certificate1173.Valid := by decide +kernel
theorem bound1173 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1173.a certificate1173.b certificate1173.c x ≤ (certificate1173.bound:ℝ) :=
  rat_majority_certificate_sound certificate1173 valid1173 x hx0 hx1

def certificate1174 : RatMajorityCertificate := ⟨0,(20022137679862257/20000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135437738085712947/250000000000000000),false⟩
theorem valid1174 : certificate1174.Valid := by decide +kernel
theorem bound1174 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1174.a certificate1174.b certificate1174.c x ≤ (certificate1174.bound:ℝ) :=
  rat_majority_certificate_sound certificate1174 valid1174 x hx0 hx1

def certificate1175 : RatMajorityCertificate := ⟨(34696677133738987/250000000000000000),(4310832773360113703500702449286341/5000000000000000000000000000000000),1,(9073403904161789617/25000000000000000000),(36293615616647158469/100000000000000000000),(135437738085712947/250000000000000000),false⟩
theorem valid1175 : certificate1175.Valid := by decide +kernel
theorem bound1175 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1175.a certificate1175.b certificate1175.c x ≤ (certificate1175.bound:ℝ) :=
  rat_majority_certificate_sound certificate1175 valid1175 x hx0 hx1

def certificate1176 : RatMajorityCertificate := ⟨0,(12514037597092049/12500000000000000),(2601879037/2207590000),(43689560238170481791/100000000000000000000),(341324689360706889/781250000000000000),(700956362445595957/1000000000000000000),false⟩
theorem valid1176 : certificate1176.Valid := by decide +kernel
theorem bound1176 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1176.a certificate1176.b certificate1176.c x ≤ (certificate1176.bound:ℝ) :=
  rat_majority_certificate_sound certificate1176 valid1176 x hx0 hx1

def certificate1177 : RatMajorityCertificate := ⟨(161794557606517229/1000000000000000000),(10489334420199217036832618982587779/12500000000000000000000000000000000),(2601879037/2207590000),(2014617994796441659/5000000000000000000),(40292359895928833181/100000000000000000000),(700956362445595957/1000000000000000000),false⟩
theorem valid1177 : certificate1177.Valid := by decide +kernel
theorem bound1177 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1177.a certificate1177.b certificate1177.c x ≤ (certificate1177.bound:ℝ) :=
  rat_majority_certificate_sound certificate1177 valid1177 x hx0 hx1

def certificate1178 : RatMajorityCertificate := ⟨0,(12514037597092049/12500000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(541669420172137427/1000000000000000000),false⟩
theorem valid1178 : certificate1178.Valid := by decide +kernel
theorem bound1178 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1178.a certificate1178.b certificate1178.c x ≤ (certificate1178.bound:ℝ) :=
  rat_majority_certificate_sound certificate1178 valid1178 x hx0 hx1

def certificate1179 : RatMajorityCertificate := ⟨(8623947953786319/62500000000000000),(674206940889206022244566480122369/781250000000000000000000000000000),1,(36312818973569122963/100000000000000000000),(9078204743392280741/25000000000000000000),(541669420172137427/1000000000000000000),false⟩
theorem valid1179 : certificate1179.Valid := by decide +kernel
theorem bound1179 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1179.a certificate1179.b certificate1179.c x ≤ (certificate1179.bound:ℝ) :=
  rat_majority_certificate_sound certificate1179 valid1179 x hx0 hx1

def certificate1180 : RatMajorityCertificate := ⟨0,(1001139104212702707/1000000000000000000),(2598819493/2206590000),(21835020581949506737/50000000000000000000),(1746801646555960539/4000000000000000000),(87513954149018631/125000000000000000),false⟩
theorem valid1180 : certificate1180.Valid := by decide +kernel
theorem bound1180 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1180.a certificate1180.b certificate1180.c x ≤ (certificate1180.bound:ℝ) :=
  rat_majority_certificate_sound certificate1180 valid1180 x hx0 hx1

def certificate1181 : RatMajorityCertificate := ⟨(160854842102593353/1000000000000000000),(840101031681836661151945110096693429/1000000000000000000000000000000000000),(2598819493/2206590000),(40294983719086947631/100000000000000000000),(2518436482442934227/6250000000000000000),(87513954149018631/125000000000000000),false⟩
theorem valid1181 : certificate1181.Valid := by decide +kernel
theorem bound1181 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1181.a certificate1181.b certificate1181.c x ≤ (certificate1181.bound:ℝ) :=
  rat_majority_certificate_sound certificate1181 valid1181 x hx0 hx1

def certificate1182 : RatMajorityCertificate := ⟨0,(1001139104212702707/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(541657130056756421/1000000000000000000),false⟩
theorem valid1182 : certificate1182.Valid := by decide +kernel
theorem bound1182 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1182.a certificate1182.b certificate1182.c x ≤ (certificate1182.bound:ℝ) :=
  rat_majority_certificate_sound certificate1182 valid1182 x hx0 hx1

def certificate1183 : RatMajorityCertificate := ⟨(137805767374759209/1000000000000000000),(863176361707792180525167696772521237/1000000000000000000000000000000000000),1,(9079272535945430281/25000000000000000000),(290536721150253769/800000000000000000),(541657130056756421/1000000000000000000),false⟩
theorem valid1183 : certificate1183.Valid := by decide +kernel
theorem bound1183 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1183.a certificate1183.b certificate1183.c x ≤ (certificate1183.bound:ℝ) :=
  rat_majority_certificate_sound certificate1183 valid1183 x hx0 hx1

def certificate1184 : RatMajorityCertificate := ⟨0,(500589138267680531/500000000000000000),(2592284867/2203790000),(21818185260919186089/50000000000000000000),(43636370521838372179/100000000000000000000),(698739681585178127/1000000000000000000),false⟩
theorem valid1184 : certificate1184.Valid := by decide +kernel
theorem bound1184 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1184.a certificate1184.b certificate1184.c x ≤ (certificate1184.bound:ℝ) :=
  rat_majority_certificate_sound certificate1184 valid1184 x hx0 hx1

def certificate1185 : RatMajorityCertificate := ⟨(8004859233844407/50000000000000000),(21022311327559769453453109962859883/25000000000000000000000000000000000),(2592284867/2203790000),(40278669537006614839/100000000000000000000),(1006966738425165371/2500000000000000000),(698739681585178127/1000000000000000000),false⟩
theorem valid1185 : certificate1185.Valid := by decide +kernel
theorem bound1185 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1185.a certificate1185.b certificate1185.c x ≤ (certificate1185.bound:ℝ) :=
  rat_majority_certificate_sound certificate1185 valid1185 x hx0 hx1

def certificate1186 : RatMajorityCertificate := ⟨0,(500589138267680531/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(67708500607370811/125000000000000000),false⟩
theorem valid1186 : certificate1186.Valid := by decide +kernel
theorem bound1186 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1186.a certificate1186.b certificate1186.c x ≤ (certificate1186.bound:ℝ) :=
  rat_majority_certificate_sound certificate1186 valid1186 x hx0 hx1

def certificate1187 : RatMajorityCertificate := ⟨(13774337461167837/100000000000000000),(43163630106873815137066895511718553/50000000000000000000000000000000000),1,(36318686657262647489/100000000000000000000),(3631868665726264749/10000000000000000000),(67708500607370811/125000000000000000),false⟩
theorem valid1187 : certificate1187.Valid := by decide +kernel
theorem bound1187 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1187.a certificate1187.b certificate1187.c x ≤ (certificate1187.bound:ℝ) :=
  rat_majority_certificate_sound certificate1187 valid1187 x hx0 hx1

def certificate1188 : RatMajorityCertificate := ⟨0,(250296810885410091/250000000000000000),(2587448847/2203670000),(8717489421947698217/20000000000000000000),(21793723554869245543/50000000000000000000),(34824010613830009/50000000000000000),false⟩
theorem valid1188 : certificate1188.Valid := by decide +kernel
theorem bound1188 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1188.a certificate1188.b certificate1188.c x ≤ (certificate1188.bound:ℝ) :=
  rat_majority_certificate_sound certificate1188 valid1188 x hx0 hx1

def certificate1189 : RatMajorityCertificate := ⟨(39065301554912579/250000000000000000),(52796282325881052192749421930565311/62500000000000000000000000000000000),(2587448847/2203670000),(2016023153900188167/5000000000000000000),(40320463078003763341/100000000000000000000),(34824010613830009/50000000000000000),false⟩
theorem valid1189 : certificate1189.Valid := by decide +kernel
theorem bound1189 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1189.a certificate1189.b certificate1189.c x ≤ (certificate1189.bound:ℝ) :=
  rat_majority_certificate_sound certificate1189 valid1189 x hx0 hx1

def certificate1190 : RatMajorityCertificate := ⟨0,(250296810885410091/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270765805377105911/500000000000000000),false⟩
theorem valid1190 : certificate1190.Valid := by decide +kernel
theorem bound1190 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1190.a certificate1190.b certificate1190.c x ≤ (certificate1190.bound:ℝ) :=
  rat_majority_certificate_sound certificate1190 valid1190 x hx0 hx1

def certificate1191 : RatMajorityCertificate := ⟨(6823418072256363/50000000000000000),(10806960761446864172610419060840967/12500000000000000000000000000000000),1,(9087259415490624887/25000000000000000000),(36349037661962499549/100000000000000000000),(270765805377105911/500000000000000000),false⟩
theorem valid1191 : certificate1191.Valid := by decide +kernel
theorem bound1191 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1191.a certificate1191.b certificate1191.c x ≤ (certificate1191.bound:ℝ) :=
  rat_majority_certificate_sound certificate1191 valid1191 x hx0 hx1

def certificate1192 : RatMajorityCertificate := ⟨0,(1001203224296483923/1000000000000000000),(646209473/550682500),(5446464088609555277/12500000000000000000),(43571712708876442217/100000000000000000000),(17397661652873903/25000000000000000),false⟩
theorem valid1192 : certificate1192.Valid := by decide +kernel
theorem bound1192 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1192.a certificate1192.b certificate1192.c x ≤ (certificate1192.bound:ℝ) :=
  rat_majority_certificate_sound certificate1192 valid1192 x hx0 hx1

def certificate1193 : RatMajorityCertificate := ⟨(31331796642584611/200000000000000000),(168871149037739322390782421671291047/200000000000000000000000000000000000),(646209473/550682500),(2014738704008033781/5000000000000000000),(40294774080160675621/100000000000000000000),(17397661652873903/25000000000000000),false⟩
theorem valid1193 : certificate1193.Valid := by decide +kernel
theorem bound1193 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1193.a certificate1193.b certificate1193.c x ≤ (certificate1193.bound:ℝ) :=
  rat_majority_certificate_sound certificate1193 valid1193 x hx0 hx1

def certificate1194 : RatMajorityCertificate := ⟨0,(1001203224296483923/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(541453419687024859/1000000000000000000),false⟩
theorem valid1194 : certificate1194.Valid := by decide +kernel
theorem bound1194 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1194.a certificate1194.b certificate1194.c x ≤ (certificate1194.bound:ℝ) :=
  rat_majority_certificate_sound certificate1194 valid1194 x hx0 hx1

def certificate1195 : RatMajorityCertificate := ⟨(135690653335733567/1000000000000000000),(865349304669851024099168667973056659/1000000000000000000000000000000000000),1,(36367545197420995157/100000000000000000000),(18183772598710497579/50000000000000000000),(541453419687024859/1000000000000000000),false⟩
theorem valid1195 : certificate1195.Valid := by decide +kernel
theorem bound1195 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1195.a certificate1195.b certificate1195.c x ≤ (certificate1195.bound:ℝ) :=
  rat_majority_certificate_sound certificate1195 valid1195 x hx0 hx1

def certificate1196 : RatMajorityCertificate := ⟨0,(31288833269612019/31250000000000000),(23021617/19643125),(5442215648798185781/12500000000000000000),(43537725190385486249/100000000000000000000),(347263098407813301/500000000000000000),false⟩
theorem valid1196 : certificate1196.Valid := by decide +kernel
theorem bound1196 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1196.a certificate1196.b certificate1196.c x ≤ (certificate1196.bound:ℝ) :=
  rat_majority_certificate_sound certificate1196 valid1196 x hx0 hx1

def certificate1197 : RatMajorityCertificate := ⟨(155872858354732877/1000000000000000000),(26411753393292931203616909826351337/31250000000000000000000000000000000),(23021617/19643125),(1611148950029016771/4000000000000000000),(10069680937681354819/25000000000000000000),(347263098407813301/500000000000000000),false⟩
theorem valid1197 : certificate1197.Valid := by decide +kernel
theorem bound1197 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1197.a certificate1197.b certificate1197.c x ≤ (certificate1197.bound:ℝ) :=
  rat_majority_certificate_sound certificate1197 valid1197 x hx0 hx1

def certificate1198 : RatMajorityCertificate := ⟨0,(31288833269612019/31250000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(84603137347941/156250000000000),false⟩
theorem valid1198 : certificate1198.Valid := by decide +kernel
theorem bound1198 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1198.a certificate1198.b certificate1198.c x ≤ (certificate1198.bound:ℝ) :=
  rat_majority_certificate_sound certificate1198 valid1198 x hx0 hx1

def certificate1199 : RatMajorityCertificate := ⟨(8474247309842029/62500000000000000),(1690402768187645759026014990253449/1953125000000000000000000000000000),1,(9092522695567967859/25000000000000000000),(36370090782271871437/100000000000000000000),(84603137347941/156250000000000),false⟩
theorem valid1199 : certificate1199.Valid := by decide +kernel
theorem bound1199 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1199.a certificate1199.b certificate1199.c x ≤ (certificate1199.bound:ℝ) :=
  rat_majority_certificate_sound certificate1199 valid1199 x hx0 hx1

end Cycle12.MajorityCertificates.Batch029
