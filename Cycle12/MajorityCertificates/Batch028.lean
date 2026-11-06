import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch028

def certificate1120 : RatMajorityCertificate := ⟨0,(250189620573805721/250000000000000000),(1331165781/1117375000),(1759163777214557413/4000000000000000000),(21989547215181967663/50000000000000000000),(89265922304246939/125000000000000000),false⟩
theorem valid1120 : certificate1120.Valid := by decide +kernel
theorem bound1120 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1120.a certificate1120.b certificate1120.c x ≤ (certificate1120.bound:ℝ) :=
  rat_majority_certificate_sound certificate1120 valid1120 x hx0 hx1

def certificate1121 : RatMajorityCertificate := ⟨(91200336397223381/500000000000000000),(102277432727478098970643475467237299/125000000000000000000000000000000000),(1331165781/1117375000),(5010365127278062353/12500000000000000000),(1603316840728979953/4000000000000000000),(89265922304246939/125000000000000000),false⟩
theorem valid1121 : certificate1121.Valid := by decide +kernel
theorem bound1121 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1121.a certificate1121.b certificate1121.c x ≤ (certificate1121.bound:ℝ) :=
  rat_majority_certificate_sound certificate1121 valid1121 x hx0 hx1

def certificate1122 : RatMajorityCertificate := ⟨0,(250189620573805721/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(542695171675267371/1000000000000000000),false⟩
theorem valid1122 : certificate1122.Valid := by decide +kernel
theorem bound1122 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1122.a certificate1122.b certificate1122.c x ≤ (certificate1122.bound:ℝ) :=
  rat_majority_certificate_sound certificate1122 valid1122 x hx0 hx1

def certificate1123 : RatMajorityCertificate := ⟨(18575590360708237/125000000000000000),(26626282667445678359173219997576123/31250000000000000000000000000000000),1,(7211238055788558487/20000000000000000000),(9014047569735698109/25000000000000000000),(542695171675267371/1000000000000000000),false⟩
theorem valid1123 : certificate1123.Valid := by decide +kernel
theorem bound1123 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1123.a certificate1123.b certificate1123.c x ≤ (certificate1123.bound:ℝ) :=
  rat_majority_certificate_sound certificate1123 valid1123 x hx0 hx1

def certificate1124 : RatMajorityCertificate := ⟨0,(250197507141416213/250000000000000000),(166074073/139496875),(5495093057113688847/12500000000000000000),(43960744456909510777/100000000000000000000),(142650925546224317/200000000000000000),false⟩
theorem valid1124 : certificate1124.Valid := by decide +kernel
theorem bound1124 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1124.a certificate1124.b certificate1124.c x ≤ (certificate1124.bound:ℝ) :=
  rat_majority_certificate_sound certificate1124 valid1124 x hx0 hx1

def certificate1125 : RatMajorityCertificate := ⟨(180707520935090677/1000000000000000000),(204984935881751243524399018647053799/250000000000000000000000000000000000),(166074073/139496875),(40106441247836431389/100000000000000000000),(4010644124783643139/10000000000000000000),(142650925546224317/200000000000000000),false⟩
theorem valid1125 : certificate1125.Valid := by decide +kernel
theorem bound1125 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1125.a certificate1125.b certificate1125.c x ≤ (certificate1125.bound:ℝ) :=
  rat_majority_certificate_sound certificate1125 valid1125 x hx0 hx1

def certificate1126 : RatMajorityCertificate := ⟨0,(250197507141416213/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(542579069794660991/1000000000000000000),false⟩
theorem valid1126 : certificate1126.Valid := by decide +kernel
theorem bound1126 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1126.a certificate1126.b certificate1126.c x ≤ (certificate1126.bound:ℝ) :=
  rat_majority_certificate_sound certificate1126 valid1126 x hx0 hx1

def certificate1127 : RatMajorityCertificate := ⟨(5898277391930989/40000000000000000),(8532165985766941104165179778275343/10000000000000000000000000000000000),1,(18042073157767872667/50000000000000000000),(7216829263107149067/20000000000000000000),(542579069794660991/1000000000000000000),false⟩
theorem valid1127 : certificate1127.Valid := by decide +kernel
theorem bound1127 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1127.a certificate1127.b certificate1127.c x ≤ (certificate1127.bound:ℝ) :=
  rat_majority_certificate_sound certificate1127 valid1127 x hx0 hx1

def certificate1128 : RatMajorityCertificate := ⟨0,(1000821803921194051/1000000000000000000),(1326066993/1114615000),(43942334346541882831/100000000000000000000),(2746395896658867677/6250000000000000000),(712383108462862189/1000000000000000000),false⟩
theorem valid1128 : certificate1128.Valid := by decide +kernel
theorem bound1128 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1128.a certificate1128.b certificate1128.c x ≤ (certificate1128.bound:ℝ) :=
  rat_majority_certificate_sound certificate1128 valid1128 x hx0 hx1

def certificate1129 : RatMajorityCertificate := ⟨(1432313505770239/8000000000000000),(6573083844743892227596584660351811/8000000000000000000000000000000000),(1326066993/1114615000),(40129154672303483893/100000000000000000000),(20064577336151741947/50000000000000000000),(712383108462862189/1000000000000000000),false⟩
theorem valid1129 : certificate1129.Valid := by decide +kernel
theorem bound1129 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1129.a certificate1129.b certificate1129.c x ≤ (certificate1129.bound:ℝ) :=
  rat_majority_certificate_sound certificate1129 valid1129 x hx0 hx1

def certificate1130 : RatMajorityCertificate := ⟨0,(1000821803921194051/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135617496786760383/250000000000000000),false⟩
theorem valid1130 : certificate1130.Valid := by decide +kernel
theorem bound1130 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1130.a certificate1130.b certificate1130.c x ≤ (certificate1130.bound:ℝ) :=
  rat_majority_certificate_sound certificate1130 valid1130 x hx0 hx1

def certificate1131 : RatMajorityCertificate := ⟨(146366705190625249/1000000000000000000),(854334813998310892512421252650806301/1000000000000000000000000000000000000),1,(36110650161228734291/100000000000000000000),(9027662540307183573/25000000000000000000),(135617496786760383/250000000000000000),false⟩
theorem valid1131 : certificate1131.Valid := by decide +kernel
theorem bound1131 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1131.a certificate1131.b certificate1131.c x ≤ (certificate1131.bound:ℝ) :=
  rat_majority_certificate_sound certificate1131 valid1131 x hx0 hx1

def certificate1132 : RatMajorityCertificate := ⟨0,(1000853786179341187/1000000000000000000),(331147133/278321250),(21972223379763599899/50000000000000000000),(43944446759527199799/100000000000000000000),(356192691062841067/500000000000000000),false⟩
theorem valid1132 : certificate1132.Valid := by decide +kernel
theorem bound1132 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1132.a certificate1132.b certificate1132.c x ≤ (certificate1132.bound:ℝ) :=
  rat_majority_certificate_sound certificate1132 valid1132 x hx0 hx1

def certificate1133 : RatMajorityCertificate := ⟨(88977068541218831/500000000000000000),(411373857157052976351193290421707603/500000000000000000000000000000000000),(331147133/278321250),(8031699399730395853/20000000000000000000),(20079248499325989633/50000000000000000000),(356192691062841067/500000000000000000),false⟩
theorem valid1133 : certificate1133.Valid := by decide +kernel
theorem bound1133 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1133.a certificate1133.b certificate1133.c x ≤ (certificate1133.bound:ℝ) :=
  rat_majority_certificate_sound certificate1133 valid1133 x hx0 hx1

def certificate1134 : RatMajorityCertificate := ⟨0,(1000853786179341187/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135613221592827663/250000000000000000),false⟩
theorem valid1134 : certificate1134.Valid := by decide +kernel
theorem bound1134 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1134.a certificate1134.b certificate1134.c x ≤ (certificate1134.bound:ℝ) :=
  rat_majority_certificate_sound certificate1134 valid1134 x hx0 hx1

def certificate1135 : RatMajorityCertificate := ⟨(14608815886842183/100000000000000000),(85464089925991209878134427219108779/100000000000000000000000000000000000),1,(36117484947475976041/100000000000000000000),(18058742473737988021/50000000000000000000),(135613221592827663/250000000000000000),false⟩
theorem valid1135 : certificate1135.Valid := by decide +kernel
theorem bound1135 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1135.a certificate1135.b certificate1135.c x ≤ (certificate1135.bound:ℝ) :=
  rat_majority_certificate_sound certificate1135 valid1135 x hx0 hx1

def certificate1136 : RatMajorityCertificate := ⟨0,(500442971135576883/500000000000000000),(2644890537/2223980000),(2196608757702571551/5000000000000000000),(43932175154051431021/100000000000000000000),(142385851332866939/200000000000000000),false⟩
theorem valid1136 : certificate1136.Valid := by decide +kernel
theorem bound1136 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1136.a certificate1136.b certificate1136.c x ≤ (certificate1136.bound:ℝ) :=
  rat_majority_certificate_sound certificate1136 valid1136 x hx0 hx1

def certificate1137 : RatMajorityCertificate := ⟨(44529517413784621/250000000000000000),(102826258786106435490195868851483657/125000000000000000000000000000000000),(2644890537/2223980000),(40141818286383363743/100000000000000000000),(1254431821449480117/3125000000000000000),(142385851332866939/200000000000000000),false⟩
theorem valid1137 : certificate1137.Valid := by decide +kernel
theorem bound1137 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1137.a certificate1137.b certificate1137.c x ≤ (certificate1137.bound:ℝ) :=
  rat_majority_certificate_sound certificate1137 valid1137 x hx0 hx1

def certificate1138 : RatMajorityCertificate := ⟨0,(500442971135576883/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(542358579001953007/1000000000000000000),false⟩
theorem valid1138 : certificate1138.Valid := by decide +kernel
theorem bound1138 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1138.a certificate1138.b certificate1138.c x ≤ (certificate1138.bound:ℝ) :=
  rat_majority_certificate_sound certificate1138 valid1138 x hx0 hx1

def certificate1139 : RatMajorityCertificate := ⟨(145123365383360139/1000000000000000000),(427817002981934207546720963287933263/500000000000000000000000000000000000),1,(18070446744359354341/50000000000000000000),(36140893488718708683/100000000000000000000),(542358579001953007/1000000000000000000),false⟩
theorem valid1139 : certificate1139.Valid := by decide +kernel
theorem bound1139 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1139.a certificate1139.b certificate1139.c x ≤ (certificate1139.bound:ℝ) :=
  rat_majority_certificate_sound certificate1139 valid1139 x hx0 hx1

def certificate1140 : RatMajorityCertificate := ⟨0,(125114780321076651/125000000000000000),(2639465099/2221460000),(5488424341640900777/12500000000000000000),(43907394733127206217/100000000000000000000),(710647051426388659/1000000000000000000),false⟩
theorem valid1140 : certificate1140.Valid := by decide +kernel
theorem bound1140 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1140.a certificate1140.b certificate1140.c x ≤ (certificate1140.bound:ℝ) :=
  rat_majority_certificate_sound certificate1140 valid1140 x hx0 hx1

def certificate1141 : RatMajorityCertificate := ⟨(174717174775983307/1000000000000000000),(103255079380660344911768144556535143/125000000000000000000000000000000000),(2639465099/2221460000),(40200685442846957077/100000000000000000000),(20100342721423478539/50000000000000000000),(710647051426388659/1000000000000000000),false⟩
theorem valid1141 : certificate1141.Valid := by decide +kernel
theorem bound1141 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1141.a certificate1141.b certificate1141.c x ≤ (certificate1141.bound:ℝ) :=
  rat_majority_certificate_sound certificate1141 valid1141 x hx0 hx1

def certificate1142 : RatMajorityCertificate := ⟨0,(125114780321076651/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(542273192185609531/1000000000000000000),false⟩
theorem valid1142 : certificate1142.Valid := by decide +kernel
theorem bound1142 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1142.a certificate1142.b certificate1142.c x ≤ (certificate1142.bound:ℝ) :=
  rat_majority_certificate_sound certificate1142 valid1142 x hx0 hx1

def certificate1143 : RatMajorityCertificate := ⟨(144234786030146567/1000000000000000000),(107068876752257367845778695228492883/125000000000000000000000000000000000),1,(3616242325850494659/10000000000000000000),(36162423258504946591/100000000000000000000),(542273192185609531/1000000000000000000),false⟩
theorem valid1143 : certificate1143.Valid := by decide +kernel
theorem bound1143 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1143.a certificate1143.b certificate1143.c x ≤ (certificate1143.bound:ℝ) :=
  rat_majority_certificate_sound certificate1143 valid1143 x hx0 hx1

def certificate1144 : RatMajorityCertificate := ⟨0,(250237663267691597/250000000000000000),(2634786251/2219020000),(21944598958460499371/50000000000000000000),(43889197916920998743/100000000000000000000),(141961543097391603/200000000000000000),false⟩
theorem valid1144 : certificate1144.Valid := by decide +kernel
theorem bound1144 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1144.a certificate1144.b certificate1144.c x ≤ (certificate1144.bound:ℝ) :=
  rat_majority_certificate_sound certificate1144 valid1144 x hx0 hx1

def certificate1145 : RatMajorityCertificate := ⟨(34652440705482333/200000000000000000),(41376186864876181909893848623944199/50000000000000000000000000000000000),(2634786251/2219020000),(10054479406867145361/25000000000000000000),(8043583525493716289/20000000000000000000),(141961543097391603/200000000000000000),false⟩
theorem valid1145 : certificate1145.Valid := by decide +kernel
theorem bound1145 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1145.a certificate1145.b certificate1145.c x ≤ (certificate1145.bound:ℝ) :=
  rat_majority_certificate_sound certificate1145 valid1145 x hx0 hx1

def certificate1146 : RatMajorityCertificate := ⟨0,(250237663267691597/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(542267065774470489/1000000000000000000),false⟩
theorem valid1146 : certificate1146.Valid := by decide +kernel
theorem bound1146 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1146.a certificate1146.b certificate1146.c x ≤ (certificate1146.bound:ℝ) :=
  rat_majority_certificate_sound certificate1146 valid1146 x hx0 hx1

def certificate1147 : RatMajorityCertificate := ⟨(36012587307162941/250000000000000000),(53547710120954714725596739784493223/62500000000000000000000000000000000),1,(36166963826745903729/100000000000000000000),(3616696382674590373/10000000000000000000),(542267065774470489/1000000000000000000),false⟩
theorem valid1147 : certificate1147.Valid := by decide +kernel
theorem bound1147 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1147.a certificate1147.b certificate1147.c x ≤ (certificate1147.bound:ℝ) :=
  rat_majority_certificate_sound certificate1147 valid1147 x hx0 hx1

def certificate1148 : RatMajorityCertificate := ⟨0,(1000983152417468819/1000000000000000000),(525638231/443328000),(43850572075368137027/100000000000000000000),(10962643018842034257/25000000000000000000),(5532134810859069/7812500000000000),false⟩
theorem valid1148 : certificate1148.Valid := by decide +kernel
theorem bound1148 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1148.a certificate1148.b certificate1148.c x ≤ (certificate1148.bound:ℝ) :=
  rat_majority_certificate_sound certificate1148 valid1148 x hx0 hx1

def certificate1149 : RatMajorityCertificate := ⟨(171328229618787477/1000000000000000000),(829486481035550978174096467764820337/1000000000000000000000000000000000000),(525638231/443328000),(40225713763024105813/100000000000000000000),(20112856881512052907/50000000000000000000),(5532134810859069/7812500000000000),false⟩
theorem valid1149 : certificate1149.Valid := by decide +kernel
theorem bound1149 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1149.a certificate1149.b certificate1149.c x ≤ (certificate1149.bound:ℝ) :=
  rat_majority_certificate_sound certificate1149 valid1149 x hx0 hx1

def certificate1150 : RatMajorityCertificate := ⟨0,(1000983152417468819/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135540766362372857/250000000000000000),false⟩
theorem valid1150 : certificate1150.Valid := by decide +kernel
theorem bound1150 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1150.a certificate1150.b certificate1150.c x ≤ (certificate1150.bound:ℝ) :=
  rat_majority_certificate_sound certificate1150 valid1150 x hx0 hx1

def certificate1151 : RatMajorityCertificate := ⟨(71495912868570377/500000000000000000),(428925371960588157488142718495425237/500000000000000000000000000000000000),1,(3619253708370133909/10000000000000000000),(36192537083701339091/100000000000000000000),(135540766362372857/250000000000000000),false⟩
theorem valid1151 : certificate1151.Valid := by decide +kernel
theorem bound1151 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1151.a certificate1151.b certificate1151.c x ≤ (certificate1151.bound:ℝ) :=
  rat_majority_certificate_sound certificate1151 valid1151 x hx0 hx1

def certificate1152 : RatMajorityCertificate := ⟨0,(1001015706636243659/1000000000000000000),(163976869/138395625),(21915927283261614147/50000000000000000000),(8766370913304645659/20000000000000000000),(707248880558204027/1000000000000000000),false⟩
theorem valid1152 : certificate1152.Valid := by decide +kernel
theorem bound1152 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1152.a certificate1152.b certificate1152.c x ≤ (certificate1152.bound:ℝ) :=
  rat_majority_certificate_sound certificate1152 valid1152 x hx0 hx1

def certificate1153 : RatMajorityCertificate := ⟨(16979407633283771/100000000000000000),(83104916933327982333839677353641911/100000000000000000000000000000000000),(163976869/138395625),(20122073994306748633/50000000000000000000),(40244147988613497267/100000000000000000000),(707248880558204027/1000000000000000000),false⟩
theorem valid1153 : certificate1153.Valid := by decide +kernel
theorem bound1153 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1153.a certificate1153.b certificate1153.c x ≤ (certificate1153.bound:ℝ) :=
  rat_majority_certificate_sound certificate1153 valid1153 x hx0 hx1

def certificate1154 : RatMajorityCertificate := ⟨0,(1001015706636243659/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(33880173265323237/62500000000000000),false⟩
theorem valid1154 : certificate1154.Valid := by decide +kernel
theorem bound1154 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1154.a certificate1154.b certificate1154.c x ≤ (certificate1154.bound:ℝ) :=
  rat_majority_certificate_sound certificate1154 valid1154 x hx0 hx1

def certificate1155 : RatMajorityCertificate := ⟨(28428458703219351/200000000000000000),(171745807649866342100806519040154691/200000000000000000000000000000000000),1,(7242608699540337783/20000000000000000000),(9053260874425422229/25000000000000000000),(33880173265323237/62500000000000000),false⟩
theorem valid1155 : certificate1155.Valid := by decide +kernel
theorem bound1155 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1155.a certificate1155.b certificate1155.c x ≤ (certificate1155.bound:ℝ) :=
  rat_majority_certificate_sound certificate1155 valid1155 x hx0 hx1

def certificate1156 : RatMajorityCertificate := ⟨0,(500524145299260239/500000000000000000),(218098947/184340000),(43792977930862650327/100000000000000000000),(5474122241357831291/12500000000000000000),(705548641582900779/1000000000000000000),false⟩
theorem valid1156 : certificate1156.Valid := by decide +kernel
theorem bound1156 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1156.a certificate1156.b certificate1156.c x ≤ (certificate1156.bound:ℝ) :=
  rat_majority_certificate_sound certificate1156 valid1156 x hx0 hx1

def certificate1157 : RatMajorityCertificate := ⟨(167849310515754373/1000000000000000000),(416511512614292147643234048070724853/500000000000000000000000000000000000),(218098947/184340000),(4025168996127096483/10000000000000000000),(40251689961270964831/100000000000000000000),(705548641582900779/1000000000000000000),false⟩
theorem valid1157 : certificate1157.Valid := by decide +kernel
theorem bound1157 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1157.a certificate1157.b certificate1157.c x ≤ (certificate1157.bound:ℝ) :=
  rat_majority_certificate_sound certificate1157 valid1157 x hx0 hx1

def certificate1158 : RatMajorityCertificate := ⟨0,(500524145299260239/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(541983381706013357/1000000000000000000),false⟩
theorem valid1158 : certificate1158.Valid := by decide +kernel
theorem bound1158 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1158.a certificate1158.b certificate1158.c x ≤ (certificate1158.bound:ℝ) :=
  rat_majority_certificate_sound certificate1158 valid1158 x hx0 hx1

def certificate1159 : RatMajorityCertificate := ⟨(141119085551529303/1000000000000000000),(429890635618167849903866958968716583/500000000000000000000000000000000000),1,(36237679399330160869/100000000000000000000),(3623767939933016087/10000000000000000000),(541983381706013357/1000000000000000000),false⟩
theorem valid1159 : certificate1159.Valid := by decide +kernel
theorem bound1159 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1159.a certificate1159.b certificate1159.c x ≤ (certificate1159.bound:ℝ) :=
  rat_majority_certificate_sound certificate1159 valid1159 x hx0 hx1

end Cycle12.MajorityCertificates.Batch028
