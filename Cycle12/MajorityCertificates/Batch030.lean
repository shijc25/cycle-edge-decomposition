import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch030

def certificate1200 : RatMajorityCertificate := ⟨0,(100127459651088709/100000000000000000),(2570699131/2198260000),(43478473800150086853/100000000000000000000),(21739236900075043427/50000000000000000000),(692025253624891523/1000000000000000000),false⟩
theorem valid1200 : certificate1200.Valid := by decide +kernel
theorem bound1200 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1200.a certificate1200.b certificate1200.c x ≤ (certificate1200.bound:ℝ) :=
  rat_majority_certificate_sound certificate1200 valid1200 x hx0 hx1

def certificate1201 : RatMajorityCertificate := ⟨(76804598760858471/500000000000000000),(42373480462098440087674469384896061/50000000000000000000000000000000000),(2570699131/2198260000),(4027191583074049461/10000000000000000000),(40271915830740494611/100000000000000000000),(692025253624891523/1000000000000000000),false⟩
theorem valid1201 : certificate1201.Valid := by decide +kernel
theorem bound1201 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1201.a certificate1201.b certificate1201.c x ≤ (certificate1201.bound:ℝ) :=
  rat_majority_certificate_sound certificate1201 valid1201 x hx0 hx1

def certificate1202 : RatMajorityCertificate := ⟨0,(100127459651088709/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(541348396687249177/1000000000000000000),false⟩
theorem valid1202 : certificate1202.Valid := by decide +kernel
theorem bound1202 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1202.a certificate1202.b certificate1202.c x ≤ (certificate1202.bound:ℝ) :=
  rat_majority_certificate_sound certificate1202 valid1202 x hx0 hx1

def certificate1203 : RatMajorityCertificate := ⟨(134435866655231199/1000000000000000000),(86666737836907905122756029546567909/100000000000000000000000000000000000),1,(36397475559780794529/100000000000000000000),(3639747555978079453/10000000000000000000),(541348396687249177/1000000000000000000),false⟩
theorem valid1203 : certificate1203.Valid := by decide +kernel
theorem bound1203 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1203.a certificate1203.b certificate1203.c x ≤ (certificate1203.bound:ℝ) :=
  rat_majority_certificate_sound certificate1203 valid1203 x hx0 hx1

def certificate1204 : RatMajorityCertificate := ⟨0,(1001282476043732383/1000000000000000000),(2566446543/2198270000),(4343363845613844949/10000000000000000000),(43433638456138449491/100000000000000000000),(5520510224332153/8000000000000000),false⟩
theorem valid1204 : certificate1204.Valid := by decide +kernel
theorem bound1204 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1204.a certificate1204.b certificate1204.c x ≤ (certificate1204.bound:ℝ) :=
  rat_majority_certificate_sound certificate1204 valid1204 x hx0 hx1

def certificate1205 : RatMajorityCertificate := ⟨(151164661607566119/1000000000000000000),(849923949378995648156481878786068423/1000000000000000000000000000000000000),(2566446543/2198270000),(4028399358030598627/10000000000000000000),(40283993580305986271/100000000000000000000),(5520510224332153/8000000000000000),false⟩
theorem valid1205 : certificate1205.Valid := by decide +kernel
theorem bound1205 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1205.a certificate1205.b certificate1205.c x ≤ (certificate1205.bound:ℝ) :=
  rat_majority_certificate_sound certificate1205 valid1205 x hx0 hx1

def certificate1206 : RatMajorityCertificate := ⟨0,(1001282476043732383/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270607852280851683/500000000000000000),false⟩
theorem valid1206 : certificate1206.Valid := by decide +kernel
theorem bound1206 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1206.a certificate1206.b certificate1206.c x ≤ (certificate1206.bound:ℝ) :=
  rat_majority_certificate_sound certificate1206 valid1206 x hx0 hx1

def certificate1207 : RatMajorityCertificate := ⟨(33296991351033941/250000000000000000),(216980925066163089366970980246188597/250000000000000000000000000000000000),1,(36426999142378744497/100000000000000000000),(18213499571189372249/50000000000000000000),(270607852280851683/500000000000000000),false⟩
theorem valid1207 : certificate1207.Valid := by decide +kernel
theorem bound1207 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1207.a certificate1207.b certificate1207.c x ≤ (certificate1207.bound:ℝ) :=
  rat_majority_certificate_sound certificate1207 valid1207 x hx0 hx1

def certificate1208 : RatMajorityCertificate := ⟨0,(1001298168168712383/1000000000000000000),(2562194357/2197430000),(21699585869582593591/50000000000000000000),(43399171739165187183/100000000000000000000),(5510058380429187/8000000000000000),false⟩
theorem valid1208 : certificate1208.Valid := by decide +kernel
theorem bound1208 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1208.a certificate1208.b certificate1208.c x ≤ (certificate1208.bound:ℝ) :=
  rat_majority_certificate_sound certificate1208 valid1208 x hx0 hx1

def certificate1209 : RatMajorityCertificate := ⟨(151480018335493871/1000000000000000000),(849621503295219405722206807541695407/1000000000000000000000000000000000000),(2562194357/2197430000),(40241098061761867631/100000000000000000000),(2515068628860116727/6250000000000000000),(5510058380429187/8000000000000000),false⟩
theorem valid1209 : certificate1209.Valid := by decide +kernel
theorem bound1209 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1209.a certificate1209.b certificate1209.c x ≤ (certificate1209.bound:ℝ) :=
  rat_majority_certificate_sound certificate1209 valid1209 x hx0 hx1

def certificate1210 : RatMajorityCertificate := ⟨0,(1001298168168712383/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(10822394050735463/20000000000000000),false⟩
theorem valid1210 : certificate1210.Valid := by decide +kernel
theorem bound1210 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1210.a certificate1210.b certificate1210.c x ≤ (certificate1210.bound:ℝ) :=
  rat_majority_certificate_sound certificate1210 valid1210 x hx0 hx1

def certificate1211 : RatMajorityCertificate := ⟨(66120346679803301/500000000000000000),(434442902075188942355211679117023717/500000000000000000000000000000000000),1,(7289878380765406257/20000000000000000000),(18224695951913515643/50000000000000000000),(10822394050735463/20000000000000000),false⟩
theorem valid1211 : certificate1211.Valid := by decide +kernel
theorem bound1211 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1211.a certificate1211.b certificate1211.c x ≤ (certificate1211.bound:ℝ) :=
  rat_majority_certificate_sound certificate1211 valid1211 x hx0 hx1

def certificate1212 : RatMajorityCertificate := ⟨0,(1001313803434737897/1000000000000000000),(121851213/104600000),(43374362049102110213/100000000000000000000),(21687181024551055107/50000000000000000000),(687573471917092191/1000000000000000000),false⟩
theorem valid1212 : certificate1212.Valid := by decide +kernel
theorem bound1212 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1212.a certificate1212.b certificate1212.c x ≤ (certificate1212.bound:ℝ) :=
  rat_majority_certificate_sound certificate1212 valid1212 x hx0 hx1

def certificate1213 : RatMajorityCertificate := ⟨(930592754888207/6250000000000000),(5326395900621190528005243418719321/6250000000000000000000000000000000),(121851213/104600000),(20138474558249570029/50000000000000000000),(40276949116499140059/100000000000000000000),(687573471917092191/1000000000000000000),false⟩
theorem valid1213 : certificate1213.Valid := by decide +kernel
theorem bound1213 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1213.a certificate1213.b certificate1213.c x ≤ (certificate1213.bound:ℝ) :=
  rat_majority_certificate_sound certificate1213 valid1213 x hx0 hx1

def certificate1214 : RatMajorityCertificate := ⟨0,(1001313803434737897/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270554046986062407/500000000000000000),false⟩
theorem valid1214 : certificate1214.Valid := by decide +kernel
theorem bound1214 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1214.a certificate1214.b certificate1214.c x ≤ (certificate1214.bound:ℝ) :=
  rat_majority_certificate_sound certificate1214 valid1214 x hx0 hx1

def certificate1215 : RatMajorityCertificate := ⟨(33017074680646979/250000000000000000),(217267998231917063595292448750136837/250000000000000000000000000000000000),1,(36453497479069098429/100000000000000000000),(3645349747906909843/10000000000000000000),(270554046986062407/500000000000000000),false⟩
theorem valid1215 : certificate1215.Valid := by decide +kernel
theorem bound1215 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1215.a certificate1215.b certificate1215.c x ≤ (certificate1215.bound:ℝ) :=
  rat_majority_certificate_sound certificate1215 valid1215 x hx0 hx1

def certificate1216 : RatMajorityCertificate := ⟨0,(1001329372318796259/1000000000000000000),(2554192211/2195790000),(43334832797836968249/100000000000000000000),(173339331191347873/400000000000000000),(685929594937430631/1000000000000000000),false⟩
theorem valid1216 : certificate1216.Valid := by decide +kernel
theorem bound1216 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1216.a certificate1216.b certificate1216.c x ≤ (certificate1216.bound:ℝ) :=
  rat_majority_certificate_sound certificate1216 valid1216 x hx0 hx1

def certificate1217 : RatMajorityCertificate := ⟨(29512781202989583/200000000000000000),(170713859786387723891869525323630003/200000000000000000000000000000000000),(2554192211/2195790000),(20133915167629732031/50000000000000000000),(40267830335259464063/100000000000000000000),(685929594937430631/1000000000000000000),false⟩
theorem valid1217 : certificate1217.Valid := by decide +kernel
theorem bound1217 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1217.a certificate1217.b certificate1217.c x ≤ (certificate1217.bound:ℝ) :=
  rat_majority_certificate_sound certificate1217 valid1217 x hx0 hx1

def certificate1218 : RatMajorityCertificate := ⟨0,(1001329372318796259/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135252844390707223/250000000000000000),false⟩
theorem valid1218 : certificate1218.Valid := by decide +kernel
theorem bound1218 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1218.a certificate1218.b certificate1218.c x ≤ (certificate1218.bound:ℝ) :=
  rat_majority_certificate_sound certificate1218 valid1218 x hx0 hx1

def certificate1219 : RatMajorityCertificate := ⟨(131112059841110263/1000000000000000000),(870043015734672865380325077749093883/1000000000000000000000000000000000000),1,(36476054766683408779/100000000000000000000),(1823802738334170439/5000000000000000000),(135252844390707223/250000000000000000),false⟩
theorem valid1219 : certificate1219.Valid := by decide +kernel
theorem bound1219 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1219.a certificate1219.b certificate1219.c x ≤ (certificate1219.bound:ℝ) :=
  rat_majority_certificate_sound certificate1219 valid1219 x hx0 hx1

def certificate1220 : RatMajorityCertificate := ⟨0,(1001344871150872827/1000000000000000000),(1274776353/1097500000),(43295427470737207533/100000000000000000000),(21647713735368603767/50000000000000000000),(684297183287436997/1000000000000000000),false⟩
theorem valid1220 : certificate1220.Valid := by decide +kernel
theorem bound1220 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1220.a certificate1220.b certificate1220.c x ≤ (certificate1220.bound:ℝ) :=
  rat_majority_certificate_sound certificate1220 valid1220 x hx0 hx1

def certificate1221 : RatMajorityCertificate := ⟨(146274778536148131/1000000000000000000),(854873371884971118570366308785263663/1000000000000000000000000000000000000),(1274776353/1097500000),(20128900447581582593/50000000000000000000),(40257800895163165187/100000000000000000000),(684297183287436997/1000000000000000000),false⟩
theorem valid1221 : certificate1221.Valid := by decide +kernel
theorem bound1221 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1221.a certificate1221.b certificate1221.c x ≤ (certificate1221.bound:ℝ) :=
  rat_majority_certificate_sound certificate1221 valid1221 x hx0 hx1

def certificate1222 : RatMajorityCertificate := ⟨0,(1001344871150872827/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(54091200367750547/100000000000000000),false⟩
theorem valid1222 : certificate1222.Valid := by decide +kernel
theorem bound1222 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1222.a certificate1222.b certificate1222.c x ≤ (certificate1222.bound:ℝ) :=
  rat_majority_certificate_sound certificate1222 valid1222 x hx0 hx1

def certificate1223 : RatMajorityCertificate := ⟨(65064554583616709/500000000000000000),(435520377549415808025424400228733657/500000000000000000000000000000000000),1,(36499199794367519177/100000000000000000000),(18249599897183759589/50000000000000000000),(54091200367750547/100000000000000000),false⟩
theorem valid1223 : certificate1223.Valid := by decide +kernel
theorem bound1223 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1223.a certificate1223.b certificate1223.c x ≤ (certificate1223.bound:ℝ) :=
  rat_majority_certificate_sound certificate1223 valid1223 x hx0 hx1

def certificate1224 : RatMajorityCertificate := ⟨0,(500680151240516327/500000000000000000),(2546799299/2194220000),(21637915179920466301/50000000000000000000),(43275830359840932603/100000000000000000000),(136694066337953067/200000000000000000),false⟩
theorem valid1224 : certificate1224.Valid := by decide +kernel
theorem bound1224 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1224.a certificate1224.b certificate1224.c x ≤ (certificate1224.bound:ℝ) :=
  rat_majority_certificate_sound certificate1224 valid1224 x hx0 hx1

def certificate1225 : RatMajorityCertificate := ⟨(14539831864617363/100000000000000000),(42788209907063332880662857590814299/50000000000000000000000000000000000),(2546799299/2194220000),(40258355951198963077/100000000000000000000),(20129177975599481539/50000000000000000000),(136694066337953067/200000000000000000),false⟩
theorem valid1225 : certificate1225.Valid := by decide +kernel
theorem bound1225 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1225.a certificate1225.b certificate1225.c x ≤ (certificate1225.bound:ℝ) :=
  rat_majority_certificate_sound certificate1225 valid1225 x hx0 hx1

def certificate1226 : RatMajorityCertificate := ⟨0,(500680151240516327/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540900370328915759/1000000000000000000),false⟩
theorem valid1226 : certificate1226.Valid := by decide +kernel
theorem bound1226 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1226.a certificate1226.b certificate1226.c x ≤ (certificate1226.bound:ℝ) :=
  rat_majority_certificate_sound certificate1226 valid1226 x hx0 hx1

def certificate1227 : RatMajorityCertificate := ⟨(64978112807844491/500000000000000000),(217806824272303252733667445237495443/250000000000000000000000000000000000),1,(7300659996252684057/20000000000000000000),(18251649990631710143/50000000000000000000),(540900370328915759/1000000000000000000),false⟩
theorem valid1227 : certificate1227.Valid := by decide +kernel
theorem bound1227 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1227.a certificate1227.b certificate1227.c x ≤ (certificate1227.bound:ℝ) :=
  rat_majority_certificate_sound certificate1227 valid1227 x hx0 hx1

def certificate1228 : RatMajorityCertificate := ⟨0,(500687828303413407/500000000000000000),(508476429/438692000),(43238274275558838033/100000000000000000000),(21619137137779419017/50000000000000000000),(681967941236421713/1000000000000000000),false⟩
theorem valid1228 : certificate1228.Valid := by decide +kernel
theorem bound1228 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1228.a certificate1228.b certificate1228.c x ≤ (certificate1228.bound:ℝ) :=
  rat_majority_certificate_sound certificate1228 valid1228 x hx0 hx1

def certificate1229 : RatMajorityCertificate := ⟨(72364480828701227/500000000000000000),(214111899399280292418412621330849611/250000000000000000000000000000000000),(508476429/438692000),(8047116097450253919/20000000000000000000),(10058895121812817399/25000000000000000000),(681967941236421713/1000000000000000000),false⟩
theorem valid1229 : certificate1229.Valid := by decide +kernel
theorem bound1229 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1229.a certificate1229.b certificate1229.c x ≤ (certificate1229.bound:ℝ) :=
  rat_majority_certificate_sound certificate1229 valid1229 x hx0 hx1

def certificate1230 : RatMajorityCertificate := ⟨0,(500687828303413407/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(33800475964468037/62500000000000000),false⟩
theorem valid1230 : certificate1230.Valid := by decide +kernel
theorem bound1230 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1230.a certificate1230.b certificate1230.c x ≤ (certificate1230.bound:ℝ) :=
  rat_majority_certificate_sound certificate1230 valid1230 x hx0 hx1

def certificate1231 : RatMajorityCertificate := ⟨(64516084288257383/500000000000000000),(218041496018779143560566533331066119/250000000000000000000000000000000000),1,(9131253852860667779/25000000000000000000),(36525015411442671117/100000000000000000000),(33800475964468037/62500000000000000),false⟩
theorem valid1231 : certificate1231.Valid := by decide +kernel
theorem bound1231 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1231.a certificate1231.b certificate1231.c x ≤ (certificate1231.bound:ℝ) :=
  rat_majority_certificate_sound certificate1231 valid1231 x hx0 hx1

def certificate1232 : RatMajorityCertificate := ⟨0,(500695464951012553/500000000000000000),(1268832261/1096360000),(43197186798644830853/100000000000000000000),(21598593399322415427/50000000000000000000),(170057146159946381/250000000000000000),false⟩
theorem valid1232 : certificate1232.Valid := by decide +kernel
theorem bound1232 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1232.a certificate1232.b certificate1232.c x ≤ (certificate1232.bound:ℝ) :=
  rat_majority_certificate_sound certificate1232 valid1232 x hx0 hx1

def certificate1233 : RatMajorityCertificate := ⟨(71437565081867349/500000000000000000),(214579267611872485057384742420168003/250000000000000000000000000000000000),(1268832261/1096360000),(40236960245902611691/100000000000000000000),(10059240061475652923/25000000000000000000),(170057146159946381/250000000000000000),false⟩
theorem valid1233 : certificate1233.Valid := by decide +kernel
theorem bound1233 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1233.a certificate1233.b certificate1233.c x ≤ (certificate1233.bound:ℝ) :=
  rat_majority_certificate_sound certificate1233 valid1233 x hx0 hx1

def certificate1234 : RatMajorityCertificate := ⟨0,(500695464951012553/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(2112395644097261/3906250000000000),false⟩
theorem valid1234 : certificate1234.Valid := by decide +kernel
theorem bound1234 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1234.a certificate1234.b certificate1234.c x ≤ (certificate1234.bound:ℝ) :=
  rat_majority_certificate_sound certificate1234 valid1234 x hx0 hx1

def certificate1235 : RatMajorityCertificate := ⟨(128648772664085439/1000000000000000000),(436281607906591180252662799246484233/500000000000000000000000000000000000),1,(36534037855971546389/100000000000000000000),(3653403785597154639/10000000000000000000),(2112395644097261/3906250000000000),false⟩
theorem valid1235 : certificate1235.Valid := by decide +kernel
theorem bound1235 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1235.a certificate1235.b certificate1235.c x ≤ (certificate1235.bound:ℝ) :=
  rat_majority_certificate_sound certificate1235 valid1235 x hx0 hx1

def certificate1236 : RatMajorityCertificate := ⟨0,(125175765647367107/125000000000000000),(2533125569/2191990000),(10789446581913546693/25000000000000000000),(43157786327654186773/100000000000000000000),(339302969839736151/500000000000000000),false⟩
theorem valid1236 : certificate1236.Valid := by decide +kernel
theorem bound1236 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1236.a certificate1236.b certificate1236.c x ≤ (certificate1236.bound:ℝ) :=
  rat_majority_certificate_sound certificate1236 valid1236 x hx0 hx1

def certificate1237 : RatMajorityCertificate := ⟨(141577531135107187/1000000000000000000),(107453689789066109763140179216901991/125000000000000000000000000000000000),(2533125569/2191990000),(40226954750700029387/100000000000000000000),(10056738687675007347/25000000000000000000),(339302969839736151/500000000000000000),false⟩
theorem valid1237 : certificate1237.Valid := by decide +kernel
theorem bound1237 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1237.a certificate1237.b certificate1237.c x ≤ (certificate1237.bound:ℝ) :=
  rat_majority_certificate_sound certificate1237 valid1237 x hx0 hx1

def certificate1238 : RatMajorityCertificate := ⟨0,(125175765647367107/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(54067922660640677/100000000000000000),false⟩
theorem valid1238 : certificate1238.Valid := by decide +kernel
theorem bound1238 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1238.a certificate1238.b certificate1238.c x ≤ (certificate1238.bound:ℝ) :=
  rat_majority_certificate_sound certificate1238 valid1238 x hx0 hx1

def certificate1239 : RatMajorityCertificate := ⟨(63854997550494669/500000000000000000),(54594784614889632147747394710547417/62500000000000000000000000000000000),1,(1827802258203137579/5000000000000000000),(36556045164062751581/100000000000000000000),(54067922660640677/100000000000000000),false⟩
theorem valid1239 : certificate1239.Valid := by decide +kernel
theorem bound1239 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1239.a certificate1239.b certificate1239.c x ≤ (certificate1239.bound:ℝ) :=
  rat_majority_certificate_sound certificate1239 valid1239 x hx0 hx1

end Cycle12.MajorityCertificates.Batch030
