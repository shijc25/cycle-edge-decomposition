import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch023

def certificate920 : RatMajorityCertificate := ⟨0,(125485787118178843/125000000000000000),(2377450717/2068680000),(8601664718821782523/20000000000000000000),(5376040449263614077/12500000000000000000),(337753373735367069/500000000000000000),false⟩
theorem valid920 : certificate920.Valid := by decide +kernel
theorem bound920 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate920.a certificate920.b certificate920.c x ≤ (certificate920.bound:ℝ) :=
  rat_majority_certificate_sound certificate920 valid920 x hx0 hx1

def certificate921 : RatMajorityCertificate := ⟨(38868722821207557/250000000000000000),(26493974502047159477609636050883449/31250000000000000000000000000000000),(2377450717/2068680000),(39751871602471614397/100000000000000000000),(19875935801235807199/50000000000000000000),(337753373735367069/500000000000000000),false⟩
theorem valid921 : certificate921.Valid := by decide +kernel
theorem bound921 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate921.a certificate921.b certificate921.c x ≤ (certificate921.bound:ℝ) :=
  rat_majority_certificate_sound certificate921 valid921 x hx0 hx1

def certificate922 : RatMajorityCertificate := ⟨0,(125485787118178843/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(53999064742750823/100000000000000000),false⟩
theorem valid922 : certificate922.Valid := by decide +kernel
theorem bound922 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate922.a certificate922.b certificate922.c x ≤ (certificate922.bound:ℝ) :=
  rat_majority_certificate_sound certificate922 valid922 x hx0 hx1

def certificate923 : RatMajorityCertificate := ⟨(22021578321497489/200000000000000000),(22333762334378032527242701722574773/25000000000000000000000000000000000),1,(9241672350602002007/25000000000000000000),(36966689402408008029/100000000000000000000),(53999064742750823/100000000000000000),false⟩
theorem valid923 : certificate923.Valid := by decide +kernel
theorem bound923 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate923.a certificate923.b certificate923.c x ≤ (certificate923.bound:ℝ) :=
  rat_majority_certificate_sound certificate923 valid923 x hx0 hx1

def certificate924 : RatMajorityCertificate := ⟨0,(1003926004580156381/1000000000000000000),(2372703849/2067770000),(42966153355527297437/100000000000000000000),(21483076677763648719/50000000000000000000),(673788532970444511/1000000000000000000),false⟩
theorem valid924 : certificate924.Valid := by decide +kernel
theorem bound924 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate924.a certificate924.b certificate924.c x ≤ (certificate924.bound:ℝ) :=
  rat_majority_certificate_sound certificate924 valid924 x hx0 hx1

def certificate925 : RatMajorityCertificate := ⟨(154009625982725163/1000000000000000000),(849311736100434867829859948916284897/1000000000000000000000000000000000000),(2372703849/2067770000),(19871868200259399901/50000000000000000000),(39743736400518799803/100000000000000000000),(673788532970444511/1000000000000000000),false⟩
theorem valid925 : certificate925.Valid := by decide +kernel
theorem bound925 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate925.a certificate925.b certificate925.c x ≤ (certificate925.bound:ℝ) :=
  rat_majority_certificate_sound certificate925 valid925 x hx0 hx1

def certificate926 : RatMajorityCertificate := ⟨0,(1003926004580156381/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(539916811243660673/1000000000000000000),false⟩
theorem valid926 : certificate926.Valid := by decide +kernel
theorem bound926 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate926.a certificate926.b certificate926.c x ≤ (certificate926.bound:ℝ) :=
  rat_majority_certificate_sound certificate926 valid926 x hx0 hx1

def certificate927 : RatMajorityCertificate := ⟨(54598003240301801/500000000000000000),(447150647038987571698347029784057819/500000000000000000000000000000000000),1,(4623421902494249283/12500000000000000000),(7397475043990798853/20000000000000000000),(539916811243660673/1000000000000000000),false⟩
theorem valid927 : certificate927.Valid := by decide +kernel
theorem bound927 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate927.a certificate927.b certificate927.c x ≤ (certificate927.bound:ℝ) :=
  rat_majority_certificate_sound certificate927 valid927 x hx0 hx1

def certificate928 : RatMajorityCertificate := ⟨0,(250991356201191259/250000000000000000),(94864393/82675600),(10741298036758602881/25000000000000000000),(1718607685881376461/4000000000000000000),(337077095229768533/500000000000000000),false⟩
theorem valid928 : certificate928.Valid := by decide +kernel
theorem bound928 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate928.a certificate928.b certificate928.c x ≤ (certificate928.bound:ℝ) :=
  rat_majority_certificate_sound certificate928 valid928 x hx0 hx1

def certificate929 : RatMajorityCertificate := ⟨(79101624381284187/500000000000000000),(105641854119419894985296766380678567/125000000000000000000000000000000000),(94864393/82675600),(1585688213304279213/4000000000000000000),(19821102666303490163/50000000000000000000),(337077095229768533/500000000000000000),false⟩
theorem valid929 : certificate929.Valid := by decide +kernel
theorem bound929 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate929.a certificate929.b certificate929.c x ≤ (certificate929.bound:ℝ) :=
  rat_majority_certificate_sound certificate929 valid929 x hx0 hx1

def certificate930 : RatMajorityCertificate := ⟨0,(250991356201191259/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(269950916366418811/500000000000000000),false⟩
theorem valid930 : certificate930.Valid := by decide +kernel
theorem bound930 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate930.a certificate930.b certificate930.c x ≤ (certificate930.bound:ℝ) :=
  rat_majority_certificate_sound certificate930 valid930 x hx0 hx1

def certificate931 : RatMajorityCertificate := ⟨(108865217247462893/1000000000000000000),(223667127681113229806921518001547713/250000000000000000000000000000000000),1,(36994925048117629609/100000000000000000000),(3699492504811762961/10000000000000000000),(269950916366418811/500000000000000000),false⟩
theorem valid931 : certificate931.Valid := by decide +kernel
theorem bound931 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate931.a certificate931.b certificate931.c x ≤ (certificate931.bound:ℝ) :=
  rat_majority_certificate_sound certificate931 valid931 x hx0 hx1

def certificate932 : RatMajorityCertificate := ⟨0,(100400456703208171/100000000000000000),(1182789507/1033015000),(4290755324141338737/10000000000000000000),(42907553241413387371/100000000000000000000),(83933242094376899/125000000000000000),false⟩
theorem valid932 : certificate932.Valid := by decide +kernel
theorem bound932 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate932.a certificate932.b certificate932.c x ≤ (certificate932.bound:ℝ) :=
  rat_majority_certificate_sound certificate932 valid932 x hx0 hx1

def certificate933 : RatMajorityCertificate := ⟨(152489909156318807/1000000000000000000),(85090400181283037382052906636628003/100000000000000000000000000000000000),(1182789507/1033015000),(19860038151273818203/50000000000000000000),(39720076302547636407/100000000000000000000),(83933242094376899/125000000000000000),false⟩
theorem valid933 : certificate933.Valid := by decide +kernel
theorem bound933 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate933.a certificate933.b certificate933.c x ≤ (certificate933.bound:ℝ) :=
  rat_majority_certificate_sound certificate933 valid933 x hx0 hx1

def certificate934 : RatMajorityCertificate := ⟨0,(100400456703208171/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(134969272012137467/250000000000000000),false⟩
theorem valid934 : certificate934.Valid := by decide +kernel
theorem bound934 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate934.a certificate934.b certificate934.c x ≤ (certificate934.bound:ℝ) :=
  rat_majority_certificate_sound certificate934 valid934 x hx0 hx1

def certificate935 : RatMajorityCertificate := ⟨(108438651515042169/1000000000000000000),(89513166566817900575571753349637101/100000000000000000000000000000000000),1,(37004628236809096761/100000000000000000000),(18502314118404548381/50000000000000000000),(134969272012137467/250000000000000000),false⟩
theorem valid935 : certificate935.Valid := by decide +kernel
theorem bound935 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate935.a certificate935.b certificate935.c x ≤ (certificate935.bound:ℝ) :=
  rat_majority_certificate_sound certificate935 valid935 x hx0 hx1

def certificate936 : RatMajorityCertificate := ⟨0,(1004043421889635797/1000000000000000000),(590225883/516297500),(10716253332073568671/25000000000000000000),(8573002665658854937/20000000000000000000),(669745515767289457/1000000000000000000),false⟩
theorem valid936 : certificate936.Valid := by decide +kernel
theorem bound936 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate936.a certificate936.b certificate936.c x ≤ (certificate936.bound:ℝ) :=
  rat_majority_certificate_sound certificate936 valid936 x hx0 hx1

def certificate937 : RatMajorityCertificate := ⟨(37768220546981923/250000000000000000),(213089922075734767068335377987302369/250000000000000000000000000000000000),(590225883/516297500),(7942055101476676923/20000000000000000000),(4963784438422923077/12500000000000000000),(669745515767289457/1000000000000000000),false⟩
theorem valid937 : certificate937.Valid := by decide +kernel
theorem bound937 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate937.a certificate937.b certificate937.c x ≤ (certificate937.bound:ℝ) :=
  rat_majority_certificate_sound certificate937 valid937 x hx0 hx1

def certificate938 : RatMajorityCertificate := ⟨0,(1004043421889635797/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(269898087741099833/500000000000000000),false⟩
theorem valid938 : certificate938.Valid := by decide +kernel
theorem bound938 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate938.a certificate938.b certificate938.c x ≤ (certificate938.bound:ℝ) :=
  rat_majority_certificate_sound certificate938 valid938 x hx0 hx1

def certificate939 : RatMajorityCertificate := ⟨(13431968501093877/125000000000000000),(112019148119652376117017236363285031/125000000000000000000000000000000000),1,(7405369216966952081/20000000000000000000),(18513423042417380203/50000000000000000000),(269898087741099833/500000000000000000),false⟩
theorem valid939 : certificate939.Valid := by decide +kernel
theorem bound939 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate939.a certificate939.b certificate939.c x ≤ (certificate939.bound:ℝ) :=
  rat_majority_certificate_sound certificate939 valid939 x hx0 hx1

def certificate940 : RatMajorityCertificate := ⟨0,(502040990032828799/500000000000000000),(235999473/206437000),(1714613659987674429/4000000000000000000),(21432670749845930363/50000000000000000000),(670219642856864893/1000000000000000000),false⟩
theorem valid940 : certificate940.Valid := by decide +kernel
theorem bound940 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate940.a certificate940.b certificate940.c x ≤ (certificate940.bound:ℝ) :=
  rat_majority_certificate_sound certificate940 valid940 x hx0 hx1

def certificate941 : RatMajorityCertificate := ⟨(9745847865201533/62500000000000000),(26484746766096691280011049778651133/31250000000000000000000000000000000),(235999473/206437000),(7918907908447793229/20000000000000000000),(19797269771119483073/50000000000000000000),(670219642856864893/1000000000000000000),false⟩
theorem valid941 : certificate941.Valid := by decide +kernel
theorem bound941 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate941.a certificate941.b certificate941.c x ≤ (certificate941.bound:ℝ) :=
  rat_majority_certificate_sound certificate941 valid941 x hx0 hx1

def certificate942 : RatMajorityCertificate := ⟨0,(502040990032828799/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(539791495123494283/1000000000000000000),false⟩
theorem valid942 : certificate942.Valid := by decide +kernel
theorem bound942 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate942.a certificate942.b certificate942.c x ≤ (certificate942.bound:ℝ) :=
  rat_majority_certificate_sound certificate942 valid942 x hx0 hx1

def certificate943 : RatMajorityCertificate := ⟨(53614624429613409/500000000000000000),(224103755887532994599504821748234209/250000000000000000000000000000000000),1,(37032023775078080141/100000000000000000000),(18516011887539040071/50000000000000000000),(539791495123494283/1000000000000000000),false⟩
theorem valid943 : certificate943.Valid := by decide +kernel
theorem bound943 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate943.a certificate943.b certificate943.c x ≤ (certificate943.bound:ℝ) :=
  rat_majority_certificate_sound certificate943 valid943 x hx0 hx1

def certificate944 : RatMajorityCertificate := ⟨0,(125515026535188333/125000000000000000),(9415003/8254320),(267524925241093503/625000000000000000),(42803988038574960481/100000000000000000000),(667290096979147881/1000000000000000000),false⟩
theorem valid944 : certificate944.Valid := by decide +kernel
theorem bound944 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate944.a certificate944.b certificate944.c x ≤ (certificate944.bound:ℝ) :=
  rat_majority_certificate_sound certificate944 valid944 x hx0 hx1

def certificate945 : RatMajorityCertificate := ⟨(18623082521047951/125000000000000000),(13351901620102206018227183691244317/15625000000000000000000000000000000),(9415003/8254320),(9924370925816583153/25000000000000000000),(39697483703266332613/100000000000000000000),(667290096979147881/1000000000000000000),false⟩
theorem valid945 : certificate945.Valid := by decide +kernel
theorem bound945 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate945.a certificate945.b certificate945.c x ≤ (certificate945.bound:ℝ) :=
  rat_majority_certificate_sound certificate945 valid945 x hx0 hx1

def certificate946 : RatMajorityCertificate := ⟨0,(125515026535188333/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(134927739516464753/250000000000000000),false⟩
theorem valid946 : certificate946.Valid := by decide +kernel
theorem bound946 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate946.a certificate946.b certificate946.c x ≤ (certificate946.bound:ℝ) :=
  rat_majority_certificate_sound certificate946 valid946 x hx0 hx1

def certificate947 : RatMajorityCertificate := ⟨(106249346311501031/1000000000000000000),(112179137013553866460216258491328677/125000000000000000000000000000000000),1,(37054123368643897407/100000000000000000000),(578970677635060897/1562500000000000000),(134927739516464753/250000000000000000),false⟩
theorem valid947 : certificate947.Valid := by decide +kernel
theorem bound947 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate947.a certificate947.b certificate947.c x ≤ (certificate947.bound:ℝ) :=
  rat_majority_certificate_sound certificate947 valid947 x hx0 hx1

def certificate948 : RatMajorityCertificate := ⟨0,(251039527194461451/250000000000000000),(2349139771/2062820000),(2672554459788257141/6250000000000000000),(42760871356612114257/100000000000000000000),(665531169852599333/1000000000000000000),false⟩
theorem valid948 : certificate948.Valid := by decide +kernel
theorem bound948 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate948.a certificate948.b certificate948.c x ≤ (certificate948.bound:ℝ) :=
  rat_majority_certificate_sound certificate948 valid948 x hx0 hx1

def certificate949 : RatMajorityCertificate := ⟨(73647438312467309/500000000000000000),(107031345504185666329001772701794641/125000000000000000000000000000000000),(2349139771/2062820000),(39693383223372916529/100000000000000000000),(3969338322337291653/10000000000000000000),(665531169852599333/1000000000000000000),false⟩
theorem valid949 : certificate949.Valid := by decide +kernel
theorem bound949 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate949.a certificate949.b certificate949.c x ≤ (certificate949.bound:ℝ) :=
  rat_majority_certificate_sound certificate949 valid949 x hx0 hx1

def certificate950 : RatMajorityCertificate := ⟨0,(251039527194461451/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(539684419916150699/1000000000000000000),false⟩
theorem valid950 : certificate950.Valid := by decide +kernel
theorem bound950 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate950.a certificate950.b certificate950.c x ≤ (certificate950.bound:ℝ) :=
  rat_majority_certificate_sound certificate950 valid950 x hx0 hx1

def certificate951 : RatMajorityCertificate := ⟨(5290351017911081/50000000000000000),(11223889141493936912458997199761469/12500000000000000000000000000000000),1,(7412825958250200013/20000000000000000000),(18532064895625500033/50000000000000000000),(539684419916150699/1000000000000000000),false⟩
theorem valid951 : certificate951.Valid := by decide +kernel
theorem bound951 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate951.a certificate951.b certificate951.c x ≤ (certificate951.bound:ℝ) :=
  rat_majority_certificate_sound certificate951 valid951 x hx0 hx1

def certificate952 : RatMajorityCertificate := ⟨0,(502097850350640981/500000000000000000),(586173133/515517500),(10679852069130562653/25000000000000000000),(42719408276522250613/100000000000000000000),(663871736754526731/1000000000000000000),false⟩
theorem valid952 : certificate952.Valid := by decide +kernel
theorem bound952 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate952.a certificate952.b certificate952.c x ≤ (certificate952.bound:ℝ) :=
  rat_majority_certificate_sound certificate952 valid952 x hx0 hx1

def certificate953 : RatMajorityCertificate := ⟨(912399888820987/6250000000000000),(2679997541854324731591568184931753/3125000000000000000000000000000000),(586173133/515517500),(19840972222226552197/50000000000000000000),(7936388888890620879/20000000000000000000),(663871736754526731/1000000000000000000),false⟩
theorem valid953 : certificate953.Valid := by decide +kernel
theorem bound953 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate953.a certificate953.b certificate953.c x ≤ (certificate953.bound:ℝ) :=
  rat_majority_certificate_sound certificate953 valid953 x hx0 hx1

def certificate954 : RatMajorityCertificate := ⟨0,(502097850350640981/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(26982192714536241/50000000000000000),false⟩
theorem valid954 : certificate954.Valid := by decide +kernel
theorem bound954 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate954.a certificate954.b certificate954.c x ≤ (certificate954.bound:ℝ) :=
  rat_majority_certificate_sound certificate954 valid954 x hx0 hx1

def certificate955 : RatMajorityCertificate := ⟨(52612684792171983/500000000000000000),(224632209239995077596892484760164677/250000000000000000000000000000000000),1,(463465619293515111/1250000000000000000),(37077249543481208881/100000000000000000000),(26982192714536241/50000000000000000),false⟩
theorem valid955 : certificate955.Valid := by decide +kernel
theorem bound955 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate955.a certificate955.b certificate955.c x ≤ (certificate955.bound:ℝ) :=
  rat_majority_certificate_sound certificate955 valid955 x hx0 hx1

def certificate956 : RatMajorityCertificate := ⟨0,(200846587676723613/200000000000000000),(292775623/257668750),(42700120311160810411/100000000000000000000),(10675030077790202603/25000000000000000000),(66311529739928901/100000000000000000),false⟩
theorem valid956 : certificate956.Valid := by decide +kernel
theorem bound956 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate956.a certificate956.b certificate956.c x ≤ (certificate956.bound:ℝ) :=
  rat_majority_certificate_sound certificate956 valid956 x hx0 hx1

def certificate957 : RatMajorityCertificate := ⟨(1163306480472391/8000000000000000),(1373126564388690059428892615731317/1600000000000000000000000000000000),(292775623/257668750),(2479733790973450753/6250000000000000000),(39675740655575212049/100000000000000000000),(66311529739928901/100000000000000000),false⟩
theorem valid957 : certificate957.Valid := by decide +kernel
theorem bound957 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate957.a certificate957.b certificate957.c x ≤ (certificate957.bound:ℝ) :=
  rat_majority_certificate_sound certificate957 valid957 x hx0 hx1

def certificate958 : RatMajorityCertificate := ⟨0,(200846587676723613/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(539594315969969431/1000000000000000000),false⟩
theorem valid958 : certificate958.Valid := by decide +kernel
theorem bound958 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate958.a certificate958.b certificate958.c x ≤ (certificate958.bound:ℝ) :=
  rat_majority_certificate_sound certificate958 valid958 x hx0 hx1

def certificate959 : RatMajorityCertificate := ⟨(52277261460313193/500000000000000000),(89923584260974008481708908921473691/100000000000000000000000000000000000),1,(37092350792668305687/100000000000000000000),(4636543849083538211/12500000000000000000),(539594315969969431/1000000000000000000),false⟩
theorem valid959 : certificate959.Valid := by decide +kernel
theorem bound959 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate959.a certificate959.b certificate959.c x ≤ (certificate959.bound:ℝ) :=
  rat_majority_certificate_sound certificate959 valid959 x hx0 hx1

end Cycle12.MajorityCertificates.Batch023
