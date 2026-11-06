import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch007

def certificate280 : RatMajorityCertificate := ⟨0,(251403715751578669/250000000000000000),(2389923277/1994260000),(44138362996549379231/100000000000000000000),(1379323843642168101/3125000000000000000),(726186720740312439/1000000000000000000),false⟩
theorem valid280 : certificate280.Valid := by decide +kernel
theorem bound280 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate280.a certificate280.b certificate280.c x ≤ (certificate280.bound:ℝ) :=
  rat_majority_certificate_sound certificate280 valid280 x hx0 hx1

def certificate281 : RatMajorityCertificate := ⟨(213174877253248307/1000000000000000000),(197810759505225358292504756498436617/250000000000000000000000000000000000),(2389923277/1994260000),(986864915646057187/2500000000000000000),(39474596625842287481/100000000000000000000),(726186720740312439/1000000000000000000),false⟩
theorem valid281 : certificate281.Valid := by decide +kernel
theorem bound281 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate281.a certificate281.b certificate281.c x ≤ (certificate281.bound:ℝ) :=
  rat_majority_certificate_sound certificate281 valid281 x hx0 hx1

def certificate282 : RatMajorityCertificate := ⟨0,(251403715751578669/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(542944942135122611/1000000000000000000),false⟩
theorem valid282 : certificate282.Valid := by decide +kernel
theorem bound282 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate282.a certificate282.b certificate282.c x ≤ (certificate282.bound:ℝ) :=
  rat_majority_certificate_sound certificate282 valid282 x hx0 hx1

def certificate283 : RatMajorityCertificate := ⟨(8179511013062727/62500000000000000),(13656372772758737716400669027829637/15625000000000000000000000000000000),1,(9123274211402926367/25000000000000000000),(36493096845611705469/100000000000000000000),(542944942135122611/1000000000000000000),false⟩
theorem valid283 : certificate283.Valid := by decide +kernel
theorem bound283 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate283.a certificate283.b certificate283.c x ≤ (certificate283.bound:ℝ) :=
  rat_majority_certificate_sound certificate283 valid283 x hx0 hx1

def certificate284 : RatMajorityCertificate := ⟨0,(502830730077786809/500000000000000000),(2387847583/1993220000),(8825803395800068197/20000000000000000000),(22064508489500170493/50000000000000000000),(145149463984587353/200000000000000000),false⟩
theorem valid284 : certificate284.Valid := by decide +kernel
theorem bound284 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate284.a certificate284.b certificate284.c x ≤ (certificate284.bound:ℝ) :=
  rat_majority_certificate_sound certificate284 valid284 x hx0 hx1

def certificate285 : RatMajorityCertificate := ⟨(2653355594359/12500000000000),(4951195395304819195602514989569/6250000000000000000000000000000),(2387847583/1993220000),(39489056529484011757/100000000000000000000),(19744528264742005879/50000000000000000000),(145149463984587353/200000000000000000),false⟩
theorem valid285 : certificate285.Valid := by decide +kernel
theorem bound285 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate285.a certificate285.b certificate285.c x ≤ (certificate285.bound:ℝ) :=
  rat_majority_certificate_sound certificate285 valid285 x hx0 hx1

def certificate286 : RatMajorityCertificate := ⟨0,(502830730077786809/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271483336283526381/500000000000000000),false⟩
theorem valid286 : certificate286.Valid := by decide +kernel
theorem bound286 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate286.a certificate286.b certificate286.c x ≤ (certificate286.bound:ℝ) :=
  rat_majority_certificate_sound certificate286 valid286 x hx0 hx1

def certificate287 : RatMajorityCertificate := ⟨(130876169782552757/1000000000000000000),(437022170076241425312650387158817587/500000000000000000000000000000000000),1,(7298625350462541767/20000000000000000000),(9123281688078177209/25000000000000000000),(271483336283526381/500000000000000000),false⟩
theorem valid287 : certificate287.Valid := by decide +kernel
theorem bound287 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate287.a certificate287.b certificate287.c x ≤ (certificate287.bound:ℝ) :=
  rat_majority_certificate_sound certificate287 valid287 x hx0 hx1

def certificate288 : RatMajorityCertificate := ⟨0,(25142701813632421/25000000000000000),(1194505301/996095000),(22078015911797334939/50000000000000000000),(44156031823594669879/100000000000000000000),(45478139175459991/62500000000000000),false⟩
theorem valid288 : certificate288.Valid := by decide +kernel
theorem bound288 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate288.a certificate288.b certificate288.c x ≤ (certificate288.bound:ℝ) :=
  rat_majority_certificate_sound certificate288 valid288 x hx0 hx1

def certificate289 : RatMajorityCertificate := ⟨(5505533091514701/25000000000000000),(490143568495770542507878268278879/625000000000000000000000000000000),(1194505301/996095000),(19652650980128457429/50000000000000000000),(39305301960256914859/100000000000000000000),(45478139175459991/62500000000000000),false⟩
theorem valid289 : certificate289.Valid := by decide +kernel
theorem bound289 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate289.a certificate289.b certificate289.c x ≤ (certificate289.bound:ℝ) :=
  rat_majority_certificate_sound certificate289 valid289 x hx0 hx1

def certificate290 : RatMajorityCertificate := ⟨0,(25142701813632421/25000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135738677964928859/250000000000000000),false⟩
theorem valid290 : certificate290.Valid := by decide +kernel
theorem bound290 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate290.a certificate290.b certificate290.c x ≤ (certificate290.bound:ℝ) :=
  rat_majority_certificate_sound certificate290 valid290 x hx0 hx1

def certificate291 : RatMajorityCertificate := ⟨(130561968645481227/1000000000000000000),(21860021167778260868876891565939433/25000000000000000000000000000000000),1,(9125151593400071331/25000000000000000000),(1460024254944011413/4000000000000000000),(135738677964928859/250000000000000000),false⟩
theorem valid291 : certificate291.Valid := by decide +kernel
theorem bound291 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate291.a certificate291.b certificate291.c x ≤ (certificate291.bound:ℝ) :=
  rat_majority_certificate_sound certificate291 valid291 x hx0 hx1

def certificate292 : RatMajorityCertificate := ⟨0,(100575472619027981/100000000000000000),(158954591/132744000),(44117044204913376731/100000000000000000000),(11029261051228344183/25000000000000000000),(725259056286153483/1000000000000000000),false⟩
theorem valid292 : certificate292.Valid := by decide +kernel
theorem bound292 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate292.a certificate292.b certificate292.c x ≤ (certificate292.bound:ℝ) :=
  rat_majority_certificate_sound certificate292 valid292 x hx0 hx1

def certificate293 : RatMajorityCertificate := ⟨(42334876206334941/200000000000000000),(15857244341085417174940390063015879/20000000000000000000000000000000000),(158954591/132744000),(39492679552368091049/100000000000000000000),(789853591047361821/2000000000000000000),(725259056286153483/1000000000000000000),false⟩
theorem valid293 : certificate293.Valid := by decide +kernel
theorem bound293 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate293.a certificate293.b certificate293.c x ≤ (certificate293.bound:ℝ) :=
  rat_majority_certificate_sound certificate293 valid293 x hx0 hx1

def certificate294 : RatMajorityCertificate := ⟨0,(100575472619027981/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(542975856841041669/1000000000000000000),false⟩
theorem valid294 : certificate294.Valid := by decide +kernel
theorem bound294 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate294.a certificate294.b certificate294.c x ≤ (certificate294.bound:ℝ) :=
  rat_majority_certificate_sound certificate294 valid294 x hx0 hx1

def certificate295 : RatMajorityCertificate := ⟨(65280057628387901/500000000000000000),(43722163660941494484571117359142119/50000000000000000000000000000000000),1,(18250386498195247303/50000000000000000000),(36500772996390494607/100000000000000000000),(542975856841041669/1000000000000000000),false⟩
theorem valid295 : certificate295.Valid := by decide +kernel
theorem bound295 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate295.a certificate295.b certificate295.c x ≤ (certificate295.bound:ℝ) :=
  rat_majority_certificate_sound certificate295 valid295 x hx0 hx1

def certificate296 : RatMajorityCertificate := ⟨0,(201160272052086753/200000000000000000),(238348641/199015000),(22060650751538229503/50000000000000000000),(44121301503076459007/100000000000000000000),(725618654364167109/1000000000000000000),false⟩
theorem valid296 : certificate296.Valid := by decide +kernel
theorem bound296 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate296.a certificate296.b certificate296.c x ≤ (certificate296.bound:ℝ) :=
  rat_majority_certificate_sound certificate296 valid296 x hx0 hx1

def certificate297 : RatMajorityCertificate := ⟨(213330344208536807/1000000000000000000),(158246681974132179235673458842382329/200000000000000000000000000000000000),(238348641/199015000),(19726736837946685223/50000000000000000000),(39453473675893370447/100000000000000000000),(725618654364167109/1000000000000000000),false⟩
theorem valid297 : certificate297.Valid := by decide +kernel
theorem bound297 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate297.a certificate297.b certificate297.c x ≤ (certificate297.bound:ℝ) :=
  rat_majority_certificate_sound certificate297 valid297 x hx0 hx1

def certificate298 : RatMajorityCertificate := ⟨0,(201160272052086753/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135745506266726243/250000000000000000),false⟩
theorem valid298 : certificate298.Valid := by decide +kernel
theorem bound298 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate298.a certificate298.b certificate298.c x ≤ (certificate298.bound:ℝ) :=
  rat_majority_certificate_sound certificate298 valid298 x hx0 hx1

def certificate299 : RatMajorityCertificate := ⟨(65208386541816579/500000000000000000),(87462799249213920970918387678322013/100000000000000000000000000000000000),1,(36504250451231085543/100000000000000000000),(4563031306403885693/12500000000000000000),(135745506266726243/250000000000000000),false⟩
theorem valid299 : certificate299.Valid := by decide +kernel
theorem bound299 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate299.a certificate299.b certificate299.c x ≤ (certificate299.bound:ℝ) :=
  rat_majority_certificate_sound certificate299 valid299 x hx0 hx1

def certificate300 : RatMajorityCertificate := ⟨0,(1005848030043886201/1000000000000000000),(2381126389/1989140000),(44108300487419329289/100000000000000000000),(4410830048741932929/10000000000000000000),(72492174666023131/100000000000000000),false⟩
theorem valid300 : certificate300.Valid := by decide +kernel
theorem bound300 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate300.a certificate300.b certificate300.c x ≤ (certificate300.bound:ℝ) :=
  rat_majority_certificate_sound certificate300 valid300 x hx0 hx1

def certificate301 : RatMajorityCertificate := ⟨(105646536909890377/500000000000000000),(396659653990171152124811322027012223/500000000000000000000000000000000000),(2381126389/1989140000),(39494036582666956879/100000000000000000000),(493675457283336961/1250000000000000000),(72492174666023131/100000000000000000),false⟩
theorem valid301 : certificate301.Valid := by decide +kernel
theorem bound301 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate301.a certificate301.b certificate301.c x ≤ (certificate301.bound:ℝ) :=
  rat_majority_certificate_sound certificate301 valid301 x hx0 hx1

def certificate302 : RatMajorityCertificate := ⟨0,(1005848030043886201/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(108600645202111751/200000000000000000),false⟩
theorem valid302 : certificate302.Valid := by decide +kernel
theorem bound302 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate302.a certificate302.b certificate302.c x ≤ (certificate302.bound:ℝ) :=
  rat_majority_certificate_sound certificate302 valid302 x hx0 hx1

def certificate303 : RatMajorityCertificate := ⟨(16301917714059161/125000000000000000),(109333751936861835492212509134462639/125000000000000000000000000000000000),1,(730088141138347859/2000000000000000000),(36504407056917392951/100000000000000000000),(108600645202111751/200000000000000000),false⟩
theorem valid303 : certificate303.Valid := by decide +kernel
theorem bound303 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate303.a certificate303.b certificate303.c x ≤ (certificate303.bound:ℝ) :=
  rat_majority_certificate_sound certificate303 valid303 x hx0 hx1

def certificate304 : RatMajorityCertificate := ⟨0,(2011789406963521/2000000000000000),(339970391/284020000),(5513344450302122377/12500000000000000000),(44106755602416979017/100000000000000000000),(90621785116226011/125000000000000000),false⟩
theorem valid304 : certificate304.Valid := by decide +kernel
theorem bound304 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate304.a certificate304.b certificate304.c x ≤ (certificate304.bound:ℝ) :=
  rat_majority_certificate_sound certificate304 valid304 x hx0 hx1

def certificate305 : RatMajorityCertificate := ⟨(106099808075927703/500000000000000000),(792444233513746510305559645677737/1000000000000000000000000000000000),(339970391/284020000),(39468654550616216367/100000000000000000000),(2466790909413513523/6250000000000000000),(90621785116226011/125000000000000000),false⟩
theorem valid305 : certificate305.Valid := by decide +kernel
theorem bound305 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate305.a certificate305.b certificate305.c x ≤ (certificate305.bound:ℝ) :=
  rat_majority_certificate_sound certificate305 valid305 x hx0 hx1

def certificate306 : RatMajorityCertificate := ⟨0,(2011789406963521/2000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543006979578935267/1000000000000000000),false⟩
theorem valid306 : certificate306.Valid := by decide +kernel
theorem bound306 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate306.a certificate306.b certificate306.c x ≤ (certificate306.bound:ℝ) :=
  rat_majority_certificate_sound certificate306 valid306 x hx0 hx1

def certificate307 : RatMajorityCertificate := ⟨(65124410197350463/500000000000000000),(874878104911983732429643706539777/1000000000000000000000000000000000),1,(36508425410380836497/100000000000000000000),(18254212705190418249/50000000000000000000),(543006979578935267/1000000000000000000),false⟩
theorem valid307 : certificate307.Valid := by decide +kernel
theorem bound307 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate307.a certificate307.b certificate307.c x ≤ (certificate307.bound:ℝ) :=
  rat_majority_certificate_sound certificate307 valid307 x hx0 hx1

def certificate308 : RatMajorityCertificate := ⟨0,(502970688770813271/500000000000000000),(2379886393/1987150000),(11030305323459673809/25000000000000000000),(44121221293838695237/100000000000000000000),(90749062905134489/125000000000000000),false⟩
theorem valid308 : certificate308.Valid := by decide +kernel
theorem bound308 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate308.a certificate308.b certificate308.c x ≤ (certificate308.bound:ℝ) :=
  rat_majority_certificate_sound certificate308 valid308 x hx0 hx1

def certificate309 : RatMajorityCertificate := ⟨(108181266072166363/500000000000000000),(197073338476990506689424379679796627/250000000000000000000000000000000000),(2379886393/1987150000),(9843333688174814781/25000000000000000000),(314986678021594073/800000000000000000),(90749062905134489/125000000000000000),false⟩
theorem valid309 : certificate309.Valid := by decide +kernel
theorem bound309 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate309.a certificate309.b certificate309.c x ≤ (certificate309.bound:ℝ) :=
  rat_majority_certificate_sound certificate309 valid309 x hx0 hx1

def certificate310 : RatMajorityCertificate := ⟨0,(502970688770813271/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543028256866526031/1000000000000000000),false⟩
theorem valid310 : certificate310.Valid := by decide +kernel
theorem bound310 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate310.a certificate310.b certificate310.c x ≤ (certificate310.bound:ℝ) :=
  rat_majority_certificate_sound certificate310 valid310 x hx0 hx1

def certificate311 : RatMajorityCertificate := ⟨(130248050395874441/1000000000000000000),(437459737152144705281597769227493489/500000000000000000000000000000000000),1,(1460342654097479037/4000000000000000000),(18254283176218487963/50000000000000000000),(543028256866526031/1000000000000000000),false⟩
theorem valid311 : certificate311.Valid := by decide +kernel
theorem bound311 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate311.a certificate311.b certificate311.c x ≤ (certificate311.bound:ℝ) :=
  rat_majority_certificate_sound certificate311 valid311 x hx0 hx1

def certificate312 : RatMajorityCertificate := ⟨0,(1005988049187207481/1000000000000000000),(95045517/79446800),(44092069268122962483/100000000000000000000),(11023017317030740621/25000000000000000000),(362162033528628973/500000000000000000),false⟩
theorem valid312 : certificate312.Valid := by decide +kernel
theorem bound312 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate312.a certificate312.b certificate312.c x ≤ (certificate312.bound:ℝ) :=
  rat_majority_certificate_sound certificate312 valid312 x hx0 hx1

def certificate313 : RatMajorityCertificate := ⟨(105529740406776341/500000000000000000),(396832366910558385965914776870992979/500000000000000000000000000000000000),(95045517/79446800),(3948387270117879867/10000000000000000000),(39483872701178798671/100000000000000000000),(362162033528628973/500000000000000000),false⟩
theorem valid313 : certificate313.Valid := by decide +kernel
theorem bound313 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate313.a certificate313.b certificate313.c x ≤ (certificate313.bound:ℝ) :=
  rat_majority_certificate_sound certificate313 valid313 x hx0 hx1

def certificate314 : RatMajorityCertificate := ⟨0,(1005988049187207481/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543031805300947067/1000000000000000000),false⟩
theorem valid314 : certificate314.Valid := by decide +kernel
theorem bound314 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate314.a certificate314.b certificate314.c x ≤ (certificate314.bound:ℝ) :=
  rat_majority_certificate_sound certificate314 valid314 x hx0 hx1

def certificate315 : RatMajorityCertificate := ⟨(65039699832985049/500000000000000000),(437564863838897566839591347266048431/500000000000000000000000000000000000),1,(9128158194492168359/25000000000000000000),(36512632777968673437/100000000000000000000),(543031805300947067/1000000000000000000),false⟩
theorem valid315 : certificate315.Valid := by decide +kernel
theorem bound315 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate315.a certificate315.b certificate315.c x ≤ (certificate315.bound:ℝ) :=
  rat_majority_certificate_sound certificate315 valid315 x hx0 hx1

def certificate316 : RatMajorityCertificate := ⟨0,(4024232188047261/4000000000000000),(2376825059/1977590000),(5527043728193987427/12500000000000000000),(44216349825551899417/100000000000000000000),(729665532219830377/1000000000000000000),false⟩
theorem valid316 : certificate316.Valid := by decide +kernel
theorem bound316 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate316.a certificate316.b certificate316.c x ≤ (certificate316.bound:ℝ) :=
  rat_majority_certificate_sound certificate316 valid316 x hx0 hx1

def certificate317 : RatMajorityCertificate := ⟨(107039614180627361/500000000000000000),(1581363833241789828624513502291779/2000000000000000000000000000000000),(2376825059/1977590000),(19767033812309862709/50000000000000000000),(39534067624619725419/100000000000000000000),(729665532219830377/1000000000000000000),false⟩
theorem valid317 : certificate317.Valid := by decide +kernel
theorem bound317 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate317.a certificate317.b certificate317.c x ≤ (certificate317.bound:ℝ) :=
  rat_majority_certificate_sound certificate317 valid317 x hx0 hx1

def certificate318 : RatMajorityCertificate := ⟨0,(4024232188047261/4000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271601229843435523/500000000000000000),false⟩
theorem valid318 : certificate318.Valid := by decide +kernel
theorem bound318 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate318.a certificate318.b certificate318.c x ≤ (certificate318.bound:ℝ) :=
  rat_majority_certificate_sound certificate318 valid318 x hx0 hx1

def certificate319 : RatMajorityCertificate := ⟨(16423831685322513/125000000000000000),(436935711386762274315071528713107/500000000000000000000000000000000),1,(7296425327384501661/20000000000000000000),(18241063318461254153/50000000000000000000),(271601229843435523/500000000000000000),false⟩
theorem valid319 : certificate319.Valid := by decide +kernel
theorem bound319 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate319.a certificate319.b certificate319.c x ≤ (certificate319.bound:ℝ) :=
  rat_majority_certificate_sound certificate319 valid319 x hx0 hx1

end Cycle12.MajorityCertificates.Batch007
