import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch022

def certificate880 : RatMajorityCertificate := ⟨0,(1003349511063246311/1000000000000000000),(1213821843/1041340000),(43390798016457199501/100000000000000000000),(21695399008228599751/50000000000000000000),(4319391409990637/6250000000000000),false⟩
theorem valid880 : certificate880.Valid := by decide +kernel
theorem bound880 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate880.a certificate880.b certificate880.c x ≤ (certificate880.bound:ℝ) :=
  rat_majority_certificate_sound certificate880 valid880 x hx0 hx1

def certificate881 : RatMajorityCertificate := ⟨(168275271425760267/1000000000000000000),(834510599754174684152117515741874963/1000000000000000000000000000000000000),(1213821843/1041340000),(4979231314662745779/12500000000000000000),(39833850517301966233/100000000000000000000),(4319391409990637/6250000000000000),false⟩
theorem valid881 : certificate881.Valid := by decide +kernel
theorem bound881 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate881.a certificate881.b certificate881.c x ≤ (certificate881.bound:ℝ) :=
  rat_majority_certificate_sound certificate881 valid881 x hx0 hx1

def certificate882 : RatMajorityCertificate := ⟨0,(1003349511063246311/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(67556581733346349/125000000000000000),false⟩
theorem valid882 : certificate882.Valid := by decide +kernel
theorem bound882 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate882.a certificate882.b certificate882.c x ≤ (certificate882.bound:ℝ) :=
  rat_majority_certificate_sound certificate882 valid882 x hx0 hx1

def certificate883 : RatMajorityCertificate := ⟨(3658006507192747/31250000000000000),(27684413180268431116359346786293683/31250000000000000000000000000000000),1,(9201843145368747903/25000000000000000000),(36807372581474991613/100000000000000000000),(67556581733346349/125000000000000000),false⟩
theorem valid883 : certificate883.Valid := by decide +kernel
theorem bound883 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate883.a certificate883.b certificate883.c x ≤ (certificate883.bound:ℝ) :=
  rat_majority_certificate_sound certificate883 valid883 x hx0 hx1

def certificate884 : RatMajorityCertificate := ⟨0,(50172819154152491/50000000000000000),(605030463/519762500),(21677044868984278471/50000000000000000000),(43354089737968556943/100000000000000000000),(689580742084930241/1000000000000000000),false⟩
theorem valid884 : certificate884.Valid := by decide +kernel
theorem bound884 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate884.a certificate884.b certificate884.c x ≤ (certificate884.bound:ℝ) :=
  rat_majority_certificate_sound certificate884 valid884 x hx0 hx1

def certificate885 : RatMajorityCertificate := ⟨(83283436656681003/500000000000000000),(20907844771164275176074454595171527/25000000000000000000000000000000000),(605030463/519762500),(19919062792720584309/50000000000000000000),(39838125585441168619/100000000000000000000),(689580742084930241/1000000000000000000),false⟩
theorem valid885 : certificate885.Valid := by decide +kernel
theorem bound885 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate885.a certificate885.b certificate885.c x ≤ (certificate885.bound:ℝ) :=
  rat_majority_certificate_sound certificate885 valid885 x hx0 hx1

def certificate886 : RatMajorityCertificate := ⟨0,(50172819154152491/50000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270219997706550467/500000000000000000),false⟩
theorem valid886 : certificate886.Valid := by decide +kernel
theorem bound886 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate886.a certificate886.b certificate886.c x ≤ (certificate886.bound:ℝ) :=
  rat_majority_certificate_sound certificate886 valid886 x hx0 hx1

def certificate887 : RatMajorityCertificate := ⟨(116453620072321409/1000000000000000000),(44330012734417526416302083650020181/50000000000000000000000000000000000),1,(36821414179566748521/100000000000000000000),(18410707089783374261/50000000000000000000),(270219997706550467/500000000000000000),false⟩
theorem valid887 : certificate887.Valid := by decide +kernel
theorem bound887 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate887.a certificate887.b certificate887.c x ≤ (certificate887.bound:ℝ) :=
  rat_majority_certificate_sound certificate887 valid887 x hx0 hx1

def certificate888 : RatMajorityCertificate := ⟨0,(1003541192477395193/1000000000000000000),(2412021201/2076710000),(2164696068845158229/5000000000000000000),(43293921376903164581/100000000000000000000),(687112301972079277/1000000000000000000),false⟩
theorem valid888 : certificate888.Valid := by decide +kernel
theorem bound888 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate888.a certificate888.b certificate888.c x ≤ (certificate888.bound:ℝ) :=
  rat_majority_certificate_sound certificate888 valid888 x hx0 hx1

def certificate889 : RatMajorityCertificate := ⟨(164542999917904463/1000000000000000000),(838415514125973408856253118730553641/1000000000000000000000000000000000000),(2412021201/2076710000),(39825710343745617013/100000000000000000000),(19912855171872808507/50000000000000000000),(687112301972079277/1000000000000000000),false⟩
theorem valid889 : certificate889.Valid := by decide +kernel
theorem bound889 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate889.a certificate889.b certificate889.c x ≤ (certificate889.bound:ℝ) :=
  rat_majority_certificate_sound certificate889 valid889 x hx0 hx1

def certificate890 : RatMajorityCertificate := ⟨0,(1003541192477395193/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270209718432302693/500000000000000000),false⟩
theorem valid890 : certificate890.Valid := by decide +kernel
theorem bound890 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate890.a certificate890.b certificate890.c x ≤ (certificate890.bound:ℝ) :=
  rat_majority_certificate_sound certificate890 valid890 x hx0 hx1

def certificate891 : RatMajorityCertificate := ⟨(115872418741966103/1000000000000000000),(887258447197842453863087499058857121/1000000000000000000000000000000000000),1,(3683489817884001/10000000000000000),(36834898178840010001/100000000000000000000),(270209718432302693/500000000000000000),false⟩
theorem valid891 : certificate891.Valid := by decide +kernel
theorem bound891 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate891.a certificate891.b certificate891.c x ≤ (certificate891.bound:ℝ) :=
  rat_majority_certificate_sound certificate891 valid891 x hx0 hx1

def certificate892 : RatMajorityCertificate := ⟨0,(1003625300518014481/1000000000000000000),(1202015249/1037235000),(43233400960627620457/100000000000000000000),(21616700480313810229/50000000000000000000),(684641862048884403/1000000000000000000),false⟩
theorem valid892 : certificate892.Valid := by decide +kernel
theorem bound892 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate892.a certificate892.b certificate892.c x ≤ (certificate892.bound:ℝ) :=
  rat_majority_certificate_sound certificate892 valid892 x hx0 hx1

def certificate893 : RatMajorityCertificate := ⟨(162574029684375041/1000000000000000000),(840461891119608973552832569327031279/1000000000000000000000000000000000000),(1202015249/1037235000),(39811464023756575071/100000000000000000000),(1244108250742392971/3125000000000000000),(684641862048884403/1000000000000000000),false⟩
theorem valid893 : certificate893.Valid := by decide +kernel
theorem bound893 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate893.a certificate893.b certificate893.c x ≤ (certificate893.bound:ℝ) :=
  rat_majority_certificate_sound certificate893 valid893 x hx0 hx1

def certificate894 : RatMajorityCertificate := ⟨0,(1003625300518014481/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540330690158854977/1000000000000000000),false⟩
theorem valid894 : certificate894.Valid := by decide +kernel
theorem bound894 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate894.a certificate894.b certificate894.c x ≤ (certificate894.bound:ℝ) :=
  rat_majority_certificate_sound certificate894 valid894 x hx0 hx1

def certificate895 : RatMajorityCertificate := ⟨(114630392275135481/1000000000000000000),(888579338622383748179499984605099639/1000000000000000000000000000000000000),1,(18431718287016027713/50000000000000000000),(36863436574032055427/100000000000000000000),(540330690158854977/1000000000000000000),false⟩
theorem valid895 : certificate895.Valid := by decide +kernel
theorem bound895 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate895.a certificate895.b certificate895.c x ≤ (certificate895.bound:ℝ) :=
  rat_majority_certificate_sound certificate895 valid895 x hx0 hx1

def certificate896 : RatMajorityCertificate := ⟨0,(40145713252148057/40000000000000000),(299984213/259328750),(21592265519156638787/50000000000000000000),(1727381241532531103/4000000000000000000),(136501593886747567/200000000000000000),false⟩
theorem valid896 : certificate896.Valid := by decide +kernel
theorem bound896 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate896.a certificate896.b certificate896.c x ≤ (certificate896.bound:ℝ) :=
  rat_majority_certificate_sound certificate896 valid896 x hx0 hx1

def certificate897 : RatMajorityCertificate := ⟨(9981462883154767/62500000000000000),(2108394131515163279931036470662281/2500000000000000000000000000000000),(299984213/259328750),(39830648034111067371/100000000000000000000),(9957662008527766843/25000000000000000000),(136501593886747567/200000000000000000),false⟩
theorem valid897 : certificate897.Valid := by decide +kernel
theorem bound897 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate897.a certificate897.b certificate897.c x ≤ (certificate897.bound:ℝ) :=
  rat_majority_certificate_sound certificate897 valid897 x hx0 hx1

def certificate898 : RatMajorityCertificate := ⟨0,(40145713252148057/40000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270098254027137529/500000000000000000),false⟩
theorem valid898 : certificate898.Valid := by decide +kernel
theorem bound898 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate898.a certificate898.b certificate898.c x ≤ (certificate898.bound:ℝ) :=
  rat_majority_certificate_sound certificate898 valid898 x hx0 hx1

def certificate899 : RatMajorityCertificate := ⟨(7077709829431819/62500000000000000),(2224967368964974022357018425174317/2500000000000000000000000000000000),1,(1844752711169362387/5000000000000000000),(36895054223387247741/100000000000000000000),(270098254027137529/500000000000000000),false⟩
theorem valid899 : certificate899.Valid := by decide +kernel
theorem bound899 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate899.a certificate899.b certificate899.c x ≤ (certificate899.bound:ℝ) :=
  rat_majority_certificate_sound certificate899 valid899 x hx0 hx1

def certificate900 : RatMajorityCertificate := ⟨0,(125460497637424747/125000000000000000),(2395013701/2073580000),(43143407294570783029/100000000000000000000),(4314340729457078303/10000000000000000000),(42552020310731221/62500000000000000),false⟩
theorem valid900 : certificate900.Valid := by decide +kernel
theorem bound900 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate900.a certificate900.b certificate900.c x ≤ (certificate900.bound:ℝ) :=
  rat_majority_certificate_sound certificate900 valid900 x hx0 hx1

def certificate901 : RatMajorityCertificate := ⟨(158409239399218783/1000000000000000000),(105586395632032807726575384248577099/125000000000000000000000000000000000),(2395013701/2073580000),(9954913931032326547/25000000000000000000),(39819655724129306189/100000000000000000000),(42552020310731221/62500000000000000),false⟩
theorem valid901 : certificate901.Valid := by decide +kernel
theorem bound901 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate901.a certificate901.b certificate901.c x ≤ (certificate901.bound:ℝ) :=
  rat_majority_certificate_sound certificate901 valid901 x hx0 hx1

def certificate902 : RatMajorityCertificate := ⟨0,(125460497637424747/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(33760409422890077/62500000000000000),false⟩
theorem valid902 : certificate902.Valid := by decide +kernel
theorem bound902 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate902.a certificate902.b certificate902.c x ≤ (certificate902.bound:ℝ) :=
  rat_majority_certificate_sound certificate902 valid902 x hx0 hx1

def certificate903 : RatMajorityCertificate := ⟨(112762990963032909/1000000000000000000),(111313196676118208623929688628000977/125000000000000000000000000000000000),1,(576657272008206809/1562500000000000000),(36906065408525235777/100000000000000000000),(33760409422890077/62500000000000000),false⟩
theorem valid903 : certificate903.Valid := by decide +kernel
theorem bound903 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate903.a certificate903.b certificate903.c x ≤ (certificate903.bound:ℝ) :=
  rat_majority_certificate_sound certificate903 valid903 x hx0 hx1

def certificate904 : RatMajorityCertificate := ⟨0,(1003724921230936827/1000000000000000000),(3987939/3454250),(43131423321641144477/100000000000000000000),(21565711660820572239/50000000000000000000),(680526454747379423/1000000000000000000),false⟩
theorem valid904 : certificate904.Valid := by decide +kernel
theorem bound904 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate904.a certificate904.b certificate904.c x ≤ (certificate904.bound:ℝ) :=
  rat_majority_certificate_sound certificate904 valid904 x hx0 hx1

def certificate905 : RatMajorityCertificate := ⟨(159862560767786823/1000000000000000000),(843266885016514146199676644283969379/1000000000000000000000000000000000000),(3987939/3454250),(9943102445218194091/25000000000000000000),(7954481956174555273/20000000000000000000),(680526454747379423/1000000000000000000),false⟩
theorem valid905 : certificate905.Valid := by decide +kernel
theorem bound905 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate905.a certificate905.b certificate905.c x ≤ (certificate905.bound:ℝ) :=
  rat_majority_certificate_sound certificate905 valid905 x hx0 hx1

def certificate906 : RatMajorityCertificate := ⟨0,(1003724921230936827/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270056518064326981/500000000000000000),false⟩
theorem valid906 : certificate906.Valid := by decide +kernel
theorem bound906 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate906.a certificate906.b certificate906.c x ≤ (certificate906.bound:ℝ) :=
  rat_majority_certificate_sound certificate906 valid906 x hx0 hx1

def certificate907 : RatMajorityCertificate := ⟨(4482085681275073/40000000000000000),(35650215751849340608229968327186629/40000000000000000000000000000000000),1,(36922296403627294261/100000000000000000000),(18461148201813647131/50000000000000000000),(270056518064326981/500000000000000000),false⟩
theorem valid907 : certificate907.Valid := by decide +kernel
theorem bound907 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate907.a certificate907.b certificate907.c x ≤ (certificate907.bound:ℝ) :=
  rat_majority_certificate_sound certificate907 valid907 x hx0 hx1

def certificate908 : RatMajorityCertificate := ⟨0,(125470702967251849/125000000000000000),(1194132047/1035775000),(21546787148681507163/50000000000000000000),(43093574297363014327/100000000000000000000),(169768855876873601/250000000000000000),false⟩
theorem valid908 : certificate908.Valid := by decide +kernel
theorem bound908 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate908.a certificate908.b certificate908.c x ≤ (certificate908.bound:ℝ) :=
  rat_majority_certificate_sound certificate908 valid908 x hx0 hx1

def certificate909 : RatMajorityCertificate := ⟨(39904919784891673/250000000000000000),(26360777404550807598602401026046623/31250000000000000000000000000000000),(1194132047/1035775000),(39739455811938221213/100000000000000000000),(19869727905969110607/50000000000000000000),(169768855876873601/250000000000000000),false⟩
theorem valid909 : certificate909.Valid := by decide +kernel
theorem bound909 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate909.a certificate909.b certificate909.c x ≤ (certificate909.bound:ℝ) :=
  rat_majority_certificate_sound certificate909 valid909 x hx0 hx1

def certificate910 : RatMajorityCertificate := ⟨0,(125470702967251849/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270041907150661391/500000000000000000),false⟩
theorem valid910 : certificate910.Valid := by decide +kernel
theorem bound910 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate910.a certificate910.b certificate910.c x ≤ (certificate910.bound:ℝ) :=
  rat_majority_certificate_sound certificate910 valid910 x hx0 hx1

def certificate911 : RatMajorityCertificate := ⟨(111579127188652589/1000000000000000000),(111470791442419205141022133471112939/125000000000000000000000000000000000),1,(9233278775626413603/25000000000000000000),(36933115102505654413/100000000000000000000),(270041907150661391/500000000000000000),false⟩
theorem valid911 : certificate911.Valid := by decide +kernel
theorem bound911 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate911.a certificate911.b certificate911.c x ≤ (certificate911.bound:ℝ) :=
  rat_majority_certificate_sound certificate911 valid911 x hx0 hx1

def certificate912 : RatMajorityCertificate := ⟨0,(1003806096752928541/1000000000000000000),(596281133/517642500),(5383849227845494513/12500000000000000000),(8614158764552791221/20000000000000000000),(135614873992521279/200000000000000000),false⟩
theorem valid912 : certificate912.Valid := by decide +kernel
theorem bound912 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate912.a certificate912.b certificate912.c x ≤ (certificate912.bound:ℝ) :=
  rat_majority_certificate_sound certificate912 valid912 x hx0 hx1

def certificate913 : RatMajorityCertificate := ⟨(7897728556192793/50000000000000000),(42262516762440397646305595851794987/50000000000000000000000000000000000),(596281133/517642500),(4969536269807646271/12500000000000000000),(39756290158461170169/100000000000000000000),(135614873992521279/200000000000000000),false⟩
theorem valid913 : certificate913.Valid := by decide +kernel
theorem bound913 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate913.a certificate913.b certificate913.c x ≤ (certificate913.bound:ℝ) :=
  rat_majority_certificate_sound certificate913 valid913 x hx0 hx1

def certificate914 : RatMajorityCertificate := ⟨0,(1003806096752928541/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540075416770798237/1000000000000000000),false⟩
theorem valid914 : certificate914.Valid := by decide +kernel
theorem bound914 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate914.a certificate914.b certificate914.c x ≤ (certificate914.bound:ℝ) :=
  rat_majority_certificate_sound certificate914 valid914 x hx0 hx1

def certificate915 : RatMajorityCertificate := ⟨(111310868620056253/1000000000000000000),(892071568197251836468140074090783127/1000000000000000000000000000000000000),1,(36939285140861690801/100000000000000000000),(18469642570430845401/50000000000000000000),(540075416770798237/1000000000000000000),false⟩
theorem valid915 : certificate915.Valid := by decide +kernel
theorem bound915 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate915.a certificate915.b certificate915.c x ≤ (certificate915.bound:ℝ) :=
  rat_majority_certificate_sound certificate915 valid915 x hx0 hx1

def certificate916 : RatMajorityCertificate := ⟨0,(50192316531731491/50000000000000000),(238030463/206961000),(336161090555920221/781250000000000000),(43028619591157788289/100000000000000000000),(676338450161962633/1000000000000000000),false⟩
theorem valid916 : certificate916.Valid := by decide +kernel
theorem bound916 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate916.a certificate916.b certificate916.c x ≤ (certificate916.bound:ℝ) :=
  rat_majority_certificate_sound certificate916 valid916 x hx0 hx1

def certificate917 : RatMajorityCertificate := ⟨(39086942830378247/250000000000000000),(10586214926132834987221162628723723/12500000000000000000000000000000000),(238030463/206961000),(39751672237900418057/100000000000000000000),(19875836118950209029/50000000000000000000),(676338450161962633/1000000000000000000),false⟩
theorem valid917 : certificate917.Valid := by decide +kernel
theorem bound917 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate917.a certificate917.b certificate917.c x ≤ (certificate917.bound:ℝ) :=
  rat_majority_certificate_sound certificate917 valid917 x hx0 hx1

def certificate918 : RatMajorityCertificate := ⟨0,(50192316531731491/50000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(539993860959519651/1000000000000000000),false⟩
theorem valid918 : certificate918.Valid := by decide +kernel
theorem bound918 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate918.a certificate918.b certificate918.c x ≤ (certificate918.bound:ℝ) :=
  rat_majority_certificate_sound certificate918 valid918 x hx0 hx1

def certificate919 : RatMajorityCertificate := ⟨(110323981664402653/1000000000000000000),(44654900322990851825916167695954377/50000000000000000000000000000000000),1,(1478468592956731163/4000000000000000000),(9240428705979569769/25000000000000000000),(539993860959519651/1000000000000000000),false⟩
theorem valid919 : certificate919.Valid := by decide +kernel
theorem bound919 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate919.a certificate919.b certificate919.c x ≤ (certificate919.bound:ℝ) :=
  rat_majority_certificate_sound certificate919 valid919 x hx0 hx1

end Cycle12.MajorityCertificates.Batch022
