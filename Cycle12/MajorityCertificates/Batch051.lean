import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch051

def certificate2040 : RatMajorityCertificate := ⟨0,(1000055199604832851/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(276098957335667393/500000000000000000),false⟩
theorem valid2040 : certificate2040.Valid := by decide +kernel
theorem bound2040 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2040.a certificate2040.b certificate2040.c x ≤ (certificate2040.bound:ℝ) :=
  rat_majority_certificate_sound certificate2040 valid2040 x hx0 hx1

def certificate2041 : RatMajorityCertificate := ⟨(113233322147182879/500000000000000000),(386788027220597111089780016676041971/500000000000000000000000000000000000),1,(17007155478719027719/50000000000000000000),(34014310957438055439/100000000000000000000),(276098957335667393/500000000000000000),false⟩
theorem valid2041 : certificate2041.Valid := by decide +kernel
theorem bound2041 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2041.a certificate2041.b certificate2041.c x ≤ (certificate2041.bound:ℝ) :=
  rat_majority_certificate_sound certificate2041 valid2041 x hx0 hx1

def certificate2042 : RatMajorityCertificate := ⟨0,(1000055199604832851/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(545229031101170699/1000000000000000000),false⟩
theorem valid2042 : certificate2042.Valid := by decide +kernel
theorem bound2042 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2042.a certificate2042.b certificate2042.c x ≤ (certificate2042.bound:ℝ) :=
  rat_majority_certificate_sound certificate2042 valid2042 x hx0 hx1

def certificate2043 : RatMajorityCertificate := ⟨(10802039292554253/62500000000000000),(51700814414447462263359041085834697/62500000000000000000000000000000000),1,(35451529106296057351/100000000000000000000),(4431441138287007169/12500000000000000000),(545229031101170699/1000000000000000000),false⟩
theorem valid2043 : certificate2043.Valid := by decide +kernel
theorem bound2043 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2043.a certificate2043.b certificate2043.c x ≤ (certificate2043.bound:ℝ) :=
  rat_majority_certificate_sound certificate2043 valid2043 x hx0 hx1

def certificate2044 : RatMajorityCertificate := ⟨0,(1000056660732523499/1000000000000000000),(2288091/1880000),(5569230734859882789/12500000000000000000),(44553845878879062313/100000000000000000000),(735875482742043257/1000000000000000000),false⟩
theorem valid2044 : certificate2044.Valid := by decide +kernel
theorem bound2044 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2044.a certificate2044.b certificate2044.c x ≤ (certificate2044.bound:ℝ) :=
  rat_majority_certificate_sound certificate2044 valid2044 x hx0 hx1

def certificate2045 : RatMajorityCertificate := ⟨(168970749789879023/1000000000000000000),(831076336936186336589821123285338523/1000000000000000000000000000000000000),(2288091/1880000),(5126049146988163149/12500000000000000000),(41008393175905305193/100000000000000000000),(735875482742043257/1000000000000000000),false⟩
theorem valid2045 : certificate2045.Valid := by decide +kernel
theorem bound2045 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2045.a certificate2045.b certificate2045.c x ≤ (certificate2045.bound:ℝ) :=
  rat_majority_certificate_sound certificate2045 valid2045 x hx0 hx1

def certificate2046 : RatMajorityCertificate := ⟨0,(1000056660732523499/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(276136880931338173/500000000000000000),false⟩
theorem valid2046 : certificate2046.Valid := by decide +kernel
theorem bound2046 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2046.a certificate2046.b certificate2046.c x ≤ (certificate2046.bound:ℝ) :=
  rat_majority_certificate_sound certificate2046 valid2046 x hx0 hx1

def certificate2047 : RatMajorityCertificate := ⟨(113503500508439707/500000000000000000),(386518398666339252965010846797825207/500000000000000000000000000000000000),1,(33999051719407035031/100000000000000000000),(4249881464925879379/12500000000000000000),(276136880931338173/500000000000000000),false⟩
theorem valid2047 : certificate2047.Valid := by decide +kernel
theorem bound2047 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2047.a certificate2047.b certificate2047.c x ≤ (certificate2047.bound:ℝ) :=
  rat_majority_certificate_sound certificate2047 valid2047 x hx0 hx1

def certificate2048 : RatMajorityCertificate := ⟨0,(1000056660732523499/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(13624106345986543/25000000000000000),false⟩
theorem valid2048 : certificate2048.Valid := by decide +kernel
theorem bound2048 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2048.a certificate2048.b certificate2048.c x ≤ (certificate2048.bound:ℝ) :=
  rat_majority_certificate_sound certificate2048 valid2048 x hx0 hx1

def certificate2049 : RatMajorityCertificate := ⟨(8531835865459271/50000000000000000),(41470513751096996766645221565090771/50000000000000000000000000000000000),1,(35507272645740958699/100000000000000000000),(355072726457409587/1000000000000000000),(13624106345986543/25000000000000000),false⟩
theorem valid2049 : certificate2049.Valid := by decide +kernel
theorem bound2049 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2049.a certificate2049.b certificate2049.c x ≤ (certificate2049.bound:ℝ) :=
  rat_majority_certificate_sound certificate2049 valid2049 x hx0 hx1

def certificate2050 : RatMajorityCertificate := ⟨0,(1000058113853359197/1000000000000000000),(114496289/94000000),(5571920046355937177/12500000000000000000),(44575360370847497417/100000000000000000000),(368340894508433853/500000000000000000),false⟩
theorem valid2050 : certificate2050.Valid := by decide +kernel
theorem bound2050 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2050.a certificate2050.b certificate2050.c x ≤ (certificate2050.bound:ℝ) :=
  rat_majority_certificate_sound certificate2050 valid2050 x hx0 hx1

def certificate2051 : RatMajorityCertificate := ⟨(41994507338072613/250000000000000000),(208017580662625849775812478442628239/250000000000000000000000000000000000),(114496289/94000000),(20527420627700550807/50000000000000000000),(8210968251080220323/20000000000000000000),(368340894508433853/500000000000000000),false⟩
theorem valid2051 : certificate2051.Valid := by decide +kernel
theorem bound2051 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2051.a certificate2051.b certificate2051.c x ≤ (certificate2051.bound:ℝ) :=
  rat_majority_certificate_sound certificate2051 valid2051 x hx0 hx1

def certificate2052 : RatMajorityCertificate := ⟨0,(1000058113853359197/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(110469616590953897/200000000000000000),false⟩
theorem valid2052 : certificate2052.Valid := by decide +kernel
theorem bound2052 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2052.a certificate2052.b certificate2052.c x ≤ (certificate2052.bound:ℝ) :=
  rat_majority_certificate_sound certificate2052 valid2052 x hx0 hx1

def certificate2053 : RatMajorityCertificate := ⟨(56883922011883229/250000000000000000),(193127300707554275669641826242792887/250000000000000000000000000000000000),1,(33984106088770324643/100000000000000000000),(8496026522192581161/25000000000000000000),(110469616590953897/200000000000000000),false⟩
theorem valid2053 : certificate2053.Valid := by decide +kernel
theorem bound2053 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2053.a certificate2053.b certificate2053.c x ≤ (certificate2053.bound:ℝ) :=
  rat_majority_certificate_sound certificate2053 valid2053 x hx0 hx1

def certificate2054 : RatMajorityCertificate := ⟨0,(1000058113853359197/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(136175635106000661/250000000000000000),false⟩
theorem valid2054 : certificate2054.Valid := by decide +kernel
theorem bound2054 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2054.a certificate2054.b certificate2054.c x ≤ (certificate2054.bound:ℝ) :=
  rat_majority_certificate_sound certificate2054 valid2054 x hx0 hx1

def certificate2055 : RatMajorityCertificate := ⟨(21056759884196767/125000000000000000),(103949280658017002592079362922883901/125000000000000000000000000000000000),1,(17781225659098383049/50000000000000000000),(35562451318196766099/100000000000000000000),(136175635106000661/250000000000000000),false⟩
theorem valid2055 : certificate2055.Valid := by decide +kernel
theorem bound2055 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2055.a certificate2055.b certificate2055.c x ≤ (certificate2055.bound:ℝ) :=
  rat_majority_certificate_sound certificate2055 valid2055 x hx0 hx1

def certificate2056 : RatMajorityCertificate := ⟨0,(1000059557749470313/1000000000000000000),(2854790141/2350000000),(44503827960946836161/100000000000000000000),(22251913980473418081/50000000000000000000),(733394602007579383/1000000000000000000),false⟩
theorem valid2056 : certificate2056.Valid := by decide +kernel
theorem bound2056 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2056.a certificate2056.b certificate2056.c x ≤ (certificate2056.bound:ℝ) :=
  rat_majority_certificate_sound certificate2056 valid2056 x hx0 hx1

def certificate2057 : RatMajorityCertificate := ⟨(164072182888396249/1000000000000000000),(835977603091110549520638726193944063/1000000000000000000000000000000000000),(2854790141/2350000000),(41075320071901759253/100000000000000000000),(20537660035950879627/50000000000000000000),(733394602007579383/1000000000000000000),false⟩
theorem valid2057 : certificate2057.Valid := by decide +kernel
theorem bound2057 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2057.a certificate2057.b certificate2057.c x ≤ (certificate2057.bound:ℝ) :=
  rat_majority_certificate_sound certificate2057 valid2057 x hx0 hx1

def certificate2058 : RatMajorityCertificate := ⟨0,(1000059557749470313/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(69059014200840639/125000000000000000),false⟩
theorem valid2058 : certificate2058.Valid := by decide +kernel
theorem bound2058 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2058.a certificate2058.b certificate2058.c x ≤ (certificate2058.bound:ℝ) :=
  rat_majority_certificate_sound certificate2058 valid2058 x hx0 hx1

def certificate2059 : RatMajorityCertificate := ⟨(456838373948229/2000000000000000),(1543253533285287592212056765574323/2000000000000000000000000000000000),1,(1697954486681986391/5000000000000000000),(33959089733639727821/100000000000000000000),(69059014200840639/125000000000000000),false⟩
theorem valid2059 : certificate2059.Valid := by decide +kernel
theorem bound2059 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2059.a certificate2059.b certificate2059.c x ≤ (certificate2059.bound:ℝ) :=
  rat_majority_certificate_sound certificate2059 valid2059 x hx0 hx1

def certificate2060 : RatMajorityCertificate := ⟨0,(1000059557749470313/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(136116762475769427/250000000000000000),false⟩
theorem valid2060 : certificate2060.Valid := by decide +kernel
theorem bound2060 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2060.a certificate2060.b certificate2060.c x ≤ (certificate2060.bound:ℝ) :=
  rat_majority_certificate_sound certificate2060 valid2060 x hx0 hx1

def certificate2061 : RatMajorityCertificate := ⟨(166479249441171239/1000000000000000000),(833570393178868850977839193420072193/1000000000000000000000000000000000000),1,(17806091165669467187/50000000000000000000),(11395898346028459/32000000000000000),(136116762475769427/250000000000000000),false⟩
theorem valid2061 : certificate2061.Valid := by decide +kernel
theorem bound2061 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2061.a certificate2061.b certificate2061.c x ≤ (certificate2061.bound:ℝ) :=
  rat_majority_certificate_sound certificate2061 valid2061 x hx0 hx1

def certificate2062 : RatMajorityCertificate := ⟨0,(1000060991212358183/1000000000000000000),(573402831/470000000),(22309257649134690803/50000000000000000000),(44618515298269381607/100000000000000000000),(184576527645271549/250000000000000000),false⟩
theorem valid2062 : certificate2062.Valid := by decide +kernel
theorem bound2062 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2062.a certificate2062.b certificate2062.c x ≤ (certificate2062.bound:ℝ) :=
  rat_majority_certificate_sound certificate2062 valid2062 x hx0 hx1

def certificate2063 : RatMajorityCertificate := ⟨(166008827734885323/1000000000000000000),(834042038397807148589524654094351891/1000000000000000000000000000000000000),(573402831/470000000),(82294626095456259773599/200000000000000000000000),(102868282619320324716999/250000000000000000000000),(184576527645271549/250000000000000000),false⟩
theorem valid2063 : certificate2063.Valid := by decide +kernel
theorem bound2063 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2063.a certificate2063.b certificate2063.c x ≤ (certificate2063.bound:ℝ) :=
  rat_majority_certificate_sound certificate2063 valid2063 x hx0 hx1

def certificate2064 : RatMajorityCertificate := ⟨0,(1000060991212358183/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(552482429345435931/1000000000000000000),false⟩
theorem valid2064 : certificate2064.Valid := by decide +kernel
theorem bound2064 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2064.a certificate2064.b certificate2064.c x ≤ (certificate2064.bound:ℝ) :=
  rat_majority_certificate_sound certificate2064 valid2064 x hx0 hx1

def certificate2065 : RatMajorityCertificate := ⟨(11424440362762999/50000000000000000),(38577912407386671474699779672729183/50000000000000000000000000000000000),1,(33957123130712770609/100000000000000000000),(3395712313071277061/10000000000000000000),(552482429345435931/1000000000000000000),false⟩
theorem valid2065 : certificate2065.Valid := by decide +kernel
theorem bound2065 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2065.a certificate2065.b certificate2065.c x ≤ (certificate2065.bound:ℝ) :=
  rat_majority_certificate_sound certificate2065 valid2065 x hx0 hx1

def certificate2066 : RatMajorityCertificate := ⟨0,(1000060991212358183/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(136047078208834831/250000000000000000),false⟩
theorem valid2066 : certificate2066.Valid := by decide +kernel
theorem bound2066 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2066.a certificate2066.b certificate2066.c x ≤ (certificate2066.bound:ℝ) :=
  rat_majority_certificate_sound certificate2066 valid2066 x hx0 hx1

def certificate2067 : RatMajorityCertificate := ⟨(5129060127168669/31250000000000000),(26122533020622110185355733516631573/31250000000000000000000000000000000),1,(35671103913248333721/100000000000000000000),(17835551956624166861/50000000000000000000),(136047078208834831/250000000000000000),false⟩
theorem valid2067 : certificate2067.Valid := by decide +kernel
theorem bound2067 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2067.a certificate2067.b certificate2067.c x ≤ (certificate2067.bound:ℝ) :=
  rat_majority_certificate_sound certificate2067 valid2067 x hx0 hx1

def certificate2068 : RatMajorityCertificate := ⟨0,(250015603260897273/250000000000000000),(179332621/146875000),(446401023580719251/1000000000000000000),(44640102358071925101/100000000000000000000),(369560304095658153/500000000000000000),false⟩
theorem valid2068 : certificate2068.Valid := by decide +kernel
theorem bound2068 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2068.a certificate2068.b certificate2068.c x ≤ (certificate2068.bound:ℝ) :=
  rat_majority_certificate_sound certificate2068 valid2068 x hx0 hx1

def certificate2069 : RatMajorityCertificate := ⟨(165016820708327417/1000000000000000000),(208758823283309468195379997513566159/250000000000000000000000000000000000),(179332621/146875000),(20596829066247125319/50000000000000000000),(41193658132494250639/100000000000000000000),(369560304095658153/500000000000000000),false⟩
theorem valid2069 : certificate2069.Valid := by decide +kernel
theorem bound2069 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2069.a certificate2069.b certificate2069.c x ≤ (certificate2069.bound:ℝ) :=
  rat_majority_certificate_sound certificate2069 valid2069 x hx0 hx1

def certificate2070 : RatMajorityCertificate := ⟨0,(250015603260897273/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(276299219750931971/500000000000000000),false⟩
theorem valid2070 : certificate2070.Valid := by decide +kernel
theorem bound2070 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2070.a certificate2070.b certificate2070.c x ≤ (certificate2070.bound:ℝ) :=
  rat_majority_certificate_sound certificate2070 valid2070 x hx0 hx1

def certificate2071 : RatMajorityCertificate := ⟨(22931298332414293/100000000000000000),(19268377939955560188509984450077011/25000000000000000000000000000000000),1,(8483435858550928821/25000000000000000000),(6786748686840743057/20000000000000000000),(276299219750931971/500000000000000000),false⟩
theorem valid2071 : certificate2071.Valid := by decide +kernel
theorem bound2071 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2071.a certificate2071.b certificate2071.c x ≤ (certificate2071.bound:ℝ) :=
  rat_majority_certificate_sound certificate2071 valid2071 x hx0 hx1

def certificate2072 : RatMajorityCertificate := ⟨0,(250015603260897273/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135983832466823693/250000000000000000),false⟩
theorem valid2072 : certificate2072.Valid := by decide +kernel
theorem bound2072 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2072.a certificate2072.b certificate2072.c x ≤ (certificate2072.bound:ℝ) :=
  rat_majority_certificate_sound certificate2072 valid2072 x hx0 hx1

def certificate2073 : RatMajorityCertificate := ⟨(80992527573777541/500000000000000000),(104758405989465788021651910244454307/125000000000000000000000000000000000),1,(8931168157117827051/25000000000000000000),(7144934525694261641/20000000000000000000),(135983832466823693/250000000000000000),false⟩
theorem valid2073 : certificate2073.Valid := by decide +kernel
theorem bound2073 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2073.a certificate2073.b certificate2073.c x ≤ (certificate2073.bound:ℝ) :=
  rat_majority_certificate_sound certificate2073 valid2073 x hx0 hx1

def certificate2074 : RatMajorityCertificate := ⟨0,(125007977756940237/125000000000000000),(1435815847/1175000000),(4466168732288429781/10000000000000000000),(44661687322884297811/100000000000000000000),(184984027884811653/250000000000000000),false⟩
theorem valid2074 : certificate2074.Valid := by decide +kernel
theorem bound2074 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2074.a certificate2074.b certificate2074.c x ≤ (certificate2074.bound:ℝ) :=
  rat_majority_certificate_sound certificate2074 valid2074 x hx0 hx1

def certificate2075 : RatMajorityCertificate := ⟨(164017351055725541/1000000000000000000),(104504500384413840272126351788506783/125000000000000000000000000000000000),(1435815847/1175000000),(20620063595427372861/50000000000000000000),(41240127190854745723/100000000000000000000),(184984027884811653/250000000000000000),false⟩
theorem valid2075 : certificate2075.Valid := by decide +kernel
theorem bound2075 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2075.a certificate2075.b certificate2075.c x ≤ (certificate2075.bound:ℝ) :=
  rat_majority_certificate_sound certificate2075 valid2075 x hx0 hx1

def certificate2076 : RatMajorityCertificate := ⟨0,(125007977756940237/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(276346420714477933/500000000000000000),false⟩
theorem valid2076 : certificate2076.Valid := by decide +kernel
theorem bound2076 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2076.a certificate2076.b certificate2076.c x ≤ (certificate2076.bound:ℝ) :=
  rat_majority_certificate_sound certificate2076 valid2076 x hx0 hx1

def certificate2077 : RatMajorityCertificate := ⟨(57495405151999399/250000000000000000),(24064610110867651273628730897082437/31250000000000000000000000000000000),1,(33914748664056794259/100000000000000000000),(1695737433202839713/5000000000000000000),(276346420714477933/500000000000000000),false⟩
theorem valid2077 : certificate2077.Valid := by decide +kernel
theorem bound2077 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2077.a certificate2077.b certificate2077.c x ≤ (certificate2077.bound:ℝ) :=
  rat_majority_certificate_sound certificate2077 valid2077 x hx0 hx1

def certificate2078 : RatMajorityCertificate := ⟨0,(125007977756940237/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(108737140019444433/200000000000000000),false⟩
theorem valid2078 : certificate2078.Valid := by decide +kernel
theorem bound2078 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2078.a certificate2078.b certificate2078.c x ≤ (certificate2078.bound:ℝ) :=
  rat_majority_certificate_sound certificate2078 valid2078 x hx0 hx1

def certificate2079 : RatMajorityCertificate := ⟨(159857129489333141/1000000000000000000),(105024561269449364482738726279505583/125000000000000000000000000000000000),1,(35777606937752412327/100000000000000000000),(4472200867219051541/12500000000000000000),(108737140019444433/200000000000000000),false⟩
theorem valid2079 : certificate2079.Valid := by decide +kernel
theorem bound2079 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2079.a certificate2079.b certificate2079.c x ≤ (certificate2079.bound:ℝ) :=
  rat_majority_certificate_sound certificate2079 valid2079 x hx0 hx1

end Cycle12.MajorityCertificates.Batch051
