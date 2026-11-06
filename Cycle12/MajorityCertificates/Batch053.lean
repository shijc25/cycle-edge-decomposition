import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch053

def certificate2120 : RatMajorityCertificate := ⟨0,(250018307267395363/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(542091886134429767/1000000000000000000),false⟩
theorem valid2120 : certificate2120.Valid := by decide +kernel
theorem bound2120 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2120.a certificate2120.b certificate2120.c x ≤ (certificate2120.bound:ℝ) :=
  rat_majority_certificate_sound certificate2120 valid2120 x hx0 hx1

def certificate2121 : RatMajorityCertificate := ⟨(18249179596109409/125000000000000000),(26689659416786456147495568192729533/31250000000000000000000000000000000),1,(36117422574882472553/100000000000000000000),(18058711287441236277/50000000000000000000),(542091886134429767/1000000000000000000),false⟩
theorem valid2121 : certificate2121.Valid := by decide +kernel
theorem bound2121 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2121.a certificate2121.b certificate2121.c x ≤ (certificate2121.bound:ℝ) :=
  rat_majority_certificate_sound certificate2121 valid2121 x hx0 hx1

def certificate2122 : RatMajorityCertificate := ⟨0,(1000074494332884877/1000000000000000000),(728524479/587500000),(5499864132514411/12207031250000000),(45054886973558054913/100000000000000000000),(378205042645124763/500000000000000000),false⟩
theorem valid2122 : certificate2122.Valid := by decide +kernel
theorem bound2122 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2122.a certificate2122.b certificate2122.c x ≤ (certificate2122.bound:ℝ) :=
  rat_majority_certificate_sound certificate2122 valid2122 x hx0 hx1

def certificate2123 : RatMajorityCertificate := ⟨(32577152858361863/200000000000000000),(167435319194945640069111690813754149/200000000000000000000000000000000000),(728524479/587500000),(20837443944970547973/50000000000000000000),(41674887889941095947/100000000000000000000),(378205042645124763/500000000000000000),false⟩
theorem valid2123 : certificate2123.Valid := by decide +kernel
theorem bound2123 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2123.a certificate2123.b certificate2123.c x ≤ (certificate2123.bound:ℝ) :=
  rat_majority_certificate_sound certificate2123 valid2123 x hx0 hx1

def certificate2124 : RatMajorityCertificate := ⟨0,(1000074494332884877/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(554402853441509513/1000000000000000000),false⟩
theorem valid2124 : certificate2124.Valid := by decide +kernel
theorem bound2124 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2124.a certificate2124.b certificate2124.c x ≤ (certificate2124.bound:ℝ) :=
  rat_majority_certificate_sound certificate2124 valid2124 x hx0 hx1

def certificate2125 : RatMajorityCertificate := ⟨(24193538497204179/100000000000000000),(75812108654573834885052996029699017/100000000000000000000000000000000000),1,(419633780985941887/1250000000000000000),(33570702478875350961/100000000000000000000),(554402853441509513/1000000000000000000),false⟩
theorem valid2125 : certificate2125.Valid := by decide +kernel
theorem bound2125 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2125.a certificate2125.b certificate2125.c x ≤ (certificate2125.bound:ℝ) :=
  rat_majority_certificate_sound certificate2125 valid2125 x hx0 hx1

def certificate2126 : RatMajorityCertificate := ⟨0,(1000074494332884877/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270931736225729173/500000000000000000),false⟩
theorem valid2126 : certificate2126.Valid := by decide +kernel
theorem bound2126 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2126.a certificate2126.b certificate2126.c x ≤ (certificate2126.bound:ℝ) :=
  rat_majority_certificate_sound certificate2126 valid2126 x hx0 hx1

def certificate2127 : RatMajorityCertificate := ⟨(35991688499093667/250000000000000000),(214024253907303411967327392049226041/250000000000000000000000000000000000),1,(9041594224458436877/25000000000000000000),(36166376897833747509/100000000000000000000),(270931736225729173/500000000000000000),false⟩
theorem valid2127 : certificate2127.Valid := by decide +kernel
theorem bound2127 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2127.a certificate2127.b certificate2127.c x ≤ (certificate2127.bound:ℝ) :=
  rat_majority_certificate_sound certificate2127 valid2127 x hx0 hx1

def certificate2128 : RatMajorityCertificate := ⟨0,(200015147341928797/200000000000000000),(145793151/117500000),(22535540528973608487/50000000000000000000),(1802843242317888679/4000000000000000000),(18922542911236537/25000000000000000),false⟩
theorem valid2128 : certificate2128.Valid := by decide +kernel
theorem bound2128 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2128.a certificate2128.b certificate2128.c x ≤ (certificate2128.bound:ℝ) :=
  rat_majority_certificate_sound certificate2128 valid2128 x hx0 hx1

def certificate2129 : RatMajorityCertificate := ⟨(80187985814390993/500000000000000000),(83968761873246487796261251475874579/100000000000000000000000000000000000),(145793151/117500000),(4175163086648546171/10000000000000000000),(41751630866485461711/100000000000000000000),(18922542911236537/25000000000000000),false⟩
theorem valid2129 : certificate2129.Valid := by decide +kernel
theorem bound2129 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2129.a certificate2129.b certificate2129.c x ≤ (certificate2129.bound:ℝ) :=
  rat_majority_certificate_sound certificate2129 valid2129 x hx0 hx1

def certificate2130 : RatMajorityCertificate := ⟨0,(200015147341928797/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(139114934993200877/250000000000000000),false⟩
theorem valid2130 : certificate2130.Valid := by decide +kernel
theorem bound2130 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2130.a certificate2130.b certificate2130.c x ≤ (certificate2130.bound:ℝ) :=
  rat_majority_certificate_sound certificate2130 valid2130 x hx0 hx1

def certificate2131 : RatMajorityCertificate := ⟨(255860119197146639/1000000000000000000),(148839247901788047262502110894136717/200000000000000000000000000000000000),1,(33159070462749831949/100000000000000000000),(663181409254996639/2000000000000000000),(139114934993200877/250000000000000000),false⟩
theorem valid2131 : certificate2131.Valid := by decide +kernel
theorem bound2131 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2131.a certificate2131.b certificate2131.c x ≤ (certificate2131.bound:ℝ) :=
  rat_majority_certificate_sound certificate2131 valid2131 x hx0 hx1

def certificate2132 : RatMajorityCertificate := ⟨0,(200015147341928797/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(541635478721362307/1000000000000000000),false⟩
theorem valid2132 : certificate2132.Valid := by decide +kernel
theorem bound2132 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2132.a certificate2132.b certificate2132.c x ≤ (certificate2132.bound:ℝ) :=
  rat_majority_certificate_sound certificate2132 valid2132 x hx0 hx1

def certificate2133 : RatMajorityCertificate := ⟨(14193356630729821/100000000000000000),(17162628416420912477263892073444663/20000000000000000000000000000000000),1,(7243061307913022503/20000000000000000000),(9053826634891278129/25000000000000000000),(541635478721362307/1000000000000000000),false⟩
theorem valid2133 : certificate2133.Valid := by decide +kernel
theorem bound2133 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2133.a certificate2133.b certificate2133.c x ≤ (certificate2133.bound:ℝ) :=
  rat_majority_certificate_sound certificate2133 valid2133 x hx0 hx1

end Cycle12.MajorityCertificates.Batch053
