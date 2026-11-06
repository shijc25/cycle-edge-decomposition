import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch046

def certificate1840 : RatMajorityCertificate := ⟨0,(1000027586346918613/1000000000000000000),(2814786207/2350000000),(22062221263343484921/50000000000000000000),(44124442526686969843/100000000000000000000),(720039081481378339/1000000000000000000),false⟩
theorem valid1840 : certificate1840.Valid := by decide +kernel
theorem bound1840 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1840.a certificate1840.b certificate1840.c x ≤ (certificate1840.bound:ℝ) :=
  rat_majority_certificate_sound certificate1840 valid1840 x hx0 hx1

def certificate1841 : RatMajorityCertificate := ⟨(7509784674848169/40000000000000000),(32491111611503251075082983224930403/40000000000000000000000000000000000),(2814786207/2350000000),(40096241648320027991/100000000000000000000),(5012030206040003499/12500000000000000000),(720039081481378339/1000000000000000000),false⟩
theorem valid1841 : certificate1841.Valid := by decide +kernel
theorem bound1841 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1841.a certificate1841.b certificate1841.c x ≤ (certificate1841.bound:ℝ) :=
  rat_majority_certificate_sound certificate1841 valid1841 x hx0 hx1

def certificate1842 : RatMajorityCertificate := ⟨0,(1000027586346918613/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(551236090696366019/1000000000000000000),false⟩
theorem valid1842 : certificate1842.Valid := by decide +kernel
theorem bound1842 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1842.a certificate1842.b certificate1842.c x ≤ (certificate1842.bound:ℝ) :=
  rat_majority_certificate_sound certificate1842 valid1842 x hx0 hx1

def certificate1843 : RatMajorityCertificate := ⟨(219574788965266537/1000000000000000000),(780446740115349098919712345808646819/1000000000000000000000000000000000000),1,(17103723135656492017/50000000000000000000),(6841489254262596807/20000000000000000000),(551236090696366019/1000000000000000000),false⟩
theorem valid1843 : certificate1843.Valid := by decide +kernel
theorem bound1843 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1843.a certificate1843.b certificate1843.c x ≤ (certificate1843.bound:ℝ) :=
  rat_majority_certificate_sound certificate1843 valid1843 x hx0 hx1

def certificate1844 : RatMajorityCertificate := ⟨0,(1000027586346918613/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(109831994942805579/200000000000000000),false⟩
theorem valid1844 : certificate1844.Valid := by decide +kernel
theorem bound1844 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1844.a certificate1844.b certificate1844.c x ≤ (certificate1844.bound:ℝ) :=
  rat_majority_certificate_sound certificate1844 valid1844 x hx0 hx1

def certificate1845 : RatMajorityCertificate := ⟨(51020000865528837/250000000000000000),(198985488265757151835974454356456919/250000000000000000000000000000000000),1,(8658105417348295189/25000000000000000000),(34632421669393180757/100000000000000000000),(109831994942805579/200000000000000000),false⟩
theorem valid1845 : certificate1845.Valid := by decide +kernel
theorem bound1845 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1845.a certificate1845.b certificate1845.c x ≤ (certificate1845.bound:ℝ) :=
  rat_majority_certificate_sound certificate1845 valid1845 x hx0 hx1

def certificate1846 : RatMajorityCertificate := ⟨0,(1000028959701933309/1000000000000000000),(1408507273/1175000000),(2759108748476441931/6250000000000000000),(44145739975623070897/100000000000000000000),(180202319904564067/250000000000000000),false⟩
theorem valid1846 : certificate1846.Valid := by decide +kernel
theorem bound1846 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1846.a certificate1846.b certificate1846.c x ≤ (certificate1846.bound:ℝ) :=
  rat_majority_certificate_sound certificate1846 valid1846 x hx0 hx1

def certificate1847 : RatMajorityCertificate := ⟨(186815255698513669/1000000000000000000),(813208293889298016138520622937099279/1000000000000000000000000000000000000),(1408507273/1175000000),(40141908669836994027/100000000000000000000),(10035477167459248507/25000000000000000000),(180202319904564067/250000000000000000),false⟩
theorem valid1847 : certificate1847.Valid := by decide +kernel
theorem bound1847 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1847.a certificate1847.b certificate1847.c x ≤ (certificate1847.bound:ℝ) :=
  rat_majority_certificate_sound certificate1847 valid1847 x hx0 hx1

def certificate1848 : RatMajorityCertificate := ⟨0,(1000028959701933309/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(137820273353862757/250000000000000000),false⟩
theorem valid1848 : certificate1848.Valid := by decide +kernel
theorem bound1848 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1848.a certificate1848.b certificate1848.c x ≤ (certificate1848.bound:ℝ) :=
  rat_majority_certificate_sound certificate1848 valid1848 x hx0 hx1

def certificate1849 : RatMajorityCertificate := ⟨(219899758141533137/1000000000000000000),(780122833328949186461299571812439667/1000000000000000000000000000000000000),1,(6839679866041120207/20000000000000000000),(8549599832551400259/25000000000000000000),(137820273353862757/250000000000000000),false⟩
theorem valid1849 : certificate1849.Valid := by decide +kernel
theorem bound1849 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1849.a certificate1849.b certificate1849.c x ≤ (certificate1849.bound:ℝ) :=
  rat_majority_certificate_sound certificate1849 valid1849 x hx0 hx1

def certificate1850 : RatMajorityCertificate := ⟨0,(1000028959701933309/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(137217733536665771/250000000000000000),false⟩
theorem valid1850 : certificate1850.Valid := by decide +kernel
theorem bound1850 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1850.a certificate1850.b certificate1850.c x ≤ (certificate1850.bound:ℝ) :=
  rat_majority_certificate_sound certificate1850 valid1850 x hx0 hx1

def certificate1851 : RatMajorityCertificate := ⟨(201868202868327383/1000000000000000000),(798154910790621046486067371755499653/1000000000000000000000000000000000000),1,(34692040143293670219/100000000000000000000),(1734602007164683511/5000000000000000000),(137217733536665771/250000000000000000),false⟩
theorem valid1851 : certificate1851.Valid := by decide +kernel
theorem bound1851 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1851.a certificate1851.b certificate1851.c x ≤ (certificate1851.bound:ℝ) :=
  rat_majority_certificate_sound certificate1851 valid1851 x hx0 hx1

def certificate1852 : RatMajorityCertificate := ⟨0,(250007378022010031/250000000000000000),(1409589719/1175000000),(8833282473672954881/20000000000000000000),(22083206184182387203/50000000000000000000),(721539197102998961/1000000000000000000),false⟩
theorem valid1852 : certificate1852.Valid := by decide +kernel
theorem bound1852 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1852.a certificate1852.b certificate1852.c x ≤ (certificate1852.bound:ℝ) :=
  rat_majority_certificate_sound certificate1852 valid1852 x hx0 hx1

def certificate1853 : RatMajorityCertificate := ⟨(46428209639704173/250000000000000000),(50894449547223856429167218321440637/62500000000000000000000000000000000),(1409589719/1175000000),(40191241789018603679/100000000000000000000),(251195261181366273/625000000000000000),(721539197102998961/1000000000000000000),false⟩
theorem valid1853 : certificate1853.Valid := by decide +kernel
theorem bound1853 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1853.a certificate1853.b certificate1853.c x ≤ (certificate1853.bound:ℝ) :=
  rat_majority_certificate_sound certificate1853 valid1853 x hx0 hx1

def certificate1854 : RatMajorityCertificate := ⟨0,(250007378022010031/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(275637400938662273/500000000000000000),false⟩
theorem valid1854 : certificate1854.Valid := by decide +kernel
theorem bound1854 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1854.a certificate1854.b certificate1854.c x ≤ (certificate1854.bound:ℝ) :=
  rat_majority_certificate_sound certificate1854 valid1854 x hx0 hx1

def certificate1855 : RatMajorityCertificate := ⟨(219852130268161869/1000000000000000000),(195042723381113493049112236950292061/250000000000000000000000000000000000),1,(34199729228753782551/100000000000000000000),(4274966153594222819/12500000000000000000),(275637400938662273/500000000000000000),false⟩
theorem valid1855 : certificate1855.Valid := by decide +kernel
theorem bound1855 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1855.a certificate1855.b certificate1855.c x ≤ (certificate1855.bound:ℝ) :=
  rat_majority_certificate_sound certificate1855 valid1855 x hx0 hx1

def certificate1856 : RatMajorityCertificate := ⟨0,(250007378022010031/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(109708807877825233/200000000000000000),false⟩
theorem valid1856 : certificate1856.Valid := by decide +kernel
theorem bound1856 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1856.a certificate1856.b certificate1856.c x ≤ (certificate1856.bound:ℝ) :=
  rat_majority_certificate_sound certificate1856 valid1856 x hx0 hx1

def certificate1857 : RatMajorityCertificate := ⟨(49838655499212419/250000000000000000),(50041812920002179458236632182225011/62500000000000000000000000000000000),1,(17379738355386394801/50000000000000000000),(34759476710772789603/100000000000000000000),(109708807877825233/200000000000000000),false⟩
theorem valid1857 : certificate1857.Valid := by decide +kernel
theorem bound1857 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1857.a certificate1857.b certificate1857.c x ≤ (certificate1857.bound:ℝ) :=
  rat_majority_certificate_sound certificate1857 valid1857 x hx0 hx1

def certificate1858 : RatMajorityCertificate := ⟨0,(12500377561107687/12500000000000000),(1410150117/1175000000),(44177107545469329347/100000000000000000000),(11044276886367332337/25000000000000000000),(360964142323120277/500000000000000000),false⟩
theorem valid1858 : certificate1858.Valid := by decide +kernel
theorem bound1858 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1858.a certificate1858.b certificate1858.c x ≤ (certificate1858.bound:ℝ) :=
  rat_majority_certificate_sound certificate1858 valid1858 x hx0 hx1

def certificate1859 : RatMajorityCertificate := ⟨(185255598054308743/1000000000000000000),(10184612640120021110049009831392559/12500000000000000000000000000000000),(1410150117/1175000000),(1608555529484186739/4000000000000000000),(10053472059276167119/25000000000000000000),(360964142323120277/500000000000000000),false⟩
theorem valid1859 : certificate1859.Valid := by decide +kernel
theorem bound1859 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1859.a certificate1859.b certificate1859.c x ≤ (certificate1859.bound:ℝ) :=
  rat_majority_certificate_sound certificate1859 valid1859 x hx0 hx1

def certificate1860 : RatMajorityCertificate := ⟨0,(12500377561107687/12500000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(110258207363515651/200000000000000000),false⟩
theorem valid1860 : certificate1860.Valid := by decide +kernel
theorem bound1860 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1860.a certificate1860.b certificate1860.c x ≤ (certificate1860.bound:ℝ) :=
  rat_majority_certificate_sound certificate1860 valid1860 x hx0 hx1

def certificate1861 : RatMajorityCertificate := ⟨(27496090769201523/125000000000000000),(1218835679068953955477111592592699/1562500000000000000000000000000000),1,(34196483111531836289/100000000000000000000),(3419648311153183629/10000000000000000000),(110258207363515651/200000000000000000),false⟩
theorem valid1861 : certificate1861.Valid := by decide +kernel
theorem bound1861 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1861.a certificate1861.b certificate1861.c x ≤ (certificate1861.bound:ℝ) :=
  rat_majority_certificate_sound certificate1861 valid1861 x hx0 hx1

def certificate1862 : RatMajorityCertificate := ⟨0,(12500377561107687/12500000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(34275103943959219/62500000000000000),false⟩
theorem valid1862 : certificate1862.Valid := by decide +kernel
theorem bound1862 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1862.a certificate1862.b certificate1862.c x ≤ (certificate1862.bound:ℝ) :=
  rat_majority_certificate_sound certificate1862 valid1862 x hx0 hx1

def certificate1863 : RatMajorityCertificate := ⟨(99126636086720153/500000000000000000),(5011068403107319399292042533883889/6250000000000000000000000000000000),1,(34788922707364393431/100000000000000000000),(4348615338420549179/12500000000000000000),(34275103943959219/62500000000000000),false⟩
theorem valid1863 : certificate1863.Valid := by decide +kernel
theorem bound1863 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1863.a certificate1863.b certificate1863.c x ≤ (certificate1863.bound:ℝ) :=
  rat_majority_certificate_sound certificate1863 valid1863 x hx0 hx1

def certificate1864 : RatMajorityCertificate := ⟨0,(1000031753799748341/1000000000000000000),(2821498731/2350000000),(44188538735362911649/100000000000000000000),(883770774707258233/2000000000000000000),(22573946640848489/31250000000000000),false⟩
theorem valid1864 : certificate1864.Valid := by decide +kernel
theorem bound1864 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1864.a certificate1864.b certificate1864.c x ≤ (certificate1864.bound:ℝ) :=
  rat_majority_certificate_sound certificate1864 valid1864 x hx0 hx1

def certificate1865 : RatMajorityCertificate := ⟨(5781090611676391/31250000000000000),(25469718122972134469947708068882669/31250000000000000000000000000000000),(2821498731/2350000000),(20116169533107201333/50000000000000000000),(40232339066214402667/100000000000000000000),(22573946640848489/31250000000000000),false⟩
theorem valid1865 : certificate1865.Valid := by decide +kernel
theorem bound1865 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1865.a certificate1865.b certificate1865.c x ≤ (certificate1865.bound:ℝ) :=
  rat_majority_certificate_sound certificate1865 valid1865 x hx0 hx1

def certificate1866 : RatMajorityCertificate := ⟨0,(1000031753799748341/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(551330303135748461/1000000000000000000),false⟩
theorem valid1866 : certificate1866.Valid := by decide +kernel
theorem bound1866 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1866.a certificate1866.b certificate1866.c x ≤ (certificate1866.bound:ℝ) :=
  rat_majority_certificate_sound certificate1866 valid1866 x hx0 hx1

def certificate1867 : RatMajorityCertificate := ⟨(22025096067663877/100000000000000000),(77977379931820986528433809623621943/100000000000000000000000000000000000),1,(34188621760362630251/100000000000000000000),(8547155440090657563/25000000000000000000),(551330303135748461/1000000000000000000),false⟩
theorem valid1867 : certificate1867.Valid := by decide +kernel
theorem bound1867 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1867.a certificate1867.b certificate1867.c x ≤ (certificate1867.bound:ℝ) :=
  rat_majority_certificate_sound certificate1867 valid1867 x hx0 hx1

def certificate1868 : RatMajorityCertificate := ⟨0,(1000031753799748341/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(548789952904577891/1000000000000000000),false⟩
theorem valid1868 : certificate1868.Valid := by decide +kernel
theorem bound1868 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1868.a certificate1868.b certificate1868.c x ≤ (certificate1868.bound:ℝ) :=
  rat_majority_certificate_sound certificate1868 valid1868 x hx0 hx1

def certificate1869 : RatMajorityCertificate := ⟨(201238526057309973/1000000000000000000),(798786837654580292876808409170495207/1000000000000000000000000000000000000),1,(17354488095308565933/50000000000000000000),(34708976190617131867/100000000000000000000),(548789952904577891/1000000000000000000),false⟩
theorem valid1869 : certificate1869.Valid := by decide +kernel
theorem bound1869 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1869.a certificate1869.b certificate1869.c x ≤ (certificate1869.bound:ℝ) :=
  rat_majority_certificate_sound certificate1869 valid1869 x hx0 hx1

def certificate1870 : RatMajorityCertificate := ⟨0,(200006460941167221/200000000000000000),(705916709/587500000),(11052300921857269357/25000000000000000000),(44209203687429077429/100000000000000000000),(2892391364982577/4000000000000000),false⟩
theorem valid1870 : certificate1870.Valid := by decide +kernel
theorem bound1870 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1870.a certificate1870.b certificate1870.c x ≤ (certificate1870.bound:ℝ) :=
  rat_majority_certificate_sound certificate1870 valid1870 x hx0 hx1

def certificate1871 : RatMajorityCertificate := ⟨(183878077844368027/1000000000000000000),(163229657346850721454940053527157033/200000000000000000000000000000000000),(705916709/587500000),(40281912469657716419/100000000000000000000),(2014095623482885821/5000000000000000000),(2892391364982577/4000000000000000),false⟩
theorem valid1871 : certificate1871.Valid := by decide +kernel
theorem bound1871 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1871.a certificate1871.b certificate1871.c x ≤ (certificate1871.bound:ℝ) :=
  rat_majority_certificate_sound certificate1871 valid1871 x hx0 hx1

def certificate1872 : RatMajorityCertificate := ⟨0,(200006460941167221/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(137823822394712631/250000000000000000),false⟩
theorem valid1872 : certificate1872.Valid := by decide +kernel
theorem bound1872 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1872.a certificate1872.b certificate1872.c x ≤ (certificate1872.bound:ℝ) :=
  rat_majority_certificate_sound certificate1872 valid1872 x hx0 hx1

def certificate1873 : RatMajorityCertificate := ⟨(21999356458679331/100000000000000000),(15600632665833059649518112712590849/20000000000000000000000000000000000),1,(17097900415461110493/50000000000000000000),(34195800830922220987/100000000000000000000),(137823822394712631/250000000000000000),false⟩
theorem valid1873 : certificate1873.Valid := by decide +kernel
theorem bound1873 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1873.a certificate1873.b certificate1873.c x ≤ (certificate1873.bound:ℝ) :=
  rat_majority_certificate_sound certificate1873 valid1873 x hx0 hx1

def certificate1874 : RatMajorityCertificate := ⟨0,(200006460941167221/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(274231777807833171/500000000000000000),false⟩
theorem valid1874 : certificate1874.Valid := by decide +kernel
theorem bound1874 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1874.a certificate1874.b certificate1874.c x ≤ (certificate1874.bound:ℝ) :=
  rat_majority_certificate_sound certificate1874 valid1874 x hx0 hx1

def certificate1875 : RatMajorityCertificate := ⟨(198724661015455407/1000000000000000000),(160260244789732842805987576544386053/200000000000000000000000000000000000),1,(4347042181228406623/12500000000000000000),(6955267489965450597/20000000000000000000),(274231777807833171/500000000000000000),false⟩
theorem valid1875 : certificate1875.Valid := by decide +kernel
theorem bound1875 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1875.a certificate1875.b certificate1875.c x ≤ (certificate1875.bound:ℝ) :=
  rat_majority_certificate_sound certificate1875 valid1875 x hx0 hx1

def certificate1876 : RatMajorityCertificate := ⟨0,(200006602248025787/200000000000000000),(11299163/9400000),(8843981770475405213/20000000000000000000),(22109954426188513033/50000000000000000000),(180872162713286889/250000000000000000),false⟩
theorem valid1876 : certificate1876.Valid := by decide +kernel
theorem bound1876 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1876.a certificate1876.b certificate1876.c x ≤ (certificate1876.bound:ℝ) :=
  rat_majority_certificate_sound certificate1876 valid1876 x hx0 hx1

def certificate1877 : RatMajorityCertificate := ⟨(183417747906984939/1000000000000000000),(163321841697164786011035179707378007/200000000000000000000000000000000000),(11299163/9400000),(40304598836335426839/100000000000000000000),(1007614970908385671/2500000000000000000),(180872162713286889/250000000000000000),false⟩
theorem valid1877 : certificate1877.Valid := by decide +kernel
theorem bound1877 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1877.a certificate1877.b certificate1877.c x ≤ (certificate1877.bound:ℝ) :=
  rat_majority_certificate_sound certificate1877 valid1877 x hx0 hx1

def certificate1878 : RatMajorityCertificate := ⟨0,(200006602248025787/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(110272917850142537/200000000000000000),false⟩
theorem valid1878 : certificate1878.Valid := by decide +kernel
theorem bound1878 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1878.a certificate1878.b certificate1878.c x ≤ (certificate1878.bound:ℝ) :=
  rat_majority_certificate_sound certificate1878 valid1878 x hx0 hx1

def certificate1879 : RatMajorityCertificate := ⟨(220497513696284199/1000000000000000000),(155905643729494454965654034567360387/200000000000000000000000000000000000),1,(34181750208792531659/100000000000000000000),(1709087510439626583/5000000000000000000),(110272917850142537/200000000000000000),false⟩
theorem valid1879 : certificate1879.Valid := by decide +kernel
theorem bound1879 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1879.a certificate1879.b certificate1879.c x ≤ (certificate1879.bound:ℝ) :=
  rat_majority_certificate_sound certificate1879 valid1879 x hx0 hx1

end Cycle12.MajorityCertificates.Batch046
