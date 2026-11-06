import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch045

def certificate1800 : RatMajorityCertificate := ⟨0,(500009268785964179/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(274753193407695321/500000000000000000),false⟩
theorem valid1800 : certificate1800.Valid := by decide +kernel
theorem bound1800 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1800.a certificate1800.b certificate1800.c x ≤ (certificate1800.bound:ℝ) :=
  rat_majority_certificate_sound certificate1800 valid1800 x hx0 hx1

def certificate1801 : RatMajorityCertificate := ⟨(103368714870108771/500000000000000000),(198319318855434180714740240160285991/250000000000000000000000000000000000),1,(17280207986941939929/50000000000000000000),(34560415973883879859/100000000000000000000),(274753193407695321/500000000000000000),false⟩
theorem valid1801 : certificate1801.Valid := by decide +kernel
theorem bound1801 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1801.a certificate1801.b certificate1801.c x ≤ (certificate1801.bound:ℝ) :=
  rat_majority_certificate_sound certificate1801 valid1801 x hx0 hx1

def certificate1802 : RatMajorityCertificate := ⟨0,(500009268785964179/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(68838747796782151/125000000000000000),false⟩
theorem valid1802 : certificate1802.Valid := by decide +kernel
theorem bound1802 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1802.a certificate1802.b certificate1802.c x ≤ (certificate1802.bound:ℝ) :=
  rat_majority_certificate_sound certificate1802 valid1802 x hx0 hx1

def certificate1803 : RatMajorityCertificate := ⟨(215734247121413273/1000000000000000000),(392140145630695830820821139566852133/500000000000000000000000000000000000),1,(171569784654489169654257/500000000000000000000000),(68627913861795667861703/200000000000000000000000),(68838747796782151/125000000000000000),false⟩
theorem valid1803 : certificate1803.Valid := by decide +kernel
theorem bound1803 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1803.a certificate1803.b certificate1803.c x ≤ (certificate1803.bound:ℝ) :=
  rat_majority_certificate_sound certificate1803 valid1803 x hx0 hx1

def certificate1804 : RatMajorityCertificate := ⟨0,(200003952107789179/200000000000000000),(1354789413/1175000000),(1077412528017793359/2500000000000000000),(43096501120711734361/100000000000000000000),(339045418981944037/500000000000000000),false⟩
theorem valid1804 : certificate1804.Valid := by decide +kernel
theorem bound1804 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1804.a certificate1804.b certificate1804.c x ≤ (certificate1804.bound:ℝ) :=
  rat_majority_certificate_sound certificate1804 valid1804 x hx0 hx1

def certificate1805 : RatMajorityCertificate := ⟨(17001152607522701/100000000000000000),(16600097498886732488667066835347521/20000000000000000000000000000000000),(1354789413/1175000000),(39476086720426878837/100000000000000000000),(19738043360213439419/50000000000000000000),(339045418981944037/500000000000000000),false⟩
theorem valid1805 : certificate1805.Valid := by decide +kernel
theorem bound1805 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1805.a certificate1805.b certificate1805.c x ≤ (certificate1805.bound:ℝ) :=
  rat_majority_certificate_sound certificate1805 valid1805 x hx0 hx1

def certificate1806 : RatMajorityCertificate := ⟨0,(200003952107789179/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(109895378694535889/200000000000000000),false⟩
theorem valid1806 : certificate1806.Valid := by decide +kernel
theorem bound1806 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1806.a certificate1806.b certificate1806.c x ≤ (certificate1806.bound:ℝ) :=
  rat_majority_certificate_sound certificate1806 valid1806 x hx0 hx1

def certificate1807 : RatMajorityCertificate := ⟨(12906904828031421/62500000000000000),(9918815031651434432479564944206641/12500000000000000000000000000000000),1,(3456658219958693421/10000000000000000000),(34566582199586934211/100000000000000000000),(109895378694535889/200000000000000000),false⟩
theorem valid1807 : certificate1807.Valid := by decide +kernel
theorem bound1807 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1807.a certificate1807.b certificate1807.c x ≤ (certificate1807.bound:ℝ) :=
  rat_majority_certificate_sound certificate1807 valid1807 x hx0 hx1

def certificate1808 : RatMajorityCertificate := ⟨0,(200003952107789179/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(275206836437776093/500000000000000000),false⟩
theorem valid1808 : certificate1808.Valid := by decide +kernel
theorem bound1808 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1808.a certificate1808.b certificate1808.c x ≤ (certificate1808.bound:ℝ) :=
  rat_majority_certificate_sound certificate1808 valid1808 x hx0 hx1

def certificate1809 : RatMajorityCertificate := ⟨(213535050859183543/1000000000000000000),(157296098022414707086803425289718803/200000000000000000000000000000000000),1,(34374612894739078751/100000000000000000000),(1074206652960596211/3125000000000000000),(275206836437776093/500000000000000000),false⟩
theorem valid1809 : certificate1809.Valid := by decide +kernel
theorem bound1809 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1809.a certificate1809.b certificate1809.c x ≤ (certificate1809.bound:ℝ) :=
  rat_majority_certificate_sound certificate1809 valid1809 x hx0 hx1

def certificate1810 : RatMajorityCertificate := ⟨0,(1000021008941608367/1000000000000000000),(84654919/73437500),(21545148839790683129/50000000000000000000),(43090297679581366259/100000000000000000000),(677672826563199479/1000000000000000000),false⟩
theorem valid1810 : certificate1810.Valid := by decide +kernel
theorem bound1810 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1810.a certificate1810.b certificate1810.c x ≤ (certificate1810.bound:ℝ) :=
  rat_majority_certificate_sound certificate1810 valid1810 x hx0 hx1

def certificate1811 : RatMajorityCertificate := ⟨(84060022283140529/500000000000000000),(415948716175563909971755202856793857/500000000000000000000000000000000000),(84654919/73437500),(7903269664570719087/20000000000000000000),(9879087080713398859/25000000000000000000),(677672826563199479/1000000000000000000),false⟩
theorem valid1811 : certificate1811.Valid := by decide +kernel
theorem bound1811 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1811.a certificate1811.b certificate1811.c x ≤ (certificate1811.bound:ℝ) :=
  rat_majority_certificate_sound certificate1811 valid1811 x hx0 hx1

def certificate1812 : RatMajorityCertificate := ⟨0,(1000021008941608367/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549457404790653087/1000000000000000000),false⟩
theorem valid1812 : certificate1812.Valid := by decide +kernel
theorem bound1812 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1812.a certificate1812.b certificate1812.c x ≤ (certificate1812.bound:ℝ) :=
  rat_majority_certificate_sound certificate1812 valid1812 x hx0 hx1

def certificate1813 : RatMajorityCertificate := ⟨(206359055176147123/1000000000000000000),(793657618380120690541165226160221859/1000000000000000000000000000000000000),1,(8642674168766152467/25000000000000000000),(34570696675064609869/100000000000000000000),(549457404790653087/1000000000000000000),false⟩
theorem valid1813 : certificate1813.Valid := by decide +kernel
theorem bound1813 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1813.a certificate1813.b certificate1813.c x ≤ (certificate1813.bound:ℝ) :=
  rat_majority_certificate_sound certificate1813 valid1813 x hx0 hx1

def certificate1814 : RatMajorityCertificate := ⟨0,(1000021008941608367/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(275058126342356187/500000000000000000),false⟩
theorem valid1814 : certificate1814.Valid := by decide +kernel
theorem bound1814 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1814.a certificate1814.b certificate1814.c x ≤ (certificate1814.bound:ℝ) :=
  rat_majority_certificate_sound certificate1814 valid1814 x hx0 hx1

def certificate1815 : RatMajorityCertificate := ⟨(264143506239273/1250000000000000),(985877205562238648539199839202809/1250000000000000000000000000000000),1,(34435581913410309527/100000000000000000000),(4304447739176288691/12500000000000000000),(275058126342356187/500000000000000000),false⟩
theorem valid1815 : certificate1815.Valid := by decide +kernel
theorem bound1815 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1815.a certificate1815.b certificate1815.c x ≤ (certificate1815.bound:ℝ) :=
  rat_majority_certificate_sound certificate1815 valid1815 x hx0 hx1

def certificate1816 : RatMajorityCertificate := ⟨0,(250005570364969943/250000000000000000),(2202413/1880000),(43526266490665714559/100000000000000000000),(68009791391665179/156250000000000000),(10866059021811753/15625000000000000),false⟩
theorem valid1816 : certificate1816.Valid := by decide +kernel
theorem bound1816 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1816.a certificate1816.b certificate1816.c x ≤ (certificate1816.bound:ℝ) :=
  rat_majority_certificate_sound certificate1816 valid1816 x hx0 hx1

def certificate1817 : RatMajorityCertificate := ⟨(178006352852180829/1000000000000000000),(205502990591572380648684145414177253/250000000000000000000000000000000000),(2202413/1880000),(19860616573125227823/50000000000000000000),(39721233146250455647/100000000000000000000),(10866059021811753/15625000000000000),false⟩
theorem valid1817 : certificate1817.Valid := by decide +kernel
theorem bound1817 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1817.a certificate1817.b certificate1817.c x ≤ (certificate1817.bound:ℝ) :=
  rat_majority_certificate_sound certificate1817 valid1817 x hx0 hx1

def certificate1818 : RatMajorityCertificate := ⟨0,(250005570364969943/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(551559841097079717/1000000000000000000),false⟩
theorem valid1818 : certificate1818.Valid := by decide +kernel
theorem bound1818 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1818.a certificate1818.b certificate1818.c x ≤ (certificate1818.bound:ℝ) :=
  rat_majority_certificate_sound certificate1818 valid1818 x hx0 hx1

def certificate1819 : RatMajorityCertificate := ⟨(22195133812094817/100000000000000000),(19451649948477399959591691928914569/25000000000000000000000000000000000),1,(34141075062645375813/100000000000000000000),(17070537531322687907/50000000000000000000),(551559841097079717/1000000000000000000),false⟩
theorem valid1819 : certificate1819.Valid := by decide +kernel
theorem bound1819 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1819.a certificate1819.b certificate1819.c x ≤ (certificate1819.bound:ℝ) :=
  rat_majority_certificate_sound certificate1819 valid1819 x hx0 hx1

def certificate1820 : RatMajorityCertificate := ⟨0,(250005570364969943/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(109965697289271103/200000000000000000),false⟩
theorem valid1820 : certificate1820.Valid := by decide +kernel
theorem bound1820 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1820.a certificate1820.b certificate1820.c x ≤ (certificate1820.bound:ℝ) :=
  rat_majority_certificate_sound certificate1820 valid1820 x hx0 hx1

def certificate1821 : RatMajorityCertificate := ⟨(209154151316335767/1000000000000000000),(197715867470928190575641370149148719/250000000000000000000000000000000000),1,(689893168908111511/2000000000000000000),(34494658445405575551/100000000000000000000),(109965697289271103/200000000000000000),false⟩
theorem valid1821 : certificate1821.Valid := by decide +kernel
theorem bound1821 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1821.a certificate1821.b certificate1821.c x ≤ (certificate1821.bound:ℝ) :=
  rat_majority_certificate_sound certificate1821 valid1821 x hx0 hx1

def certificate1822 : RatMajorityCertificate := ⟨0,(500011788387687321/500000000000000000),(279901581/235000000),(43973158265438392811/100000000000000000000),(10993289566359598203/25000000000000000000),(357049934808549923/500000000000000000),false⟩
theorem valid1822 : certificate1822.Valid := by decide +kernel
theorem bound1822 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1822.a certificate1822.b certificate1822.c x ≤ (certificate1822.bound:ℝ) :=
  rat_majority_certificate_sound certificate1822 valid1822 x hx0 hx1

def certificate1823 : RatMajorityCertificate := ⟨(9450469324355427/50000000000000000),(20275243351410429913674488454558933/25000000000000000000000000000000000),(279901581/235000000),(39906938965024966611/100000000000000000000),(9976734741256241653/25000000000000000000),(357049934808549923/500000000000000000),false⟩
theorem valid1823 : certificate1823.Valid := by decide +kernel
theorem bound1823 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1823.a certificate1823.b certificate1823.c x ≤ (certificate1823.bound:ℝ) :=
  rat_majority_certificate_sound certificate1823 valid1823 x hx0 hx1

def certificate1824 : RatMajorityCertificate := ⟨0,(500011788387687321/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(4409408863281547/8000000000000000),false⟩
theorem valid1824 : certificate1824.Valid := by decide +kernel
theorem bound1824 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1824.a certificate1824.b certificate1824.c x ≤ (certificate1824.bound:ℝ) :=
  rat_majority_certificate_sound certificate1824 valid1824 x hx0 hx1

def certificate1825 : RatMajorityCertificate := ⟨(43829543792727141/200000000000000000),(78087069101519506618807327421720739/100000000000000000000000000000000000),1,(17109658123602995767/50000000000000000000),(6843863249441198307/20000000000000000000),(4409408863281547/8000000000000000),false⟩
theorem valid1825 : certificate1825.Valid := by decide +kernel
theorem bound1825 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1825.a certificate1825.b certificate1825.c x ≤ (certificate1825.bound:ℝ) :=
  rat_majority_certificate_sound certificate1825 valid1825 x hx0 hx1

def certificate1826 : RatMajorityCertificate := ⟨0,(500011788387687321/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(275022571868365613/500000000000000000),false⟩
theorem valid1826 : certificate1826.Valid := by decide +kernel
theorem bound1826 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1826.a certificate1826.b certificate1826.c x ≤ (certificate1826.bound:ℝ) :=
  rat_majority_certificate_sound certificate1826 valid1826 x hx0 hx1

def certificate1827 : RatMajorityCertificate := ⟨(210775075000618999/1000000000000000000),(394621766189078890042675734935988321/500000000000000000000000000000000000),1,(34450373059779019481/100000000000000000000),(17225186529889509741/50000000000000000000),(275022571868365613/500000000000000000),false⟩
theorem valid1827 : certificate1827.Valid := by decide +kernel
theorem bound1827 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1827.a certificate1827.b certificate1827.c x ≤ (certificate1827.bound:ℝ) :=
  rat_majority_certificate_sound certificate1827 valid1827 x hx0 hx1

def certificate1828 : RatMajorityCertificate := ⟨0,(500012446785696537/500000000000000000),(702582113/587500000),(11020444702723195849/25000000000000000000),(44081778810892783397/100000000000000000000),(718497297846570721/1000000000000000000),false⟩
theorem valid1828 : certificate1828.Valid := by decide +kernel
theorem bound1828 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1828.a certificate1828.b certificate1828.c x ≤ (certificate1828.bound:ℝ) :=
  rat_majority_certificate_sound certificate1828 valid1828 x hx0 hx1

def certificate1829 : RatMajorityCertificate := ⟨(189567368771151939/1000000000000000000),(405226402895706416571271182026864757/500000000000000000000000000000000000),(702582113/587500000),(40005602259316481503/100000000000000000000),(1250175070603640047/3125000000000000000),(718497297846570721/1000000000000000000),false⟩
theorem valid1829 : certificate1829.Valid := by decide +kernel
theorem bound1829 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1829.a certificate1829.b certificate1829.c x ≤ (certificate1829.bound:ℝ) :=
  rat_majority_certificate_sound certificate1829 valid1829 x hx0 hx1

def certificate1830 : RatMajorityCertificate := ⟨0,(500012446785696537/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(137794463322967939/250000000000000000),false⟩
theorem valid1830 : certificate1830.Valid := by decide +kernel
theorem bound1830 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1830.a certificate1830.b certificate1830.c x ≤ (certificate1830.bound:ℝ) :=
  rat_majority_certificate_sound certificate1830 valid1830 x hx0 hx1

def certificate1831 : RatMajorityCertificate := ⟨(219156575537169941/1000000000000000000),(390431431222181868422580976575805683/500000000000000000000000000000000000),1,(684381521284720391/2000000000000000000),(34219076064236019551/100000000000000000000),(137794463322967939/250000000000000000),false⟩
theorem valid1831 : certificate1831.Valid := by decide +kernel
theorem bound1831 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1831.a certificate1831.b certificate1831.c x ≤ (certificate1831.bound:ℝ) :=
  rat_majority_certificate_sound certificate1831 valid1831 x hx0 hx1

def certificate1832 : RatMajorityCertificate := ⟨0,(500012446785696537/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(109949451129340399/200000000000000000),false⟩
theorem valid1832 : certificate1832.Valid := by decide +kernel
theorem bound1832 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1832.a certificate1832.b certificate1832.c x ≤ (certificate1832.bound:ℝ) :=
  rat_majority_certificate_sound certificate1832 valid1832 x hx0 hx1

def certificate1833 : RatMajorityCertificate := ⟨(208535031775674849/1000000000000000000),(395742335307008380141496656302702087/500000000000000000000000000000000000),1,(6902310029109431311/20000000000000000000),(8627887536386789139/25000000000000000000),(109949451129340399/200000000000000000),false⟩
theorem valid1833 : certificate1833.Valid := by decide +kernel
theorem bound1833 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1833.a certificate1833.b certificate1833.c x ≤ (certificate1833.bound:ℝ) :=
  rat_majority_certificate_sound certificate1833 valid1833 x hx0 hx1

def certificate1834 : RatMajorityCertificate := ⟨0,(250006557633241737/250000000000000000),(2812555759/2350000000),(8820621079457898187/20000000000000000000),(5512888174661186367/12500000000000000000),(179816829343774037/250000000000000000),false⟩
theorem valid1834 : certificate1834.Valid := by decide +kernel
theorem bound1834 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1834.a certificate1834.b certificate1834.c x ≤ (certificate1834.bound:ℝ) :=
  rat_majority_certificate_sound certificate1834 valid1834 x hx0 hx1

def certificate1835 : RatMajorityCertificate := ⟨(188657401154641687/1000000000000000000),(202840970198536203859387233511509681/250000000000000000000000000000000000),(2812555759/2350000000),(4005090470349650601/10000000000000000000),(40050904703496506011/100000000000000000000),(179816829343774037/250000000000000000),false⟩
theorem valid1835 : certificate1835.Valid := by decide +kernel
theorem bound1835 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1835.a certificate1835.b certificate1835.c x ≤ (certificate1835.bound:ℝ) :=
  rat_majority_certificate_sound certificate1835 valid1835 x hx0 hx1

def certificate1836 : RatMajorityCertificate := ⟨0,(250006557633241737/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(551220633014092207/1000000000000000000),false⟩
theorem valid1836 : certificate1836.Valid := by decide +kernel
theorem bound1836 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1836.a certificate1836.b certificate1836.c x ≤ (certificate1836.bound:ℝ) :=
  rat_majority_certificate_sound certificate1836 valid1836 x hx0 hx1

def certificate1837 : RatMajorityCertificate := ⟨(109732868212518323/500000000000000000),(97569342175586986194468900999152949/125000000000000000000000000000000000),1,(6842095329476114739/20000000000000000000),(66817337201915183/195312500000000000),(551220633014092207/1000000000000000000),false⟩
theorem valid1837 : certificate1837.Valid := by decide +kernel
theorem bound1837 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1837.a certificate1837.b certificate1837.c x ≤ (certificate1837.bound:ℝ) :=
  rat_majority_certificate_sound certificate1837 valid1837 x hx0 hx1

def certificate1838 : RatMajorityCertificate := ⟨0,(250006557633241737/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549452312694602683/1000000000000000000),false⟩
theorem valid1838 : certificate1838.Valid := by decide +kernel
theorem bound1838 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1838.a certificate1838.b certificate1838.c x ≤ (certificate1838.bound:ℝ) :=
  rat_majority_certificate_sound certificate1838 valid1838 x hx0 hx1

def certificate1839 : RatMajorityCertificate := ⟨(20630411907240461/100000000000000000),(19842917499839144803130790599679243/25000000000000000000000000000000000),1,(34572210289627884667/100000000000000000000),(8643052572406971167/25000000000000000000),(549452312694602683/1000000000000000000),false⟩
theorem valid1839 : certificate1839.Valid := by decide +kernel
theorem bound1839 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1839.a certificate1839.b certificate1839.c x ≤ (certificate1839.bound:ℝ) :=
  rat_majority_certificate_sound certificate1839 valid1839 x hx0 hx1

end Cycle12.MajorityCertificates.Batch045
