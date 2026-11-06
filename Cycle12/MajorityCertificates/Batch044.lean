import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch044

def certificate1760 : RatMajorityCertificate := ⟨0,(500005400111264623/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(137585667946818217/250000000000000000),false⟩
theorem valid1760 : certificate1760.Valid := by decide +kernel
theorem bound1760 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1760.a certificate1760.b certificate1760.c x ≤ (certificate1760.bound:ℝ) :=
  rat_majority_certificate_sound certificate1760 valid1760 x hx0 hx1

def certificate1761 : RatMajorityCertificate := ⟨(53258618627740749/250000000000000000),(98371753111479391326839048220777373/125000000000000000000000000000000000),1,(6877667954948995061/20000000000000000000),(17194169887372487653/50000000000000000000),(137585667946818217/250000000000000000),false⟩
theorem valid1761 : certificate1761.Valid := by decide +kernel
theorem bound1761 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1761.a certificate1761.b certificate1761.c x ≤ (certificate1761.bound:ℝ) :=
  rat_majority_certificate_sound certificate1761 valid1761 x hx0 hx1

def certificate1762 : RatMajorityCertificate := ⟨0,(500005904021854133/500000000000000000),(42392251/36718750),(10782915750078415257/25000000000000000000),(43131663000313661029/100000000000000000000),(42528336719473387/62500000000000000),false⟩
theorem valid1762 : certificate1762.Valid := by decide +kernel
theorem bound1762 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1762.a certificate1762.b certificate1762.c x ≤ (certificate1762.bound:ℝ) :=
  rat_majority_certificate_sound certificate1762 valid1762 x hx0 hx1

def certificate1763 : RatMajorityCertificate := ⟨(36096149210872063/200000000000000000),(81952893086481004065697804889213621/100000000000000000000000000000000000),(42392251/36718750),(196255518067877402898287/500000000000000000000000),(15700441445430192231863/40000000000000000000000),(42528336719473387/62500000000000000),false⟩
theorem valid1763 : certificate1763.Valid := by decide +kernel
theorem bound1763 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1763.a certificate1763.b certificate1763.c x ≤ (certificate1763.bound:ℝ) :=
  rat_majority_certificate_sound certificate1763 valid1763 x hx0 hx1

def certificate1764 : RatMajorityCertificate := ⟨0,(500005904021854133/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(274836263871131467/500000000000000000),false⟩
theorem valid1764 : certificate1764.Valid := by decide +kernel
theorem bound1764 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1764.a certificate1764.b certificate1764.c x ≤ (certificate1764.bound:ℝ) :=
  rat_majority_certificate_sound certificate1764 valid1764 x hx0 hx1

def certificate1765 : RatMajorityCertificate := ⟨(208012862709085911/1000000000000000000),(395998244554823802289426352192579837/500000000000000000000000000000000000),1,(2157857006145900379/6250000000000000000),(6905142419666881213/20000000000000000000),(274836263871131467/500000000000000000),false⟩
theorem valid1765 : certificate1765.Valid := by decide +kernel
theorem bound1765 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1765.a certificate1765.b certificate1765.c x ≤ (certificate1765.bound:ℝ) :=
  rat_majority_certificate_sound certificate1765 valid1765 x hx0 hx1

def certificate1766 : RatMajorityCertificate := ⟨0,(500005904021854133/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(276351299769452219/500000000000000000),false⟩
theorem valid1766 : certificate1766.Valid := by decide +kernel
theorem bound1766 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1766.a certificate1766.b certificate1766.c x ≤ (certificate1766.bound:ℝ) :=
  rat_majority_certificate_sound certificate1766 valid1766 x hx0 hx1

def certificate1767 : RatMajorityCertificate := ⟨(230199355437206327/1000000000000000000),(384904867201225660903606411781300509/500000000000000000000000000000000000),1,(8477073283123245439/25000000000000000000),(33908293132492981757/100000000000000000000),(276351299769452219/500000000000000000),false⟩
theorem valid1767 : certificate1767.Valid := by decide +kernel
theorem bound1767 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1767.a certificate1767.b certificate1767.c x ≤ (certificate1767.bound:ℝ) :=
  rat_majority_certificate_sound certificate1767 valid1767 x hx0 hx1

def certificate1768 : RatMajorityCertificate := ⟨0,(200002570117167423/200000000000000000),(2711771859/2350000000),(5389797632652493617/12500000000000000000),(43118381061219948937/100000000000000000000),(339781175174906391/500000000000000000),false⟩
theorem valid1768 : certificate1768.Valid := by decide +kernel
theorem bound1768 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1768.a certificate1768.b certificate1768.c x ≤ (certificate1768.bound:ℝ) :=
  rat_majority_certificate_sound certificate1768 valid1768 x hx0 hx1

def certificate1769 : RatMajorityCertificate := ⟨(2207346803416417/12500000000000000),(2058557092641395470684720824216609/2500000000000000000000000000000000),(2711771859/2350000000),(3933513937352800471/10000000000000000000),(39335139373528004711/100000000000000000000),(339781175174906391/500000000000000000),false⟩
theorem valid1769 : certificate1769.Valid := by decide +kernel
theorem bound1769 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1769.a certificate1769.b certificate1769.c x ≤ (certificate1769.bound:ℝ) :=
  rat_majority_certificate_sound certificate1769 valid1769 x hx0 hx1

def certificate1770 : RatMajorityCertificate := ⟨0,(200002570117167423/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(274817890871439709/500000000000000000),false⟩
theorem valid1770 : certificate1770.Valid := by decide +kernel
theorem bound1770 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1770.a certificate1770.b certificate1770.c x ≤ (certificate1770.bound:ℝ) :=
  rat_majority_certificate_sound certificate1770 valid1770 x hx0 hx1

def certificate1771 : RatMajorityCertificate := ⟨(207732530713075961/1000000000000000000),(158455530077608812897860767246381497/200000000000000000000000000000000000),1,(34533345327491984373/100000000000000000000),(17266672663745992187/50000000000000000000),(274817890871439709/500000000000000000),false⟩
theorem valid1771 : certificate1771.Valid := by decide +kernel
theorem bound1771 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1771.a certificate1771.b certificate1771.c x ≤ (certificate1771.bound:ℝ) :=
  rat_majority_certificate_sound certificate1771 valid1771 x hx0 hx1

def certificate1772 : RatMajorityCertificate := ⟨0,(200002570117167423/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(550704562688572901/1000000000000000000),false⟩
theorem valid1772 : certificate1772.Valid := by decide +kernel
theorem bound1772 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1772.a certificate1772.b certificate1772.c x ≤ (certificate1772.bound:ℝ) :=
  rat_majority_certificate_sound certificate1772 valid1772 x hx0 hx1

def certificate1773 : RatMajorityCertificate := ⟨(107855694855234799/500000000000000000),(78429868885763799924504350541247023/100000000000000000000000000000000000),1,(8578640518428151863/25000000000000000000),(34314562073712607453/100000000000000000000),(550704562688572901/1000000000000000000),false⟩
theorem valid1773 : certificate1773.Valid := by decide +kernel
theorem bound1773 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1773.a certificate1773.b certificate1773.c x ≤ (certificate1773.bound:ℝ) :=
  rat_majority_certificate_sound certificate1773 valid1773 x hx0 hx1

def certificate1774 : RatMajorityCertificate := ⟨0,(1000013926517624653/1000000000000000000),(2711927931/2350000000),(21559968726683154969/50000000000000000000),(43119937453366309939/100000000000000000000),(679666595750471377/1000000000000000000),false⟩
theorem valid1774 : certificate1774.Valid := by decide +kernel
theorem bound1774 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1774.a certificate1774.b certificate1774.c x ≤ (certificate1774.bound:ℝ) :=
  rat_majority_certificate_sound certificate1774 valid1774 x hx0 hx1

def certificate1775 : RatMajorityCertificate := ⟨(44259461753304331/250000000000000000),(205743403495927667201865568062727857/250000000000000000000000000000000000),(2711927931/2350000000),(7865097077613862081/20000000000000000000),(19662742694034655203/50000000000000000000),(679666595750471377/1000000000000000000),false⟩
theorem valid1775 : certificate1775.Valid := by decide +kernel
theorem bound1775 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1775.a certificate1775.b certificate1775.c x ≤ (certificate1775.bound:ℝ) :=
  rat_majority_certificate_sound certificate1775 valid1775 x hx0 hx1

def certificate1776 : RatMajorityCertificate := ⟨0,(1000013926517624653/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549603339716925573/1000000000000000000),false⟩
theorem valid1776 : certificate1776.Valid := by decide +kernel
theorem bound1776 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1776.a certificate1776.b certificate1776.c x ≤ (certificate1776.bound:ℝ) :=
  rat_majority_certificate_sound certificate1776 valid1776 x hx0 hx1

def certificate1777 : RatMajorityCertificate := ⟨(207484376264711549/1000000000000000000),(792526660718090213360025874303782503/1000000000000000000000000000000000000),1,(17270049774798089901/50000000000000000000),(34540099549596179803/100000000000000000000),(549603339716925573/1000000000000000000),false⟩
theorem valid1777 : certificate1777.Valid := by decide +kernel
theorem bound1777 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1777.a certificate1777.b certificate1777.c x ≤ (certificate1777.bound:ℝ) :=
  rat_majority_certificate_sound certificate1777 valid1777 x hx0 hx1

def certificate1778 : RatMajorityCertificate := ⟨0,(1000013926517624653/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(275208965385968709/500000000000000000),false⟩
theorem valid1778 : certificate1778.Valid := by decide +kernel
theorem bound1778 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1778.a certificate1778.b certificate1778.c x ≤ (certificate1778.bound:ℝ) :=
  rat_majority_certificate_sound certificate1778 valid1778 x hx0 hx1

def certificate1779 : RatMajorityCertificate := ⟨(106792235568327699/500000000000000000),(393213240446533809089313843014836553/500000000000000000000000000000000000),1,(34373225898946908553/100000000000000000000),(17186612949473454277/50000000000000000000),(275208965385968709/500000000000000000),false⟩
theorem valid1779 : certificate1779.Valid := by decide +kernel
theorem bound1779 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1779.a certificate1779.b certificate1779.c x ≤ (certificate1779.bound:ℝ) :=
  rat_majority_certificate_sound certificate1779 valid1779 x hx0 hx1

def certificate1780 : RatMajorityCertificate := ⟨0,(125001879313674497/125000000000000000),(678167903/587500000),(10781838071947338629/25000000000000000000),(43127352287789354517/100000000000000000000),(10627555971708857/15625000000000000),false⟩
theorem valid1780 : certificate1780.Valid := by decide +kernel
theorem bound1780 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1780.a certificate1780.b certificate1780.c x ≤ (certificate1780.bound:ℝ) :=
  rat_majority_certificate_sound certificate1780 valid1780 x hx0 hx1

def certificate1781 : RatMajorityCertificate := ⟨(89599971326065169/500000000000000000),(51300774854627754761629534124705007/62500000000000000000000000000000000),(678167903/587500000),(3927890173419345031/10000000000000000000),(39278901734193450311/100000000000000000000),(10627555971708857/15625000000000000),false⟩
theorem valid1781 : certificate1781.Valid := by decide +kernel
theorem bound1781 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1781.a certificate1781.b certificate1781.c x ≤ (certificate1781.bound:ℝ) :=
  rat_majority_certificate_sound certificate1781 valid1781 x hx0 hx1

def certificate1782 : RatMajorityCertificate := ⟨0,(125001879313674497/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549573079104923131/1000000000000000000),false⟩
theorem valid1782 : certificate1782.Valid := by decide +kernel
theorem bound1782 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1782.a certificate1782.b certificate1782.c x ≤ (certificate1782.bound:ℝ) :=
  rat_majority_certificate_sound certificate1782 valid1782 x hx0 hx1

def certificate1783 : RatMajorityCertificate := ⟨(207252435477490129/1000000000000000000),(99094935386652165220620937963459887/125000000000000000000000000000000000),1,(34546409939427723399/100000000000000000000),(172732049697138617/500000000000000000),(549573079104923131/1000000000000000000),false⟩
theorem valid1783 : certificate1783.Valid := by decide +kernel
theorem bound1783 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1783.a certificate1783.b certificate1783.c x ≤ (certificate1783.bound:ℝ) :=
  rat_majority_certificate_sound certificate1783 valid1783 x hx0 hx1

def certificate1784 : RatMajorityCertificate := ⟨0,(125001879313674497/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(274932415826038253/500000000000000000),false⟩
theorem valid1784 : certificate1784.Valid := by decide +kernel
theorem bound1784 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1784.a certificate1784.b certificate1784.c x ≤ (certificate1784.bound:ℝ) :=
  rat_majority_certificate_sound certificate1784 valid1784 x hx0 hx1

def certificate1785 : RatMajorityCertificate := ⟨(104724837577186671/500000000000000000),(49410138148869596340814463298970513/62500000000000000000000000000000000),1,(6897312226791174169/20000000000000000000),(17243280566977935423/50000000000000000000),(274932415826038253/500000000000000000),false⟩
theorem valid1785 : certificate1785.Valid := by decide +kernel
theorem bound1785 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1785.a certificate1785.b certificate1785.c x ≤ (certificate1785.bound:ℝ) :=
  rat_majority_certificate_sound certificate1785 valid1785 x hx0 hx1

def certificate1786 : RatMajorityCertificate := ⟨0,(62501010827067679/62500000000000000),(2710612479/2350000000),(21553408162655389361/50000000000000000000),(43106816325310778723/100000000000000000000),(678782599826410173/1000000000000000000),false⟩
theorem valid1786 : certificate1786.Valid := by decide +kernel
theorem bound1786 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1786.a certificate1786.b certificate1786.c x ≤ (certificate1786.bound:ℝ) :=
  rat_majority_certificate_sound certificate1786 valid1786 x hx0 hx1

def certificate1787 : RatMajorityCertificate := ⟨(173108808983544069/1000000000000000000),(51681535282526400447516167657954149/62500000000000000000000000000000000),(2710612479/2350000000),(3940996132783701077/10000000000000000000),(39409961327837010771/100000000000000000000),(678782599826410173/1000000000000000000),false⟩
theorem valid1787 : certificate1787.Valid := by decide +kernel
theorem bound1787 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1787.a certificate1787.b certificate1787.c x ≤ (certificate1787.bound:ℝ) :=
  rat_majority_certificate_sound certificate1787 valid1787 x hx0 hx1

def certificate1788 : RatMajorityCertificate := ⟨0,(62501010827067679/62500000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549546355702336977/1000000000000000000),false⟩
theorem valid1788 : certificate1788.Valid := by decide +kernel
theorem bound1788 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1788.a certificate1788.b certificate1788.c x ≤ (certificate1788.bound:ℝ) :=
  rat_majority_certificate_sound certificate1788 valid1788 x hx0 hx1

def certificate1789 : RatMajorityCertificate := ⟨(51761746869200153/250000000000000000),(12390091205267104451250582871845113/15625000000000000000000000000000000),1,(6910399566601327547/20000000000000000000),(4318999729125829717/12500000000000000000),(549546355702336977/1000000000000000000),false⟩
theorem valid1789 : certificate1789.Valid := by decide +kernel
theorem bound1789 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1789.a certificate1789.b certificate1789.c x ≤ (certificate1789.bound:ℝ) :=
  rat_majority_certificate_sound certificate1789 valid1789 x hx0 hx1

def certificate1790 : RatMajorityCertificate := ⟨0,(62501010827067679/62500000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(68731169903724979/125000000000000000),false⟩
theorem valid1790 : certificate1790.Valid := by decide +kernel
theorem bound1790 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1790.a certificate1790.b certificate1790.c x ≤ (certificate1790.bound:ℝ) :=
  rat_majority_certificate_sound certificate1790 valid1790 x hx0 hx1

def certificate1791 : RatMajorityCertificate := ⟨(6541560402981189/31250000000000000),(1544302450773220465717153333109669/1953125000000000000000000000000000),1,(8622458628536830539/25000000000000000000),(34489834514147322157/100000000000000000000),(68731169903724979/125000000000000000),false⟩
theorem valid1791 : certificate1791.Valid := by decide +kernel
theorem bound1791 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1791.a certificate1791.b certificate1791.c x ≤ (certificate1791.bound:ℝ) :=
  rat_majority_certificate_sound certificate1791 valid1791 x hx0 hx1

def certificate1792 : RatMajorityCertificate := ⟨0,(1000017341362217191/1000000000000000000),(542174349/470000000),(21554701479010925989/50000000000000000000),(43109402958021851979/100000000000000000000),(678959615663269053/1000000000000000000),false⟩
theorem valid1792 : certificate1792.Valid := by decide +kernel
theorem bound1792 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1792.a certificate1792.b certificate1792.c x ≤ (certificate1792.bound:ℝ) :=
  rat_majority_certificate_sound certificate1792 valid1792 x hx0 hx1

def certificate1793 : RatMajorityCertificate := ⟨(17390598137952371/100000000000000000),(82610834421607864260595550684590139/100000000000000000000000000000000000),(542174349/470000000),(19696403784720707779/50000000000000000000),(39392807569441415559/100000000000000000000),(678959615663269053/1000000000000000000),false⟩
theorem valid1793 : certificate1793.Valid := by decide +kernel
theorem bound1793 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1793.a certificate1793.b certificate1793.c x ≤ (certificate1793.bound:ℝ) :=
  rat_majority_certificate_sound certificate1793 valid1793 x hx0 hx1

def certificate1794 : RatMajorityCertificate := ⟨0,(1000017341362217191/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(137381679258698441/250000000000000000),false⟩
theorem valid1794 : certificate1794.Valid := by decide +kernel
theorem bound1794 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1794.a certificate1794.b certificate1794.c x ≤ (certificate1794.bound:ℝ) :=
  rat_majority_certificate_sound certificate1794 valid1794 x hx0 hx1

def certificate1795 : RatMajorityCertificate := ⟨(206894898352637103/1000000000000000000),(793118855170206866006474138108962327/1000000000000000000000000000000000000),1,(34556134430856711939/100000000000000000000),(1727806721542835597/5000000000000000000),(137381679258698441/250000000000000000),false⟩
theorem valid1795 : certificate1795.Valid := by decide +kernel
theorem bound1795 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1795.a certificate1795.b certificate1795.c x ≤ (certificate1795.bound:ℝ) :=
  rat_majority_certificate_sound certificate1795 valid1795 x hx0 hx1

def certificate1796 : RatMajorityCertificate := ⟨0,(1000017341362217191/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(275504242992023193/500000000000000000),false⟩
theorem valid1796 : certificate1796.Valid := by decide +kernel
theorem bound1796 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1796.a certificate1796.b certificate1796.c x ≤ (certificate1796.bound:ℝ) :=
  rat_majority_certificate_sound certificate1796 valid1796 x hx0 hx1

def certificate1797 : RatMajorityCertificate := ⟨(27242117165927217/125000000000000000),(97759578088928594374394965547812553/125000000000000000000000000000000000),1,(8563234611882049097/25000000000000000000),(34252938447528196389/100000000000000000000),(275504242992023193/500000000000000000),false⟩
theorem valid1797 : certificate1797.Valid := by decide +kernel
theorem bound1797 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1797.a certificate1797.b certificate1797.c x ≤ (certificate1797.bound:ℝ) :=
  rat_majority_certificate_sound certificate1797 valid1797 x hx0 hx1

def certificate1798 : RatMajorityCertificate := ⟨0,(500009268785964179/500000000000000000),(2709918839/2350000000),(21549947356590213169/50000000000000000000),(43099894713180426339/100000000000000000000),(5299369278903319/7812500000000000),false⟩
theorem valid1798 : certificate1798.Valid := by decide +kernel
theorem bound1798 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1798.a certificate1798.b certificate1798.c x ≤ (certificate1798.bound:ℝ) :=
  rat_majority_certificate_sound certificate1798 valid1798 x hx0 hx1

def certificate1799 : RatMajorityCertificate := ⟨(85521257363272131/500000000000000000),(207243213033116136363318006805004551/250000000000000000000000000000000000),(2709918839/2350000000),(2465880202002462147/6250000000000000000),(39454083232039394353/100000000000000000000),(5299369278903319/7812500000000000),false⟩
theorem valid1799 : certificate1799.Valid := by decide +kernel
theorem bound1799 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1799.a certificate1799.b certificate1799.c x ≤ (certificate1799.bound:ℝ) :=
  rat_majority_certificate_sound certificate1799 valid1799 x hx0 hx1

end Cycle12.MajorityCertificates.Batch044
