import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch043

def certificate1720 : RatMajorityCertificate := ⟨0,(1000005557194308863/1000000000000000000),(543034429/470000000),(10788066831160301281/25000000000000000000),(345218138597129641/800000000000000000),(852291105503603/1250000000000000),false⟩
theorem valid1720 : certificate1720.Valid := by decide +kernel
theorem bound1720 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1720.a certificate1720.b certificate1720.c x ≤ (certificate1720.bound:ℝ) :=
  rat_majority_certificate_sound certificate1720 valid1720 x hx0 hx1

def certificate1721 : RatMajorityCertificate := ⟨(186432947125666301/1000000000000000000),(813571574024529810690638005935274237/1000000000000000000000000000000000000),(543034429/470000000),(7824304036313568429/20000000000000000000),(19560760090783921073/50000000000000000000),(852291105503603/1250000000000000),false⟩
theorem valid1721 : certificate1721.Valid := by decide +kernel
theorem bound1721 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1721.a certificate1721.b certificate1721.c x ≤ (certificate1721.bound:ℝ) :=
  rat_majority_certificate_sound certificate1721 valid1721 x hx0 hx1

def certificate1722 : RatMajorityCertificate := ⟨0,(1000005557194308863/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549932231936935263/1000000000000000000),false⟩
theorem valid1722 : certificate1722.Valid := by decide +kernel
theorem bound1722 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1722.a certificate1722.b certificate1722.c x ≤ (certificate1722.bound:ℝ) :=
  rat_majority_certificate_sound certificate1722 valid1722 x hx0 hx1

def certificate1723 : RatMajorityCertificate := ⟨(209984811004102459/1000000000000000000),(790019579263809744329158299856205883/1000000000000000000000000000000000000),1,(8617975695046823351/25000000000000000000),(6894380556037458681/20000000000000000000),(549932231936935263/1000000000000000000),false⟩
theorem valid1723 : certificate1723.Valid := by decide +kernel
theorem bound1723 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1723.a certificate1723.b certificate1723.c x ≤ (certificate1723.bound:ℝ) :=
  rat_majority_certificate_sound certificate1723 valid1723 x hx0 hx1

def certificate1724 : RatMajorityCertificate := ⟨0,(1000005557194308863/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(552067991192576559/1000000000000000000),false⟩
theorem valid1724 : certificate1724.Valid := by decide +kernel
theorem bound1724 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1724.a certificate1724.b certificate1724.c x ≤ (certificate1724.bound:ℝ) :=
  rat_majority_certificate_sound certificate1724 valid1724 x hx0 hx1

def certificate1725 : RatMajorityCertificate := ⟨(45135227187846177/200000000000000000),(154865633425787938062677332928233249/200000000000000000000000000000000000),1,(17018185211912544271/50000000000000000000),(34036370423825088543/100000000000000000000),(552067991192576559/1000000000000000000),false⟩
theorem valid1725 : certificate1725.Valid := by decide +kernel
theorem bound1725 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1725.a certificate1725.b certificate1725.c x ≤ (certificate1725.bound:ℝ) :=
  rat_majority_certificate_sound certificate1725 valid1725 x hx0 hx1

def certificate1726 : RatMajorityCertificate := ⟨0,(250001582160172739/250000000000000000),(543166431/470000000),(43158839375614709439/100000000000000000000),(134871373048795967/312500000000000000),(682271832786265391/1000000000000000000),false⟩
theorem valid1726 : certificate1726.Valid := by decide +kernel
theorem bound1726 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1726.a certificate1726.b certificate1726.c x ≤ (certificate1726.bound:ℝ) :=
  rat_majority_certificate_sound certificate1726 valid1726 x hx0 hx1

def certificate1727 : RatMajorityCertificate := ⟨(37657047946674983/200000000000000000),(40585994865884317897903636030111563/50000000000000000000000000000000000),(543166431/470000000),(19540512278244108617/50000000000000000000),(7816204911297643447/20000000000000000000),(682271832786265391/1000000000000000000),false⟩
theorem valid1727 : certificate1727.Valid := by decide +kernel
theorem bound1727 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1727.a certificate1727.b certificate1727.c x ≤ (certificate1727.bound:ℝ) :=
  rat_majority_certificate_sound certificate1727 valid1727 x hx0 hx1

def certificate1728 : RatMajorityCertificate := ⟨0,(250001582160172739/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(55005708164417749/100000000000000000),false⟩
theorem valid1728 : certificate1728.Valid := by decide +kernel
theorem bound1728 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1728.a certificate1728.b certificate1728.c x ≤ (certificate1728.bound:ℝ) :=
  rat_majority_certificate_sound certificate1728 valid1728 x hx0 hx1

def certificate1729 : RatMajorityCertificate := ⟨(42183510625607181/200000000000000000),(39454372034562294401900552281161241/50000000000000000000000000000000000),1,(17223197263288748749/50000000000000000000),(34446394526577497499/100000000000000000000),(55005708164417749/100000000000000000),false⟩
theorem valid1729 : certificate1729.Valid := by decide +kernel
theorem bound1729 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1729.a certificate1729.b certificate1729.c x ≤ (certificate1729.bound:ℝ) :=
  rat_majority_certificate_sound certificate1729 valid1729 x hx0 hx1

def certificate1730 : RatMajorityCertificate := ⟨0,(250001582160172739/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(551776907104492493/1000000000000000000),false⟩
theorem valid1730 : certificate1730.Valid := by decide +kernel
theorem bound1730 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1730.a certificate1730.b certificate1730.c x ≤ (certificate1730.bound:ℝ) :=
  rat_majority_certificate_sound certificate1730 valid1730 x hx0 hx1

def certificate1731 : RatMajorityCertificate := ⟨(55893188627421417/250000000000000000),(48527009951210856805420567131848837/62500000000000000000000000000000000),1,(34095550992810404371/100000000000000000000),(8523887748202601093/25000000000000000000),(551776907104492493/1000000000000000000),false⟩
theorem valid1731 : certificate1731.Valid := by decide +kernel
theorem bound1731 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1731.a certificate1731.b certificate1731.c x ≤ (certificate1731.bound:ℝ) :=
  rat_majority_certificate_sound certificate1731 valid1731 x hx0 hx1

def certificate1732 : RatMajorityCertificate := ⟨0,(500003571415180477/500000000000000000),(169729809/146875000),(43157294020076476537/100000000000000000000),(21578647010038238269/50000000000000000000),(682168924706227663/1000000000000000000),false⟩
theorem valid1732 : certificate1732.Valid := by decide +kernel
theorem bound1732 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1732.a certificate1732.b certificate1732.c x ≤ (certificate1732.bound:ℝ) :=
  rat_majority_certificate_sound certificate1732 valid1732 x hx0 hx1

def certificate1733 : RatMajorityCertificate := ⟨(23481038830596877/125000000000000000),(50759843151060588161409499412429671/62500000000000000000000000000000000),(169729809/146875000),(39090600737648366389/100000000000000000000),(3909060073764836639/10000000000000000000),(682168924706227663/1000000000000000000),false⟩
theorem valid1733 : certificate1733.Valid := by decide +kernel
theorem bound1733 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1733.a certificate1733.b certificate1733.c x ≤ (certificate1733.bound:ℝ) :=
  rat_majority_certificate_sound certificate1733 valid1733 x hx0 hx1

def certificate1734 : RatMajorityCertificate := ⟨0,(500003571415180477/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549849541365278761/1000000000000000000),false⟩
theorem valid1734 : certificate1734.Valid := by decide +kernel
theorem bound1734 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1734.a certificate1734.b certificate1734.c x ≤ (certificate1734.bound:ℝ) :=
  rat_majority_certificate_sound certificate1734 valid1734 x hx0 hx1

def certificate1735 : RatMajorityCertificate := ⟨(209359296148184169/1000000000000000000),(395323175632119954895145135030731387/500000000000000000000000000000000000),1,(6897798470414027063/20000000000000000000),(8622248088017533829/25000000000000000000),(549849541365278761/1000000000000000000),false⟩
theorem valid1735 : certificate1735.Valid := by decide +kernel
theorem bound1735 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1735.a certificate1735.b certificate1735.c x ≤ (certificate1735.bound:ℝ) :=
  rat_majority_certificate_sound certificate1735 valid1735 x hx0 hx1

def certificate1736 : RatMajorityCertificate := ⟨0,(500003571415180477/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(551486281036359801/1000000000000000000),false⟩
theorem valid1736 : certificate1736.Valid := by decide +kernel
theorem bound1736 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1736.a certificate1736.b certificate1736.c x ≤ (certificate1736.bound:ℝ) :=
  rat_majority_certificate_sound certificate1736 valid1736 x hx0 hx1

def certificate1737 : RatMajorityCertificate := ⟨(110730461621224243/500000000000000000),(194636159432526541733898172467296089/250000000000000000000000000000000000),1,(17077359392388117529/50000000000000000000),(34154718784776235059/100000000000000000000),(551486281036359801/1000000000000000000),false⟩
theorem valid1737 : certificate1737.Valid := by decide +kernel
theorem bound1737 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1737.a certificate1737.b certificate1737.c x ≤ (certificate1737.bound:ℝ) :=
  rat_majority_certificate_sound certificate1737 valid1737 x hx0 hx1

def certificate1738 : RatMajorityCertificate := ⟨0,(100000799842209183/100000000000000000),(2715113393/2350000000),(8630336443228075579/20000000000000000000),(5393960277017547237/12500000000000000000),(340896844657473063/500000000000000000),false⟩
theorem valid1738 : certificate1738.Valid := by decide +kernel
theorem bound1738 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1738.a certificate1738.b certificate1738.c x ≤ (certificate1738.bound:ℝ) :=
  rat_majority_certificate_sound certificate1738 valid1738 x hx0 hx1

def certificate1739 : RatMajorityCertificate := ⟨(46563258771725197/250000000000000000),(20343836840120013313615335334115949/25000000000000000000000000000000000),(2715113393/2350000000),(39125509494095555679/100000000000000000000),(244534434338097223/625000000000000000),(340896844657473063/500000000000000000),false⟩
theorem valid1739 : certificate1739.Valid := by decide +kernel
theorem bound1739 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1739.a certificate1739.b certificate1739.c x ≤ (certificate1739.bound:ℝ) :=
  rat_majority_certificate_sound certificate1739 valid1739 x hx0 hx1

def certificate1740 : RatMajorityCertificate := ⟨0,(100000799842209183/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549809049353861957/1000000000000000000),false⟩
theorem valid1740 : certificate1740.Valid := by decide +kernel
theorem bound1740 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1740.a certificate1740.b certificate1740.c x ≤ (certificate1740.bound:ℝ) :=
  rat_majority_certificate_sound certificate1740 valid1740 x hx0 hx1

def certificate1741 : RatMajorityCertificate := ⟨(104526187064036837/500000000000000000),(39547697610244529025259603828325829/50000000000000000000000000000000000),1,(344973703423905669/1000000000000000000),(34497370342390566901/100000000000000000000),(549809049353861957/1000000000000000000),false⟩
theorem valid1741 : certificate1741.Valid := by decide +kernel
theorem bound1741 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1741.a certificate1741.b certificate1741.c x ≤ (certificate1741.bound:ℝ) :=
  rat_majority_certificate_sound certificate1741 valid1741 x hx0 hx1

def certificate1742 : RatMajorityCertificate := ⟨0,(100000799842209183/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(55119827850272469/100000000000000000),false⟩
theorem valid1742 : certificate1742.Valid := by decide +kernel
theorem bound1742 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1742.a certificate1742.b certificate1742.c x ≤ (certificate1742.bound:ℝ) :=
  rat_majority_certificate_sound certificate1742 valid1742 x hx0 hx1

def certificate1743 : RatMajorityCertificate := ⟨(27419554255453361/125000000000000000),(9758122623413961280055012537585937/12500000000000000000000000000000000),1,(534584888687565683/1562500000000000000),(34213432876004203713/100000000000000000000),(55119827850272469/100000000000000000),false⟩
theorem valid1743 : certificate1743.Valid := by decide +kernel
theorem bound1743 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1743.a certificate1743.b certificate1743.c x ≤ (certificate1743.bound:ℝ) :=
  rat_majority_certificate_sound certificate1743 valid1743 x hx0 hx1

def certificate1744 : RatMajorityCertificate := ⟨0,(31250277939885501/31250000000000000),(2714132979/2350000000),(5392739532308205799/12500000000000000000),(43141916258465646393/100000000000000000000),(681140924723339557/1000000000000000000),false⟩
theorem valid1744 : certificate1744.Valid := by decide +kernel
theorem bound1744 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1744.a certificate1744.b certificate1744.c x ≤ (certificate1744.bound:ℝ) :=
  rat_majority_certificate_sound certificate1744 valid1744 x hx0 hx1

def certificate1745 : RatMajorityCertificate := ⟨(91732472763520571/500000000000000000),(12758473699969756039741446601858929/15625000000000000000000000000000000),(2714132979/2350000000),(39186267955504208113/100000000000000000000),(19593133977752104057/50000000000000000000),(681140924723339557/1000000000000000000),false⟩
theorem valid1745 : certificate1745.Valid := by decide +kernel
theorem bound1745 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1745.a certificate1745.b certificate1745.c x ≤ (certificate1745.bound:ℝ) :=
  rat_majority_certificate_sound certificate1745 valid1745 x hx0 hx1

def certificate1746 : RatMajorityCertificate := ⟨0,(31250277939885501/31250000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(69443456176330337/125000000000000000),false⟩
theorem valid1746 : certificate1746.Valid := by decide +kernel
theorem bound1746 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1746.a certificate1746.b certificate1746.c x ≤ (certificate1746.bound:ℝ) :=
  rat_majority_certificate_sound certificate1746 valid1746 x hx0 hx1

def certificate1747 : RatMajorityCertificate := ⟨(249923275990174843/1000000000000000000),(23440106101545824412231735609348657/31250000000000000000000000000000000),1,(16667827924807902403/50000000000000000000),(33335655849615804807/100000000000000000000),(69443456176330337/125000000000000000),false⟩
theorem valid1747 : certificate1747.Valid := by decide +kernel
theorem bound1747 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1747.a certificate1747.b certificate1747.c x ≤ (certificate1747.bound:ℝ) :=
  rat_majority_certificate_sound certificate1747 valid1747 x hx0 hx1

def certificate1748 : RatMajorityCertificate := ⟨0,(31250277939885501/31250000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(550911898954496921/1000000000000000000),false⟩
theorem valid1748 : certificate1748.Valid := by decide +kernel
theorem bound1748 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1748.a certificate1748.b certificate1748.c x ≤ (certificate1748.bound:ℝ) :=
  rat_majority_certificate_sound certificate1748 valid1748 x hx0 hx1

def certificate1749 : RatMajorityCertificate := ⟨(27156516218823409/125000000000000000),(3057636062768447627922241601507091/3906250000000000000000000000000000),1,(34271895935680743711/100000000000000000000),(1070996747990023241/3125000000000000000),(550911898954496921/1000000000000000000),false⟩
theorem valid1749 : certificate1749.Valid := by decide +kernel
theorem bound1749 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1749.a certificate1749.b certificate1749.c x ≤ (certificate1749.bound:ℝ) :=
  rat_majority_certificate_sound certificate1749 valid1749 x hx0 hx1

def certificate1750 : RatMajorityCertificate := ⟨0,(250002457113804721/250000000000000000),(2714028587/2350000000),(21570438087557597631/50000000000000000000),(43140876175115195263/100000000000000000000),(340535253230200629/500000000000000000),false⟩
theorem valid1750 : certificate1750.Valid := by decide +kernel
theorem bound1750 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1750.a certificate1750.b certificate1750.c x ≤ (certificate1750.bound:ℝ) :=
  rat_majority_certificate_sound certificate1750 valid1750 x hx0 hx1

def certificate1751 : RatMajorityCertificate := ⟨(91576605136610009/500000000000000000),(102106852258609187601508818039947511/125000000000000000000000000000000000),(2714028587/2350000000),(19596547517597871837/50000000000000000000),(1567723801407829747/4000000000000000000),(340535253230200629/500000000000000000),false⟩
theorem valid1751 : certificate1751.Valid := by decide +kernel
theorem bound1751 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1751.a certificate1751.b certificate1751.c x ≤ (certificate1751.bound:ℝ) :=
  rat_majority_certificate_sound certificate1751 valid1751 x hx0 hx1

def certificate1752 : RatMajorityCertificate := ⟨0,(250002457113804721/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(137433255931191113/250000000000000000),false⟩
theorem valid1752 : certificate1752.Valid := by decide +kernel
theorem bound1752 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1752.a certificate1752.b certificate1752.c x ≤ (certificate1752.bound:ℝ) :=
  rat_majority_certificate_sound certificate1752 valid1752 x hx0 hx1

def certificate1753 : RatMajorityCertificate := ⟨(208474751491741733/1000000000000000000),(197883256994679461611500017271878507/250000000000000000000000000000000000),1,(34513124823620723749/100000000000000000000),(27610499858896579/80000000000000000),(137433255931191113/250000000000000000),false⟩
theorem valid1753 : certificate1753.Valid := by decide +kernel
theorem bound1753 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1753.a certificate1753.b certificate1753.c x ≤ (certificate1753.bound:ℝ) :=
  rat_majority_certificate_sound certificate1753 valid1753 x hx0 hx1

def certificate1754 : RatMajorityCertificate := ⟨0,(250002457113804721/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(275313157612473413/500000000000000000),false⟩
theorem valid1754 : certificate1754.Valid := by decide +kernel
theorem bound1754 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1754.a certificate1754.b certificate1754.c x ≤ (certificate1754.bound:ℝ) :=
  rat_majority_certificate_sound certificate1754 valid1754 x hx0 hx1

def certificate1755 : RatMajorityCertificate := ⟨(215141976134527287/1000000000000000000),(196216434451853364147077304636078073/250000000000000000000000000000000000),1,(8582569066623682777/25000000000000000000),(34330276266494731109/100000000000000000000),(275313157612473413/500000000000000000),false⟩
theorem valid1755 : certificate1755.Valid := by decide +kernel
theorem bound1755 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1755.a certificate1755.b certificate1755.c x ≤ (certificate1755.bound:ℝ) :=
  rat_majority_certificate_sound certificate1755 valid1755 x hx0 hx1

def certificate1756 : RatMajorityCertificate := ⟨0,(500005400111264623/500000000000000000),(678435109/587500000),(8627601005333879949/20000000000000000000),(21569002513334699873/50000000000000000000),(680877741122903079/1000000000000000000),false⟩
theorem valid1756 : certificate1756.Valid := by decide +kernel
theorem bound1756 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1756.a certificate1756.b certificate1756.c x ≤ (certificate1756.bound:ℝ) :=
  rat_majority_certificate_sound certificate1756 valid1756 x hx0 hx1

def certificate1757 : RatMajorityCertificate := ⟨(182316151231160267/1000000000000000000),(408846339968182503401012167039665659/500000000000000000000000000000000000),(678435109/587500000),(7842263417175096801/20000000000000000000),(19605658542937742003/50000000000000000000),(680877741122903079/1000000000000000000),false⟩
theorem valid1757 : certificate1757.Valid := by decide +kernel
theorem bound1757 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1757.a certificate1757.b certificate1757.c x ≤ (certificate1757.bound:ℝ) :=
  rat_majority_certificate_sound certificate1757 valid1757 x hx0 hx1

def certificate1758 : RatMajorityCertificate := ⟨0,(500005400111264623/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549697602364586891/1000000000000000000),false⟩
theorem valid1758 : certificate1758.Valid := by decide +kernel
theorem bound1758 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1758.a certificate1758.b certificate1758.c x ≤ (certificate1758.bound:ℝ) :=
  rat_majority_certificate_sound certificate1758 valid1758 x hx0 hx1

def certificate1759 : RatMajorityCertificate := ⟨(208204959644916009/1000000000000000000),(395901795958858689611929606391950393/500000000000000000000000000000000000),1,(34520477687870273831/100000000000000000000),(4315059710983784229/12500000000000000000),(549697602364586891/1000000000000000000),false⟩
theorem valid1759 : certificate1759.Valid := by decide +kernel
theorem bound1759 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1759.a certificate1759.b certificate1759.c x ≤ (certificate1759.bound:ℝ) :=
  rat_majority_certificate_sound certificate1759 valid1759 x hx0 hx1

end Cycle12.MajorityCertificates.Batch043
