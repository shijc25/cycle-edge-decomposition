import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch042
import Cycle12.MergedCutProfiles.Batch043
import Cycle12.MergedCutProfiles.Batch044
import Cycle12.MergedCutProfiles.Batch045

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch022

def retention264 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(436348967853034210/29508253281651770749),(361183457578753937/500000000000000000),(18/5),(1419502063599129199893/640000000000000000000),true,MergedCutProfiles.Batch043.profile1720,![MergedCutProfiles.Batch043.profile1720,MergedCutProfiles.Batch043.profile1721,MergedCutProfiles.Batch043.profile1722,MergedCutProfiles.Batch043.profile1723,MergedCutProfiles.Batch043.profile1724,MergedCutProfiles.Batch043.profile1725,MergedCutProfiles.Batch043.profile1726,MergedCutProfiles.Batch043.profile1727,MergedCutProfiles.Batch043.profile1728,MergedCutProfiles.Batch042.profile1715,MergedCutProfiles.Batch043.profile1729,MergedCutProfiles.Batch043.profile1730,MergedCutProfiles.Batch043.profile1731,MergedCutProfiles.Batch043.profile1732,MergedCutProfiles.Batch043.profile1733,MergedCutProfiles.Batch043.profile1734]⟩
theorem profilesValid264 : retention264.ProfilesValid := by
  change ∀ j : Fin 16, (retention264.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch043.valid1720
  · exact MergedCutProfiles.Batch043.valid1721
  · exact MergedCutProfiles.Batch043.valid1722
  · exact MergedCutProfiles.Batch043.valid1723
  · exact MergedCutProfiles.Batch043.valid1724
  · exact MergedCutProfiles.Batch043.valid1725
  · exact MergedCutProfiles.Batch043.valid1726
  · exact MergedCutProfiles.Batch043.valid1727
  · exact MergedCutProfiles.Batch043.valid1728
  · exact MergedCutProfiles.Batch042.valid1715
  · exact MergedCutProfiles.Batch043.valid1729
  · exact MergedCutProfiles.Batch043.valid1730
  · exact MergedCutProfiles.Batch043.valid1731
  · exact MergedCutProfiles.Batch043.valid1732
  · exact MergedCutProfiles.Batch043.valid1733
  · exact MergedCutProfiles.Batch043.valid1734
theorem numericValid264 : retention264.NumericValid := by decide +kernel
def certificate264 : RatCutBinCertificate := ⟨⟨retention264,(1991563315965953267/1000000000000000000),(39310593322721927/1000000000000000000),(9659167729003702169/1000000000000000000),(22917354861350491377/40000000000000000),(2188792466135313137/1000000000000000000)⟩,(249162666740009357/250000000000000000),(446176625111110577/1000000000000000000),(193740503649808989/1000000000000000000),(95098784568466431/1000000000000000000)⟩
theorem valid264 : certificate264.Valid := by decide +kernel
theorem sound264 : certificate264.Sound := rat_cut_bin_certificate_sound certificate264 profilesValid264 numericValid264 valid264

def retention265 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(516874911500000000/29508253281651770749),(43634896785303421/50000000000000000),(61/20),(140316462952719143909/64000000000000000000),true,MergedCutProfiles.Batch043.profile1735,![MergedCutProfiles.Batch043.profile1735,MergedCutProfiles.Batch043.profile1736,MergedCutProfiles.Batch043.profile1737,MergedCutProfiles.Batch043.profile1738,MergedCutProfiles.Batch043.profile1739,MergedCutProfiles.Batch043.profile1740,MergedCutProfiles.Batch042.profile1713,MergedCutProfiles.Batch043.profile1741,MergedCutProfiles.Batch043.profile1742,MergedCutProfiles.Batch043.profile1743,MergedCutProfiles.Batch043.profile1731,MergedCutProfiles.Batch043.profile1744,MergedCutProfiles.Batch043.profile1745,MergedCutProfiles.Batch043.profile1746,MergedCutProfiles.Batch043.profile1747,MergedCutProfiles.Batch043.profile1748]⟩
theorem profilesValid265 : retention265.ProfilesValid := by
  change ∀ j : Fin 16, (retention265.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch043.valid1735
  · exact MergedCutProfiles.Batch043.valid1736
  · exact MergedCutProfiles.Batch043.valid1737
  · exact MergedCutProfiles.Batch043.valid1738
  · exact MergedCutProfiles.Batch043.valid1739
  · exact MergedCutProfiles.Batch043.valid1740
  · exact MergedCutProfiles.Batch042.valid1713
  · exact MergedCutProfiles.Batch043.valid1741
  · exact MergedCutProfiles.Batch043.valid1742
  · exact MergedCutProfiles.Batch043.valid1743
  · exact MergedCutProfiles.Batch043.valid1731
  · exact MergedCutProfiles.Batch043.valid1744
  · exact MergedCutProfiles.Batch043.valid1745
  · exact MergedCutProfiles.Batch043.valid1746
  · exact MergedCutProfiles.Batch043.valid1747
  · exact MergedCutProfiles.Batch043.valid1748
theorem numericValid265 : retention265.NumericValid := by decide +kernel
def certificate265 : RatCutBinCertificate := ⟨⟨retention265,(1991563315965953267/1000000000000000000),(39310593322721927/1000000000000000000),(9659167729003702169/1000000000000000000),(22917354861350491377/40000000000000000),(2167723220821842231/1000000000000000000)⟩,(249162666740009357/250000000000000000),(102415934651548629/250000000000000000),(224743718064858201/1000000000000000000),(62789569974390727/500000000000000000)⟩
theorem valid265 : certificate265.Valid := by decide +kernel
theorem sound265 : certificate265.Sound := rat_cut_bin_certificate_sound certificate265 profilesValid265 numericValid265 valid265

def retention266 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(527157093580047437/29508253281651770749),(1033749823/1000000000),(53/20),(17443682837128095373/8000000000000000000),true,MergedCutProfiles.Batch043.profile1749,![MergedCutProfiles.Batch043.profile1749,MergedCutProfiles.Batch043.profile1750,MergedCutProfiles.Batch043.profile1751,MergedCutProfiles.Batch043.profile1752,MergedCutProfiles.Batch043.profile1753,MergedCutProfiles.Batch043.profile1754,MergedCutProfiles.Batch043.profile1755,MergedCutProfiles.Batch043.profile1756,MergedCutProfiles.Batch043.profile1757,MergedCutProfiles.Batch043.profile1758,MergedCutProfiles.Batch042.profile1719,MergedCutProfiles.Batch043.profile1759,MergedCutProfiles.Batch044.profile1760,MergedCutProfiles.Batch044.profile1761,MergedCutProfiles.Batch044.profile1762,MergedCutProfiles.Batch044.profile1763]⟩
theorem profilesValid266 : retention266.ProfilesValid := by
  change ∀ j : Fin 16, (retention266.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch043.valid1749
  · exact MergedCutProfiles.Batch043.valid1750
  · exact MergedCutProfiles.Batch043.valid1751
  · exact MergedCutProfiles.Batch043.valid1752
  · exact MergedCutProfiles.Batch043.valid1753
  · exact MergedCutProfiles.Batch043.valid1754
  · exact MergedCutProfiles.Batch043.valid1755
  · exact MergedCutProfiles.Batch043.valid1756
  · exact MergedCutProfiles.Batch043.valid1757
  · exact MergedCutProfiles.Batch043.valid1758
  · exact MergedCutProfiles.Batch042.valid1719
  · exact MergedCutProfiles.Batch043.valid1759
  · exact MergedCutProfiles.Batch044.valid1760
  · exact MergedCutProfiles.Batch044.valid1761
  · exact MergedCutProfiles.Batch044.valid1762
  · exact MergedCutProfiles.Batch044.valid1763
theorem numericValid266 : retention266.NumericValid := by decide +kernel
def certificate266 : RatCutBinCertificate := ⟨⟨retention266,(1991563315965953267/1000000000000000000),(39310593322721927/1000000000000000000),(9659167729003702169/1000000000000000000),(22917354861350491377/40000000000000000),(431796204629464993/200000000000000000)⟩,(249162666740009357/250000000000000000),(380618096721459477/1000000000000000000),(12585905650802807/50000000000000000),(157457739814444783/1000000000000000000)⟩
theorem valid266 : certificate266.Valid := by decide +kernel
theorem sound266 : certificate266.Sound := rat_cut_bin_certificate_sound certificate266 profilesValid266 numericValid266 valid266

def retention267 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(682803554439420223/29508253281651770749),(527157093580047437/500000000000000000),(13/5),(1378563716880368886673/640000000000000000000),true,MergedCutProfiles.Batch044.profile1764,![MergedCutProfiles.Batch044.profile1764,MergedCutProfiles.Batch044.profile1765,MergedCutProfiles.Batch044.profile1766,MergedCutProfiles.Batch044.profile1767,MergedCutProfiles.Batch044.profile1768,MergedCutProfiles.Batch044.profile1769,MergedCutProfiles.Batch043.profile1729,MergedCutProfiles.Batch044.profile1770,MergedCutProfiles.Batch044.profile1771,MergedCutProfiles.Batch044.profile1760,MergedCutProfiles.Batch044.profile1772,MergedCutProfiles.Batch044.profile1773,MergedCutProfiles.Batch044.profile1774,MergedCutProfiles.Batch044.profile1775,MergedCutProfiles.Batch044.profile1776,MergedCutProfiles.Batch044.profile1777]⟩
theorem profilesValid267 : retention267.ProfilesValid := by
  change ∀ j : Fin 16, (retention267.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch044.valid1764
  · exact MergedCutProfiles.Batch044.valid1765
  · exact MergedCutProfiles.Batch044.valid1766
  · exact MergedCutProfiles.Batch044.valid1767
  · exact MergedCutProfiles.Batch044.valid1768
  · exact MergedCutProfiles.Batch044.valid1769
  · exact MergedCutProfiles.Batch043.valid1729
  · exact MergedCutProfiles.Batch044.valid1770
  · exact MergedCutProfiles.Batch044.valid1771
  · exact MergedCutProfiles.Batch044.valid1760
  · exact MergedCutProfiles.Batch044.valid1772
  · exact MergedCutProfiles.Batch044.valid1773
  · exact MergedCutProfiles.Batch044.valid1774
  · exact MergedCutProfiles.Batch044.valid1775
  · exact MergedCutProfiles.Batch044.valid1776
  · exact MergedCutProfiles.Batch044.valid1777
theorem numericValid267 : retention267.NumericValid := by decide +kernel
def certificate267 : RatCutBinCertificate := ⟨⟨retention267,(1991563315965953267/1000000000000000000),(39310593322721927/1000000000000000000),(9659167729003702169/1000000000000000000),(22917354861350491377/40000000000000000),(426586349376027467/200000000000000000)⟩,(249162666740009357/250000000000000000),(11936927733729409/31250000000000000),(25040347485379701/100000000000000000),(7874742183137667/50000000000000000)⟩
theorem valid267 : certificate267.Valid := by decide +kernel
theorem sound267 : certificate267.Sound := rat_cut_bin_certificate_sound certificate267 profilesValid267 numericValid267 valid267

def retention268 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(3037398965059018572/29508253281651770749),(682803554439420223/500000000000000000),(11/5),(1205629323663655778123/640000000000000000000),true,MergedCutProfiles.Batch043.profile1726,![MergedCutProfiles.Batch043.profile1726,MergedCutProfiles.Batch043.profile1732,MergedCutProfiles.Batch044.profile1778,MergedCutProfiles.Batch044.profile1779,MergedCutProfiles.Batch044.profile1780,MergedCutProfiles.Batch044.profile1781,MergedCutProfiles.Batch044.profile1782,MergedCutProfiles.Batch044.profile1783,MergedCutProfiles.Batch044.profile1784,MergedCutProfiles.Batch044.profile1785,MergedCutProfiles.Batch044.profile1786,MergedCutProfiles.Batch044.profile1787,MergedCutProfiles.Batch044.profile1788,MergedCutProfiles.Batch044.profile1789,MergedCutProfiles.Batch044.profile1790,MergedCutProfiles.Batch044.profile1791]⟩
theorem profilesValid268 : retention268.ProfilesValid := by
  change ∀ j : Fin 16, (retention268.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch043.valid1726
  · exact MergedCutProfiles.Batch043.valid1732
  · exact MergedCutProfiles.Batch044.valid1778
  · exact MergedCutProfiles.Batch044.valid1779
  · exact MergedCutProfiles.Batch044.valid1780
  · exact MergedCutProfiles.Batch044.valid1781
  · exact MergedCutProfiles.Batch044.valid1782
  · exact MergedCutProfiles.Batch044.valid1783
  · exact MergedCutProfiles.Batch044.valid1784
  · exact MergedCutProfiles.Batch044.valid1785
  · exact MergedCutProfiles.Batch044.valid1786
  · exact MergedCutProfiles.Batch044.valid1787
  · exact MergedCutProfiles.Batch044.valid1788
  · exact MergedCutProfiles.Batch044.valid1789
  · exact MergedCutProfiles.Batch044.valid1790
  · exact MergedCutProfiles.Batch044.valid1791
theorem numericValid268 : retention268.NumericValid := by decide +kernel
def certificate268 : RatCutBinCertificate := ⟨⟨retention268,(1991563315965953267/1000000000000000000),(39310593322721927/1000000000000000000),(9659167729003702169/1000000000000000000),(22917354861350491377/40000000000000000),(1865963959759375683/1000000000000000000)⟩,(249162666740009357/250000000000000000),(393606385517353711/1000000000000000000),(119695929633176867/500000000000000000),(78868483044180043/500000000000000000)⟩
theorem valid268 : certificate268.Valid := by decide +kernel
theorem sound268 : certificate268.Sound := rat_cut_bin_certificate_sound certificate268 profilesValid268 numericValid268 valid268

def retention269 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(25205092013788799181/59016506563303541498),(759349741264754643/125000000000000000),(11/10),(19180870165207107839350240114393975631/16874438694772325400000000000000000000),false,MergedCutProfiles.Batch044.profile1792,(fun _ => MergedCutProfiles.Batch044.profile1792)⟩
theorem profilesValid269 : retention269.ProfilesValid := by
  exact MergedCutProfiles.Batch044.valid1792
theorem numericValid269 : retention269.NumericValid := by decide +kernel
def certificate269 : RatCutBinCertificate := ⟨⟨retention269,(1991563315965953267/1000000000000000000),(39310593322721927/1000000000000000000),(9659167729003702169/1000000000000000000),(22917354861350491377/40000000000000000),(563883074848541697/500000000000000000)⟩,(249162666740009357/250000000000000000),(464337468472977823/1000000000000000000),(179448799700588177/1000000000000000000),(39733538647216663/250000000000000000)⟩
theorem valid269 : certificate269.Valid := by decide +kernel
theorem sound269 : certificate269.Sound := rat_cut_bin_certificate_sound certificate269 profilesValid269 numericValid269 valid269

def retention270 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(29262329345253074907/59016506563303541498),(25205092013788799181/1000000000000000000),1,(20158332140371048618725838594951248367/20164073611031039344800000000000000000),false,MergedCutProfiles.Batch044.profile1793,(fun _ => MergedCutProfiles.Batch044.profile1793)⟩
theorem profilesValid270 : retention270.ProfilesValid := by
  exact MergedCutProfiles.Batch044.valid1793
theorem numericValid270 : retention270.NumericValid := by decide +kernel
def certificate270 : RatCutBinCertificate := ⟨⟨retention270,(1991563315965953267/1000000000000000000),(39310593322721927/1000000000000000000),(9659167729003702169/1000000000000000000),(22917354861350491377/40000000000000000),(495805017597225707/500000000000000000)⟩,(249162666740009357/250000000000000000),(120326962535075273/250000000000000000),(166736556827185059/1000000000000000000),(158535381163452861/1000000000000000000)⟩
theorem valid270 : certificate270.Valid := by decide +kernel
theorem sound270 : certificate270.Sound := rat_cut_bin_certificate_sound certificate270 profilesValid270 numericValid270 valid270

def retention271 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(1/2),(29262329345253074907/1000000000000000000),1,(38739862696574115692278459973205938649/39016439127004099876000000000000000000),false,MergedCutProfiles.Batch044.profile1794,(fun _ => MergedCutProfiles.Batch044.profile1794)⟩
theorem profilesValid271 : retention271.ProfilesValid := by
  exact MergedCutProfiles.Batch044.valid1794
theorem numericValid271 : retention271.NumericValid := by decide +kernel
def certificate271 : RatCutBinCertificate := ⟨⟨retention271,(1991563315965953267/1000000000000000000),(39310593322721927/1000000000000000000),(9659167729003702169/1000000000000000000),(22917354861350491377/40000000000000000),(984806060553123461/1000000000000000000)⟩,(249162666740009357/250000000000000000),(120639750388624817/250000000000000000),(82911641752110079/500000000000000000),(157448199564288167/1000000000000000000)⟩
theorem valid271 : certificate271.Valid := by decide +kernel
theorem sound271 : certificate271.Sound := rat_cut_bin_certificate_sound certificate271 profilesValid271 numericValid271 valid271

def retention272 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(24790700970915484853/59016506563303541498),(114666105452015811/31250000000000000),(5/4),(17010295792353654621053594706968225111/14677261497858023808000000000000000000),false,MergedCutProfiles.Batch044.profile1795,(fun _ => MergedCutProfiles.Batch044.profile1795)⟩
theorem profilesValid272 : retention272.ProfilesValid := by
  exact MergedCutProfiles.Batch044.valid1795
theorem numericValid272 : retention272.NumericValid := by decide +kernel
def certificate272 : RatCutBinCertificate := ⟨⟨retention272,(2373485573965953267/1000000000000000000),(39310593322721927/1000000000000000000),(9659167729003702169/1000000000000000000),(22917354861350491377/40000000000000000),(1146881087679209219/1000000000000000000)⟩,(996008267730671649/1000000000000000000),(88194637548759629/250000000000000000),(139825450893426087/500000000000000000),(53221702074532403/250000000000000000)⟩
theorem valid272 : certificate272.Valid := by decide +kernel
theorem sound272 : certificate272.Sound := rat_cut_bin_certificate_sound certificate272 profilesValid272 numericValid272 valid272

def retention273 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(29359737016696543451/59016506563303541498),(24790700970915484853/1000000000000000000),1,(24699107995480695659052380109109167253/24790700970915484853000000000000000000),false,MergedCutProfiles.Batch044.profile1796,(fun _ => MergedCutProfiles.Batch044.profile1796)⟩
theorem profilesValid273 : retention273.ProfilesValid := by
  exact MergedCutProfiles.Batch044.valid1796
theorem numericValid273 : retention273.NumericValid := by decide +kernel
def certificate273 : RatCutBinCertificate := ⟨⟨retention273,(2373485573965953267/1000000000000000000),(39310593322721927/1000000000000000000),(9659167729003702169/1000000000000000000),(22917354861350491377/40000000000000000),(986645781834470933/1000000000000000000)⟩,(996008267730671649/1000000000000000000),(102517806999923653/250000000000000000),(22438028200030579/100000000000000000),(26505672254260197/125000000000000000)⟩
theorem valid273 : certificate273.Valid := by decide +kernel
theorem sound273 : certificate273.Sound := rat_cut_bin_certificate_sound certificate273 profilesValid273 numericValid273 valid273

def retention274 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(1/2),(29359737016696543451/1000000000000000000),1,(116609795428604282147911179288806760843/117438948066786173804000000000000000000),false,MergedCutProfiles.Batch044.profile1794,(fun _ => MergedCutProfiles.Batch044.profile1794)⟩
theorem profilesValid274 : retention274.ProfilesValid := by
  exact MergedCutProfiles.Batch044.valid1794
theorem numericValid274 : retention274.NumericValid := by decide +kernel
def certificate274 : RatCutBinCertificate := ⟨⟨retention274,(2373485573965953267/1000000000000000000),(39310593322721927/1000000000000000000),(9659167729003702169/1000000000000000000),(22917354861350491377/40000000000000000),(983280149824615739/1000000000000000000)⟩,(996008267730671649/1000000000000000000),(411474845118907861/1000000000000000000),(111565752341384113/500000000000000000),(105715446661093237/500000000000000000)⟩
theorem valid274 : certificate274.Valid := by decide +kernel
theorem sound274 : certificate274.Sound := rat_cut_bin_certificate_sound certificate274 profilesValid274 numericValid274 valid274

def retention275 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(728961901444145483/54990570427380060659),(721744456875391567/1000000000000000000),(18/5),(178104113246418933759/80000000000000000000),true,MergedCutProfiles.Batch044.profile1797,![MergedCutProfiles.Batch044.profile1797,MergedCutProfiles.Batch044.profile1798,MergedCutProfiles.Batch044.profile1799,MergedCutProfiles.Batch045.profile1800,MergedCutProfiles.Batch045.profile1801,MergedCutProfiles.Batch045.profile1802,MergedCutProfiles.Batch045.profile1803,MergedCutProfiles.Batch045.profile1804,MergedCutProfiles.Batch045.profile1805,MergedCutProfiles.Batch045.profile1806,MergedCutProfiles.Batch045.profile1807,MergedCutProfiles.Batch045.profile1808,MergedCutProfiles.Batch045.profile1809,MergedCutProfiles.Batch045.profile1810,MergedCutProfiles.Batch045.profile1811,MergedCutProfiles.Batch045.profile1812]⟩
theorem profilesValid275 : retention275.ProfilesValid := by
  change ∀ j : Fin 16, (retention275.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch044.valid1797
  · exact MergedCutProfiles.Batch044.valid1798
  · exact MergedCutProfiles.Batch044.valid1799
  · exact MergedCutProfiles.Batch045.valid1800
  · exact MergedCutProfiles.Batch045.valid1801
  · exact MergedCutProfiles.Batch045.valid1802
  · exact MergedCutProfiles.Batch045.valid1803
  · exact MergedCutProfiles.Batch045.valid1804
  · exact MergedCutProfiles.Batch045.valid1805
  · exact MergedCutProfiles.Batch045.valid1806
  · exact MergedCutProfiles.Batch045.valid1807
  · exact MergedCutProfiles.Batch045.valid1808
  · exact MergedCutProfiles.Batch045.valid1809
  · exact MergedCutProfiles.Batch045.valid1810
  · exact MergedCutProfiles.Batch045.valid1811
  · exact MergedCutProfiles.Batch045.valid1812
theorem numericValid275 : retention275.NumericValid := by decide +kernel
def certificate275 : RatCutBinCertificate := ⟨⟨retention275,(499557047732608841/250000000000000000),(42146381475855499/1000000000000000000),(2449118668530467497/250000000000000000),(33840943074420866071/62500000000000000),(439070419756320811/200000000000000000)⟩,(249113519363578313/250000000000000000),(440924093420574647/1000000000000000000),(3960209791928281/20000000000000000),(48696063667462741/500000000000000000)⟩
theorem valid275 : certificate275.Valid := by decide +kernel
theorem sound275 : certificate275.Sound := rat_cut_bin_certificate_sound certificate275 profilesValid275 numericValid275 valid275

def certificates : List RatCutBinCertificate := [certificate264,certificate265,certificate266,certificate267,certificate268,certificate269,certificate270,certificate271,certificate272,certificate273,certificate274,certificate275]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound264,List.forall_mem_cons.mpr ⟨sound265,List.forall_mem_cons.mpr ⟨sound266,List.forall_mem_cons.mpr ⟨sound267,List.forall_mem_cons.mpr ⟨sound268,List.forall_mem_cons.mpr ⟨sound269,List.forall_mem_cons.mpr ⟨sound270,List.forall_mem_cons.mpr ⟨sound271,List.forall_mem_cons.mpr ⟨sound272,List.forall_mem_cons.mpr ⟨sound273,List.forall_mem_cons.mpr ⟨sound274,List.forall_mem_cons.mpr ⟨sound275,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch022
