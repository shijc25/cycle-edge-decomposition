import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch292
import Cycle12.MergedCutProfiles.Batch293

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch153

def retention1836 : RatCutRetentionCertificate := ⟨(33/500),(529/8000),(4913185670352938351/9894880052446134049),(972908053535235317/200000000000000000),(11/10),(77410343652409729624977647545925990999/77832644282818825360000000000000000000),false,MergedCutProfiles.Batch292.profile11683,(fun _ => MergedCutProfiles.Batch292.profile11683)⟩
theorem profilesValid1836 : retention1836.ProfilesValid := by
  exact MergedCutProfiles.Batch292.valid11683
theorem numericValid1836 : retention1836.NumericValid := by decide +kernel
def certificate1836 : RatCutBinCertificate := ⟨⟨retention1836,(2716049804072634489/1000000000000000000),(230375442520233127/1000000000000000000),(3551383010985760831/200000000000000000),(175842661536513036111/1000000000000000000),(955803391169577341/1000000000000000000)⟩,(494025866919223573/500000000000000000),(79164462984879141/200000000000000000),(29666506136132287/125000000000000000),(7003731742708827/40000000000000000)⟩
theorem valid1836 : certificate1836.Valid := by decide +kernel
theorem sound1836 : certificate1836.Sound := rat_cut_bin_certificate_sound certificate1836 profilesValid1836 numericValid1836 valid1836

def retention1837 : RatCutRetentionCertificate := ⟨(33/500),(529/8000),(1/2),(4913185670352938351/1000000000000000000),(11/10),(1942465956951629060368161454688953241759/1965274268141175340400000000000000000000),false,MergedCutProfiles.Batch292.profile11680,(fun _ => MergedCutProfiles.Batch292.profile11680)⟩
theorem profilesValid1837 : retention1837.ProfilesValid := by
  exact MergedCutProfiles.Batch292.valid11680
theorem numericValid1837 : retention1837.NumericValid := by decide +kernel
def certificate1837 : RatCutBinCertificate := ⟨⟨retention1837,(2716049804072634489/1000000000000000000),(230375442520233127/1000000000000000000),(3551383010985760831/200000000000000000),(175842661536513036111/1000000000000000000),(949623574028395283/1000000000000000000)⟩,(494025866919223573/500000000000000000),(99599546929006943/250000000000000000),(234953233619512073/1000000000000000000),(172612182691462573/1000000000000000000)⟩
theorem valid1837 : certificate1837.Valid := by decide +kernel
theorem sound1837 : certificate1837.Sound := rat_cut_bin_certificate_sound certificate1837 profilesValid1837 numericValid1837 valid1837

def retention1838 : RatCutRetentionCertificate := ⟨(529/8000),(53/800),(688369240879683887/4924857214933737757),(114441921121736843/125000000000000000),(12/5),(71455537753905229173/40000000000000000000),true,MergedCutProfiles.Batch292.profile11684,![MergedCutProfiles.Batch292.profile11684,MergedCutProfiles.Batch292.profile11685,MergedCutProfiles.Batch292.profile11686,MergedCutProfiles.Batch292.profile11687,MergedCutProfiles.Batch292.profile11688,MergedCutProfiles.Batch292.profile11689,MergedCutProfiles.Batch292.profile11690,MergedCutProfiles.Batch292.profile11691,MergedCutProfiles.Batch292.profile11692,MergedCutProfiles.Batch292.profile11693,MergedCutProfiles.Batch292.profile11694,MergedCutProfiles.Batch292.profile11695,MergedCutProfiles.Batch292.profile11696,MergedCutProfiles.Batch292.profile11697,MergedCutProfiles.Batch292.profile11698,MergedCutProfiles.Batch292.profile11699]⟩
theorem profilesValid1838 : retention1838.ProfilesValid := by
  change ∀ j : Fin 16, (retention1838.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch292.valid11684
  · exact MergedCutProfiles.Batch292.valid11685
  · exact MergedCutProfiles.Batch292.valid11686
  · exact MergedCutProfiles.Batch292.valid11687
  · exact MergedCutProfiles.Batch292.valid11688
  · exact MergedCutProfiles.Batch292.valid11689
  · exact MergedCutProfiles.Batch292.valid11690
  · exact MergedCutProfiles.Batch292.valid11691
  · exact MergedCutProfiles.Batch292.valid11692
  · exact MergedCutProfiles.Batch292.valid11693
  · exact MergedCutProfiles.Batch292.valid11694
  · exact MergedCutProfiles.Batch292.valid11695
  · exact MergedCutProfiles.Batch292.valid11696
  · exact MergedCutProfiles.Batch292.valid11697
  · exact MergedCutProfiles.Batch292.valid11698
  · exact MergedCutProfiles.Batch292.valid11699
theorem numericValid1838 : retention1838.NumericValid := by decide +kernel
def certificate1838 : RatCutBinCertificate := ⟨⟨retention1838,(2410228678064180813/1000000000000000000),(231439924742735297/1000000000000000000),(4449992263997118281/250000000000000000),(21933068711334907873/125000000000000000),(427782763627191077/250000000000000000)⟩,(30918526649235849/31250000000000000),(166105313076624719/500000000000000000),(301688313273688469/1000000000000000000),(160287364984119339/1000000000000000000)⟩
theorem valid1838 : certificate1838.Valid := by decide +kernel
theorem sound1838 : certificate1838.Sound := rat_cut_bin_certificate_sound certificate1838 profilesValid1838 numericValid1838 valid1838

def retention1839 : RatCutRetentionCertificate := ⟨(529/8000),(53/800),(2790416236585525213/9849714429867475514),(688369240879683887/500000000000000000),(17/10),(916422117566119090907/640000000000000000000),true,MergedCutProfiles.Batch292.profile11700,![MergedCutProfiles.Batch292.profile11700,MergedCutProfiles.Batch292.profile11701,MergedCutProfiles.Batch292.profile11702,MergedCutProfiles.Batch292.profile11703,MergedCutProfiles.Batch292.profile11704,MergedCutProfiles.Batch292.profile11705,MergedCutProfiles.Batch292.profile11706,MergedCutProfiles.Batch292.profile11707,MergedCutProfiles.Batch292.profile11708,MergedCutProfiles.Batch292.profile11709,MergedCutProfiles.Batch292.profile11710,MergedCutProfiles.Batch292.profile11711,MergedCutProfiles.Batch292.profile11712,MergedCutProfiles.Batch292.profile11713,MergedCutProfiles.Batch292.profile11714,MergedCutProfiles.Batch292.profile11715]⟩
theorem profilesValid1839 : retention1839.ProfilesValid := by
  change ∀ j : Fin 16, (retention1839.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch292.valid11700
  · exact MergedCutProfiles.Batch292.valid11701
  · exact MergedCutProfiles.Batch292.valid11702
  · exact MergedCutProfiles.Batch292.valid11703
  · exact MergedCutProfiles.Batch292.valid11704
  · exact MergedCutProfiles.Batch292.valid11705
  · exact MergedCutProfiles.Batch292.valid11706
  · exact MergedCutProfiles.Batch292.valid11707
  · exact MergedCutProfiles.Batch292.valid11708
  · exact MergedCutProfiles.Batch292.valid11709
  · exact MergedCutProfiles.Batch292.valid11710
  · exact MergedCutProfiles.Batch292.valid11711
  · exact MergedCutProfiles.Batch292.valid11712
  · exact MergedCutProfiles.Batch292.valid11713
  · exact MergedCutProfiles.Batch292.valid11714
  · exact MergedCutProfiles.Batch292.valid11715
theorem numericValid1839 : retention1839.NumericValid := by decide +kernel
def certificate1839 : RatCutBinCertificate := ⟨⟨retention1839,(2410228678064180813/1000000000000000000),(231439924742735297/1000000000000000000),(4449992263997118281/250000000000000000),(21933068711334907873/125000000000000000),(1378604197578171303/1000000000000000000)⟩,(30918526649235849/31250000000000000),(90442933370823889/250000000000000000),(27039565675890483/100000000000000000),(32152268650617553/200000000000000000)⟩
theorem valid1839 : certificate1839.Valid := by decide +kernel
theorem sound1839 : certificate1839.Sound := rat_cut_bin_certificate_sound certificate1839 profilesValid1839 numericValid1839 valid1839

def retention1840 : RatCutRetentionCertificate := ⟨(529/8000),(53/800),(4323240907184035231/9849714429867475514),(2790416236585525213/1000000000000000000),(11/10),(1386341132142856011769/1280000000000000000000),true,MergedCutProfiles.Batch292.profile11716,![MergedCutProfiles.Batch292.profile11716,MergedCutProfiles.Batch292.profile11717,MergedCutProfiles.Batch292.profile11718,MergedCutProfiles.Batch292.profile11719,MergedCutProfiles.Batch293.profile11720,MergedCutProfiles.Batch293.profile11721,MergedCutProfiles.Batch293.profile11722,MergedCutProfiles.Batch293.profile11723,MergedCutProfiles.Batch293.profile11724,MergedCutProfiles.Batch293.profile11725,MergedCutProfiles.Batch293.profile11726,MergedCutProfiles.Batch293.profile11727,MergedCutProfiles.Batch293.profile11728,MergedCutProfiles.Batch293.profile11729,MergedCutProfiles.Batch293.profile11730,MergedCutProfiles.Batch293.profile11731]⟩
theorem profilesValid1840 : retention1840.ProfilesValid := by
  change ∀ j : Fin 16, (retention1840.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch292.valid11716
  · exact MergedCutProfiles.Batch292.valid11717
  · exact MergedCutProfiles.Batch292.valid11718
  · exact MergedCutProfiles.Batch292.valid11719
  · exact MergedCutProfiles.Batch293.valid11720
  · exact MergedCutProfiles.Batch293.valid11721
  · exact MergedCutProfiles.Batch293.valid11722
  · exact MergedCutProfiles.Batch293.valid11723
  · exact MergedCutProfiles.Batch293.valid11724
  · exact MergedCutProfiles.Batch293.valid11725
  · exact MergedCutProfiles.Batch293.valid11726
  · exact MergedCutProfiles.Batch293.valid11727
  · exact MergedCutProfiles.Batch293.valid11728
  · exact MergedCutProfiles.Batch293.valid11729
  · exact MergedCutProfiles.Batch293.valid11730
  · exact MergedCutProfiles.Batch293.valid11731
theorem numericValid1840 : retention1840.NumericValid := by decide +kernel
def certificate1840 : RatCutBinCertificate := ⟨⟨retention1840,(2410228678064180813/1000000000000000000),(231439924742735297/1000000000000000000),(4449992263997118281/250000000000000000),(21933068711334907873/125000000000000000),(131073989915046081/125000000000000000)⟩,(30918526649235849/31250000000000000),(81752952359701307/200000000000000000),(45109388155165771/200000000000000000),(162030750448260927/1000000000000000000)⟩
theorem valid1840 : certificate1840.Valid := by decide +kernel
theorem sound1840 : certificate1840.Sound := rat_cut_bin_certificate_sound certificate1840 profilesValid1840 numericValid1840 valid1840

def retention1841 : RatCutRetentionCertificate := ⟨(529/8000),(53/800),(4775547559558292927/9849714429867475514),(4323240907184035231/1000000000000000000),1,(251706431882932002511/256000000000000000000),true,MergedCutProfiles.Batch293.profile11732,![MergedCutProfiles.Batch293.profile11732,MergedCutProfiles.Batch293.profile11733,MergedCutProfiles.Batch293.profile11734,MergedCutProfiles.Batch293.profile11735,MergedCutProfiles.Batch293.profile11736,MergedCutProfiles.Batch293.profile11737,MergedCutProfiles.Batch293.profile11738,MergedCutProfiles.Batch293.profile11739,MergedCutProfiles.Batch293.profile11740,MergedCutProfiles.Batch293.profile11741,MergedCutProfiles.Batch293.profile11742,MergedCutProfiles.Batch293.profile11743,MergedCutProfiles.Batch293.profile11744,MergedCutProfiles.Batch293.profile11745,MergedCutProfiles.Batch293.profile11746,MergedCutProfiles.Batch293.profile11747]⟩
theorem profilesValid1841 : retention1841.ProfilesValid := by
  change ∀ j : Fin 16, (retention1841.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch293.valid11732
  · exact MergedCutProfiles.Batch293.valid11733
  · exact MergedCutProfiles.Batch293.valid11734
  · exact MergedCutProfiles.Batch293.valid11735
  · exact MergedCutProfiles.Batch293.valid11736
  · exact MergedCutProfiles.Batch293.valid11737
  · exact MergedCutProfiles.Batch293.valid11738
  · exact MergedCutProfiles.Batch293.valid11739
  · exact MergedCutProfiles.Batch293.valid11740
  · exact MergedCutProfiles.Batch293.valid11741
  · exact MergedCutProfiles.Batch293.valid11742
  · exact MergedCutProfiles.Batch293.valid11743
  · exact MergedCutProfiles.Batch293.valid11744
  · exact MergedCutProfiles.Batch293.valid11745
  · exact MergedCutProfiles.Batch293.valid11746
  · exact MergedCutProfiles.Batch293.valid11747
theorem numericValid1841 : retention1841.NumericValid := by decide +kernel
def certificate1841 : RatCutBinCertificate := ⟨⟨retention1841,(2410228678064180813/1000000000000000000),(231439924742735297/1000000000000000000),(4449992263997118281/250000000000000000),(21933068711334907873/125000000000000000),(190376050979779369/200000000000000000)⟩,(30918526649235849/31250000000000000),(212431258519799221/500000000000000000),(211458940724731031/1000000000000000000),(16299403073749313/100000000000000000)⟩
theorem valid1841 : certificate1841.Valid := by decide +kernel
theorem sound1841 : certificate1841.Sound := rat_cut_bin_certificate_sound certificate1841 profilesValid1841 numericValid1841 valid1841

def retention1842 : RatCutRetentionCertificate := ⟨(529/8000),(53/800),(2435768032752707308/4924857214933737757),(4775547559558292927/1000000000000000000),(11/10),(1905481550356408488694955738384865498751/1910219023823317170800000000000000000000),false,MergedCutProfiles.Batch293.profile11748,(fun _ => MergedCutProfiles.Batch293.profile11748)⟩
theorem profilesValid1842 : retention1842.ProfilesValid := by
  exact MergedCutProfiles.Batch293.valid11748
theorem numericValid1842 : retention1842.NumericValid := by decide +kernel
def certificate1842 : RatCutBinCertificate := ⟨⟨retention1842,(2410228678064180813/1000000000000000000),(231439924742735297/1000000000000000000),(4449992263997118281/250000000000000000),(21933068711334907873/125000000000000000),(481519499697532993/500000000000000000)⟩,(30918526649235849/31250000000000000),(415605293626602213/1000000000000000000),(219484411325886317/1000000000000000000),(81385567665554641/500000000000000000)⟩
theorem valid1842 : certificate1842.Valid := by decide +kernel
theorem sound1842 : certificate1842.Sound := rat_cut_bin_certificate_sound certificate1842 profilesValid1842 numericValid1842 valid1842

def retention1843 : RatCutRetentionCertificate := ⟨(529/8000),(53/800),(4920251426160468763/9849714429867475514),(608942008188176827/125000000000000000),(11/10),(120442654650537870521055494929119209519/121788401637635365400000000000000000000),false,MergedCutProfiles.Batch293.profile11749,(fun _ => MergedCutProfiles.Batch293.profile11749)⟩
theorem profilesValid1843 : retention1843.ProfilesValid := by
  exact MergedCutProfiles.Batch293.valid11749
theorem numericValid1843 : retention1843.NumericValid := by decide +kernel
def certificate1843 : RatCutBinCertificate := ⟨⟨retention1843,(2410228678064180813/1000000000000000000),(231439924742735297/1000000000000000000),(4449992263997118281/250000000000000000),(21933068711334907873/125000000000000000),(190893872018711733/200000000000000000)⟩,(30918526649235849/31250000000000000),(418513143965160099/1000000000000000000),(108470741798936517/500000000000000000),(40026677075258569/250000000000000000)⟩
theorem valid1843 : certificate1843.Valid := by decide +kernel
theorem sound1843 : certificate1843.Sound := rat_cut_bin_certificate_sound certificate1843 profilesValid1843 numericValid1843 valid1843

def retention1844 : RatCutRetentionCertificate := ⟨(529/8000),(53/800),(1/2),(4920251426160468763/1000000000000000000),(11/10),(1945370599109672636392416321370016103511/1968100570464187505200000000000000000000),false,MergedCutProfiles.Batch293.profile11750,(fun _ => MergedCutProfiles.Batch293.profile11750)⟩
theorem profilesValid1844 : retention1844.ProfilesValid := by
  exact MergedCutProfiles.Batch293.valid11750
theorem numericValid1844 : retention1844.NumericValid := by decide +kernel
def certificate1844 : RatCutBinCertificate := ⟨⟨retention1844,(2410228678064180813/1000000000000000000),(231439924742735297/1000000000000000000),(4449992263997118281/250000000000000000),(21933068711334907873/125000000000000000),(119246266271088909/125000000000000000)⟩,(30918526649235849/31250000000000000),(41832623614828023/100000000000000000),(108552163194526093/500000000000000000),(20047185394824949/125000000000000000)⟩
theorem valid1844 : certificate1844.Valid := by decide +kernel
theorem sound1844 : certificate1844.Sound := rat_cut_bin_certificate_sound certificate1844 profilesValid1844 numericValid1844 valid1844

def retention1845 : RatCutRetentionCertificate := ⟨(529/8000),(53/800),(1/2),64,1,(15963646046978184903216517034413403031/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch293.profile11750,(fun _ => MergedCutProfiles.Batch293.profile11750)⟩
theorem profilesValid1845 : retention1845.ProfilesValid := by
  exact MergedCutProfiles.Batch293.valid11750
theorem numericValid1845 : retention1845.NumericValid := by decide +kernel
def certificate1845 : RatCutBinCertificate := ⟨⟨retention1845,(2410228678064180813/1000000000000000000),(231439924742735297/1000000000000000000),(4449992263997118281/250000000000000000),(21933068711334907873/125000000000000000),(241597199679039571/250000000000000000)⟩,(30918526649235849/31250000000000000),(375960388352318451/1000000000000000000),(64061382743062259/250000000000000000),(241335317155931117/1000000000000000000)⟩
theorem valid1845 : certificate1845.Valid := by decide +kernel
theorem sound1845 : certificate1845.Sound := rat_cut_bin_certificate_sound certificate1845 profilesValid1845 numericValid1845 valid1845

def retention1846 : RatCutRetentionCertificate := ⟨(529/8000),(53/800),(4515587716444890713/9849714429867475514),(728641403070763167/250000000000000000),(5/4),(21748665162595700489581371869533919/20240038974187865750000000000000000),false,MergedCutProfiles.Batch293.profile11751,(fun _ => MergedCutProfiles.Batch293.profile11751)⟩
theorem profilesValid1846 : retention1846.ProfilesValid := by
  exact MergedCutProfiles.Batch293.valid11751
theorem numericValid1846 : retention1846.NumericValid := by decide +kernel
def certificate1846 : RatCutBinCertificate := ⟨⟨retention1846,(2717485569064180813/1000000000000000000),(231439924742735297/1000000000000000000),(4449992263997118281/250000000000000000),(21933068711334907873/125000000000000000),(515176948355664273/500000000000000000)⟩,(988035810505703587/1000000000000000000),(45740628322202443/125000000000000000),(53239409762550311/200000000000000000),(176516033533836839/1000000000000000000)⟩
theorem valid1846 : certificate1846.Valid := by decide +kernel
theorem sound1846 : certificate1846.Sound := rat_cut_bin_certificate_sound certificate1846 profilesValid1846 numericValid1846 valid1846

def retention1847 : RatCutRetentionCertificate := ⟨(529/8000),(53/800),(4841321226340732139/9849714429867475514),(4515587716444890713/1000000000000000000),(11/10),(1807777888202632080695535300475252594471/1806235086577956285200000000000000000000),false,MergedCutProfiles.Batch293.profile11752,(fun _ => MergedCutProfiles.Batch293.profile11752)⟩
theorem profilesValid1847 : retention1847.ProfilesValid := by
  exact MergedCutProfiles.Batch293.valid11752
theorem numericValid1847 : retention1847.NumericValid := by decide +kernel
def certificate1847 : RatCutBinCertificate := ⟨⟨retention1847,(2717485569064180813/1000000000000000000),(231439924742735297/1000000000000000000),(4449992263997118281/250000000000000000),(21933068711334907873/125000000000000000),(961977016355167381/1000000000000000000)⟩,(988035810505703587/1000000000000000000),(391934807826265469/1000000000000000000),(15059619719386373/62500000000000000),(44204042913054091/250000000000000000)⟩
theorem valid1847 : certificate1847.Valid := by decide +kernel
theorem sound1847 : certificate1847.Sound := rat_cut_bin_certificate_sound certificate1847 profilesValid1847 numericValid1847 valid1847

def certificates : List RatCutBinCertificate := [certificate1836,certificate1837,certificate1838,certificate1839,certificate1840,certificate1841,certificate1842,certificate1843,certificate1844,certificate1845,certificate1846,certificate1847]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1836,List.forall_mem_cons.mpr ⟨sound1837,List.forall_mem_cons.mpr ⟨sound1838,List.forall_mem_cons.mpr ⟨sound1839,List.forall_mem_cons.mpr ⟨sound1840,List.forall_mem_cons.mpr ⟨sound1841,List.forall_mem_cons.mpr ⟨sound1842,List.forall_mem_cons.mpr ⟨sound1843,List.forall_mem_cons.mpr ⟨sound1844,List.forall_mem_cons.mpr ⟨sound1845,List.forall_mem_cons.mpr ⟨sound1846,List.forall_mem_cons.mpr ⟨sound1847,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch153
