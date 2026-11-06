import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch166
import Cycle12.MergedCutProfiles.Batch167
import Cycle12.MergedCutProfiles.Batch168

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch083

def retention996 : RatCutRetentionCertificate := ⟨(103/2000),(207/4000),(1/2),(8749508170727351083/1000000000000000000),(21/20),(13893785695964968795232693539899748335951/13999213073163761732800000000000000000000),false,MergedCutProfiles.Batch166.profile6669,(fun _ => MergedCutProfiles.Batch166.profile6669)⟩
theorem profilesValid996 : retention996.ProfilesValid := by
  exact MergedCutProfiles.Batch166.valid6669
theorem numericValid996 : retention996.NumericValid := by decide +kernel
def certificate996 : RatCutBinCertificate := ⟨⟨retention996,(2555171518738488223/1000000000000000000),(16182290823511013/125000000000000000),(13659846689896458373/1000000000000000000),(241178661540697140603/1000000000000000000),(241760164480500009/250000000000000000)⟩,(990749124187380419/1000000000000000000),(419058697280973697/1000000000000000000),(108233324638119777/500000000000000000),(11214918234180297/62500000000000000)⟩
theorem valid996 : certificate996.Valid := by decide +kernel
theorem sound996 : certificate996.Sound := rat_cut_bin_certificate_sound certificate996 profilesValid996 numericValid996 valid996

def retention997 : RatCutRetentionCertificate := ⟨(207/4000),(13/250),(948502854626936981/17436099028693195146),(850165604735466541/1000000000000000000),(57/20),(2609660643007679569909/1280000000000000000000),true,MergedCutProfiles.Batch166.profile6672,![MergedCutProfiles.Batch166.profile6672,MergedCutProfiles.Batch166.profile6673,MergedCutProfiles.Batch166.profile6674,MergedCutProfiles.Batch166.profile6675,MergedCutProfiles.Batch166.profile6676,MergedCutProfiles.Batch166.profile6677,MergedCutProfiles.Batch166.profile6678,MergedCutProfiles.Batch166.profile6679,MergedCutProfiles.Batch167.profile6680,MergedCutProfiles.Batch167.profile6681,MergedCutProfiles.Batch167.profile6682,MergedCutProfiles.Batch167.profile6683,MergedCutProfiles.Batch167.profile6684,MergedCutProfiles.Batch167.profile6685,MergedCutProfiles.Batch167.profile6686,MergedCutProfiles.Batch167.profile6687]⟩
theorem profilesValid997 : retention997.ProfilesValid := by
  change ∀ j : Fin 16, (retention997.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch166.valid6672
  · exact MergedCutProfiles.Batch166.valid6673
  · exact MergedCutProfiles.Batch166.valid6674
  · exact MergedCutProfiles.Batch166.valid6675
  · exact MergedCutProfiles.Batch166.valid6676
  · exact MergedCutProfiles.Batch166.valid6677
  · exact MergedCutProfiles.Batch166.valid6678
  · exact MergedCutProfiles.Batch166.valid6679
  · exact MergedCutProfiles.Batch167.valid6680
  · exact MergedCutProfiles.Batch167.valid6681
  · exact MergedCutProfiles.Batch167.valid6682
  · exact MergedCutProfiles.Batch167.valid6683
  · exact MergedCutProfiles.Batch167.valid6684
  · exact MergedCutProfiles.Batch167.valid6685
  · exact MergedCutProfiles.Batch167.valid6686
  · exact MergedCutProfiles.Batch167.valid6687
theorem numericValid997 : retention997.NumericValid := by decide +kernel
def certificate997 : RatCutBinCertificate := ⟨⟨retention997,(549689417018221649/250000000000000000),(65444215677591123/500000000000000000),(13717782655446071423/1000000000000000000),(14970718593046750777/62500000000000000),(1978992375994952369/1000000000000000000)⟩,(991999152026111801/1000000000000000000),(368641318303571487/1000000000000000000),(131738311743380083/500000000000000000),(140848691175508049/1000000000000000000)⟩
theorem valid997 : certificate997.Valid := by decide +kernel
theorem sound997 : certificate997.Sound := rat_cut_bin_certificate_sound certificate997 profilesValid997 numericValid997 valid997

def retention998 : RatCutRetentionCertificate := ⟨(207/4000),(13/250),(827952798576747605/8718049514346597573),(948502854626936981/1000000000000000000),(13/5),(2450678367549128129273/1280000000000000000000),true,MergedCutProfiles.Batch167.profile6688,![MergedCutProfiles.Batch167.profile6688,MergedCutProfiles.Batch167.profile6689,MergedCutProfiles.Batch167.profile6690,MergedCutProfiles.Batch166.profile6678,MergedCutProfiles.Batch167.profile6691,MergedCutProfiles.Batch167.profile6692,MergedCutProfiles.Batch167.profile6693,MergedCutProfiles.Batch167.profile6685,MergedCutProfiles.Batch167.profile6694,MergedCutProfiles.Batch167.profile6695,MergedCutProfiles.Batch167.profile6696,MergedCutProfiles.Batch167.profile6697,MergedCutProfiles.Batch167.profile6698,MergedCutProfiles.Batch167.profile6699,MergedCutProfiles.Batch167.profile6700,MergedCutProfiles.Batch167.profile6701]⟩
theorem profilesValid998 : retention998.ProfilesValid := by
  change ∀ j : Fin 16, (retention998.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch167.valid6688
  · exact MergedCutProfiles.Batch167.valid6689
  · exact MergedCutProfiles.Batch167.valid6690
  · exact MergedCutProfiles.Batch166.valid6678
  · exact MergedCutProfiles.Batch167.valid6691
  · exact MergedCutProfiles.Batch167.valid6692
  · exact MergedCutProfiles.Batch167.valid6693
  · exact MergedCutProfiles.Batch167.valid6685
  · exact MergedCutProfiles.Batch167.valid6694
  · exact MergedCutProfiles.Batch167.valid6695
  · exact MergedCutProfiles.Batch167.valid6696
  · exact MergedCutProfiles.Batch167.valid6697
  · exact MergedCutProfiles.Batch167.valid6698
  · exact MergedCutProfiles.Batch167.valid6699
  · exact MergedCutProfiles.Batch167.valid6700
  · exact MergedCutProfiles.Batch167.valid6701
theorem numericValid998 : retention998.NumericValid := by decide +kernel
def certificate998 : RatCutBinCertificate := ⟨⟨retention998,(549689417018221649/250000000000000000),(65444215677591123/500000000000000000),(13717782655446071423/1000000000000000000),(14970718593046750777/62500000000000000),(1860033741212840383/1000000000000000000)⟩,(991999152026111801/1000000000000000000),(187891915850359359/500000000000000000),(64104569626658623/250000000000000000),(140844062320582217/1000000000000000000)⟩
theorem valid998 : certificate998.Valid := by decide +kernel
theorem sound998 : certificate998.Sound := rat_cut_bin_certificate_sound certificate998 profilesValid998 numericValid998 valid998

def retention999 : RatCutRetentionCertificate := ⟨(207/4000),(13/250),(4850024613720657391/17436099028693195146),(165590559715349521/100000000000000000),(17/10),(185948255985975089341/128000000000000000000),true,MergedCutProfiles.Batch167.profile6702,![MergedCutProfiles.Batch167.profile6702,MergedCutProfiles.Batch167.profile6703,MergedCutProfiles.Batch167.profile6704,MergedCutProfiles.Batch167.profile6705,MergedCutProfiles.Batch167.profile6706,MergedCutProfiles.Batch167.profile6707,MergedCutProfiles.Batch167.profile6708,MergedCutProfiles.Batch167.profile6709,MergedCutProfiles.Batch167.profile6710,MergedCutProfiles.Batch167.profile6711,MergedCutProfiles.Batch167.profile6712,MergedCutProfiles.Batch167.profile6713,MergedCutProfiles.Batch167.profile6714,MergedCutProfiles.Batch167.profile6715,MergedCutProfiles.Batch167.profile6716,MergedCutProfiles.Batch167.profile6717]⟩
theorem profilesValid999 : retention999.ProfilesValid := by
  change ∀ j : Fin 16, (retention999.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch167.valid6702
  · exact MergedCutProfiles.Batch167.valid6703
  · exact MergedCutProfiles.Batch167.valid6704
  · exact MergedCutProfiles.Batch167.valid6705
  · exact MergedCutProfiles.Batch167.valid6706
  · exact MergedCutProfiles.Batch167.valid6707
  · exact MergedCutProfiles.Batch167.valid6708
  · exact MergedCutProfiles.Batch167.valid6709
  · exact MergedCutProfiles.Batch167.valid6710
  · exact MergedCutProfiles.Batch167.valid6711
  · exact MergedCutProfiles.Batch167.valid6712
  · exact MergedCutProfiles.Batch167.valid6713
  · exact MergedCutProfiles.Batch167.valid6714
  · exact MergedCutProfiles.Batch167.valid6715
  · exact MergedCutProfiles.Batch167.valid6716
  · exact MergedCutProfiles.Batch167.valid6717
theorem numericValid999 : retention999.NumericValid := by decide +kernel
def certificate999 : RatCutBinCertificate := ⟨⟨retention999,(549689417018221649/250000000000000000),(65444215677591123/500000000000000000),(13717782655446071423/1000000000000000000),(14970718593046750777/62500000000000000),(708524355712745699/500000000000000000)⟩,(991999152026111801/1000000000000000000),(206793947821726549/500000000000000000),(11063028813294327/50000000000000000),(140975653144943387/1000000000000000000)⟩
theorem valid999 : certificate999.Valid := by decide +kernel
theorem sound999 : certificate999.Sound := rat_cut_bin_certificate_sound certificate999 profilesValid999 numericValid999 valid999

def retention1000 : RatCutRetentionCertificate := ⟨(207/4000),(13/250),(7897529521238687495/17436099028693195146),(4850024613720657391/1000000000000000000),1,(267779678894272188511/256000000000000000000),true,MergedCutProfiles.Batch167.profile6718,![MergedCutProfiles.Batch167.profile6718,MergedCutProfiles.Batch167.profile6719,MergedCutProfiles.Batch168.profile6720,MergedCutProfiles.Batch168.profile6721,MergedCutProfiles.Batch168.profile6722,MergedCutProfiles.Batch168.profile6723,MergedCutProfiles.Batch168.profile6724,MergedCutProfiles.Batch168.profile6725,MergedCutProfiles.Batch168.profile6726,MergedCutProfiles.Batch168.profile6727,MergedCutProfiles.Batch168.profile6728,MergedCutProfiles.Batch168.profile6729,MergedCutProfiles.Batch168.profile6730,MergedCutProfiles.Batch168.profile6731,MergedCutProfiles.Batch168.profile6732,MergedCutProfiles.Batch168.profile6733]⟩
theorem profilesValid1000 : retention1000.ProfilesValid := by
  change ∀ j : Fin 16, (retention1000.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch167.valid6718
  · exact MergedCutProfiles.Batch167.valid6719
  · exact MergedCutProfiles.Batch168.valid6720
  · exact MergedCutProfiles.Batch168.valid6721
  · exact MergedCutProfiles.Batch168.valid6722
  · exact MergedCutProfiles.Batch168.valid6723
  · exact MergedCutProfiles.Batch168.valid6724
  · exact MergedCutProfiles.Batch168.valid6725
  · exact MergedCutProfiles.Batch168.valid6726
  · exact MergedCutProfiles.Batch168.valid6727
  · exact MergedCutProfiles.Batch168.valid6728
  · exact MergedCutProfiles.Batch168.valid6729
  · exact MergedCutProfiles.Batch168.valid6730
  · exact MergedCutProfiles.Batch168.valid6731
  · exact MergedCutProfiles.Batch168.valid6732
  · exact MergedCutProfiles.Batch168.valid6733
theorem numericValid1000 : retention1000.NumericValid := by decide +kernel
def certificate1000 : RatCutBinCertificate := ⟨⟨retention1000,(549689417018221649/250000000000000000),(65444215677591123/500000000000000000),(13717782655446071423/1000000000000000000),(14970718593046750777/62500000000000000),(25625813183595403/25000000000000000)⟩,(991999152026111801/1000000000000000000),(474504406033235979/1000000000000000000),(85879925030806507/500000000000000000),(144062550052220267/1000000000000000000)⟩
theorem valid1000 : certificate1000.Valid := by decide +kernel
theorem sound1000 : certificate1000.Sound := rat_cut_bin_certificate_sound certificate1000 profilesValid1000 numericValid1000 valid1000

def retention1001 : RatCutRetentionCertificate := ⟨(207/4000),(13/250),(4275946399984516897/8718049514346597573),(1579505904247737499/200000000000000000),(21/20),(509625525674418679781171445649149608519/505441889359275999680000000000000000000),false,MergedCutProfiles.Batch168.profile6734,(fun _ => MergedCutProfiles.Batch168.profile6734)⟩
theorem profilesValid1001 : retention1001.ProfilesValid := by
  exact MergedCutProfiles.Batch168.valid6734
theorem numericValid1001 : retention1001.NumericValid := by decide +kernel
def certificate1001 : RatCutBinCertificate := ⟨⟨retention1001,(549689417018221649/250000000000000000),(65444215677591123/500000000000000000),(13717782655446071423/1000000000000000000),(14970718593046750777/62500000000000000),(986247280354716077/1000000000000000000)⟩,(991999152026111801/1000000000000000000),(472943417653566621/1000000000000000000),(21615763277993853/125000000000000000),(144658559644132679/1000000000000000000)⟩
theorem valid1001 : certificate1001.Valid := by decide +kernel
theorem sound1001 : certificate1001.Sound := rat_cut_bin_certificate_sound certificate1001 profilesValid1001 numericValid1001 valid1001

def retention1002 : RatCutRetentionCertificate := ⟨(207/4000),(13/250),(4318705863984362066/8718049514346597573),(4275946399984516897/500000000000000000),(21/20),(3423792347114329352244931589124565379471/3420757119987613517600000000000000000000),false,MergedCutProfiles.Batch168.profile6735,(fun _ => MergedCutProfiles.Batch168.profile6735)⟩
theorem profilesValid1002 : retention1002.ProfilesValid := by
  exact MergedCutProfiles.Batch168.valid6735
theorem numericValid1002 : retention1002.NumericValid := by decide +kernel
def certificate1002 : RatCutBinCertificate := ⟨⟨retention1002,(549689417018221649/250000000000000000),(65444215677591123/500000000000000000),(13717782655446071423/1000000000000000000),(14970718593046750777/62500000000000000),(978857502733160611/1000000000000000000)⟩,(991999152026111801/1000000000000000000),(474032813443533367/1000000000000000000),(172111647402579349/1000000000000000000),(72063510696193621/500000000000000000)⟩
theorem valid1002 : certificate1002.Valid := by decide +kernel
theorem sound1002 : certificate1002.Sound := rat_cut_bin_certificate_sound certificate1002 profilesValid1002 numericValid1002 valid1002

def retention1003 : RatCutRetentionCertificate := ⟨(207/4000),(13/250),(1/2),(2159352931992181033/250000000000000000),(21/20),(856976627577434666784114790711951761831/863741172796872413200000000000000000000),false,MergedCutProfiles.Batch168.profile6736,(fun _ => MergedCutProfiles.Batch168.profile6736)⟩
theorem profilesValid1003 : retention1003.ProfilesValid := by
  exact MergedCutProfiles.Batch168.valid6736
theorem numericValid1003 : retention1003.NumericValid := by decide +kernel
def certificate1003 : RatCutBinCertificate := ⟨⟨retention1003,(549689417018221649/250000000000000000),(65444215677591123/500000000000000000),(13717782655446071423/1000000000000000000),(14970718593046750777/62500000000000000),(485069269126882033/500000000000000000)⟩,(991999152026111801/1000000000000000000),(238996985118637459/500000000000000000),(169171248314780119/1000000000000000000),(140651065561376233/1000000000000000000)⟩
theorem valid1003 : certificate1003.Valid := by decide +kernel
theorem sound1003 : certificate1003.Sound := rat_cut_bin_certificate_sound certificate1003 profilesValid1003 numericValid1003 valid1003

def retention1004 : RatCutRetentionCertificate := ⟨(207/4000),(13/250),(1/2),64,1,(63849186294016414085152309900079421591/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch168.profile6736,(fun _ => MergedCutProfiles.Batch168.profile6736)⟩
theorem profilesValid1004 : retention1004.ProfilesValid := by
  exact MergedCutProfiles.Batch168.valid6736
theorem numericValid1004 : retention1004.NumericValid := by decide +kernel
def certificate1004 : RatCutBinCertificate := ⟨⟨retention1004,(549689417018221649/250000000000000000),(65444215677591123/500000000000000000),(13717782655446071423/1000000000000000000),(14970718593046750777/62500000000000000),(976663877067172133/1000000000000000000)⟩,(991999152026111801/1000000000000000000),(449096692907207657/1000000000000000000),(191393454297604827/1000000000000000000),(182630913463881309/1000000000000000000)⟩
theorem valid1004 : certificate1004.Valid := by decide +kernel
theorem sound1004 : certificate1004.Sound := rat_cut_bin_certificate_sound certificate1004 profilesValid1004 numericValid1004 valid1004

def retention1005 : RatCutRetentionCertificate := ⟨(207/4000),(13/250),(7935953883641767135/17436099028693195146),(3688530289704540959/1000000000000000000),(6/5),(7136413988395744441741900520777855659/6586661231615251712500000000000000000),false,MergedCutProfiles.Batch168.profile6737,(fun _ => MergedCutProfiles.Batch168.profile6737)⟩
theorem profilesValid1005 : retention1005.ProfilesValid := by
  exact MergedCutProfiles.Batch168.valid6737
theorem numericValid1005 : retention1005.NumericValid := by decide +kernel
def certificate1005 : RatCutBinCertificate := ⟨⟨retention1005,(639241692768221649/250000000000000000),(65444215677591123/500000000000000000),(13717782655446071423/1000000000000000000),(14970718593046750777/62500000000000000),(131773017151787743/125000000000000000)⟩,(990693895977825093/1000000000000000000),(95790272548581001/250000000000000000),(49854067208473413/200000000000000000),(180853798193964811/1000000000000000000)⟩
theorem valid1005 : certificate1005.Valid := by decide +kernel
theorem sound1005 : certificate1005.Sound := rat_cut_bin_certificate_sound certificate1005 profilesValid1005 numericValid1005 valid1005

def retention1006 : RatCutRetentionCertificate := ⟨(207/4000),(13/250),(8593500878456692073/17436099028693195146),(1587190776728353427/200000000000000000),(21/20),(509836138034888539682827635441767453279/507901048553073096640000000000000000000),false,MergedCutProfiles.Batch168.profile6738,(fun _ => MergedCutProfiles.Batch168.profile6738)⟩
theorem profilesValid1006 : retention1006.ProfilesValid := by
  exact MergedCutProfiles.Batch168.valid6738
theorem numericValid1006 : retention1006.NumericValid := by decide +kernel
def certificate1006 : RatCutBinCertificate := ⟨⟨retention1006,(639241692768221649/250000000000000000),(65444215677591123/500000000000000000),(13717782655446071423/1000000000000000000),(14970718593046750777/62500000000000000),(978191089393067461/1000000000000000000)⟩,(990693895977825093/1000000000000000000),(412927849844976739/1000000000000000000),(221843829646325411/1000000000000000000),(184064930831468271/1000000000000000000)⟩
theorem valid1006 : certificate1006.Valid := by decide +kernel
theorem sound1006 : certificate1006.Sound := rat_cut_bin_certificate_sound certificate1006 profilesValid1006 numericValid1006 valid1006

def retention1007 : RatCutRetentionCertificate := ⟨(207/4000),(13/250),(4339717943620629497/8718049514346597573),(8593500878456692073/1000000000000000000),(21/20),(13699229872645923181419342098900897664191/13749601405530707316800000000000000000000),false,MergedCutProfiles.Batch168.profile6739,(fun _ => MergedCutProfiles.Batch168.profile6739)⟩
theorem profilesValid1007 : retention1007.ProfilesValid := by
  exact MergedCutProfiles.Batch168.valid6739
theorem numericValid1007 : retention1007.NumericValid := by decide +kernel
def certificate1007 : RatCutBinCertificate := ⟨⟨retention1007,(639241692768221649/250000000000000000),(65444215677591123/500000000000000000),(13717782655446071423/1000000000000000000),(14970718593046750777/62500000000000000),(60669859633092881/62500000000000000)⟩,(990693895977825093/1000000000000000000),(416106887467842401/1000000000000000000),(109522158842022999/500000000000000000),(90944297390522183/500000000000000000)⟩
theorem valid1007 : certificate1007.Valid := by decide +kernel
theorem sound1007 : certificate1007.Sound := rat_cut_bin_certificate_sound certificate1007 profilesValid1007 numericValid1007 valid1007

def certificates : List RatCutBinCertificate := [certificate996,certificate997,certificate998,certificate999,certificate1000,certificate1001,certificate1002,certificate1003,certificate1004,certificate1005,certificate1006,certificate1007]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound996,List.forall_mem_cons.mpr ⟨sound997,List.forall_mem_cons.mpr ⟨sound998,List.forall_mem_cons.mpr ⟨sound999,List.forall_mem_cons.mpr ⟨sound1000,List.forall_mem_cons.mpr ⟨sound1001,List.forall_mem_cons.mpr ⟨sound1002,List.forall_mem_cons.mpr ⟨sound1003,List.forall_mem_cons.mpr ⟨sound1004,List.forall_mem_cons.mpr ⟨sound1005,List.forall_mem_cons.mpr ⟨sound1006,List.forall_mem_cons.mpr ⟨sound1007,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch083
