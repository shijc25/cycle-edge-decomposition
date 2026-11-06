import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch369
import Cycle12.MergedCutProfiles.Batch370
import Cycle12.MergedCutProfiles.Batch484
import Cycle12.MergedCutProfiles.Batch485
import Cycle12.MergedCutProfiles.Batch608
import Cycle12.MergedCutProfiles.Batch609
import Cycle12.MergedCutProfiles.Batch693
import Cycle12.MergedCutProfiles.Batch694

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch412

def retention4944 : RatCutRetentionCertificate := ⟨(93/2000),(47/1000),(1/40),(51592463866795013737/1000000000000000000),(21/20),(138187265855539293/62500000000000000),false,MergedCutProfiles.Batch693.profile27731,(fun _ => MergedCutProfiles.Batch693.profile27731)⟩
theorem profilesValid4944 : retention4944.ProfilesValid := by
  exact MergedCutProfiles.Batch693.valid27731
theorem numericValid4944 : retention4944.NumericValid := by decide +kernel
def certificate4944 : RatCutBinCertificate := ⟨⟨retention4944,(374833516855403279/200000000000000000),(6511012982960937/62500000000000000),(12577396975114151283/1000000000000000000),(27699124992646009937571/1000000000000000000),(548674176746622201/250000000000000000)⟩,(62496201264749449/62500000000000000),(695631277400412811/1000000000000000000),(51899414241719787/1000000000000000000),(104442978273655821/1000000000000000000)⟩
theorem valid4944 : certificate4944.Valid := by decide +kernel
theorem sound4944 : certificate4944.Sound := rat_cut_bin_certificate_sound certificate4944 profilesValid4944 numericValid4944 valid4944

def retention4945 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(619527482969413776/2093740221358285443809),(595353734000519347/1000000000000000000),4,(581101875505319801619/256000000000000000000),true,MergedCutProfiles.Batch693.profile27732,![MergedCutProfiles.Batch693.profile27732,MergedCutProfiles.Batch693.profile27733,MergedCutProfiles.Batch693.profile27734,MergedCutProfiles.Batch693.profile27735,MergedCutProfiles.Batch608.profile24335,MergedCutProfiles.Batch693.profile27736,MergedCutProfiles.Batch693.profile27737,MergedCutProfiles.Batch693.profile27738,MergedCutProfiles.Batch608.profile24344,MergedCutProfiles.Batch693.profile27739,MergedCutProfiles.Batch693.profile27740,MergedCutProfiles.Batch693.profile27741,MergedCutProfiles.Batch693.profile27742,MergedCutProfiles.Batch693.profile27743,MergedCutProfiles.Batch608.profile24337,MergedCutProfiles.Batch693.profile27744]⟩
theorem profilesValid4945 : retention4945.ProfilesValid := by
  change ∀ j : Fin 16, (retention4945.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch693.valid27732
  · exact MergedCutProfiles.Batch693.valid27733
  · exact MergedCutProfiles.Batch693.valid27734
  · exact MergedCutProfiles.Batch693.valid27735
  · exact MergedCutProfiles.Batch608.valid24335
  · exact MergedCutProfiles.Batch693.valid27736
  · exact MergedCutProfiles.Batch693.valid27737
  · exact MergedCutProfiles.Batch693.valid27738
  · exact MergedCutProfiles.Batch608.valid24344
  · exact MergedCutProfiles.Batch693.valid27739
  · exact MergedCutProfiles.Batch693.valid27740
  · exact MergedCutProfiles.Batch693.valid27741
  · exact MergedCutProfiles.Batch693.valid27742
  · exact MergedCutProfiles.Batch693.valid27743
  · exact MergedCutProfiles.Batch608.valid24337
  · exact MergedCutProfiles.Batch693.valid27744
theorem numericValid4945 : retention4945.NumericValid := by decide +kernel
def certificate4945 : RatCutBinCertificate := ⟨⟨retention4945,(955481241585472921/500000000000000000),(13651068898300767/125000000000000000),(12679908924361190897/1000000000000000000),(26698485819870823135647/1000000000000000000),(2204094721192491001/1000000000000000000)⟩,(199987176063553577/200000000000000000),(350636439024542103/500000000000000000),(49874692128179979/1000000000000000000),(1394770170004281/62500000000000000)⟩
theorem valid4945 : certificate4945.Valid := by decide +kernel
theorem sound4945 : certificate4945.Sound := rat_cut_bin_certificate_sound certificate4945 profilesValid4945 numericValid4945 valid4945

def retention4946 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(1129163430000000000/2093740221358285443809),(38720467685588361/62500000000000000),4,(1431221734423418062679764673442754679/619527482969413776000000000000000000),true,MergedCutProfiles.Batch693.profile27745,![MergedCutProfiles.Batch693.profile27745,MergedCutProfiles.Batch693.profile27746,MergedCutProfiles.Batch693.profile27747,MergedCutProfiles.Batch693.profile27737,MergedCutProfiles.Batch608.profile24344,MergedCutProfiles.Batch693.profile27740,MergedCutProfiles.Batch693.profile27742,MergedCutProfiles.Batch693.profile27748,MergedCutProfiles.Batch693.profile27744,MergedCutProfiles.Batch608.profile24345,MergedCutProfiles.Batch608.profile24338,MergedCutProfiles.Batch609.profile24363,MergedCutProfiles.Batch693.profile27749,MergedCutProfiles.Batch484.profile19376,MergedCutProfiles.Batch608.profile24353,MergedCutProfiles.Batch693.profile27750]⟩
theorem profilesValid4946 : retention4946.ProfilesValid := by
  change ∀ j : Fin 16, (retention4946.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch693.valid27745
  · exact MergedCutProfiles.Batch693.valid27746
  · exact MergedCutProfiles.Batch693.valid27747
  · exact MergedCutProfiles.Batch693.valid27737
  · exact MergedCutProfiles.Batch608.valid24344
  · exact MergedCutProfiles.Batch693.valid27740
  · exact MergedCutProfiles.Batch693.valid27742
  · exact MergedCutProfiles.Batch693.valid27748
  · exact MergedCutProfiles.Batch693.valid27744
  · exact MergedCutProfiles.Batch608.valid24345
  · exact MergedCutProfiles.Batch608.valid24338
  · exact MergedCutProfiles.Batch609.valid24363
  · exact MergedCutProfiles.Batch693.valid27749
  · exact MergedCutProfiles.Batch484.valid19376
  · exact MergedCutProfiles.Batch608.valid24353
  · exact MergedCutProfiles.Batch693.valid27750
theorem numericValid4946 : retention4946.NumericValid := by decide +kernel
def certificate4946 : RatCutBinCertificate := ⟨⟨retention4946,(955481241585472921/500000000000000000),(13651068898300767/125000000000000000),(12679908924361190897/1000000000000000000),(26698485819870823135647/1000000000000000000),(1122174161512170549/500000000000000000)⟩,(199987176063553577/200000000000000000),(335437193199235723/500000000000000000),(61330428523173187/1000000000000000000),(28056545571585531/1000000000000000000)⟩
theorem valid4946 : certificate4946.Valid := by decide +kernel
theorem sound4946 : certificate4946.Sound := rat_cut_bin_certificate_sound certificate4946 profilesValid4946 numericValid4946 valid4946

def retention4947 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(4669812623568262086/2093740221358285443809),(112916343/100000000),(14/5),(9504937444354053877/4000000000000000000),true,MergedCutProfiles.Batch693.profile27738,![MergedCutProfiles.Batch693.profile27738,MergedCutProfiles.Batch608.profile24337,MergedCutProfiles.Batch609.profile24363,MergedCutProfiles.Batch608.profile24339,MergedCutProfiles.Batch485.profile19400,MergedCutProfiles.Batch608.profile24341,MergedCutProfiles.Batch693.profile27751,MergedCutProfiles.Batch608.profile24343,MergedCutProfiles.Batch609.profile24364,MergedCutProfiles.Batch484.profile19378,MergedCutProfiles.Batch693.profile27752,MergedCutProfiles.Batch609.profile24365,MergedCutProfiles.Batch693.profile27753,MergedCutProfiles.Batch484.profile19390,MergedCutProfiles.Batch609.profile24366,MergedCutProfiles.Batch693.profile27754]⟩
theorem profilesValid4947 : retention4947.ProfilesValid := by
  change ∀ j : Fin 16, (retention4947.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch693.valid27738
  · exact MergedCutProfiles.Batch608.valid24337
  · exact MergedCutProfiles.Batch609.valid24363
  · exact MergedCutProfiles.Batch608.valid24339
  · exact MergedCutProfiles.Batch485.valid19400
  · exact MergedCutProfiles.Batch608.valid24341
  · exact MergedCutProfiles.Batch693.valid27751
  · exact MergedCutProfiles.Batch608.valid24343
  · exact MergedCutProfiles.Batch609.valid24364
  · exact MergedCutProfiles.Batch484.valid19378
  · exact MergedCutProfiles.Batch693.valid27752
  · exact MergedCutProfiles.Batch609.valid24365
  · exact MergedCutProfiles.Batch693.valid27753
  · exact MergedCutProfiles.Batch484.valid19390
  · exact MergedCutProfiles.Batch609.valid24366
  · exact MergedCutProfiles.Batch693.valid27754
theorem numericValid4947 : retention4947.NumericValid := by decide +kernel
def certificate4947 : RatCutBinCertificate := ⟨⟨retention4947,(955481241585472921/500000000000000000),(13651068898300767/125000000000000000),(12679908924361190897/1000000000000000000),(26698485819870823135647/1000000000000000000),(2330150244622817627/1000000000000000000)⟩,(199987176063553577/200000000000000000),(227687962924605069/500000000000000000),(7456422774318829/40000000000000000),(3837396897541159/31250000000000000)⟩
theorem valid4947 : certificate4947.Valid := by decide +kernel
theorem sound4947 : certificate4947.Sound := rat_cut_bin_certificate_sound certificate4947 profilesValid4947 numericValid4947 valid4947

def retention4948 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(64000000000000000000/2093740221358285443809),(2334906311784131043/500000000000000000),(5/4),(31910913938362795314833614504317944179/14943400395418438675200000000000000000),true,MergedCutProfiles.Batch693.profile27755,![MergedCutProfiles.Batch693.profile27755,MergedCutProfiles.Batch693.profile27756,MergedCutProfiles.Batch609.profile24371,MergedCutProfiles.Batch693.profile27757,MergedCutProfiles.Batch693.profile27758,MergedCutProfiles.Batch369.profile14772,MergedCutProfiles.Batch693.profile27759,MergedCutProfiles.Batch694.profile27760,MergedCutProfiles.Batch369.profile14776,MergedCutProfiles.Batch694.profile27761,MergedCutProfiles.Batch694.profile27762,MergedCutProfiles.Batch694.profile27763,MergedCutProfiles.Batch694.profile27764,MergedCutProfiles.Batch694.profile27765,MergedCutProfiles.Batch694.profile27766,MergedCutProfiles.Batch694.profile27767]⟩
theorem profilesValid4948 : retention4948.ProfilesValid := by
  change ∀ j : Fin 16, (retention4948.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch693.valid27755
  · exact MergedCutProfiles.Batch693.valid27756
  · exact MergedCutProfiles.Batch609.valid24371
  · exact MergedCutProfiles.Batch693.valid27757
  · exact MergedCutProfiles.Batch693.valid27758
  · exact MergedCutProfiles.Batch369.valid14772
  · exact MergedCutProfiles.Batch693.valid27759
  · exact MergedCutProfiles.Batch694.valid27760
  · exact MergedCutProfiles.Batch369.valid14776
  · exact MergedCutProfiles.Batch694.valid27761
  · exact MergedCutProfiles.Batch694.valid27762
  · exact MergedCutProfiles.Batch694.valid27763
  · exact MergedCutProfiles.Batch694.valid27764
  · exact MergedCutProfiles.Batch694.valid27765
  · exact MergedCutProfiles.Batch694.valid27766
  · exact MergedCutProfiles.Batch694.valid27767
theorem numericValid4948 : retention4948.NumericValid := by decide +kernel
def certificate4948 : RatCutBinCertificate := ⟨⟨retention4948,(955481241585472921/500000000000000000),(13651068898300767/125000000000000000),(12679908924361190897/1000000000000000000),(26698485819870823135647/1000000000000000000),(2114878724317178267/1000000000000000000)⟩,(199987176063553577/200000000000000000),(307974575755715189/1000000000000000000),(1646467392656067/5000000000000000),(431907531357684779/1000000000000000000)⟩
theorem valid4948 : certificate4948.Valid := by decide +kernel
theorem sound4948 : certificate4948.Sound := rat_cut_bin_certificate_sound certificate4948 profilesValid4948 numericValid4948 valid4948

def retention4949 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(1/2),64,1,(15961943206562927268838532628520865151/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch370.profile14826,(fun _ => MergedCutProfiles.Batch370.profile14826)⟩
theorem profilesValid4949 : retention4949.ProfilesValid := by
  exact MergedCutProfiles.Batch370.valid14826
theorem numericValid4949 : retention4949.NumericValid := by decide +kernel
def certificate4949 : RatCutBinCertificate := ⟨⟨retention4949,(955481241585472921/500000000000000000),(13651068898300767/125000000000000000),(12679908924361190897/1000000000000000000),(26698485819870823135647/1000000000000000000),(981162857628339317/1000000000000000000)⟩,(199987176063553577/200000000000000000),(540362912951559733/1000000000000000000),(31758993332511247/250000000000000000),(24550604168949089/200000000000000000)⟩
theorem valid4949 : certificate4949.Valid := by decide +kernel
theorem sound4949 : certificate4949.Sound := rat_cut_bin_certificate_sound certificate4949 profilesValid4949 numericValid4949 valid4949

def retention4950 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(64000000000000000000/2093740221358285443809),(1754149598222836653/50000000000000000),1,(301437607199885381689790962538415445439/140331967857826932240000000000000000000),false,MergedCutProfiles.Batch694.profile27768,(fun _ => MergedCutProfiles.Batch694.profile27768)⟩
theorem profilesValid4950 : retention4950.ProfilesValid := by
  exact MergedCutProfiles.Batch694.valid27768
theorem numericValid4950 : retention4950.NumericValid := by decide +kernel
def certificate4950 : RatCutBinCertificate := ⟨⟨retention4950,(872155535585472921/500000000000000000),(13651068898300767/125000000000000000),(12679908924361190897/1000000000000000000),(26698485819870823135647/1000000000000000000),(2133009082650177009/1000000000000000000)⟩,(49997073605582183/50000000000000000),(297090831855809/15625000000000000),(175400749619323847/200000000000000000),(35266727703870923/20000000000000000)⟩
theorem valid4950 : certificate4950.Valid := by decide +kernel
theorem sound4950 : certificate4950.Sound := rat_cut_bin_certificate_sound certificate4950 profilesValid4950 numericValid4950 valid4950

def retention4951 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(1/2),64,1,(15961943206562927268838532628520865151/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch370.profile14826,(fun _ => MergedCutProfiles.Batch370.profile14826)⟩
theorem profilesValid4951 : retention4951.ProfilesValid := by
  exact MergedCutProfiles.Batch370.valid14826
theorem numericValid4951 : retention4951.NumericValid := by decide +kernel
def certificate4951 : RatCutBinCertificate := ⟨⟨retention4951,(872155535585472921/500000000000000000),(13651068898300767/125000000000000000),(12679908924361190897/1000000000000000000),(26698485819870823135647/1000000000000000000),(982598180273750921/1000000000000000000)⟩,(49997073605582183/50000000000000000),(41274894609325793/1000000000000000000),(203047343987852339/250000000000000000),(785941941578713191/1000000000000000000)⟩
theorem valid4951 : certificate4951.Valid := by decide +kernel
theorem sound4951 : certificate4951.Sound := rat_cut_bin_certificate_sound certificate4951 profilesValid4951 numericValid4951 valid4951

def retention4952 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(710305742666254220/2093740221358285443809),(351636506270422881/500000000000000000),4,(451919908961148325319190300914523873/187539470010892203200000000000000000),false,MergedCutProfiles.Batch694.profile27769,(fun _ => MergedCutProfiles.Batch694.profile27769)⟩
theorem profilesValid4952 : retention4952.ProfilesValid := by
  exact MergedCutProfiles.Batch694.valid27769
theorem numericValid4952 : retention4952.NumericValid := by decide +kernel
def certificate4952 : RatCutBinCertificate := ⟨⟨retention4952,(938396155085472921/500000000000000000),(13651068898300767/125000000000000000),(12679908924361190897/1000000000000000000),(26698485819870823135647/1000000000000000000),(2345074981705531987/1000000000000000000)⟩,(999937026858685813/1000000000000000000),(426094739876508989/500000000000000000),(1150589549822267/100000000000000000),(2790880208368837/500000000000000000)⟩
theorem valid4952 : certificate4952.Valid := by decide +kernel
theorem sound4952 : certificate4952.Sound := rat_cut_bin_certificate_sound certificate4952 profilesValid4952 numericValid4952 valid4952

def retention4953 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(875375072444399060/2093740221358285443809),(35515287133312711/50000000000000000),4,(1713566011490304108462675837242767071/710305742666254220000000000000000000),false,MergedCutProfiles.Batch694.profile27770,(fun _ => MergedCutProfiles.Batch694.profile27770)⟩
theorem profilesValid4953 : retention4953.ProfilesValid := by
  exact MergedCutProfiles.Batch694.valid27770
theorem numericValid4953 : retention4953.NumericValid := by decide +kernel
def certificate4953 : RatCutBinCertificate := ⟨⟨retention4953,(938396155085472921/500000000000000000),(13651068898300767/125000000000000000),(12679908924361190897/1000000000000000000),(26698485819870823135647/1000000000000000000),(4585502222182211/1953125000000000)⟩,(999937026858685813/1000000000000000000),(424590485786955033/500000000000000000),(11992412269411007/1000000000000000000),(5833297546399743/1000000000000000000)⟩
theorem valid4953 : certificate4953.Valid := by decide +kernel
theorem sound4953 : certificate4953.Sound := rat_cut_bin_certificate_sound certificate4953 profilesValid4953 numericValid4953 valid4953

def retention4954 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(4052152093674024987/2093740221358285443809),(43768753622219953/50000000000000000),(73/20),(8425086019035804884977497174863606479/3501500289777596240000000000000000000),false,MergedCutProfiles.Batch694.profile27771,(fun _ => MergedCutProfiles.Batch694.profile27771)⟩
theorem profilesValid4954 : retention4954.ProfilesValid := by
  exact MergedCutProfiles.Batch694.valid27771
theorem numericValid4954 : retention4954.NumericValid := by decide +kernel
def certificate4954 : RatCutBinCertificate := ⟨⟨retention4954,(938396155085472921/500000000000000000),(13651068898300767/125000000000000000),(12679908924361190897/1000000000000000000),(26698485819870823135647/1000000000000000000),(1173568143464737899/500000000000000000)⟩,(999937026858685813/1000000000000000000),(405583161927332387/500000000000000000),(2383879370553939/125000000000000000),(10208230834279513/1000000000000000000)⟩
theorem valid4954 : certificate4954.Valid := by decide +kernel
theorem sound4954 : certificate4954.Sound := rat_cut_bin_certificate_sound certificate4954 profilesValid4954 numericValid4954 valid4954

def retention4955 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(49243686439797646040/2093740221358285443809),(4052152093674024987/1000000000000000000),(3/2),(47930239165930500317406115001820320277/21611477832928133264000000000000000000),false,MergedCutProfiles.Batch694.profile27772,(fun _ => MergedCutProfiles.Batch694.profile27772)⟩
theorem profilesValid4955 : retention4955.ProfilesValid := by
  exact MergedCutProfiles.Batch694.valid27772
theorem numericValid4955 : retention4955.NumericValid := by decide +kernel
def certificate4955 : RatCutBinCertificate := ⟨⟨retention4955,(938396155085472921/500000000000000000),(13651068898300767/125000000000000000),(12679908924361190897/1000000000000000000),(26698485819870823135647/1000000000000000000),(2193567592861778051/1000000000000000000)⟩,(999937026858685813/1000000000000000000),(72989780990004857/100000000000000000),(40293323741388261/1000000000000000000),(23746731069493567/500000000000000000)⟩
theorem valid4955 : certificate4955.Valid := by decide +kernel
theorem sound4955 : certificate4955.Sound := rat_cut_bin_certificate_sound certificate4955 profilesValid4955 numericValid4955 valid4955

def certificates : List RatCutBinCertificate := [certificate4944,certificate4945,certificate4946,certificate4947,certificate4948,certificate4949,certificate4950,certificate4951,certificate4952,certificate4953,certificate4954,certificate4955]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4944,List.forall_mem_cons.mpr ⟨sound4945,List.forall_mem_cons.mpr ⟨sound4946,List.forall_mem_cons.mpr ⟨sound4947,List.forall_mem_cons.mpr ⟨sound4948,List.forall_mem_cons.mpr ⟨sound4949,List.forall_mem_cons.mpr ⟨sound4950,List.forall_mem_cons.mpr ⟨sound4951,List.forall_mem_cons.mpr ⟨sound4952,List.forall_mem_cons.mpr ⟨sound4953,List.forall_mem_cons.mpr ⟨sound4954,List.forall_mem_cons.mpr ⟨sound4955,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch412
