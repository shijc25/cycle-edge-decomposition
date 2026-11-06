import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch217
import Cycle12.MergedCutProfiles.Batch218
import Cycle12.MergedCutProfiles.Batch219

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch111

def retention1332 : RatCutRetentionCertificate := ⟨(471/8000),(59/1000),(1234735524102591948/12992807310559625963),(440166756006258867/500000000000000000),(53/20),(306242220077351593537/160000000000000000000),true,MergedCutProfiles.Batch217.profile8690,![MergedCutProfiles.Batch217.profile8690,MergedCutProfiles.Batch217.profile8691,MergedCutProfiles.Batch217.profile8692,MergedCutProfiles.Batch217.profile8693,MergedCutProfiles.Batch217.profile8694,MergedCutProfiles.Batch217.profile8695,MergedCutProfiles.Batch217.profile8696,MergedCutProfiles.Batch217.profile8697,MergedCutProfiles.Batch217.profile8698,MergedCutProfiles.Batch217.profile8699,MergedCutProfiles.Batch217.profile8700,MergedCutProfiles.Batch217.profile8701,MergedCutProfiles.Batch217.profile8702,MergedCutProfiles.Batch217.profile8703,MergedCutProfiles.Batch217.profile8704,MergedCutProfiles.Batch217.profile8705]⟩
theorem profilesValid1332 : retention1332.ProfilesValid := by
  change ∀ j : Fin 16, (retention1332.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch217.valid8690
  · exact MergedCutProfiles.Batch217.valid8691
  · exact MergedCutProfiles.Batch217.valid8692
  · exact MergedCutProfiles.Batch217.valid8693
  · exact MergedCutProfiles.Batch217.valid8694
  · exact MergedCutProfiles.Batch217.valid8695
  · exact MergedCutProfiles.Batch217.valid8696
  · exact MergedCutProfiles.Batch217.valid8697
  · exact MergedCutProfiles.Batch217.valid8698
  · exact MergedCutProfiles.Batch217.valid8699
  · exact MergedCutProfiles.Batch217.valid8700
  · exact MergedCutProfiles.Batch217.valid8701
  · exact MergedCutProfiles.Batch217.valid8702
  · exact MergedCutProfiles.Batch217.valid8703
  · exact MergedCutProfiles.Batch217.valid8704
  · exact MergedCutProfiles.Batch217.valid8705
theorem numericValid1332 : retention1332.NumericValid := by decide +kernel
def certificate1332 : RatCutBinCertificate := ⟨⟨retention1332,(2298574914776579933/1000000000000000000),(175338961017292427/1000000000000000000),(38850850805633293/2500000000000000),(40413199776386847259/200000000000000000),(57664440473246001/31250000000000000)⟩,(247647457227841287/250000000000000000),(354771579811131879/1000000000000000000),(5551605007865323/20000000000000000),(147169772281489853/1000000000000000000)⟩
theorem valid1332 : certificate1332.Valid := by decide +kernel
theorem sound1332 : certificate1332.Sound := rat_cut_bin_certificate_sound certificate1332 profilesValid1332 numericValid1332 valid1332

def retention1333 : RatCutRetentionCertificate := ⟨(471/8000),(59/1000),(2819992590417869906/12992807310559625963),(308683881025647987/250000000000000000),2,(101840067655243590939/64000000000000000000),true,MergedCutProfiles.Batch217.profile8706,![MergedCutProfiles.Batch217.profile8706,MergedCutProfiles.Batch217.profile8707,MergedCutProfiles.Batch217.profile8708,MergedCutProfiles.Batch217.profile8709,MergedCutProfiles.Batch217.profile8710,MergedCutProfiles.Batch217.profile8711,MergedCutProfiles.Batch217.profile8705,MergedCutProfiles.Batch217.profile8712,MergedCutProfiles.Batch217.profile8713,MergedCutProfiles.Batch217.profile8714,MergedCutProfiles.Batch217.profile8715,MergedCutProfiles.Batch217.profile8716,MergedCutProfiles.Batch217.profile8717,MergedCutProfiles.Batch217.profile8718,MergedCutProfiles.Batch217.profile8719,MergedCutProfiles.Batch218.profile8720]⟩
theorem profilesValid1333 : retention1333.ProfilesValid := by
  change ∀ j : Fin 16, (retention1333.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch217.valid8706
  · exact MergedCutProfiles.Batch217.valid8707
  · exact MergedCutProfiles.Batch217.valid8708
  · exact MergedCutProfiles.Batch217.valid8709
  · exact MergedCutProfiles.Batch217.valid8710
  · exact MergedCutProfiles.Batch217.valid8711
  · exact MergedCutProfiles.Batch217.valid8705
  · exact MergedCutProfiles.Batch217.valid8712
  · exact MergedCutProfiles.Batch217.valid8713
  · exact MergedCutProfiles.Batch217.valid8714
  · exact MergedCutProfiles.Batch217.valid8715
  · exact MergedCutProfiles.Batch217.valid8716
  · exact MergedCutProfiles.Batch217.valid8717
  · exact MergedCutProfiles.Batch217.valid8718
  · exact MergedCutProfiles.Batch217.valid8719
  · exact MergedCutProfiles.Batch218.valid8720
theorem numericValid1333 : retention1333.NumericValid := by decide +kernel
def certificate1333 : RatCutBinCertificate := ⟨⟨retention1333,(2298574914776579933/1000000000000000000),(175338961017292427/1000000000000000000),(38850850805633293/2500000000000000),(40413199776386847259/200000000000000000),(153936398810714089/100000000000000000)⟩,(247647457227841287/250000000000000000),(94594634432900901/250000000000000000),(253887872912444011/1000000000000000000),(147310653422046657/1000000000000000000)⟩
theorem valid1333 : certificate1333.Valid := by decide +kernel
theorem sound1333 : certificate1333.Sound := rat_cut_bin_certificate_sound certificate1333 profilesValid1333 numericValid1333 valid1333

def retention1334 : RatCutRetentionCertificate := ⟨(471/8000),(59/1000),(5384399349043853957/12992807310559625963),(1409996295208934953/500000000000000000),(6/5),(734420835022929196413/640000000000000000000),true,MergedCutProfiles.Batch218.profile8721,![MergedCutProfiles.Batch218.profile8721,MergedCutProfiles.Batch218.profile8722,MergedCutProfiles.Batch218.profile8723,MergedCutProfiles.Batch218.profile8724,MergedCutProfiles.Batch218.profile8725,MergedCutProfiles.Batch218.profile8726,MergedCutProfiles.Batch218.profile8727,MergedCutProfiles.Batch218.profile8728,MergedCutProfiles.Batch218.profile8729,MergedCutProfiles.Batch218.profile8730,MergedCutProfiles.Batch218.profile8731,MergedCutProfiles.Batch218.profile8732,MergedCutProfiles.Batch218.profile8733,MergedCutProfiles.Batch218.profile8734,MergedCutProfiles.Batch218.profile8735,MergedCutProfiles.Batch218.profile8736]⟩
theorem profilesValid1334 : retention1334.ProfilesValid := by
  change ∀ j : Fin 16, (retention1334.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch218.valid8721
  · exact MergedCutProfiles.Batch218.valid8722
  · exact MergedCutProfiles.Batch218.valid8723
  · exact MergedCutProfiles.Batch218.valid8724
  · exact MergedCutProfiles.Batch218.valid8725
  · exact MergedCutProfiles.Batch218.valid8726
  · exact MergedCutProfiles.Batch218.valid8727
  · exact MergedCutProfiles.Batch218.valid8728
  · exact MergedCutProfiles.Batch218.valid8729
  · exact MergedCutProfiles.Batch218.valid8730
  · exact MergedCutProfiles.Batch218.valid8731
  · exact MergedCutProfiles.Batch218.valid8732
  · exact MergedCutProfiles.Batch218.valid8733
  · exact MergedCutProfiles.Batch218.valid8734
  · exact MergedCutProfiles.Batch218.valid8735
  · exact MergedCutProfiles.Batch218.valid8736
theorem numericValid1334 : retention1334.NumericValid := by decide +kernel
def certificate1334 : RatCutBinCertificate := ⟨⟨retention1334,(2298574914776579933/1000000000000000000),(175338961017292427/1000000000000000000),(38850850805633293/2500000000000000),(40413199776386847259/200000000000000000),(558201634314986907/500000000000000000)⟩,(247647457227841287/250000000000000000),(107861077968583729/250000000000000000),(205875829603218141/1000000000000000000),(74307965560622061/500000000000000000)⟩
theorem valid1334 : certificate1334.Valid := by decide +kernel
theorem sound1334 : certificate1334.Sound := rat_cut_bin_certificate_sound certificate1334 profilesValid1334 numericValid1334 valid1334

def retention1335 : RatCutRetentionCertificate := ⟨(471/8000),(59/1000),(6313631692429886689/12992807310559625963),(5384399349043853957/1000000000000000000),(11/10),(2193872919406438510437685871714044149271/2153759739617541582800000000000000000000),false,MergedCutProfiles.Batch218.profile8737,(fun _ => MergedCutProfiles.Batch218.profile8737)⟩
theorem profilesValid1335 : retention1335.ProfilesValid := by
  exact MergedCutProfiles.Batch218.valid8737
theorem numericValid1335 : retention1335.NumericValid := by decide +kernel
def certificate1335 : RatCutBinCertificate := ⟨⟨retention1335,(2298574914776579933/1000000000000000000),(175338961017292427/1000000000000000000),(38850850805633293/2500000000000000),(40413199776386847259/200000000000000000),(495046340167065521/500000000000000000)⟩,(247647457227841287/250000000000000000),(448720276785676939/1000000000000000000),(191694936068143631/1000000000000000000),(2316296052206053/15625000000000000)⟩
theorem valid1335 : certificate1335.Valid := by decide +kernel
theorem sound1335 : certificate1335.Sound := rat_cut_bin_certificate_sound certificate1335 profilesValid1335 numericValid1335 valid1335

def retention1336 : RatCutRetentionCertificate := ⟨(471/8000),(59/1000),(6440535689447727412/12992807310559625963),(6313631692429886689/1000000000000000000),(21/20),(10012090974881722679166847761122595581279/10101810707887818702400000000000000000000),false,MergedCutProfiles.Batch218.profile8738,(fun _ => MergedCutProfiles.Batch218.profile8738)⟩
theorem profilesValid1336 : retention1336.ProfilesValid := by
  exact MergedCutProfiles.Batch218.valid8738
theorem numericValid1336 : retention1336.NumericValid := by decide +kernel
def certificate1336 : RatCutBinCertificate := ⟨⟨retention1336,(2298574914776579933/1000000000000000000),(175338961017292427/1000000000000000000),(38850850805633293/2500000000000000),(40413199776386847259/200000000000000000),(963883743360432749/1000000000000000000)⟩,(247647457227841287/250000000000000000),(56830374250764227/125000000000000000),(18698770142332477/100000000000000000),(74619450244883441/500000000000000000)⟩
theorem valid1336 : certificate1336.Valid := by decide +kernel
theorem sound1336 : certificate1336.Sound := rat_cut_bin_certificate_sound certificate1336 profilesValid1336 numericValid1336 valid1336

def retention1337 : RatCutRetentionCertificate := ⟨(471/8000),(59/1000),(1/2),(1610133922361931853/250000000000000000),(21/20),(633538881385194962062845468316380293591/644053568944772741200000000000000000000),false,MergedCutProfiles.Batch218.profile8739,(fun _ => MergedCutProfiles.Batch218.profile8739)⟩
theorem profilesValid1337 : retention1337.ProfilesValid := by
  exact MergedCutProfiles.Batch218.valid8739
theorem numericValid1337 : retention1337.NumericValid := by decide +kernel
def certificate1337 : RatCutBinCertificate := ⟨⟨retention1337,(2298574914776579933/1000000000000000000),(175338961017292427/1000000000000000000),(38850850805633293/2500000000000000),(40413199776386847259/200000000000000000),(956439566617943239/1000000000000000000)⟩,(247647457227841287/250000000000000000),(457459168687162273/1000000000000000000),(46194149345182057/250000000000000000),(146824164367950761/1000000000000000000)⟩
theorem valid1337 : certificate1337.Valid := by decide +kernel
theorem sound1337 : certificate1337.Sound := rat_cut_bin_certificate_sound certificate1337 profilesValid1337 numericValid1337 valid1337

def retention1338 : RatCutRetentionCertificate := ⟨(471/8000),(59/1000),(1/2),64,1,(623551100885077469602219086113799/625000000000000000000000000000000),false,MergedCutProfiles.Batch218.profile8739,(fun _ => MergedCutProfiles.Batch218.profile8739)⟩
theorem profilesValid1338 : retention1338.ProfilesValid := by
  exact MergedCutProfiles.Batch218.valid8739
theorem numericValid1338 : retention1338.NumericValid := by decide +kernel
def certificate1338 : RatCutBinCertificate := ⟨⟨retention1338,(2298574914776579933/1000000000000000000),(175338961017292427/1000000000000000000),(38850850805633293/2500000000000000),(40413199776386847259/200000000000000000),(242936747052958971/250000000000000000)⟩,(247647457227841287/250000000000000000),(104609566256192373/250000000000000000),(54251677898882077/250000000000000000),(102874200910529963/500000000000000000)⟩
theorem valid1338 : certificate1338.Valid := by decide +kernel
theorem sound1338 : certificate1338.Sound := rat_cut_bin_certificate_sound certificate1338 profilesValid1338 numericValid1338 valid1338

def retention1339 : RatCutRetentionCertificate := ⟨(471/8000),(59/1000),(6006815690963456358/12992807310559625963),(3580410893889384427/1000000000000000000),(6/5),(382526611477496260996417739311214305751/358041089388938442700000000000000000000),false,MergedCutProfiles.Batch218.profile8740,(fun _ => MergedCutProfiles.Batch218.profile8740)⟩
theorem profilesValid1339 : retention1339.ProfilesValid := by
  exact MergedCutProfiles.Batch218.valid8740
theorem numericValid1339 : retention1339.NumericValid := by decide +kernel
def certificate1339 : RatCutBinCertificate := ⟨⟨retention1339,(2632866551776579933/1000000000000000000),(175338961017292427/1000000000000000000),(38850850805633293/2500000000000000),(40413199776386847259/200000000000000000),(3227290166300237/3125000000000000)⟩,(39568726010753557/40000000000000000),(768657041932317/2000000000000000),(248152272266043/1000000000000000),(175805002777325339/1000000000000000000)⟩
theorem valid1339 : certificate1339.Valid := by decide +kernel
theorem sound1339 : certificate1339.Sound := rat_cut_bin_certificate_sound certificate1339 profilesValid1339 numericValid1339 valid1339

def retention1340 : RatCutRetentionCertificate := ⟨(471/8000),(59/1000),(6440119455873017852/12992807310559625963),(3003407845481728179/500000000000000000),(21/20),(24010433699067732983266597307420263501/24269962387731136800000000000000000000),false,MergedCutProfiles.Batch218.profile8741,(fun _ => MergedCutProfiles.Batch218.profile8741)⟩
theorem profilesValid1340 : retention1340.ProfilesValid := by
  exact MergedCutProfiles.Batch218.valid8741
theorem numericValid1340 : retention1340.NumericValid := by decide +kernel
def certificate1340 : RatCutBinCertificate := ⟨⟨retention1340,(2632866551776579933/1000000000000000000),(175338961017292427/1000000000000000000),(38850850805633293/2500000000000000),(40413199776386847259/200000000000000000),(958110812603603077/1000000000000000000)⟩,(39568726010753557/40000000000000000),(51782722416930309/125000000000000000),(55166545325183757/250000000000000000),(173867810873515029/1000000000000000000)⟩
theorem valid1340 : certificate1340.Valid := by decide +kernel
theorem sound1340 : certificate1340.Sound := rat_cut_bin_certificate_sound certificate1340 profilesValid1340 numericValid1340 valid1340

def retention1341 : RatCutRetentionCertificate := ⟨(471/8000),(59/1000),(1/2),(1610029863968254463/250000000000000000),(21/20),(633496484244130851205928222115048152831/644011945587301785200000000000000000000),false,MergedCutProfiles.Batch218.profile8739,(fun _ => MergedCutProfiles.Batch218.profile8739)⟩
theorem profilesValid1341 : retention1341.ProfilesValid := by
  exact MergedCutProfiles.Batch218.valid8739
theorem numericValid1341 : retention1341.NumericValid := by decide +kernel
def certificate1341 : RatCutBinCertificate := ⟨⟨retention1341,(2632866551776579933/1000000000000000000),(175338961017292427/1000000000000000000),(38850850805633293/2500000000000000),(40413199776386847259/200000000000000000),(952476459319673091/1000000000000000000)⟩,(39568726010753557/40000000000000000),(416712335665698139/1000000000000000000),(54628477073513151/250000000000000000),(17275648670363247/100000000000000000)⟩
theorem valid1341 : certificate1341.Valid := by decide +kernel
theorem sound1341 : certificate1341.Sound := rat_cut_bin_certificate_sound certificate1341 profilesValid1341 numericValid1341 valid1341

def retention1342 : RatCutRetentionCertificate := ⟨(59/1000),(237/4000),(303830859323594241/4287940861203904175),(850165584204900373/1000000000000000000),(11/4),(101579414864462986589/51200000000000000000),true,MergedCutProfiles.Batch218.profile8742,![MergedCutProfiles.Batch218.profile8742,MergedCutProfiles.Batch218.profile8743,MergedCutProfiles.Batch218.profile8744,MergedCutProfiles.Batch218.profile8745,MergedCutProfiles.Batch218.profile8746,MergedCutProfiles.Batch218.profile8747,MergedCutProfiles.Batch218.profile8748,MergedCutProfiles.Batch218.profile8749,MergedCutProfiles.Batch218.profile8750,MergedCutProfiles.Batch218.profile8751,MergedCutProfiles.Batch218.profile8752,MergedCutProfiles.Batch218.profile8753,MergedCutProfiles.Batch218.profile8754,MergedCutProfiles.Batch218.profile8755,MergedCutProfiles.Batch218.profile8756,MergedCutProfiles.Batch218.profile8757]⟩
theorem profilesValid1342 : retention1342.ProfilesValid := by
  change ∀ j : Fin 16, (retention1342.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch218.valid8742
  · exact MergedCutProfiles.Batch218.valid8743
  · exact MergedCutProfiles.Batch218.valid8744
  · exact MergedCutProfiles.Batch218.valid8745
  · exact MergedCutProfiles.Batch218.valid8746
  · exact MergedCutProfiles.Batch218.valid8747
  · exact MergedCutProfiles.Batch218.valid8748
  · exact MergedCutProfiles.Batch218.valid8749
  · exact MergedCutProfiles.Batch218.valid8750
  · exact MergedCutProfiles.Batch218.valid8751
  · exact MergedCutProfiles.Batch218.valid8752
  · exact MergedCutProfiles.Batch218.valid8753
  · exact MergedCutProfiles.Batch218.valid8754
  · exact MergedCutProfiles.Batch218.valid8755
  · exact MergedCutProfiles.Batch218.valid8756
  · exact MergedCutProfiles.Batch218.valid8757
theorem numericValid1342 : retention1342.NumericValid := by decide +kernel
def certificate1342 : RatCutBinCertificate := ⟨⟨retention1342,(2305019937538484471/1000000000000000000),(1770931297231219/10000000000000000),(7787744033161907579/500000000000000000),(100332580072107007567/500000000000000000),(191187359892792329/100000000000000000)⟩,(30953353541991321/31250000000000000),(176806590611759629/500000000000000000),(278782399990022901/1000000000000000000),(29537336824211749/200000000000000000)⟩
theorem valid1342 : certificate1342.Valid := by decide +kernel
theorem sound1342 : certificate1342.Sound := rat_cut_bin_certificate_sound certificate1342 profilesValid1342 numericValid1342 valid1342

def retention1343 : RatCutRetentionCertificate := ⟨(59/1000),(237/4000),(1291222898055456106/12863822583611712525),(911492577970782723/1000000000000000000),(51/20),(606459843557655661241/320000000000000000000),true,MergedCutProfiles.Batch218.profile8758,![MergedCutProfiles.Batch218.profile8758,MergedCutProfiles.Batch218.profile8759,MergedCutProfiles.Batch219.profile8760,MergedCutProfiles.Batch219.profile8761,MergedCutProfiles.Batch219.profile8762,MergedCutProfiles.Batch219.profile8763,MergedCutProfiles.Batch219.profile8764,MergedCutProfiles.Batch219.profile8765,MergedCutProfiles.Batch219.profile8766,MergedCutProfiles.Batch219.profile8767,MergedCutProfiles.Batch219.profile8768,MergedCutProfiles.Batch219.profile8769,MergedCutProfiles.Batch219.profile8770,MergedCutProfiles.Batch219.profile8771,MergedCutProfiles.Batch219.profile8772,MergedCutProfiles.Batch219.profile8773]⟩
theorem profilesValid1343 : retention1343.ProfilesValid := by
  change ∀ j : Fin 16, (retention1343.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch218.valid8758
  · exact MergedCutProfiles.Batch218.valid8759
  · exact MergedCutProfiles.Batch219.valid8760
  · exact MergedCutProfiles.Batch219.valid8761
  · exact MergedCutProfiles.Batch219.valid8762
  · exact MergedCutProfiles.Batch219.valid8763
  · exact MergedCutProfiles.Batch219.valid8764
  · exact MergedCutProfiles.Batch219.valid8765
  · exact MergedCutProfiles.Batch219.valid8766
  · exact MergedCutProfiles.Batch219.valid8767
  · exact MergedCutProfiles.Batch219.valid8768
  · exact MergedCutProfiles.Batch219.valid8769
  · exact MergedCutProfiles.Batch219.valid8770
  · exact MergedCutProfiles.Batch219.valid8771
  · exact MergedCutProfiles.Batch219.valid8772
  · exact MergedCutProfiles.Batch219.valid8773
theorem numericValid1343 : retention1343.NumericValid := by decide +kernel
def certificate1343 : RatCutBinCertificate := ⟨⟨retention1343,(2305019937538484471/1000000000000000000),(1770931297231219/10000000000000000),(7787744033161907579/500000000000000000),(100332580072107007567/500000000000000000),(1828331104249288667/1000000000000000000)⟩,(30953353541991321/31250000000000000),(359577870080017267/1000000000000000000),(68158161215354131/250000000000000000),(9230406360755077/62500000000000000)⟩
theorem valid1343 : certificate1343.Valid := by decide +kernel
theorem sound1343 : certificate1343.Sound := rat_cut_bin_certificate_sound certificate1343 profilesValid1343 numericValid1343 valid1343

def certificates : List RatCutBinCertificate := [certificate1332,certificate1333,certificate1334,certificate1335,certificate1336,certificate1337,certificate1338,certificate1339,certificate1340,certificate1341,certificate1342,certificate1343]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1332,List.forall_mem_cons.mpr ⟨sound1333,List.forall_mem_cons.mpr ⟨sound1334,List.forall_mem_cons.mpr ⟨sound1335,List.forall_mem_cons.mpr ⟨sound1336,List.forall_mem_cons.mpr ⟨sound1337,List.forall_mem_cons.mpr ⟨sound1338,List.forall_mem_cons.mpr ⟨sound1339,List.forall_mem_cons.mpr ⟨sound1340,List.forall_mem_cons.mpr ⟨sound1341,List.forall_mem_cons.mpr ⟨sound1342,List.forall_mem_cons.mpr ⟨sound1343,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch111
