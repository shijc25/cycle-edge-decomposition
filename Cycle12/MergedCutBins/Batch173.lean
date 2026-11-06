import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch028
import Cycle12.MergedCutProfiles.Batch029
import Cycle12.MergedCutProfiles.Batch030
import Cycle12.MergedCutProfiles.Batch323
import Cycle12.MergedCutProfiles.Batch324

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch173

def retention2076 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(12861374099150165712/114167855278157797031),(867351383685669383/500000000000000000),(39/20),(1287850382315458290002760279493259385191/693881106948535506400000000000000000000),false,MergedCutProfiles.Batch323.profile12932,(fun _ => MergedCutProfiles.Batch323.profile12932)⟩
theorem profilesValid2076 : retention2076.ProfilesValid := by
  exact MergedCutProfiles.Batch323.valid12932
theorem numericValid2076 : retention2076.NumericValid := by decide +kernel
def certificate2076 : RatCutBinCertificate := ⟨⟨retention2076,(3824476810895587/2000000000000000),(10247703429141591/500000000000000000),(1731926382999934319/200000000000000000),(496711091993987075701/250000000000000000),(184718474317104799/100000000000000000)⟩,(499527720107808973/500000000000000000),(190678907253399871/500000000000000000),(125502173128557979/500000000000000000),(185554858889144543/1000000000000000000)⟩
theorem valid2076 : certificate2076.Valid := by decide +kernel
theorem sound2076 : certificate2076.Sound := rat_cut_bin_certificate_sound certificate2076 profilesValid2076 numericValid2076 valid2076

def retention2077 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(32000000000000000000/114167855278157797031),(803835881196885357/31250000000000000),1,(615529682560117962993163270355221761/428712469971672190400000000000000000),false,MergedCutProfiles.Batch323.profile12933,(fun _ => MergedCutProfiles.Batch323.profile12933)⟩
theorem profilesValid2077 : retention2077.ProfilesValid := by
  exact MergedCutProfiles.Batch323.valid12933
theorem numericValid2077 : retention2077.NumericValid := by decide +kernel
def certificate2077 : RatCutBinCertificate := ⟨⟨retention2077,(3824476810895587/2000000000000000),(10247703429141591/500000000000000000),(1731926382999934319/200000000000000000),(496711091993987075701/250000000000000000),(89452348737681209/62500000000000000)⟩,(499527720107808973/500000000000000000),(160419376009479081/500000000000000000),(9825416668423083/31250000000000000),(212935384930636729/500000000000000000)⟩
theorem valid2077 : certificate2077.Valid := by decide +kernel
theorem sound2077 : certificate2077.Sound := rat_cut_bin_certificate_sound certificate2077 profilesValid2077 numericValid2077 valid2077

def retention2078 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(1/2),64,1,(15960748357185807596877500066049185271/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch028.profile1132,(fun _ => MergedCutProfiles.Batch028.profile1132)⟩
theorem profilesValid2078 : retention2078.ProfilesValid := by
  exact MergedCutProfiles.Batch028.valid1132
theorem numericValid2078 : retention2078.NumericValid := by decide +kernel
def certificate2078 : RatCutBinCertificate := ⟨⟨retention2078,(3824476810895587/2000000000000000),(10247703429141591/500000000000000000),(1731926382999934319/200000000000000000),(496711091993987075701/250000000000000000),(496510466050012969/500000000000000000)⟩,(499527720107808973/500000000000000000),(9034847808584107/20000000000000000),(189283329952547003/1000000000000000000),(184914162435484179/1000000000000000000)⟩
theorem valid2078 : certificate2078.Valid := by decide +kernel
theorem sound2078 : certificate2078.Sound := rat_cut_bin_certificate_sound certificate2078 profilesValid2078 numericValid2078 valid2078

def retention2079 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(32000000000000000000/114167855278157797031),(5184742592783593329/1000000000000000000),(11/10),(977470448066680040236399886032756195653/691299012371145777200000000000000000000),false,MergedCutProfiles.Batch323.profile12933,(fun _ => MergedCutProfiles.Batch323.profile12933)⟩
theorem profilesValid2079 : retention2079.ProfilesValid := by
  exact MergedCutProfiles.Batch323.valid12933
theorem numericValid2079 : retention2079.NumericValid := by decide +kernel
def certificate2079 : RatCutBinCertificate := ⟨⟨retention2079,(4415380064895587/2000000000000000),(10247703429141591/500000000000000000),(1731926382999934319/200000000000000000),(496711091993987075701/250000000000000000),(14082142471424003/10000000000000000)⟩,(499454748690144259/500000000000000000),(85856953377558499/500000000000000000),(525146057112642357/1000000000000000000),(137101617086195541/250000000000000000)⟩
theorem valid2079 : certificate2079.Valid := by decide +kernel
theorem sound2079 : certificate2079.Sound := rat_cut_bin_certificate_sound certificate2079 profilesValid2079 numericValid2079 valid2079

def retention2080 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(1/2),64,1,(15960748357185807596877500066049185271/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch028.profile1132,(fun _ => MergedCutProfiles.Batch028.profile1132)⟩
theorem profilesValid2080 : retention2080.ProfilesValid := by
  exact MergedCutProfiles.Batch028.valid1132
theorem numericValid2080 : retention2080.NumericValid := by decide +kernel
def certificate2080 : RatCutBinCertificate := ⟨⟨retention2080,(4415380064895587/2000000000000000),(10247703429141591/500000000000000000),(1731926382999934319/200000000000000000),(496711091993987075701/250000000000000000),(992321664239941603/1000000000000000000)⟩,(499454748690144259/500000000000000000),(60920258682009433/250000000000000000),(412167196853280231/1000000000000000000),(80463055885468699/200000000000000000)⟩
theorem valid2080 : certificate2080.Valid := by decide +kernel
theorem sound2080 : certificate2080.Sound := rat_cut_bin_certificate_sound certificate2080 profilesValid2080 numericValid2080 valid2080

def retention2081 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(646922150498420597/207902992142096568441),(640516980691505541/1000000000000000000),4,(117245266316293968089/51200000000000000000),true,MergedCutProfiles.Batch323.profile12934,![MergedCutProfiles.Batch323.profile12934,MergedCutProfiles.Batch323.profile12935,MergedCutProfiles.Batch323.profile12936,MergedCutProfiles.Batch323.profile12937,MergedCutProfiles.Batch029.profile1192,MergedCutProfiles.Batch323.profile12938,MergedCutProfiles.Batch029.profile1167,MergedCutProfiles.Batch323.profile12939,MergedCutProfiles.Batch323.profile12940,MergedCutProfiles.Batch029.profile1193,MergedCutProfiles.Batch028.profile1154,MergedCutProfiles.Batch323.profile12941,MergedCutProfiles.Batch323.profile12942,MergedCutProfiles.Batch029.profile1168,MergedCutProfiles.Batch029.profile1194,MergedCutProfiles.Batch323.profile12943]⟩
theorem profilesValid2081 : retention2081.ProfilesValid := by
  change ∀ j : Fin 16, (retention2081.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch323.valid12934
  · exact MergedCutProfiles.Batch323.valid12935
  · exact MergedCutProfiles.Batch323.valid12936
  · exact MergedCutProfiles.Batch323.valid12937
  · exact MergedCutProfiles.Batch029.valid1192
  · exact MergedCutProfiles.Batch323.valid12938
  · exact MergedCutProfiles.Batch029.valid1167
  · exact MergedCutProfiles.Batch323.valid12939
  · exact MergedCutProfiles.Batch323.valid12940
  · exact MergedCutProfiles.Batch029.valid1193
  · exact MergedCutProfiles.Batch028.valid1154
  · exact MergedCutProfiles.Batch323.valid12941
  · exact MergedCutProfiles.Batch323.valid12942
  · exact MergedCutProfiles.Batch029.valid1168
  · exact MergedCutProfiles.Batch029.valid1194
  · exact MergedCutProfiles.Batch323.valid12943
theorem numericValid2081 : retention2081.NumericValid := by decide +kernel
def certificate2081 : RatCutBinCertificate := ⟨⟨retention2081,(1918508090584363907/1000000000000000000),(702642711920787/31250000000000000),(8775682409316870879/1000000000000000000),(1833345959200750119597/1000000000000000000),(2270284533494102431/1000000000000000000)⟩,(4994874868312531/5000000000000000),(63330592564865051/125000000000000000),(148864544895394083/1000000000000000000),(34542606740464813/500000000000000000)⟩
theorem valid2081 : certificate2081.Valid := by decide +kernel
theorem sound2081 : certificate2081.Sound := rat_cut_bin_certificate_sound certificate2081 profilesValid2081 numericValid2081 valid2081

def retention2082 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(1107149340851481268/207902992142096568441),(646922150498420597/1000000000000000000),4,(36459569573957013017/16000000000000000000),true,MergedCutProfiles.Batch323.profile12944,![MergedCutProfiles.Batch323.profile12944,MergedCutProfiles.Batch323.profile12945,MergedCutProfiles.Batch323.profile12946,MergedCutProfiles.Batch323.profile12947,MergedCutProfiles.Batch323.profile12948,MergedCutProfiles.Batch323.profile12949,MergedCutProfiles.Batch323.profile12941,MergedCutProfiles.Batch028.profile1155,MergedCutProfiles.Batch323.profile12950,MergedCutProfiles.Batch323.profile12951,MergedCutProfiles.Batch323.profile12952,MergedCutProfiles.Batch323.profile12953,MergedCutProfiles.Batch323.profile12954,MergedCutProfiles.Batch323.profile12955,MergedCutProfiles.Batch323.profile12956,MergedCutProfiles.Batch028.profile1147]⟩
theorem profilesValid2082 : retention2082.ProfilesValid := by
  change ∀ j : Fin 16, (retention2082.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch323.valid12944
  · exact MergedCutProfiles.Batch323.valid12945
  · exact MergedCutProfiles.Batch323.valid12946
  · exact MergedCutProfiles.Batch323.valid12947
  · exact MergedCutProfiles.Batch323.valid12948
  · exact MergedCutProfiles.Batch323.valid12949
  · exact MergedCutProfiles.Batch323.valid12941
  · exact MergedCutProfiles.Batch028.valid1155
  · exact MergedCutProfiles.Batch323.valid12950
  · exact MergedCutProfiles.Batch323.valid12951
  · exact MergedCutProfiles.Batch323.valid12952
  · exact MergedCutProfiles.Batch323.valid12953
  · exact MergedCutProfiles.Batch323.valid12954
  · exact MergedCutProfiles.Batch323.valid12955
  · exact MergedCutProfiles.Batch323.valid12956
  · exact MergedCutProfiles.Batch028.valid1147
theorem numericValid2082 : retention2082.NumericValid := by decide +kernel
def certificate2082 : RatCutBinCertificate := ⟨⟨retention2082,(1918508090584363907/1000000000000000000),(702642711920787/31250000000000000),(8775682409316870879/1000000000000000000),(1833345959200750119597/1000000000000000000),(2259061025058169197/1000000000000000000)⟩,(4994874868312531/5000000000000000),(126516279659218167/250000000000000000),(18657373358465613/125000000000000000),(69111360167746329/1000000000000000000)⟩
theorem valid2082 : certificate2082.Valid := by decide +kernel
theorem sound2082 : certificate2082.Sound := rat_cut_bin_certificate_sound certificate2082 profilesValid2082 numericValid2082 valid2082

def retention2083 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(131710663000000000/23100332460232952049),(276787335212870317/250000000000000000),(53/20),(727707153081459773777/320000000000000000000),true,MergedCutProfiles.Batch323.profile12957,![MergedCutProfiles.Batch323.profile12957,MergedCutProfiles.Batch323.profile12958,MergedCutProfiles.Batch028.profile1152,MergedCutProfiles.Batch323.profile12959,MergedCutProfiles.Batch324.profile12960,MergedCutProfiles.Batch028.profile1154,MergedCutProfiles.Batch323.profile12942,MergedCutProfiles.Batch028.profile1141,MergedCutProfiles.Batch028.profile1156,MergedCutProfiles.Batch324.profile12961,MergedCutProfiles.Batch324.profile12962,MergedCutProfiles.Batch028.profile1158,MergedCutProfiles.Batch323.profile12955,MergedCutProfiles.Batch323.profile12956,MergedCutProfiles.Batch028.profile1147,MergedCutProfiles.Batch028.profile1148]⟩
theorem profilesValid2083 : retention2083.ProfilesValid := by
  change ∀ j : Fin 16, (retention2083.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch323.valid12957
  · exact MergedCutProfiles.Batch323.valid12958
  · exact MergedCutProfiles.Batch028.valid1152
  · exact MergedCutProfiles.Batch323.valid12959
  · exact MergedCutProfiles.Batch324.valid12960
  · exact MergedCutProfiles.Batch028.valid1154
  · exact MergedCutProfiles.Batch323.valid12942
  · exact MergedCutProfiles.Batch028.valid1141
  · exact MergedCutProfiles.Batch028.valid1156
  · exact MergedCutProfiles.Batch324.valid12961
  · exact MergedCutProfiles.Batch324.valid12962
  · exact MergedCutProfiles.Batch028.valid1158
  · exact MergedCutProfiles.Batch323.valid12955
  · exact MergedCutProfiles.Batch323.valid12956
  · exact MergedCutProfiles.Batch028.valid1147
  · exact MergedCutProfiles.Batch028.valid1148
theorem numericValid2083 : retention2083.NumericValid := by decide +kernel
def certificate2083 : RatCutBinCertificate := ⟨⟨retention2083,(1918508090584363907/1000000000000000000),(702642711920787/31250000000000000),(8775682409316870879/1000000000000000000),(1833345959200750119597/1000000000000000000),(452211747418983989/200000000000000000)⟩,(4994874868312531/5000000000000000),(188502118089801009/500000000000000000),(127612947552636031/500000000000000000),(42126750487634217/250000000000000000)⟩
theorem valid2083 : certificate2083.Valid := by decide +kernel
theorem sound2083 : certificate2083.Sound := rat_cut_bin_certificate_sound certificate2083 profilesValid2083 numericValid2083 valid2083

def retention2084 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(432739891274598643/69300997380698856147),(1185395967/1000000000),(5/2),(1448391379763633983/640000000000000000),true,MergedCutProfiles.Batch323.profile12935,![MergedCutProfiles.Batch323.profile12935,MergedCutProfiles.Batch323.profile12937,MergedCutProfiles.Batch324.profile12963,MergedCutProfiles.Batch323.profile12939,MergedCutProfiles.Batch029.profile1193,MergedCutProfiles.Batch324.profile12964,MergedCutProfiles.Batch029.profile1180,MergedCutProfiles.Batch323.profile12943,MergedCutProfiles.Batch324.profile12965,MergedCutProfiles.Batch029.profile1195,MergedCutProfiles.Batch323.profile12954,MergedCutProfiles.Batch324.profile12966,MergedCutProfiles.Batch324.profile12967,MergedCutProfiles.Batch324.profile12968,MergedCutProfiles.Batch029.profile1160,MergedCutProfiles.Batch029.profile1185]⟩
theorem profilesValid2084 : retention2084.ProfilesValid := by
  change ∀ j : Fin 16, (retention2084.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch323.valid12935
  · exact MergedCutProfiles.Batch323.valid12937
  · exact MergedCutProfiles.Batch324.valid12963
  · exact MergedCutProfiles.Batch323.valid12939
  · exact MergedCutProfiles.Batch029.valid1193
  · exact MergedCutProfiles.Batch324.valid12964
  · exact MergedCutProfiles.Batch029.valid1180
  · exact MergedCutProfiles.Batch323.valid12943
  · exact MergedCutProfiles.Batch324.valid12965
  · exact MergedCutProfiles.Batch029.valid1195
  · exact MergedCutProfiles.Batch323.valid12954
  · exact MergedCutProfiles.Batch324.valid12966
  · exact MergedCutProfiles.Batch324.valid12967
  · exact MergedCutProfiles.Batch324.valid12968
  · exact MergedCutProfiles.Batch029.valid1160
  · exact MergedCutProfiles.Batch029.valid1185
theorem numericValid2084 : retention2084.NumericValid := by decide +kernel
def certificate2084 : RatCutBinCertificate := ⟨⟨retention2084,(1918508090584363907/1000000000000000000),(702642711920787/31250000000000000),(8775682409316870879/1000000000000000000),(1833345959200750119597/1000000000000000000),(2250822742445013109/1000000000000000000)⟩,(4994874868312531/5000000000000000),(91682728701651497/250000000000000000),(66346959861719713/250000000000000000),(5720195444417319/31250000000000000)⟩
theorem valid2084 : certificate2084.Valid := by decide +kernel
theorem sound2084 : certificate2084.Sound := rat_cut_bin_certificate_sound certificate2084 profilesValid2084 numericValid2084 valid2084

def retention2085 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(5549690435187193825/207902992142096568441),(1298219673823795929/1000000000000000000),(47/20),(687760555153524999771/320000000000000000000),true,MergedCutProfiles.Batch323.profile12948,![MergedCutProfiles.Batch323.profile12948,MergedCutProfiles.Batch323.profile12951,MergedCutProfiles.Batch323.profile12956,MergedCutProfiles.Batch324.profile12969,MergedCutProfiles.Batch324.profile12970,MergedCutProfiles.Batch324.profile12971,MergedCutProfiles.Batch324.profile12972,MergedCutProfiles.Batch324.profile12973,MergedCutProfiles.Batch324.profile12974,MergedCutProfiles.Batch324.profile12975,MergedCutProfiles.Batch324.profile12976,MergedCutProfiles.Batch324.profile12977,MergedCutProfiles.Batch324.profile12978,MergedCutProfiles.Batch324.profile12979,MergedCutProfiles.Batch324.profile12980,MergedCutProfiles.Batch324.profile12981]⟩
theorem profilesValid2085 : retention2085.ProfilesValid := by
  change ∀ j : Fin 16, (retention2085.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch323.valid12948
  · exact MergedCutProfiles.Batch323.valid12951
  · exact MergedCutProfiles.Batch323.valid12956
  · exact MergedCutProfiles.Batch324.valid12969
  · exact MergedCutProfiles.Batch324.valid12970
  · exact MergedCutProfiles.Batch324.valid12971
  · exact MergedCutProfiles.Batch324.valid12972
  · exact MergedCutProfiles.Batch324.valid12973
  · exact MergedCutProfiles.Batch324.valid12974
  · exact MergedCutProfiles.Batch324.valid12975
  · exact MergedCutProfiles.Batch324.valid12976
  · exact MergedCutProfiles.Batch324.valid12977
  · exact MergedCutProfiles.Batch324.valid12978
  · exact MergedCutProfiles.Batch324.valid12979
  · exact MergedCutProfiles.Batch324.valid12980
  · exact MergedCutProfiles.Batch324.valid12981
theorem numericValid2085 : retention2085.NumericValid := by decide +kernel
def certificate2085 : RatCutBinCertificate := ⟨⟨retention2085,(1918508090584363907/1000000000000000000),(702642711920787/31250000000000000),(8775682409316870879/1000000000000000000),(1833345959200750119597/1000000000000000000),(2137700275093602073/1000000000000000000)⟩,(4994874868312531/5000000000000000),(370616254035788861/1000000000000000000),(130755622159935397/500000000000000000),(183033836513510423/1000000000000000000)⟩
theorem valid2085 : certificate2085.Valid := by decide +kernel
theorem sound2085 : certificate2085.Sound := rat_cut_bin_certificate_sound certificate2085 profilesValid2085 numericValid2085 valid2085

def retention2086 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(64000000000000000000/207902992142096568441),(221987617407487753/40000000000000000),(23/20),(19642724132714374381516379766486218551/14207207514079216192000000000000000000),false,MergedCutProfiles.Batch324.profile12982,(fun _ => MergedCutProfiles.Batch324.profile12982)⟩
theorem profilesValid2086 : retention2086.ProfilesValid := by
  exact MergedCutProfiles.Batch324.valid12982
theorem numericValid2086 : retention2086.NumericValid := by decide +kernel
def certificate2086 : RatCutBinCertificate := ⟨⟨retention2086,(1918508090584363907/1000000000000000000),(702642711920787/31250000000000000),(8775682409316870879/1000000000000000000),(1833345959200750119597/1000000000000000000),(688467919623037111/500000000000000000)⟩,(4994874868312531/5000000000000000),(1489968509533707/3906250000000000),(125466450921666263/500000000000000000),(252710512956257693/1000000000000000000)⟩
theorem valid2086 : certificate2086.Valid := by decide +kernel
theorem sound2086 : certificate2086.Sound := rat_cut_bin_certificate_sound certificate2086 profilesValid2086 numericValid2086 valid2086

def retention2087 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(1/2),64,1,(255372377798511361897078253271756735919/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch030.profile1208,(fun _ => MergedCutProfiles.Batch030.profile1208)⟩
theorem profilesValid2087 : retention2087.ProfilesValid := by
  exact MergedCutProfiles.Batch030.valid1208
theorem numericValid2087 : retention2087.NumericValid := by decide +kernel
def certificate2087 : RatCutBinCertificate := ⟨⟨retention2087,(1918508090584363907/1000000000000000000),(702642711920787/31250000000000000),(8775682409316870879/1000000000000000000),(1833345959200750119597/1000000000000000000),(992632854801700411/1000000000000000000)⟩,(4994874868312531/5000000000000000),(56759418756728529/125000000000000000),(37487098534935633/200000000000000000),(45755911118853573/250000000000000000)⟩
theorem valid2087 : certificate2087.Valid := by decide +kernel
theorem sound2087 : certificate2087.Sound := rat_cut_bin_certificate_sound certificate2087 profilesValid2087 numericValid2087 valid2087

def certificates : List RatCutBinCertificate := [certificate2076,certificate2077,certificate2078,certificate2079,certificate2080,certificate2081,certificate2082,certificate2083,certificate2084,certificate2085,certificate2086,certificate2087]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2076,List.forall_mem_cons.mpr ⟨sound2077,List.forall_mem_cons.mpr ⟨sound2078,List.forall_mem_cons.mpr ⟨sound2079,List.forall_mem_cons.mpr ⟨sound2080,List.forall_mem_cons.mpr ⟨sound2081,List.forall_mem_cons.mpr ⟨sound2082,List.forall_mem_cons.mpr ⟨sound2083,List.forall_mem_cons.mpr ⟨sound2084,List.forall_mem_cons.mpr ⟨sound2085,List.forall_mem_cons.mpr ⟨sound2086,List.forall_mem_cons.mpr ⟨sound2087,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch173
