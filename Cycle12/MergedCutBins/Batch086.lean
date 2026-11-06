import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch172
import Cycle12.MergedCutProfiles.Batch173
import Cycle12.MergedCutProfiles.Batch174

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch086

def retention1032 : RatCutRetentionCertificate := ⟨(209/4000),(21/400),(1/2),(8451876461406736101/1000000000000000000),(21/20),(13410076010164884446325102215329000536359/13523002338250777761600000000000000000000),false,MergedCutProfiles.Batch172.profile6889,(fun _ => MergedCutProfiles.Batch172.profile6889)⟩
theorem profilesValid1032 : retention1032.ProfilesValid := by
  exact MergedCutProfiles.Batch172.valid6889
theorem numericValid1032 : retention1032.NumericValid := by decide +kernel
def certificate1032 : RatCutBinCertificate := ⟨⟨retention1032,(1280862713542186467/500000000000000000),(26755931122933953/200000000000000000),(34586963781175297/2500000000000000),(59077136701526038033/250000000000000000),(965637705878280591/1000000000000000000)⟩,(39623202511761841/40000000000000000),(25978434598383601/62500000000000000),(109720406591316791/500000000000000000),(22631024872194929/125000000000000000)⟩
theorem valid1032 : certificate1032.Valid := by decide +kernel
theorem sound1032 : certificate1032.Sound := rat_cut_bin_certificate_sound certificate1032 profilesValid1032 numericValid1032 valid1032

def retention1033 : RatCutRetentionCertificate := ⟨(21/400),(211/4000),(851495611393460617/16870065927358992572),(843064961775703581/1000000000000000000),(57/20),(81887784785926424241/40000000000000000000),true,MergedCutProfiles.Batch172.profile6892,![MergedCutProfiles.Batch172.profile6892,MergedCutProfiles.Batch172.profile6893,MergedCutProfiles.Batch172.profile6894,MergedCutProfiles.Batch172.profile6895,MergedCutProfiles.Batch172.profile6896,MergedCutProfiles.Batch172.profile6897,MergedCutProfiles.Batch172.profile6898,MergedCutProfiles.Batch172.profile6899,MergedCutProfiles.Batch172.profile6900,MergedCutProfiles.Batch172.profile6901,MergedCutProfiles.Batch172.profile6902,MergedCutProfiles.Batch172.profile6903,MergedCutProfiles.Batch172.profile6904,MergedCutProfiles.Batch172.profile6905,MergedCutProfiles.Batch172.profile6906,MergedCutProfiles.Batch172.profile6907]⟩
theorem profilesValid1033 : retention1033.ProfilesValid := by
  change ∀ j : Fin 16, (retention1033.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch172.valid6892
  · exact MergedCutProfiles.Batch172.valid6893
  · exact MergedCutProfiles.Batch172.valid6894
  · exact MergedCutProfiles.Batch172.valid6895
  · exact MergedCutProfiles.Batch172.valid6896
  · exact MergedCutProfiles.Batch172.valid6897
  · exact MergedCutProfiles.Batch172.valid6898
  · exact MergedCutProfiles.Batch172.valid6899
  · exact MergedCutProfiles.Batch172.valid6900
  · exact MergedCutProfiles.Batch172.valid6901
  · exact MergedCutProfiles.Batch172.valid6902
  · exact MergedCutProfiles.Batch172.valid6903
  · exact MergedCutProfiles.Batch172.valid6904
  · exact MergedCutProfiles.Batch172.valid6905
  · exact MergedCutProfiles.Batch172.valid6906
  · exact MergedCutProfiles.Batch172.valid6907
theorem numericValid1033 : retention1033.NumericValid := by decide +kernel
def certificate1033 : RatCutBinCertificate := ⟨⟨retention1033,(1103490021555746827/500000000000000000),(135240887695497653/1000000000000000000),(3473464720970437089/250000000000000000),(234731906921777485191/1000000000000000000),(496488748686784801/250000000000000000)⟩,(61990319460155311/62500000000000000),(183997976428928031/500000000000000000),(264121154647554509/1000000000000000000),(70642364330271597/500000000000000000)⟩
theorem valid1033 : certificate1033.Valid := by decide +kernel
theorem sound1033 : certificate1033.Sound := rat_cut_bin_certificate_sound certificate1033 profilesValid1033 numericValid1033 valid1033

def retention1034 : RatCutRetentionCertificate := ⟨(21/400),(211/4000),(456459273569450829/8435032963679496286),(851495611393460617/1000000000000000000),(57/20),(2612333283529064891073/1280000000000000000000),true,MergedCutProfiles.Batch172.profile6908,![MergedCutProfiles.Batch172.profile6908,MergedCutProfiles.Batch172.profile6909,MergedCutProfiles.Batch172.profile6910,MergedCutProfiles.Batch172.profile6911,MergedCutProfiles.Batch172.profile6912,MergedCutProfiles.Batch172.profile6913,MergedCutProfiles.Batch172.profile6914,MergedCutProfiles.Batch172.profile6915,MergedCutProfiles.Batch172.profile6916,MergedCutProfiles.Batch172.profile6917,MergedCutProfiles.Batch172.profile6918,MergedCutProfiles.Batch172.profile6919,MergedCutProfiles.Batch173.profile6920,MergedCutProfiles.Batch172.profile6906,MergedCutProfiles.Batch173.profile6921,MergedCutProfiles.Batch173.profile6922]⟩
theorem profilesValid1034 : retention1034.ProfilesValid := by
  change ∀ j : Fin 16, (retention1034.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch172.valid6908
  · exact MergedCutProfiles.Batch172.valid6909
  · exact MergedCutProfiles.Batch172.valid6910
  · exact MergedCutProfiles.Batch172.valid6911
  · exact MergedCutProfiles.Batch172.valid6912
  · exact MergedCutProfiles.Batch172.valid6913
  · exact MergedCutProfiles.Batch172.valid6914
  · exact MergedCutProfiles.Batch172.valid6915
  · exact MergedCutProfiles.Batch172.valid6916
  · exact MergedCutProfiles.Batch172.valid6917
  · exact MergedCutProfiles.Batch172.valid6918
  · exact MergedCutProfiles.Batch172.valid6919
  · exact MergedCutProfiles.Batch173.valid6920
  · exact MergedCutProfiles.Batch172.valid6906
  · exact MergedCutProfiles.Batch173.valid6921
  · exact MergedCutProfiles.Batch173.valid6922
theorem numericValid1034 : retention1034.NumericValid := by decide +kernel
def certificate1034 : RatCutBinCertificate := ⟨⟨retention1034,(1103490021555746827/500000000000000000),(135240887695497653/1000000000000000000),(3473464720970437089/250000000000000000),(234731906921777485191/1000000000000000000),(989822949106706993/500000000000000000)⟩,(61990319460155311/62500000000000000),(22979283605796407/62500000000000000),(5288971574782307/20000000000000000),(35356707893110377/250000000000000000)⟩
theorem valid1034 : certificate1034.Valid := by decide +kernel
theorem sound1034 : certificate1034.Sound := rat_cut_bin_certificate_sound certificate1034 profilesValid1034 numericValid1034 valid1034

def retention1035 : RatCutRetentionCertificate := ⟨(21/400),(211/4000),(672876889383742259/8435032963679496286),(456459273569450829/500000000000000000),(27/10),(314077359636769763297/160000000000000000000),true,MergedCutProfiles.Batch173.profile6923,![MergedCutProfiles.Batch173.profile6923,MergedCutProfiles.Batch173.profile6924,MergedCutProfiles.Batch173.profile6925,MergedCutProfiles.Batch173.profile6926,MergedCutProfiles.Batch173.profile6927,MergedCutProfiles.Batch173.profile6928,MergedCutProfiles.Batch173.profile6929,MergedCutProfiles.Batch173.profile6930,MergedCutProfiles.Batch173.profile6931,MergedCutProfiles.Batch173.profile6932,MergedCutProfiles.Batch173.profile6933,MergedCutProfiles.Batch173.profile6934,MergedCutProfiles.Batch173.profile6935,MergedCutProfiles.Batch173.profile6936,MergedCutProfiles.Batch173.profile6937,MergedCutProfiles.Batch173.profile6938]⟩
theorem profilesValid1035 : retention1035.ProfilesValid := by
  change ∀ j : Fin 16, (retention1035.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch173.valid6923
  · exact MergedCutProfiles.Batch173.valid6924
  · exact MergedCutProfiles.Batch173.valid6925
  · exact MergedCutProfiles.Batch173.valid6926
  · exact MergedCutProfiles.Batch173.valid6927
  · exact MergedCutProfiles.Batch173.valid6928
  · exact MergedCutProfiles.Batch173.valid6929
  · exact MergedCutProfiles.Batch173.valid6930
  · exact MergedCutProfiles.Batch173.valid6931
  · exact MergedCutProfiles.Batch173.valid6932
  · exact MergedCutProfiles.Batch173.valid6933
  · exact MergedCutProfiles.Batch173.valid6934
  · exact MergedCutProfiles.Batch173.valid6935
  · exact MergedCutProfiles.Batch173.valid6936
  · exact MergedCutProfiles.Batch173.valid6937
  · exact MergedCutProfiles.Batch173.valid6938
theorem numericValid1035 : retention1035.NumericValid := by decide +kernel
def certificate1035 : RatCutBinCertificate := ⟨⟨retention1035,(1103490021555746827/500000000000000000),(135240887695497653/1000000000000000000),(3473464720970437089/250000000000000000),(234731906921777485191/1000000000000000000),(952483680821144633/500000000000000000)⟩,(61990319460155311/62500000000000000),(185796235166997531/500000000000000000),(8141988697053999/31250000000000000),(35383422877436241/250000000000000000)⟩
theorem valid1035 : certificate1035.Valid := by decide +kernel
theorem sound1035 : certificate1035.Sound := rat_cut_bin_certificate_sound certificate1035 profilesValid1035 numericValid1035 valid1035

def retention1036 : RatCutRetentionCertificate := ⟨(21/400),(211/4000),(1820006715903284557/8435032963679496286),(672876889383742259/500000000000000000),(39/20),(1020725966352776825979/640000000000000000000),true,MergedCutProfiles.Batch173.profile6939,![MergedCutProfiles.Batch173.profile6939,MergedCutProfiles.Batch172.profile6915,MergedCutProfiles.Batch173.profile6940,MergedCutProfiles.Batch173.profile6941,MergedCutProfiles.Batch173.profile6942,MergedCutProfiles.Batch173.profile6943,MergedCutProfiles.Batch173.profile6944,MergedCutProfiles.Batch173.profile6945,MergedCutProfiles.Batch173.profile6946,MergedCutProfiles.Batch173.profile6947,MergedCutProfiles.Batch173.profile6948,MergedCutProfiles.Batch173.profile6949,MergedCutProfiles.Batch173.profile6950,MergedCutProfiles.Batch173.profile6951,MergedCutProfiles.Batch173.profile6952,MergedCutProfiles.Batch173.profile6953]⟩
theorem profilesValid1036 : retention1036.ProfilesValid := by
  change ∀ j : Fin 16, (retention1036.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch173.valid6939
  · exact MergedCutProfiles.Batch172.valid6915
  · exact MergedCutProfiles.Batch173.valid6940
  · exact MergedCutProfiles.Batch173.valid6941
  · exact MergedCutProfiles.Batch173.valid6942
  · exact MergedCutProfiles.Batch173.valid6943
  · exact MergedCutProfiles.Batch173.valid6944
  · exact MergedCutProfiles.Batch173.valid6945
  · exact MergedCutProfiles.Batch173.valid6946
  · exact MergedCutProfiles.Batch173.valid6947
  · exact MergedCutProfiles.Batch173.valid6948
  · exact MergedCutProfiles.Batch173.valid6949
  · exact MergedCutProfiles.Batch173.valid6950
  · exact MergedCutProfiles.Batch173.valid6951
  · exact MergedCutProfiles.Batch173.valid6952
  · exact MergedCutProfiles.Batch173.valid6953
theorem numericValid1036 : retention1036.NumericValid := by decide +kernel
def certificate1036 : RatCutBinCertificate := ⟨⟨retention1036,(1103490021555746827/500000000000000000),(135240887695497653/1000000000000000000),(3473464720970437089/250000000000000000),(234731906921777485191/1000000000000000000),(62119374969518299/40000000000000000)⟩,(61990319460155311/62500000000000000),(12451383570629231/31250000000000000),(14681926540646491/62500000000000000),(35538283324921541/250000000000000000)⟩
theorem valid1036 : certificate1036.Valid := by decide +kernel
theorem sound1036 : certificate1036.Sound := rat_cut_bin_certificate_sound certificate1036 profilesValid1036 numericValid1036 valid1036

def retention1037 : RatCutRetentionCertificate := ⟨(21/400),(211/4000),(3616161195750787641/8435032963679496286),(1820006715903284557/500000000000000000),(11/10),(711143125313898557641/640000000000000000000),true,MergedCutProfiles.Batch173.profile6954,![MergedCutProfiles.Batch173.profile6954,MergedCutProfiles.Batch173.profile6955,MergedCutProfiles.Batch173.profile6956,MergedCutProfiles.Batch173.profile6957,MergedCutProfiles.Batch173.profile6958,MergedCutProfiles.Batch173.profile6959,MergedCutProfiles.Batch174.profile6960,MergedCutProfiles.Batch174.profile6961,MergedCutProfiles.Batch174.profile6962,MergedCutProfiles.Batch174.profile6963,MergedCutProfiles.Batch174.profile6964,MergedCutProfiles.Batch174.profile6965,MergedCutProfiles.Batch174.profile6966,MergedCutProfiles.Batch174.profile6967,MergedCutProfiles.Batch174.profile6968,MergedCutProfiles.Batch174.profile6969]⟩
theorem profilesValid1037 : retention1037.ProfilesValid := by
  change ∀ j : Fin 16, (retention1037.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch173.valid6954
  · exact MergedCutProfiles.Batch173.valid6955
  · exact MergedCutProfiles.Batch173.valid6956
  · exact MergedCutProfiles.Batch173.valid6957
  · exact MergedCutProfiles.Batch173.valid6958
  · exact MergedCutProfiles.Batch173.valid6959
  · exact MergedCutProfiles.Batch174.valid6960
  · exact MergedCutProfiles.Batch174.valid6961
  · exact MergedCutProfiles.Batch174.valid6962
  · exact MergedCutProfiles.Batch174.valid6963
  · exact MergedCutProfiles.Batch174.valid6964
  · exact MergedCutProfiles.Batch174.valid6965
  · exact MergedCutProfiles.Batch174.valid6966
  · exact MergedCutProfiles.Batch174.valid6967
  · exact MergedCutProfiles.Batch174.valid6968
  · exact MergedCutProfiles.Batch174.valid6969
theorem numericValid1037 : retention1037.NumericValid := by decide +kernel
def certificate1037 : RatCutBinCertificate := ⟨⟨retention1037,(1103490021555746827/500000000000000000),(135240887695497653/1000000000000000000),(3473464720970437089/250000000000000000),(234731906921777485191/1000000000000000000),(543763526471432311/500000000000000000)⟩,(61990319460155311/62500000000000000),(2300348558719063/5000000000000000),(91371214383583551/500000000000000000),(71785943789957309/500000000000000000)⟩
theorem valid1037 : certificate1037.Valid := by decide +kernel
theorem sound1037 : certificate1037.Sound := rat_cut_bin_certificate_sound certificate1037 profilesValid1037 numericValid1037 valid1037

def retention1038 : RatCutRetentionCertificate := ⟨(21/400),(211/4000),(8231057515695160703/16870065927358992572),(3616161195750787641/500000000000000000),(21/20),(2923518444817395547598244314078422625039/2892928956600630112800000000000000000000),false,MergedCutProfiles.Batch174.profile6970,(fun _ => MergedCutProfiles.Batch174.profile6970)⟩
theorem profilesValid1038 : retention1038.ProfilesValid := by
  exact MergedCutProfiles.Batch174.valid6970
theorem numericValid1038 : retention1038.NumericValid := by decide +kernel
def certificate1038 : RatCutBinCertificate := ⟨⟨retention1038,(1103490021555746827/500000000000000000),(135240887695497653/1000000000000000000),(3473464720970437089/250000000000000000),(234731906921777485191/1000000000000000000),(988015611977342813/1000000000000000000)⟩,(61990319460155311/62500000000000000),(23574050838697271/50000000000000000),(174023378748597257/1000000000000000000),(36106592994875551/250000000000000000)⟩
theorem valid1038 : certificate1038.Valid := by decide +kernel
theorem sound1038 : certificate1038.Sound := rat_cut_bin_certificate_sound certificate1038 profilesValid1038 numericValid1038 valid1038

def retention1039 : RatCutRetentionCertificate := ⟨(21/400),(211/4000),(8396501771760633435/16870065927358992572),(8231057515695160703/1000000000000000000),(21/20),(13109168627545829924372583042918718387151/13169692025112257124800000000000000000000),false,MergedCutProfiles.Batch174.profile6971,(fun _ => MergedCutProfiles.Batch174.profile6971)⟩
theorem profilesValid1039 : retention1039.ProfilesValid := by
  exact MergedCutProfiles.Batch174.valid6971
theorem numericValid1039 : retention1039.NumericValid := by decide +kernel
def certificate1039 : RatCutBinCertificate := ⟨⟨retention1039,(1103490021555746827/500000000000000000),(135240887695497653/1000000000000000000),(3473464720970437089/250000000000000000),(234731906921777485191/1000000000000000000),(194569256053919509/200000000000000000)⟩,(61990319460155311/62500000000000000),(4744716027392589/10000000000000000),(171784305400970747/1000000000000000000),(28501235095821303/200000000000000000)⟩
theorem valid1039 : certificate1039.Valid := by decide +kernel
theorem sound1039 : certificate1039.Sound := rat_cut_bin_certificate_sound certificate1039 profilesValid1039 numericValid1039 valid1039

def retention1040 : RatCutRetentionCertificate := ⟨(21/400),(211/4000),(1/2),(1679300354352126687/200000000000000000),(21/20),(532802746786867462744662001084335893351/537376113392680539840000000000000000000),false,MergedCutProfiles.Batch174.profile6972,(fun _ => MergedCutProfiles.Batch174.profile6972)⟩
theorem profilesValid1040 : retention1040.ProfilesValid := by
  exact MergedCutProfiles.Batch174.valid6972
theorem numericValid1040 : retention1040.NumericValid := by decide +kernel
def certificate1040 : RatCutBinCertificate := ⟨⟨retention1040,(1103490021555746827/500000000000000000),(135240887695497653/1000000000000000000),(3473464720970437089/250000000000000000),(234731906921777485191/1000000000000000000),(484465708535997187/500000000000000000)⟩,(61990319460155311/62500000000000000),(118940968552073947/250000000000000000),(85411305703422999/500000000000000000),(141463306286402721/1000000000000000000)⟩
theorem valid1040 : certificate1040.Valid := by decide +kernel
theorem sound1040 : certificate1040.Sound := rat_cut_bin_certificate_sound certificate1040 profilesValid1040 numericValid1040 valid1040

def retention1041 : RatCutRetentionCertificate := ⟨(21/400),(211/4000),(1/2),64,1,(10215907763277447380914566952156895959/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch174.profile6972,(fun _ => MergedCutProfiles.Batch174.profile6972)⟩
theorem profilesValid1041 : retention1041.ProfilesValid := by
  exact MergedCutProfiles.Batch174.valid6972
theorem numericValid1041 : retention1041.NumericValid := by decide +kernel
def certificate1041 : RatCutBinCertificate := ⟨⟨retention1041,(1103490021555746827/500000000000000000),(135240887695497653/1000000000000000000),(3473464720970437089/250000000000000000),(234731906921777485191/1000000000000000000),(122020576586396293/125000000000000000)⟩,(61990319460155311/62500000000000000),(8908661958951729/20000000000000000),(97170586122221181/500000000000000000),(9266059453141149/50000000000000000)⟩
theorem valid1041 : certificate1041.Valid := by decide +kernel
theorem sound1041 : certificate1041.Sound := rat_cut_bin_certificate_sound certificate1041 profilesValid1041 numericValid1041 valid1041

def retention1042 : RatCutRetentionCertificate := ⟨(21/400),(211/4000),(3830917198390243683/8435032963679496286),(741143783834817013/200000000000000000),(6/5),(287343143356422224245463835311330131/264694208512434647500000000000000000),false,MergedCutProfiles.Batch174.profile6973,(fun _ => MergedCutProfiles.Batch174.profile6973)⟩
theorem profilesValid1042 : retention1042.ProfilesValid := by
  exact MergedCutProfiles.Batch174.valid6973
theorem numericValid1042 : retention1042.NumericValid := by decide +kernel
def certificate1042 : RatCutBinCertificate := ⟨⟨retention1042,(1282358131055746827/500000000000000000),(135240887695497653/1000000000000000000),(3473464720970437089/250000000000000000),(234731906921777485191/1000000000000000000),(527802512884548441/500000000000000000)⟩,(247630331440919763/250000000000000000),(379073017829512699/1000000000000000000),(10128544964855019/40000000000000000),(184027483688909249/1000000000000000000)⟩
theorem valid1042 : certificate1042.Valid := by decide +kernel
theorem sound1042 : certificate1042.Sound := rat_cut_bin_certificate_sound certificate1042 profilesValid1042 numericValid1042 valid1042

def retention1043 : RatCutRetentionCertificate := ⟨(21/400),(211/4000),(8379635441505283145/16870065927358992572),(3830917198390243683/500000000000000000),(21/20),(3050630822308895644611831818665064953151/3064733758712194946400000000000000000000),false,MergedCutProfiles.Batch174.profile6974,(fun _ => MergedCutProfiles.Batch174.profile6974)⟩
theorem profilesValid1043 : retention1043.ProfilesValid := by
  exact MergedCutProfiles.Batch174.valid6974
theorem numericValid1043 : retention1043.NumericValid := by decide +kernel
def certificate1043 : RatCutBinCertificate := ⟨⟨retention1043,(1282358131055746827/500000000000000000),(135240887695497653/1000000000000000000),(3473464720970437089/250000000000000000),(234731906921777485191/1000000000000000000),(484591809089478677/500000000000000000)⟩,(247630331440919763/250000000000000000),(206437343372638967/500000000000000000),(110945426704021949/500000000000000000),(90945741443335221/500000000000000000)⟩
theorem valid1043 : certificate1043.Valid := by decide +kernel
theorem sound1043 : certificate1043.Sound := rat_cut_bin_certificate_sound certificate1043 profilesValid1043 numericValid1043 valid1043

def certificates : List RatCutBinCertificate := [certificate1032,certificate1033,certificate1034,certificate1035,certificate1036,certificate1037,certificate1038,certificate1039,certificate1040,certificate1041,certificate1042,certificate1043]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1032,List.forall_mem_cons.mpr ⟨sound1033,List.forall_mem_cons.mpr ⟨sound1034,List.forall_mem_cons.mpr ⟨sound1035,List.forall_mem_cons.mpr ⟨sound1036,List.forall_mem_cons.mpr ⟨sound1037,List.forall_mem_cons.mpr ⟨sound1038,List.forall_mem_cons.mpr ⟨sound1039,List.forall_mem_cons.mpr ⟨sound1040,List.forall_mem_cons.mpr ⟨sound1041,List.forall_mem_cons.mpr ⟨sound1042,List.forall_mem_cons.mpr ⟨sound1043,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch086
