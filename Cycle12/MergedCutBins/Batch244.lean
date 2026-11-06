import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch028
import Cycle12.MergedCutProfiles.Batch029
import Cycle12.MergedCutProfiles.Batch030
import Cycle12.MergedCutProfiles.Batch031
import Cycle12.MergedCutProfiles.Batch323
import Cycle12.MergedCutProfiles.Batch324
import Cycle12.MergedCutProfiles.Batch325
import Cycle12.MergedCutProfiles.Batch457
import Cycle12.MergedCutProfiles.Batch458

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch244

def retention2928 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(1/2),64,1,(15960748357185807596877500066049185271/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch028.profile1132,(fun _ => MergedCutProfiles.Batch028.profile1132)⟩
theorem profilesValid2928 : retention2928.ProfilesValid := by
  exact MergedCutProfiles.Batch028.valid1132
theorem numericValid2928 : retention2928.NumericValid := by decide +kernel
def certificate2928 : RatCutBinCertificate := ⟨⟨retention2928,(10108927032895587/5000000000000000),(10247703429141591/500000000000000000),(8659647871970517101/1000000000000000000),(4967120072758941344351/1000000000000000000),(49638083407609617/50000000000000000)⟩,(499800268223694363/500000000000000000),(137503307461482377/1000000000000000000),(36769906882465787/62500000000000000),(574907007909006127/1000000000000000000)⟩
theorem valid2928 : certificate2928.Valid := by decide +kernel
theorem sound2928 : certificate2928.Sound := rat_cut_bin_certificate_sound certificate2928 profilesValid2928 numericValid2928 valid2928

def retention2929 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(616567978518404689/519757480355241421102),(30220957676620169/50000000000000000),4,(1365546371613293775754478869007767999/604419153532403380000000000000000000),true,MergedCutProfiles.Batch457.profile18312,![MergedCutProfiles.Batch457.profile18312,MergedCutProfiles.Batch457.profile18313,MergedCutProfiles.Batch457.profile18314,MergedCutProfiles.Batch457.profile18315,MergedCutProfiles.Batch457.profile18316,MergedCutProfiles.Batch457.profile18317,MergedCutProfiles.Batch457.profile18318,MergedCutProfiles.Batch323.profile12936,MergedCutProfiles.Batch323.profile12945,MergedCutProfiles.Batch457.profile18319,MergedCutProfiles.Batch028.profile1136,MergedCutProfiles.Batch458.profile18320,MergedCutProfiles.Batch029.profile1192,MergedCutProfiles.Batch458.profile18321,MergedCutProfiles.Batch458.profile18322,MergedCutProfiles.Batch324.profile12963]⟩
theorem profilesValid2929 : retention2929.ProfilesValid := by
  change ∀ j : Fin 16, (retention2929.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch457.valid18312
  · exact MergedCutProfiles.Batch457.valid18313
  · exact MergedCutProfiles.Batch457.valid18314
  · exact MergedCutProfiles.Batch457.valid18315
  · exact MergedCutProfiles.Batch457.valid18316
  · exact MergedCutProfiles.Batch457.valid18317
  · exact MergedCutProfiles.Batch457.valid18318
  · exact MergedCutProfiles.Batch323.valid12936
  · exact MergedCutProfiles.Batch323.valid12945
  · exact MergedCutProfiles.Batch457.valid18319
  · exact MergedCutProfiles.Batch028.valid1136
  · exact MergedCutProfiles.Batch458.valid18320
  · exact MergedCutProfiles.Batch029.valid1192
  · exact MergedCutProfiles.Batch458.valid18321
  · exact MergedCutProfiles.Batch458.valid18322
  · exact MergedCutProfiles.Batch324.valid12963
theorem numericValid2929 : retention2929.NumericValid := by decide +kernel
def certificate2929 : RatCutBinCertificate := ⟨⟨retention2929,(1873308559233745563/1000000000000000000),(702642711920787/31250000000000000),(175514033116750683/20000000000000000),(572921868759744189203/125000000000000000),(2240071767854887161/1000000000000000000)⟩,(62474978458217451/62500000000000000),(577133722723089451/1000000000000000000),(52813334410733197/500000000000000000),(24002536630208591/500000000000000000)⟩
theorem valid2929 : certificate2929.Valid := by decide +kernel
theorem sound2929 : certificate2929.Sound := rat_cut_bin_certificate_sound certificate2929 profilesValid2929 numericValid2929 valid2929

def retention2930 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(602954831000000000/259878740177620710551),(616567978518404689/1000000000000000000),4,(28536081969252290326576545389378787/12583019969763361000000000000000000),true,MergedCutProfiles.Batch457.profile18313,![MergedCutProfiles.Batch457.profile18313,MergedCutProfiles.Batch458.profile18323,MergedCutProfiles.Batch458.profile18324,MergedCutProfiles.Batch323.profile12936,MergedCutProfiles.Batch457.profile18319,MergedCutProfiles.Batch458.profile18325,MergedCutProfiles.Batch458.profile18321,MergedCutProfiles.Batch323.profile12938,MergedCutProfiles.Batch458.profile18326,MergedCutProfiles.Batch323.profile12959,MergedCutProfiles.Batch028.profile1153,MergedCutProfiles.Batch323.profile12940,MergedCutProfiles.Batch458.profile18327,MergedCutProfiles.Batch028.profile1139,MergedCutProfiles.Batch458.profile18328,MergedCutProfiles.Batch323.profile12941]⟩
theorem profilesValid2930 : retention2930.ProfilesValid := by
  change ∀ j : Fin 16, (retention2930.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch457.valid18313
  · exact MergedCutProfiles.Batch458.valid18323
  · exact MergedCutProfiles.Batch458.valid18324
  · exact MergedCutProfiles.Batch323.valid12936
  · exact MergedCutProfiles.Batch457.valid18319
  · exact MergedCutProfiles.Batch458.valid18325
  · exact MergedCutProfiles.Batch458.valid18321
  · exact MergedCutProfiles.Batch323.valid12938
  · exact MergedCutProfiles.Batch458.valid18326
  · exact MergedCutProfiles.Batch323.valid12959
  · exact MergedCutProfiles.Batch028.valid1153
  · exact MergedCutProfiles.Batch323.valid12940
  · exact MergedCutProfiles.Batch458.valid18327
  · exact MergedCutProfiles.Batch028.valid1139
  · exact MergedCutProfiles.Batch458.valid18328
  · exact MergedCutProfiles.Batch323.valid12941
theorem numericValid2930 : retention2930.NumericValid := by decide +kernel
def certificate2930 : RatCutBinCertificate := ⟨⟨retention2930,(1873308559233745563/1000000000000000000),(702642711920787/31250000000000000),(175514033116750683/20000000000000000),(572921868759744189203/125000000000000000),(1124312917010302471/500000000000000000)⟩,(62474978458217451/62500000000000000),(141888584733935759/250000000000000000),(27743054842222921/250000000000000000),(12694898426988201/250000000000000000)⟩
theorem valid2930 : certificate2930.Valid := by decide +kernel
theorem sound2930 : certificate2930.Sound := rat_cut_bin_certificate_sound certificate2930 profilesValid2930 numericValid2930 valid2930

def retention2931 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(1212926216465372437/519757480355241421102),(602954831/500000000),(51/20),(18555898154743590057/8000000000000000000),true,MergedCutProfiles.Batch457.profile18313,![MergedCutProfiles.Batch457.profile18313,MergedCutProfiles.Batch458.profile18323,MergedCutProfiles.Batch458.profile18324,MergedCutProfiles.Batch323.profile12936,MergedCutProfiles.Batch457.profile18319,MergedCutProfiles.Batch458.profile18325,MergedCutProfiles.Batch458.profile18321,MergedCutProfiles.Batch323.profile12938,MergedCutProfiles.Batch323.profile12947,MergedCutProfiles.Batch458.profile18329,MergedCutProfiles.Batch028.profile1138,MergedCutProfiles.Batch323.profile12940,MergedCutProfiles.Batch458.profile18330,MergedCutProfiles.Batch028.profile1139,MergedCutProfiles.Batch458.profile18328,MergedCutProfiles.Batch323.profile12941]⟩
theorem profilesValid2931 : retention2931.ProfilesValid := by
  change ∀ j : Fin 16, (retention2931.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch457.valid18313
  · exact MergedCutProfiles.Batch458.valid18323
  · exact MergedCutProfiles.Batch458.valid18324
  · exact MergedCutProfiles.Batch323.valid12936
  · exact MergedCutProfiles.Batch457.valid18319
  · exact MergedCutProfiles.Batch458.valid18325
  · exact MergedCutProfiles.Batch458.valid18321
  · exact MergedCutProfiles.Batch323.valid12938
  · exact MergedCutProfiles.Batch323.valid12947
  · exact MergedCutProfiles.Batch458.valid18329
  · exact MergedCutProfiles.Batch028.valid1138
  · exact MergedCutProfiles.Batch323.valid12940
  · exact MergedCutProfiles.Batch458.valid18330
  · exact MergedCutProfiles.Batch028.valid1139
  · exact MergedCutProfiles.Batch458.valid18328
  · exact MergedCutProfiles.Batch323.valid12941
theorem numericValid2931 : retention2931.NumericValid := by decide +kernel
def certificate2931 : RatCutBinCertificate := ⟨⟨retention2931,(1873308559233745563/1000000000000000000),(702642711920787/31250000000000000),(175514033116750683/20000000000000000),(572921868759744189203/125000000000000000),(2307248074047117741/1000000000000000000)⟩,(62474978458217451/62500000000000000),(47270451157504653/125000000000000000),(12704839907273211/50000000000000000),(88779116073120949/500000000000000000)⟩
theorem valid2931 : certificate2931.Valid := by decide +kernel
theorem sound2931 : certificate2931.Sound := rat_cut_bin_certificate_sound certificate2931 profilesValid2931 numericValid2931 valid2931

def retention2932 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(1555495387590392539/519757480355241421102),(1212926216465372437/1000000000000000000),(5/2),(589459814854461542101/256000000000000000000),true,MergedCutProfiles.Batch323.profile12934,![MergedCutProfiles.Batch323.profile12934,MergedCutProfiles.Batch457.profile18316,MergedCutProfiles.Batch458.profile18331,MergedCutProfiles.Batch458.profile18332,MergedCutProfiles.Batch458.profile18333,MergedCutProfiles.Batch458.profile18322,MergedCutProfiles.Batch323.profile12947,MergedCutProfiles.Batch458.profile18334,MergedCutProfiles.Batch458.profile18335,MergedCutProfiles.Batch458.profile18327,MergedCutProfiles.Batch028.profile1139,MergedCutProfiles.Batch458.profile18336,MergedCutProfiles.Batch458.profile18337,MergedCutProfiles.Batch458.profile18338,MergedCutProfiles.Batch458.profile18339,MergedCutProfiles.Batch323.profile12950]⟩
theorem profilesValid2932 : retention2932.ProfilesValid := by
  change ∀ j : Fin 16, (retention2932.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch323.valid12934
  · exact MergedCutProfiles.Batch457.valid18316
  · exact MergedCutProfiles.Batch458.valid18331
  · exact MergedCutProfiles.Batch458.valid18332
  · exact MergedCutProfiles.Batch458.valid18333
  · exact MergedCutProfiles.Batch458.valid18322
  · exact MergedCutProfiles.Batch323.valid12947
  · exact MergedCutProfiles.Batch458.valid18334
  · exact MergedCutProfiles.Batch458.valid18335
  · exact MergedCutProfiles.Batch458.valid18327
  · exact MergedCutProfiles.Batch028.valid1139
  · exact MergedCutProfiles.Batch458.valid18336
  · exact MergedCutProfiles.Batch458.valid18337
  · exact MergedCutProfiles.Batch458.valid18338
  · exact MergedCutProfiles.Batch458.valid18339
  · exact MergedCutProfiles.Batch323.valid12950
theorem numericValid2932 : retention2932.NumericValid := by decide +kernel
def certificate2932 : RatCutBinCertificate := ⟨⟨retention2932,(1873308559233745563/1000000000000000000),(702642711920787/31250000000000000),(175514033116750683/20000000000000000),(572921868759744189203/125000000000000000),(143161136901937397/62500000000000000)⟩,(62474978458217451/62500000000000000),(379849090091021991/1000000000000000000),(126230832054622209/500000000000000000),(177557575069018987/1000000000000000000)⟩
theorem valid2932 : certificate2932.Valid := by decide +kernel
theorem sound2932 : certificate2932.Sound := rat_cut_bin_certificate_sound certificate2932 profilesValid2932 numericValid2932 valid2932

def retention2933 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(16337255816386249693/259878740177620710551),(1555495387590392539/1000000000000000000),(43/20),(5007596410309641441940415384366501547031/2488792620144628062400000000000000000000),false,MergedCutProfiles.Batch458.profile18340,(fun _ => MergedCutProfiles.Batch458.profile18340)⟩
theorem profilesValid2933 : retention2933.ProfilesValid := by
  exact MergedCutProfiles.Batch458.valid18340
theorem numericValid2933 : retention2933.NumericValid := by decide +kernel
def certificate2933 : RatCutBinCertificate := ⟨⟨retention2933,(1873308559233745563/1000000000000000000),(702642711920787/31250000000000000),(175514033116750683/20000000000000000),(572921868759744189203/125000000000000000),(500434801400309457/250000000000000000)⟩,(62474978458217451/62500000000000000),(12139401105557587/31250000000000000),(244223099990077543/1000000000000000000),(88892281581560231/500000000000000000)⟩
theorem valid2933 : certificate2933.Valid := by decide +kernel
theorem sound2933 : certificate2933.Sound := rat_cut_bin_certificate_sound certificate2933 profilesValid2933 numericValid2933 valid2933

def retention2934 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(32000000000000000000/259878740177620710551),(16337255816386249693/500000000000000000),1,(9451913169414281997066016175319398511/5227921861243599901760000000000000000),false,MergedCutProfiles.Batch458.profile18341,(fun _ => MergedCutProfiles.Batch458.profile18341)⟩
theorem profilesValid2934 : retention2934.ProfilesValid := by
  exact MergedCutProfiles.Batch458.valid18341
theorem numericValid2934 : retention2934.NumericValid := by decide +kernel
def certificate2934 : RatCutBinCertificate := ⟨⟨retention2934,(1873308559233745563/1000000000000000000),(702642711920787/31250000000000000),(175514033116750683/20000000000000000),(572921868759744189203/125000000000000000),(225395986223606937/125000000000000000)⟩,(62474978458217451/62500000000000000),(6457450229585251/25000000000000000),(97997625895574721/250000000000000000),(133917110396648083/200000000000000000)⟩
theorem valid2934 : certificate2934.Valid := by decide +kernel
theorem sound2934 : certificate2934.Sound := rat_cut_bin_certificate_sound certificate2934 profilesValid2934 numericValid2934 valid2934

def retention2935 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(1/2),64,1,(255372377798511361897078253271756735919/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch030.profile1208,(fun _ => MergedCutProfiles.Batch030.profile1208)⟩
theorem profilesValid2935 : retention2935.ProfilesValid := by
  exact MergedCutProfiles.Batch030.valid1208
theorem numericValid2935 : retention2935.NumericValid := by decide +kernel
def certificate2935 : RatCutBinCertificate := ⟨⟨retention2935,(1873308559233745563/1000000000000000000),(702642711920787/31250000000000000),(175514033116750683/20000000000000000),(572921868759744189203/125000000000000000),(496374336817376293/500000000000000000)⟩,(62474978458217451/62500000000000000),(461471454151110251/1000000000000000000),(45414072554831521/250000000000000000),(177512700985230081/1000000000000000000)⟩
theorem valid2935 : certificate2935.Valid := by decide +kernel
theorem sound2935 : certificate2935.Sound := rat_cut_bin_certificate_sound certificate2935 profilesValid2935 numericValid2935 valid2935

def retention2936 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(32000000000000000000/259878740177620710551),(1767539082226980097/200000000000000000),1,(61460092284659046509023289066589408099/35350781644539601940000000000000000000),false,MergedCutProfiles.Batch458.profile18341,(fun _ => MergedCutProfiles.Batch458.profile18341)⟩
theorem profilesValid2936 : retention2936.ProfilesValid := by
  exact MergedCutProfiles.Batch458.valid18341
theorem numericValid2936 : retention2936.NumericValid := by decide +kernel
def certificate2936 : RatCutBinCertificate := ⟨⟨retention2936,(2029182414233745563/1000000000000000000),(702642711920787/31250000000000000),(175514033116750683/20000000000000000),(572921868759744189203/125000000000000000),(866689489569401083/500000000000000000)⟩,(999566343236284289/1000000000000000000),(79001306987950813/1000000000000000000),(714825150087557911/1000000000000000000),(1035417988507700071/1000000000000000000)⟩
theorem valid2936 : certificate2936.Valid := by decide +kernel
theorem sound2936 : certificate2936.Sound := rat_cut_bin_certificate_sound certificate2936 profilesValid2936 numericValid2936 valid2936

def retention2937 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(1/2),64,1,(255372377798511361897078253271756735919/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch030.profile1208,(fun _ => MergedCutProfiles.Batch030.profile1208)⟩
theorem profilesValid2937 : retention2937.ProfilesValid := by
  exact MergedCutProfiles.Batch030.valid1208
theorem numericValid2937 : retention2937.NumericValid := by decide +kernel
def certificate2937 : RatCutBinCertificate := ⟨⟨retention2937,(2029182414233745563/1000000000000000000),(702642711920787/31250000000000000),(175514033116750683/20000000000000000),(572921868759744189203/125000000000000000),(7752728930728919/7812500000000000)⟩,(999566343236284289/1000000000000000000),(2156171288820401/15625000000000000),(73419987847677037/125000000000000000),(286857850532385661/500000000000000000)⟩
theorem valid2937 : certificate2937.Valid := by decide +kernel
theorem sound2937 : certificate2937.Sound := rat_cut_bin_certificate_sound certificate2937 profilesValid2937 numericValid2937 valid2937

def retention2938 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(126122542821946739/95005518140300851637),(193922055436933/320000000000000),4,(578845448615942805209/256000000000000000000),true,MergedCutProfiles.Batch458.profile18342,![MergedCutProfiles.Batch458.profile18342,MergedCutProfiles.Batch458.profile18343,MergedCutProfiles.Batch458.profile18344,MergedCutProfiles.Batch458.profile18345,MergedCutProfiles.Batch458.profile18346,MergedCutProfiles.Batch458.profile18347,MergedCutProfiles.Batch030.profile1227,MergedCutProfiles.Batch324.profile12985,MergedCutProfiles.Batch031.profile1242,MergedCutProfiles.Batch031.profile1264,MergedCutProfiles.Batch030.profile1212,MergedCutProfiles.Batch458.profile18348,MergedCutProfiles.Batch324.profile12987,MergedCutProfiles.Batch030.profile1228,MergedCutProfiles.Batch458.profile18349,MergedCutProfiles.Batch324.profile12988]⟩
theorem profilesValid2938 : retention2938.ProfilesValid := by
  change ∀ j : Fin 16, (retention2938.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch458.valid18342
  · exact MergedCutProfiles.Batch458.valid18343
  · exact MergedCutProfiles.Batch458.valid18344
  · exact MergedCutProfiles.Batch458.valid18345
  · exact MergedCutProfiles.Batch458.valid18346
  · exact MergedCutProfiles.Batch458.valid18347
  · exact MergedCutProfiles.Batch030.valid1227
  · exact MergedCutProfiles.Batch324.valid12985
  · exact MergedCutProfiles.Batch031.valid1242
  · exact MergedCutProfiles.Batch031.valid1264
  · exact MergedCutProfiles.Batch030.valid1212
  · exact MergedCutProfiles.Batch458.valid18348
  · exact MergedCutProfiles.Batch324.valid12987
  · exact MergedCutProfiles.Batch030.valid1228
  · exact MergedCutProfiles.Batch458.valid18349
  · exact MergedCutProfiles.Batch324.valid12988
theorem numericValid2938 : retention2938.NumericValid := by decide +kernel
def certificate2938 : RatCutBinCertificate := ⟨⟨retention2938,(375986754775867947/200000000000000000),(12287303118992409/500000000000000000),(8894162574352425643/1000000000000000000),(265349954764930120907/62500000000000000),(2240337926344748909/1000000000000000000)⟩,(249891788975196571/250000000000000000),(577918513831659219/1000000000000000000),(105195817262044291/1000000000000000000),(11958899830398027/250000000000000000)⟩
theorem valid2938 : certificate2938.Valid := by decide +kernel
theorem sound2938 : certificate2938.Sound := rat_cut_bin_certificate_sound certificate2938 profilesValid2938 numericValid2938 valid2938

def retention2939 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(241721364600000000/95005518140300851637),(126122542821946739/200000000000000000),4,(29239212538179353243/12800000000000000000),true,MergedCutProfiles.Batch458.profile18350,![MergedCutProfiles.Batch458.profile18350,MergedCutProfiles.Batch458.profile18351,MergedCutProfiles.Batch458.profile18352,MergedCutProfiles.Batch458.profile18353,MergedCutProfiles.Batch325.profile13003,MergedCutProfiles.Batch458.profile18354,MergedCutProfiles.Batch458.profile18355,MergedCutProfiles.Batch458.profile18356,MergedCutProfiles.Batch458.profile18357,MergedCutProfiles.Batch325.profile13005,MergedCutProfiles.Batch030.profile1229,MergedCutProfiles.Batch324.profile12999,MergedCutProfiles.Batch458.profile18358,MergedCutProfiles.Batch031.profile1255,MergedCutProfiles.Batch324.profile12991,MergedCutProfiles.Batch458.profile18359]⟩
theorem profilesValid2939 : retention2939.ProfilesValid := by
  change ∀ j : Fin 16, (retention2939.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch458.valid18350
  · exact MergedCutProfiles.Batch458.valid18351
  · exact MergedCutProfiles.Batch458.valid18352
  · exact MergedCutProfiles.Batch458.valid18353
  · exact MergedCutProfiles.Batch325.valid13003
  · exact MergedCutProfiles.Batch458.valid18354
  · exact MergedCutProfiles.Batch458.valid18355
  · exact MergedCutProfiles.Batch458.valid18356
  · exact MergedCutProfiles.Batch458.valid18357
  · exact MergedCutProfiles.Batch325.valid13005
  · exact MergedCutProfiles.Batch030.valid1229
  · exact MergedCutProfiles.Batch324.valid12999
  · exact MergedCutProfiles.Batch458.valid18358
  · exact MergedCutProfiles.Batch031.valid1255
  · exact MergedCutProfiles.Batch324.valid12991
  · exact MergedCutProfiles.Batch458.valid18359
theorem numericValid2939 : retention2939.NumericValid := by decide +kernel
def certificate2939 : RatCutBinCertificate := ⟨⟨retention2939,(375986754775867947/200000000000000000),(12287303118992409/500000000000000000),(8894162574352425643/1000000000000000000),(265349954764930120907/62500000000000000),(2263536374169861589/1000000000000000000)⟩,(249891788975196571/250000000000000000),(22299727260920413/40000000000000000),(58380377896808539/500000000000000000),(6742341453773441/125000000000000000)⟩
theorem valid2939 : certificate2939.Valid := by decide +kernel
theorem sound2939 : certificate2939.Sound := rat_cut_bin_certificate_sound certificate2939 profilesValid2939 numericValid2939 valid2939

def certificates : List RatCutBinCertificate := [certificate2928,certificate2929,certificate2930,certificate2931,certificate2932,certificate2933,certificate2934,certificate2935,certificate2936,certificate2937,certificate2938,certificate2939]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2928,List.forall_mem_cons.mpr ⟨sound2929,List.forall_mem_cons.mpr ⟨sound2930,List.forall_mem_cons.mpr ⟨sound2931,List.forall_mem_cons.mpr ⟨sound2932,List.forall_mem_cons.mpr ⟨sound2933,List.forall_mem_cons.mpr ⟨sound2934,List.forall_mem_cons.mpr ⟨sound2935,List.forall_mem_cons.mpr ⟨sound2936,List.forall_mem_cons.mpr ⟨sound2937,List.forall_mem_cons.mpr ⟨sound2938,List.forall_mem_cons.mpr ⟨sound2939,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch244
