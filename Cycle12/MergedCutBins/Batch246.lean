import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch034
import Cycle12.MergedCutProfiles.Batch035
import Cycle12.MergedCutProfiles.Batch036
import Cycle12.MergedCutProfiles.Batch037
import Cycle12.MergedCutProfiles.Batch326
import Cycle12.MergedCutProfiles.Batch327
import Cycle12.MergedCutProfiles.Batch328
import Cycle12.MergedCutProfiles.Batch459
import Cycle12.MergedCutProfiles.Batch460
import Cycle12.MergedCutProfiles.Batch461

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch246

def retention2952 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(1/2),64,1,(255373261473046173696668873617783571559/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch034.profile1386,(fun _ => MergedCutProfiles.Batch034.profile1386)⟩
theorem profilesValid2952 : retention2952.ProfilesValid := by
  exact MergedCutProfiles.Batch034.valid1386
theorem numericValid2952 : retention2952.NumericValid := by decide +kernel
def certificate2952 : RatCutBinCertificate := ⟨⟨retention2952,(127457716028506109/62500000000000000),(5353370290855499/200000000000000000),(4507549105661741169/500000000000000000),(1973339312607329729513/500000000000000000),(495748409404240973/500000000000000000)⟩,(499747986425672961/500000000000000000),(68478786304741761/500000000000000000),(589384394899737529/1000000000000000000),(575165333078923519/1000000000000000000)⟩
theorem valid2952 : certificate2952.Valid := by decide +kernel
theorem sound2952 : certificate2952.Sound := rat_cut_bin_certificate_sound certificate2952 profilesValid2952 numericValid2952 valid2952

def retention2953 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(626225624201022631/400799388028762860370),(306943252720822777/500000000000000000),4,(290812670955907654393/128000000000000000000),true,MergedCutProfiles.Batch459.profile18390,![MergedCutProfiles.Batch459.profile18390,MergedCutProfiles.Batch459.profile18391,MergedCutProfiles.Batch459.profile18392,MergedCutProfiles.Batch459.profile18393,MergedCutProfiles.Batch327.profile13088,MergedCutProfiles.Batch459.profile18394,MergedCutProfiles.Batch035.profile1406,MergedCutProfiles.Batch326.profile13067,MergedCutProfiles.Batch459.profile18395,MergedCutProfiles.Batch459.profile18396,MergedCutProfiles.Batch034.profile1391,MergedCutProfiles.Batch459.profile18397,MergedCutProfiles.Batch459.profile18398,MergedCutProfiles.Batch035.profile1407,MergedCutProfiles.Batch459.profile18399,MergedCutProfiles.Batch460.profile18400]⟩
theorem profilesValid2953 : retention2953.ProfilesValid := by
  change ∀ j : Fin 16, (retention2953.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch459.valid18390
  · exact MergedCutProfiles.Batch459.valid18391
  · exact MergedCutProfiles.Batch459.valid18392
  · exact MergedCutProfiles.Batch459.valid18393
  · exact MergedCutProfiles.Batch327.valid13088
  · exact MergedCutProfiles.Batch459.valid18394
  · exact MergedCutProfiles.Batch035.valid1406
  · exact MergedCutProfiles.Batch326.valid13067
  · exact MergedCutProfiles.Batch459.valid18395
  · exact MergedCutProfiles.Batch459.valid18396
  · exact MergedCutProfiles.Batch034.valid1391
  · exact MergedCutProfiles.Batch459.valid18397
  · exact MergedCutProfiles.Batch459.valid18398
  · exact MergedCutProfiles.Batch035.valid1407
  · exact MergedCutProfiles.Batch459.valid18399
  · exact MergedCutProfiles.Batch460.valid18400
theorem numericValid2953 : retention2953.NumericValid := by decide +kernel
def certificate2953 : RatCutBinCertificate := ⟨⟨retention2953,(118176903611850779/62500000000000000),(14531335098101001/500000000000000000),(9138578609174856959/1000000000000000000),(3680829937447970025631/1000000000000000000),(561980225980610207/250000000000000000)⟩,(999500046389364401/1000000000000000000),(35607016696734533/62500000000000000),(10975402582139899/100000000000000000),(10032544038146801/200000000000000000)⟩
theorem valid2953 : certificate2953.Valid := by decide +kernel
theorem sound2953 : certificate2953.Sound := rat_cut_bin_certificate_sound certificate2953 profilesValid2953 numericValid2953 valid2953

def retention2954 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(119230379800000000/40079938802876286037),(626225624201022631/1000000000000000000),4,(145704232583867392511/64000000000000000000),true,MergedCutProfiles.Batch460.profile18401,![MergedCutProfiles.Batch460.profile18401,MergedCutProfiles.Batch460.profile18402,MergedCutProfiles.Batch034.profile1390,MergedCutProfiles.Batch460.profile18403,MergedCutProfiles.Batch460.profile18404,MergedCutProfiles.Batch460.profile18405,MergedCutProfiles.Batch460.profile18406,MergedCutProfiles.Batch459.profile18399,MergedCutProfiles.Batch034.profile1392,MergedCutProfiles.Batch327.profile13097,MergedCutProfiles.Batch035.profile1408,MergedCutProfiles.Batch034.profile1393,MergedCutProfiles.Batch460.profile18407,MergedCutProfiles.Batch460.profile18408,MergedCutProfiles.Batch460.profile18409,MergedCutProfiles.Batch035.profile1436]⟩
theorem profilesValid2954 : retention2954.ProfilesValid := by
  change ∀ j : Fin 16, (retention2954.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch460.valid18401
  · exact MergedCutProfiles.Batch460.valid18402
  · exact MergedCutProfiles.Batch034.valid1390
  · exact MergedCutProfiles.Batch460.valid18403
  · exact MergedCutProfiles.Batch460.valid18404
  · exact MergedCutProfiles.Batch460.valid18405
  · exact MergedCutProfiles.Batch460.valid18406
  · exact MergedCutProfiles.Batch459.valid18399
  · exact MergedCutProfiles.Batch034.valid1392
  · exact MergedCutProfiles.Batch327.valid13097
  · exact MergedCutProfiles.Batch035.valid1408
  · exact MergedCutProfiles.Batch034.valid1393
  · exact MergedCutProfiles.Batch460.valid18407
  · exact MergedCutProfiles.Batch460.valid18408
  · exact MergedCutProfiles.Batch460.valid18409
  · exact MergedCutProfiles.Batch035.valid1436
theorem numericValid2954 : retention2954.NumericValid := by decide +kernel
def certificate2954 : RatCutBinCertificate := ⟨⟨retention2954,(118176903611850779/62500000000000000),(14531335098101001/500000000000000000),(9138578609174856959/1000000000000000000),(3680829937447970025631/1000000000000000000),(2252575547726268239/1000000000000000000)⟩,(999500046389364401/1000000000000000000),(280664735768142251/500000000000000000),(5726618118108929/50000000000000000),(52628346290005407/1000000000000000000)⟩
theorem valid2954 : certificate2954.Valid := by decide +kernel
theorem sound2954 : certificate2954.Sound := rat_cut_bin_certificate_sound certificate2954 profilesValid2954 numericValid2954 valid2954

def retention2955 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(660395145808215587/200399694014381430185),(596151899/500000000),(51/20),(18452780065669906909/8000000000000000000),true,MergedCutProfiles.Batch460.profile18410,![MergedCutProfiles.Batch460.profile18410,MergedCutProfiles.Batch460.profile18411,MergedCutProfiles.Batch460.profile18412,MergedCutProfiles.Batch460.profile18413,MergedCutProfiles.Batch460.profile18414,MergedCutProfiles.Batch460.profile18415,MergedCutProfiles.Batch460.profile18416,MergedCutProfiles.Batch034.profile1392,MergedCutProfiles.Batch327.profile13097,MergedCutProfiles.Batch035.profile1408,MergedCutProfiles.Batch327.profile13081,MergedCutProfiles.Batch460.profile18417,MergedCutProfiles.Batch326.profile13074,MergedCutProfiles.Batch460.profile18418,MergedCutProfiles.Batch460.profile18419,MergedCutProfiles.Batch034.profile1395]⟩
theorem profilesValid2955 : retention2955.ProfilesValid := by
  change ∀ j : Fin 16, (retention2955.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch460.valid18410
  · exact MergedCutProfiles.Batch460.valid18411
  · exact MergedCutProfiles.Batch460.valid18412
  · exact MergedCutProfiles.Batch460.valid18413
  · exact MergedCutProfiles.Batch460.valid18414
  · exact MergedCutProfiles.Batch460.valid18415
  · exact MergedCutProfiles.Batch460.valid18416
  · exact MergedCutProfiles.Batch034.valid1392
  · exact MergedCutProfiles.Batch327.valid13097
  · exact MergedCutProfiles.Batch035.valid1408
  · exact MergedCutProfiles.Batch327.valid13081
  · exact MergedCutProfiles.Batch460.valid18417
  · exact MergedCutProfiles.Batch326.valid13074
  · exact MergedCutProfiles.Batch460.valid18418
  · exact MergedCutProfiles.Batch460.valid18419
  · exact MergedCutProfiles.Batch034.valid1395
theorem numericValid2955 : retention2955.NumericValid := by decide +kernel
def certificate2955 : RatCutBinCertificate := ⟨⟨retention2955,(118176903611850779/62500000000000000),(14531335098101001/500000000000000000),(9138578609174856959/1000000000000000000),(3680829937447970025631/1000000000000000000),(7160198981698101/3125000000000000)⟩,(999500046389364401/1000000000000000000),(192262280372467807/500000000000000000),(247964870189052943/1000000000000000000),(171881104710238761/1000000000000000000)⟩
theorem valid2955 : certificate2955.Valid := by decide +kernel
theorem sound2955 : certificate2955.Sound := rat_cut_bin_certificate_sound certificate2955 profilesValid2955 numericValid2955 valid2955

def retention2956 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(9193941914323359267/400799388028762860370),(660395145808215587/500000000000000000),(12/5),(1395054214806439821279/640000000000000000000),true,MergedCutProfiles.Batch460.profile18416,![MergedCutProfiles.Batch460.profile18416,MergedCutProfiles.Batch460.profile18418,MergedCutProfiles.Batch460.profile18420,MergedCutProfiles.Batch460.profile18421,MergedCutProfiles.Batch035.profile1402,MergedCutProfiles.Batch460.profile18422,MergedCutProfiles.Batch460.profile18423,MergedCutProfiles.Batch460.profile18424,MergedCutProfiles.Batch036.profile1443,MergedCutProfiles.Batch460.profile18425,MergedCutProfiles.Batch036.profile1446,MergedCutProfiles.Batch460.profile18426,MergedCutProfiles.Batch460.profile18427,MergedCutProfiles.Batch460.profile18428,MergedCutProfiles.Batch460.profile18429,MergedCutProfiles.Batch460.profile18430]⟩
theorem profilesValid2956 : retention2956.ProfilesValid := by
  change ∀ j : Fin 16, (retention2956.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch460.valid18416
  · exact MergedCutProfiles.Batch460.valid18418
  · exact MergedCutProfiles.Batch460.valid18420
  · exact MergedCutProfiles.Batch460.valid18421
  · exact MergedCutProfiles.Batch035.valid1402
  · exact MergedCutProfiles.Batch460.valid18422
  · exact MergedCutProfiles.Batch460.valid18423
  · exact MergedCutProfiles.Batch460.valid18424
  · exact MergedCutProfiles.Batch036.valid1443
  · exact MergedCutProfiles.Batch460.valid18425
  · exact MergedCutProfiles.Batch036.valid1446
  · exact MergedCutProfiles.Batch460.valid18426
  · exact MergedCutProfiles.Batch460.valid18427
  · exact MergedCutProfiles.Batch460.valid18428
  · exact MergedCutProfiles.Batch460.valid18429
  · exact MergedCutProfiles.Batch460.valid18430
theorem numericValid2956 : retention2956.NumericValid := by decide +kernel
def certificate2956 : RatCutBinCertificate := ⟨⟨retention2956,(118176903611850779/62500000000000000),(14531335098101001/500000000000000000),(9138578609174856959/1000000000000000000),(3680829937447970025631/1000000000000000000),(43306807366804603/20000000000000000)⟩,(999500046389364401/1000000000000000000),(3102655532675909/8000000000000000),(48963646405997947/200000000000000000),(42961163006778767/250000000000000000)⟩
theorem valid2956 : certificate2956.Valid := by decide +kernel
theorem sound2956 : certificate2956.Sound := rat_cut_bin_certificate_sound certificate2956 profilesValid2956 numericValid2956 valid2956

def retention2957 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(6400000000000000000/40079938802876286037),(9193941914323359267/1000000000000000000),(21/20),(24916252125488971040774721720442824856871/14710307062917374827200000000000000000000),false,MergedCutProfiles.Batch460.profile18431,(fun _ => MergedCutProfiles.Batch460.profile18431)⟩
theorem profilesValid2957 : retention2957.ProfilesValid := by
  exact MergedCutProfiles.Batch460.valid18431
theorem numericValid2957 : retention2957.NumericValid := by decide +kernel
def certificate2957 : RatCutBinCertificate := ⟨⟨retention2957,(118176903611850779/62500000000000000),(14531335098101001/500000000000000000),(9138578609174856959/1000000000000000000),(3680829937447970025631/1000000000000000000),(210935199303250373/125000000000000000)⟩,(999500046389364401/1000000000000000000),(303365210055128439/1000000000000000000),(334754317425873319/1000000000000000000),(460968393259835939/1000000000000000000)⟩
theorem valid2957 : certificate2957.Valid := by decide +kernel
theorem sound2957 : certificate2957.Sound := rat_cut_bin_certificate_sound certificate2957 profilesValid2957 numericValid2957 valid2957

def retention2958 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(1/2),64,1,(255373741328073457130936126923517436199/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch036.profile1465,(fun _ => MergedCutProfiles.Batch036.profile1465)⟩
theorem profilesValid2958 : retention2958.ProfilesValid := by
  exact MergedCutProfiles.Batch036.valid1465
theorem numericValid2958 : retention2958.NumericValid := by decide +kernel
def certificate2958 : RatCutBinCertificate := ⟨⟨retention2958,(118176903611850779/62500000000000000),(14531335098101001/500000000000000000),(9138578609174856959/1000000000000000000),(3680829937447970025631/1000000000000000000),(495770211838047203/500000000000000000)⟩,(999500046389364401/1000000000000000000),(468788096913583491/1000000000000000000),(176055813887175681/1000000000000000000),(85908254081130869/500000000000000000)⟩
theorem valid2958 : certificate2958.Valid := by decide +kernel
theorem sound2958 : certificate2958.Sound := rat_cut_bin_certificate_sound certificate2958 profilesValid2958 numericValid2958 valid2958

def retention2959 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(6400000000000000000/40079938802876286037),(914788242912512049/100000000000000000),1,(15145892006704015392353961407375827979/9147882429125120490000000000000000000),false,MergedCutProfiles.Batch460.profile18431,(fun _ => MergedCutProfiles.Batch460.profile18431)⟩
theorem profilesValid2959 : retention2959.ProfilesValid := by
  exact MergedCutProfiles.Batch460.valid18431
theorem numericValid2959 : retention2959.NumericValid := by decide +kernel
def certificate2959 : RatCutBinCertificate := ⟨⟨retention2959,(127684079486850779/62500000000000000),(14531335098101001/500000000000000000),(9138578609174856959/1000000000000000000),(3680829937447970025631/1000000000000000000),(412293724274671669/250000000000000000)⟩,(499729912591953707/500000000000000000),(16282186066682919/200000000000000000),(709073473109429569/1000000000000000000),(990209780434196809/1000000000000000000)⟩
theorem valid2959 : certificate2959.Valid := by decide +kernel
theorem sound2959 : certificate2959.Sound := rat_cut_bin_certificate_sound certificate2959 profilesValid2959 numericValid2959 valid2959

def retention2960 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(1/2),64,1,(255373741328073457130936126923517436199/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch036.profile1465,(fun _ => MergedCutProfiles.Batch036.profile1465)⟩
theorem profilesValid2960 : retention2960.ProfilesValid := by
  exact MergedCutProfiles.Batch036.valid1465
theorem numericValid2960 : retention2960.NumericValid := by decide +kernel
def certificate2960 : RatCutBinCertificate := ⟨⟨retention2960,(127684079486850779/62500000000000000),(14531335098101001/500000000000000000),(9138578609174856959/1000000000000000000),(3680829937447970025631/1000000000000000000),(991056665380006401/1000000000000000000)⟩,(499729912591953707/500000000000000000),(135472438000138943/1000000000000000000),(592294856959746941/1000000000000000000),(577731831546565303/1000000000000000000)⟩
theorem valid2960 : certificate2960.Valid := by decide +kernel
theorem sound2960 : certificate2960.Sound := rat_cut_bin_certificate_sound certificate2960 profilesValid2960 numericValid2960 valid2960

def retention2961 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(630502877515275067/369822667834612896403),(618079479967919877/1000000000000000000),4,(583059748884727917381/256000000000000000000),true,MergedCutProfiles.Batch460.profile18432,![MergedCutProfiles.Batch460.profile18432,MergedCutProfiles.Batch460.profile18433,MergedCutProfiles.Batch460.profile18434,MergedCutProfiles.Batch460.profile18435,MergedCutProfiles.Batch460.profile18436,MergedCutProfiles.Batch460.profile18437,MergedCutProfiles.Batch037.profile1484,MergedCutProfiles.Batch327.profile13112,MergedCutProfiles.Batch328.profile13131,MergedCutProfiles.Batch460.profile18438,MergedCutProfiles.Batch036.profile1469,MergedCutProfiles.Batch460.profile18439,MergedCutProfiles.Batch461.profile18440,MergedCutProfiles.Batch461.profile18441,MergedCutProfiles.Batch328.profile13126,MergedCutProfiles.Batch327.profile13115]⟩
theorem profilesValid2961 : retention2961.ProfilesValid := by
  change ∀ j : Fin 16, (retention2961.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch460.valid18432
  · exact MergedCutProfiles.Batch460.valid18433
  · exact MergedCutProfiles.Batch460.valid18434
  · exact MergedCutProfiles.Batch460.valid18435
  · exact MergedCutProfiles.Batch460.valid18436
  · exact MergedCutProfiles.Batch460.valid18437
  · exact MergedCutProfiles.Batch037.valid1484
  · exact MergedCutProfiles.Batch327.valid13112
  · exact MergedCutProfiles.Batch328.valid13131
  · exact MergedCutProfiles.Batch460.valid18438
  · exact MergedCutProfiles.Batch036.valid1469
  · exact MergedCutProfiles.Batch460.valid18439
  · exact MergedCutProfiles.Batch461.valid18440
  · exact MergedCutProfiles.Batch461.valid18441
  · exact MergedCutProfiles.Batch328.valid13126
  · exact MergedCutProfiles.Batch327.valid13115
theorem numericValid2961 : retention2961.NumericValid := by decide +kernel
def certificate2961 : RatCutBinCertificate := ⟨⟨retention2961,(1896245715664698419/1000000000000000000),(31463473579235007/1000000000000000000),(4632338185813076749/500000000000000000),(3443312750537497668733/1000000000000000000),(450363585829712069/200000000000000000)⟩,(249866323117012463/250000000000000000),(35341181956217007/62500000000000000),(28040745388888227/250000000000000000),(25699478505266813/500000000000000000)⟩
theorem valid2961 : certificate2961.Valid := by decide +kernel
theorem sound2961 : certificate2961.Sound := rat_cut_bin_certificate_sound certificate2961 profilesValid2961 numericValid2961 valid2961

def retention2962 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(1203516655000000000/369822667834612896403),(630502877515275067/1000000000000000000),4,(145967546607720277187/64000000000000000000),true,MergedCutProfiles.Batch460.profile18433,![MergedCutProfiles.Batch460.profile18433,MergedCutProfiles.Batch461.profile18442,MergedCutProfiles.Batch461.profile18443,MergedCutProfiles.Batch461.profile18444,MergedCutProfiles.Batch461.profile18445,MergedCutProfiles.Batch461.profile18446,MergedCutProfiles.Batch327.profile13114,MergedCutProfiles.Batch461.profile18447,MergedCutProfiles.Batch037.profile1501,MergedCutProfiles.Batch328.profile13150,MergedCutProfiles.Batch037.profile1486,MergedCutProfiles.Batch328.profile13133,MergedCutProfiles.Batch461.profile18448,MergedCutProfiles.Batch327.profile13119,MergedCutProfiles.Batch461.profile18449,MergedCutProfiles.Batch461.profile18450]⟩
theorem profilesValid2962 : retention2962.ProfilesValid := by
  change ∀ j : Fin 16, (retention2962.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch460.valid18433
  · exact MergedCutProfiles.Batch461.valid18442
  · exact MergedCutProfiles.Batch461.valid18443
  · exact MergedCutProfiles.Batch461.valid18444
  · exact MergedCutProfiles.Batch461.valid18445
  · exact MergedCutProfiles.Batch461.valid18446
  · exact MergedCutProfiles.Batch327.valid13114
  · exact MergedCutProfiles.Batch461.valid18447
  · exact MergedCutProfiles.Batch037.valid1501
  · exact MergedCutProfiles.Batch328.valid13150
  · exact MergedCutProfiles.Batch037.valid1486
  · exact MergedCutProfiles.Batch328.valid13133
  · exact MergedCutProfiles.Batch461.valid18448
  · exact MergedCutProfiles.Batch327.valid13119
  · exact MergedCutProfiles.Batch461.valid18449
  · exact MergedCutProfiles.Batch461.valid18450
theorem numericValid2962 : retention2962.NumericValid := by decide +kernel
def certificate2962 : RatCutBinCertificate := ⟨⟨retention2962,(1896245715664698419/1000000000000000000),(31463473579235007/1000000000000000000),(4632338185813076749/500000000000000000),(3443312750537497668733/1000000000000000000),(2254983702689123511/1000000000000000000)⟩,(249866323117012463/250000000000000000),(278773341949541567/500000000000000000),(5836474833352337/50000000000000000),(53749551746993713/1000000000000000000)⟩
theorem valid2962 : certificate2962.Valid := by decide +kernel
theorem sound2962 : certificate2962.Sound := rat_cut_bin_certificate_sound certificate2962 profilesValid2962 numericValid2962 valid2962

def retention2963 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(2019704371773296052/369822667834612896403),(240703331/200000000),(51/20),(36642654309762018549/16000000000000000000),true,MergedCutProfiles.Batch461.profile18451,![MergedCutProfiles.Batch461.profile18451,MergedCutProfiles.Batch328.profile13148,MergedCutProfiles.Batch461.profile18445,MergedCutProfiles.Batch328.profile13149,MergedCutProfiles.Batch327.profile13115,MergedCutProfiles.Batch328.profile13150,MergedCutProfiles.Batch461.profile18452,MergedCutProfiles.Batch037.profile1502,MergedCutProfiles.Batch461.profile18449,MergedCutProfiles.Batch328.profile13121,MergedCutProfiles.Batch461.profile18453,MergedCutProfiles.Batch461.profile18454,MergedCutProfiles.Batch037.profile1514,MergedCutProfiles.Batch036.profile1475,MergedCutProfiles.Batch037.profile1490,MergedCutProfiles.Batch037.profile1504]⟩
theorem profilesValid2963 : retention2963.ProfilesValid := by
  change ∀ j : Fin 16, (retention2963.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch461.valid18451
  · exact MergedCutProfiles.Batch328.valid13148
  · exact MergedCutProfiles.Batch461.valid18445
  · exact MergedCutProfiles.Batch328.valid13149
  · exact MergedCutProfiles.Batch327.valid13115
  · exact MergedCutProfiles.Batch328.valid13150
  · exact MergedCutProfiles.Batch461.valid18452
  · exact MergedCutProfiles.Batch037.valid1502
  · exact MergedCutProfiles.Batch461.valid18449
  · exact MergedCutProfiles.Batch328.valid13121
  · exact MergedCutProfiles.Batch461.valid18453
  · exact MergedCutProfiles.Batch461.valid18454
  · exact MergedCutProfiles.Batch037.valid1514
  · exact MergedCutProfiles.Batch036.valid1475
  · exact MergedCutProfiles.Batch037.valid1490
  · exact MergedCutProfiles.Batch037.valid1504
theorem numericValid2963 : retention2963.NumericValid := by decide +kernel
def certificate2963 : RatCutBinCertificate := ⟨⟨retention2963,(1896245715664698419/1000000000000000000),(31463473579235007/1000000000000000000),(4632338185813076749/500000000000000000),(3443312750537497668733/1000000000000000000),(454748881328045997/200000000000000000)⟩,(249866323117012463/250000000000000000),(192860952151867343/500000000000000000),(123411224379939291/500000000000000000),(170431071225901931/1000000000000000000)⟩
theorem valid2963 : certificate2963.Valid := by decide +kernel
theorem sound2963 : certificate2963.Sound := rat_cut_bin_certificate_sound certificate2963 profilesValid2963 numericValid2963 valid2963

def certificates : List RatCutBinCertificate := [certificate2952,certificate2953,certificate2954,certificate2955,certificate2956,certificate2957,certificate2958,certificate2959,certificate2960,certificate2961,certificate2962,certificate2963]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2952,List.forall_mem_cons.mpr ⟨sound2953,List.forall_mem_cons.mpr ⟨sound2954,List.forall_mem_cons.mpr ⟨sound2955,List.forall_mem_cons.mpr ⟨sound2956,List.forall_mem_cons.mpr ⟨sound2957,List.forall_mem_cons.mpr ⟨sound2958,List.forall_mem_cons.mpr ⟨sound2959,List.forall_mem_cons.mpr ⟨sound2960,List.forall_mem_cons.mpr ⟨sound2961,List.forall_mem_cons.mpr ⟨sound2962,List.forall_mem_cons.mpr ⟨sound2963,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch246
