import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch376
import Cycle12.MergedCutProfiles.Batch377
import Cycle12.MergedCutProfiles.Batch378

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch202

def retention2424 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(42488639541942520/1519308069253587679),(496550383/500000000),(53/20),(428712289147832233/200000000000000000),true,MergedCutProfiles.Batch376.profile15065,![MergedCutProfiles.Batch376.profile15065,MergedCutProfiles.Batch376.profile15066,MergedCutProfiles.Batch376.profile15067,MergedCutProfiles.Batch376.profile15068,MergedCutProfiles.Batch376.profile15069,MergedCutProfiles.Batch376.profile15070,MergedCutProfiles.Batch376.profile15071,MergedCutProfiles.Batch376.profile15072,MergedCutProfiles.Batch376.profile15073,MergedCutProfiles.Batch376.profile15074,MergedCutProfiles.Batch376.profile15075,MergedCutProfiles.Batch376.profile15047,MergedCutProfiles.Batch376.profile15076,MergedCutProfiles.Batch376.profile15077,MergedCutProfiles.Batch376.profile15078,MergedCutProfiles.Batch376.profile15079]⟩
theorem profilesValid2424 : retention2424.ProfilesValid := by
  change ∀ j : Fin 16, (retention2424.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch376.valid15065
  · exact MergedCutProfiles.Batch376.valid15066
  · exact MergedCutProfiles.Batch376.valid15067
  · exact MergedCutProfiles.Batch376.valid15068
  · exact MergedCutProfiles.Batch376.valid15069
  · exact MergedCutProfiles.Batch376.valid15070
  · exact MergedCutProfiles.Batch376.valid15071
  · exact MergedCutProfiles.Batch376.valid15072
  · exact MergedCutProfiles.Batch376.valid15073
  · exact MergedCutProfiles.Batch376.valid15074
  · exact MergedCutProfiles.Batch376.valid15075
  · exact MergedCutProfiles.Batch376.valid15047
  · exact MergedCutProfiles.Batch376.valid15076
  · exact MergedCutProfiles.Batch376.valid15077
  · exact MergedCutProfiles.Batch376.valid15078
  · exact MergedCutProfiles.Batch376.valid15079
theorem numericValid2424 : retention2424.NumericValid := by decide +kernel
def certificate2424 : RatCutBinCertificate := ⟨⟨retention2424,(431113381787465781/200000000000000000),(31307344283847009/250000000000000000),(13322007802705716331/1000000000000000000),(244282304990708490629/500000000000000000),(2089859970608103689/1000000000000000000)⟩,(249028534861385659/250000000000000000),(171079069456424773/500000000000000000),(29087607835211501/100000000000000000),(87848540745666257/500000000000000000)⟩
theorem valid2424 : certificate2424.Valid := by decide +kernel
theorem sound2424 : certificate2424.Sound := rat_cut_bin_certificate_sound certificate2424 profilesValid2424 numericValid2424 valid2424

def retention2425 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(444672123743085031/12154464554028701432),(3186647965645689/3125000000000000),(13/5),(33788138259569622721/16000000000000000000),true,MergedCutProfiles.Batch377.profile15080,![MergedCutProfiles.Batch377.profile15080,MergedCutProfiles.Batch377.profile15081,MergedCutProfiles.Batch377.profile15082,MergedCutProfiles.Batch377.profile15083,MergedCutProfiles.Batch377.profile15084,MergedCutProfiles.Batch377.profile15085,MergedCutProfiles.Batch377.profile15086,MergedCutProfiles.Batch377.profile15087,MergedCutProfiles.Batch377.profile15088,MergedCutProfiles.Batch377.profile15089,MergedCutProfiles.Batch377.profile15090,MergedCutProfiles.Batch377.profile15091,MergedCutProfiles.Batch377.profile15092,MergedCutProfiles.Batch377.profile15093,MergedCutProfiles.Batch377.profile15094,MergedCutProfiles.Batch377.profile15095]⟩
theorem profilesValid2425 : retention2425.ProfilesValid := by
  change ∀ j : Fin 16, (retention2425.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch377.valid15080
  · exact MergedCutProfiles.Batch377.valid15081
  · exact MergedCutProfiles.Batch377.valid15082
  · exact MergedCutProfiles.Batch377.valid15083
  · exact MergedCutProfiles.Batch377.valid15084
  · exact MergedCutProfiles.Batch377.valid15085
  · exact MergedCutProfiles.Batch377.valid15086
  · exact MergedCutProfiles.Batch377.valid15087
  · exact MergedCutProfiles.Batch377.valid15088
  · exact MergedCutProfiles.Batch377.valid15089
  · exact MergedCutProfiles.Batch377.valid15090
  · exact MergedCutProfiles.Batch377.valid15091
  · exact MergedCutProfiles.Batch377.valid15092
  · exact MergedCutProfiles.Batch377.valid15093
  · exact MergedCutProfiles.Batch377.valid15094
  · exact MergedCutProfiles.Batch377.valid15095
theorem numericValid2425 : retention2425.NumericValid := by decide +kernel
def certificate2425 : RatCutBinCertificate := ⟨⟨retention2425,(431113381787465781/200000000000000000),(31307344283847009/250000000000000000),(13322007802705716331/1000000000000000000),(244282304990708490629/500000000000000000),(1029535219677260631/500000000000000000)⟩,(249028534861385659/250000000000000000),(343500180414937483/1000000000000000000),(144719829702453057/500000000000000000),(17569668033964811/100000000000000000)⟩
theorem valid2425 : certificate2425.Valid := by decide +kernel
theorem sound2425 : certificate2425.Sound := rat_cut_bin_certificate_sound certificate2425 profilesValid2425 numericValid2425 valid2425

def retention2426 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(212437692334752079/1657426984640277468),(1334016371229255093/1000000000000000000),(21/10),(2327082859665073742049/1280000000000000000000),true,MergedCutProfiles.Batch376.profile15040,![MergedCutProfiles.Batch376.profile15040,MergedCutProfiles.Batch377.profile15086,MergedCutProfiles.Batch377.profile15096,MergedCutProfiles.Batch377.profile15093,MergedCutProfiles.Batch377.profile15097,MergedCutProfiles.Batch377.profile15098,MergedCutProfiles.Batch377.profile15099,MergedCutProfiles.Batch377.profile15100,MergedCutProfiles.Batch377.profile15101,MergedCutProfiles.Batch377.profile15102,MergedCutProfiles.Batch377.profile15103,MergedCutProfiles.Batch377.profile15104,MergedCutProfiles.Batch377.profile15105,MergedCutProfiles.Batch377.profile15106,MergedCutProfiles.Batch377.profile15107,MergedCutProfiles.Batch377.profile15108]⟩
theorem profilesValid2426 : retention2426.ProfilesValid := by
  change ∀ j : Fin 16, (retention2426.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch376.valid15040
  · exact MergedCutProfiles.Batch377.valid15086
  · exact MergedCutProfiles.Batch377.valid15096
  · exact MergedCutProfiles.Batch377.valid15093
  · exact MergedCutProfiles.Batch377.valid15097
  · exact MergedCutProfiles.Batch377.valid15098
  · exact MergedCutProfiles.Batch377.valid15099
  · exact MergedCutProfiles.Batch377.valid15100
  · exact MergedCutProfiles.Batch377.valid15101
  · exact MergedCutProfiles.Batch377.valid15102
  · exact MergedCutProfiles.Batch377.valid15103
  · exact MergedCutProfiles.Batch377.valid15104
  · exact MergedCutProfiles.Batch377.valid15105
  · exact MergedCutProfiles.Batch377.valid15106
  · exact MergedCutProfiles.Batch377.valid15107
  · exact MergedCutProfiles.Batch377.valid15108
theorem numericValid2426 : retention2426.NumericValid := by decide +kernel
def certificate2426 : RatCutBinCertificate := ⟨⟨retention2426,(431113381787465781/200000000000000000),(31307344283847009/250000000000000000),(13322007802705716331/1000000000000000000),(244282304990708490629/500000000000000000),(1775477849238131009/1000000000000000000)⟩,(249028534861385659/250000000000000000),(179952059908848273/500000000000000000),(27229913779785267/100000000000000000),(8802434479948097/50000000000000000)⟩
theorem valid2426 : certificate2426.Valid := by decide +kernel
theorem sound2426 : certificate2426.Sound := rat_cut_bin_certificate_sound certificate2426 profilesValid2426 numericValid2426 valid2426

def retention2427 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(15120855470338141681/36463393662086104296),(2336814615682272869/500000000000000000),(11/10),(735009253413897234497/640000000000000000000),true,MergedCutProfiles.Batch376.profile15050,![MergedCutProfiles.Batch376.profile15050,MergedCutProfiles.Batch377.profile15109,MergedCutProfiles.Batch377.profile15110,MergedCutProfiles.Batch377.profile15111,MergedCutProfiles.Batch377.profile15112,MergedCutProfiles.Batch377.profile15113,MergedCutProfiles.Batch377.profile15114,MergedCutProfiles.Batch377.profile15115,MergedCutProfiles.Batch377.profile15116,MergedCutProfiles.Batch377.profile15117,MergedCutProfiles.Batch377.profile15118,MergedCutProfiles.Batch377.profile15119,MergedCutProfiles.Batch378.profile15120,MergedCutProfiles.Batch378.profile15121,MergedCutProfiles.Batch378.profile15122,MergedCutProfiles.Batch378.profile15123]⟩
theorem profilesValid2427 : retention2427.ProfilesValid := by
  change ∀ j : Fin 16, (retention2427.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch376.valid15050
  · exact MergedCutProfiles.Batch377.valid15109
  · exact MergedCutProfiles.Batch377.valid15110
  · exact MergedCutProfiles.Batch377.valid15111
  · exact MergedCutProfiles.Batch377.valid15112
  · exact MergedCutProfiles.Batch377.valid15113
  · exact MergedCutProfiles.Batch377.valid15114
  · exact MergedCutProfiles.Batch377.valid15115
  · exact MergedCutProfiles.Batch377.valid15116
  · exact MergedCutProfiles.Batch377.valid15117
  · exact MergedCutProfiles.Batch377.valid15118
  · exact MergedCutProfiles.Batch377.valid15119
  · exact MergedCutProfiles.Batch378.valid15120
  · exact MergedCutProfiles.Batch378.valid15121
  · exact MergedCutProfiles.Batch378.valid15122
  · exact MergedCutProfiles.Batch378.valid15123
theorem numericValid2427 : retention2427.NumericValid := by decide +kernel
def certificate2427 : RatCutBinCertificate := ⟨⟨retention2427,(431113381787465781/200000000000000000),(31307344283847009/250000000000000000),(13322007802705716331/1000000000000000000),(244282304990708490629/500000000000000000),(1126161839691081769/1000000000000000000)⟩,(249028534861385659/250000000000000000),(213413771751717687/500000000000000000),(26222684132609433/125000000000000000),(713364069815541/4000000000000000)⟩
theorem valid2427 : certificate2427.Valid := by decide +kernel
theorem sound2427 : certificate2427.Sound := rat_cut_bin_certificate_sound certificate2427 profilesValid2427 numericValid2427 valid2427

def retention2428 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(17907696139671154151/36463393662086104296),(15120855470338141681/1000000000000000000),1,(60616000223040108939386265026380011019/60483421881352566724000000000000000000),false,MergedCutProfiles.Batch378.profile15124,(fun _ => MergedCutProfiles.Batch378.profile15124)⟩
theorem profilesValid2428 : retention2428.ProfilesValid := by
  exact MergedCutProfiles.Batch378.valid15124
theorem numericValid2428 : retention2428.NumericValid := by decide +kernel
def certificate2428 : RatCutBinCertificate := ⟨⟨retention2428,(431113381787465781/200000000000000000),(31307344283847009/250000000000000000),(13322007802705716331/1000000000000000000),(244282304990708490629/500000000000000000),(981928900637955433/1000000000000000000)⟩,(249028534861385659/250000000000000000),(445023230941564039/1000000000000000000),(97336409677972593/500000000000000000),(178775303558669083/1000000000000000000)⟩
theorem valid2428 : certificate2428.Valid := by decide +kernel
theorem sound2428 : certificate2428.Sound := rat_cut_bin_certificate_sound certificate2428 profilesValid2428 numericValid2428 valid2428

def retention2429 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(18086773101067865693/36463393662086104296),(17907696139671154151/1000000000000000000),1,(71293483781824650203451927283011786123/71630784558684616604000000000000000000),false,MergedCutProfiles.Batch378.profile15125,(fun _ => MergedCutProfiles.Batch378.profile15125)⟩
theorem profilesValid2429 : retention2429.ProfilesValid := by
  exact MergedCutProfiles.Batch378.valid15125
theorem numericValid2429 : retention2429.NumericValid := by decide +kernel
def certificate2429 : RatCutBinCertificate := ⟨⟨retention2429,(431113381787465781/200000000000000000),(31307344283847009/250000000000000000),(13322007802705716331/1000000000000000000),(244282304990708490629/500000000000000000),(39001123831519663/40000000000000000)⟩,(249028534861385659/250000000000000000),(445052954064183073/1000000000000000000),(12165547248038501/62500000000000000),(179266765192231677/1000000000000000000)⟩
theorem valid2429 : certificate2429.Valid := by decide +kernel
theorem sound2429 : certificate2429.Sound := rat_cut_bin_certificate_sound certificate2429 profilesValid2429 numericValid2429 valid2429

def retention2430 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(1/2),(18086773101067865693/1000000000000000000),1,(17864090439656640032166604478065876153/18086773101067865693000000000000000000),false,MergedCutProfiles.Batch378.profile15126,(fun _ => MergedCutProfiles.Batch378.profile15126)⟩
theorem profilesValid2430 : retention2430.ProfilesValid := by
  exact MergedCutProfiles.Batch378.valid15126
theorem numericValid2430 : retention2430.NumericValid := by decide +kernel
def certificate2430 : RatCutBinCertificate := ⟨⟨retention2430,(431113381787465781/200000000000000000),(31307344283847009/250000000000000000),(13322007802705716331/1000000000000000000),(244282304990708490629/500000000000000000),(967425072155859023/1000000000000000000)⟩,(249028534861385659/250000000000000000),(22419085776037631/50000000000000000),(299947450862411/1562500000000000),(175577690496725337/1000000000000000000)⟩
theorem valid2430 : certificate2430.Valid := by decide +kernel
theorem sound2430 : certificate2430.Sound := rat_cut_bin_certificate_sound certificate2430 profilesValid2430 numericValid2430 valid2430

def retention2431 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(493762097123188653/1104951323093518312),(68851270641261433/12500000000000000),(21/20),(11589082782365171881057957420344393/10758011037697098906250000000000000),false,MergedCutProfiles.Batch378.profile15127,(fun _ => MergedCutProfiles.Batch378.profile15127)⟩
theorem profilesValid2431 : retention2431.ProfilesValid := by
  exact MergedCutProfiles.Batch378.valid15127
theorem numericValid2431 : retention2431.NumericValid := by decide +kernel
def certificate2431 : RatCutBinCertificate := ⟨⟨retention2431,(485964531987465781/200000000000000000),(31307344283847009/250000000000000000),(13322007802705716331/1000000000000000000),(244282304990708490629/500000000000000000),(105326753868848919/100000000000000000)⟩,(995619441484230901/1000000000000000000),(56321266822183477/250000000000000000),(219397052284636559/500000000000000000),(373330451684139463/1000000000000000000)⟩
theorem valid2431 : certificate2431.Valid := by decide +kernel
theorem sound2431 : certificate2431.Sound := rat_cut_bin_certificate_sound certificate2431 profilesValid2431 numericValid2431 valid2431

def retention2432 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(17998877726666437855/36463393662086104296),(16294149205065225549/1000000000000000000),1,(65083193268348817415081052703144156403/65176596820260902196000000000000000000),false,MergedCutProfiles.Batch378.profile15128,(fun _ => MergedCutProfiles.Batch378.profile15128)⟩
theorem profilesValid2432 : retention2432.ProfilesValid := by
  exact MergedCutProfiles.Batch378.valid15128
theorem numericValid2432 : retention2432.NumericValid := by decide +kernel
def certificate2432 : RatCutBinCertificate := ⟨⟨retention2432,(485964531987465781/200000000000000000),(31307344283847009/250000000000000000),(13322007802705716331/1000000000000000000),(244282304990708490629/500000000000000000),(121965720851086511/125000000000000000)⟩,(995619441484230901/1000000000000000000),(243188666732216521/1000000000000000000),(412861612942266131/1000000000000000000),(94591042241387751/250000000000000000)⟩
theorem valid2432 : certificate2432.Valid := by decide +kernel
theorem sound2432 : certificate2432.Sound := rat_cut_bin_certificate_sound certificate2432 profilesValid2432 numericValid2432 valid2432

def retention2433 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(9089433251966551117/18231696831043052148),(3599775545333287571/200000000000000000),1,(71307395726497100653349084540349442339/71995510906665751420000000000000000000),false,MergedCutProfiles.Batch378.profile15129,(fun _ => MergedCutProfiles.Batch378.profile15129)⟩
theorem profilesValid2433 : retention2433.ProfilesValid := by
  exact MergedCutProfiles.Batch378.valid15129
theorem numericValid2433 : retention2433.NumericValid := by decide +kernel
def certificate2433 : RatCutBinCertificate := ⟨⟨retention2433,(485964531987465781/200000000000000000),(31307344283847009/250000000000000000),(13322007802705716331/1000000000000000000),(244282304990708490629/500000000000000000),(483800566930053633/500000000000000000)⟩,(995619441484230901/1000000000000000000),(122615321552931033/500000000000000000),(12812127406247061/31250000000000000),(374771657379865847/1000000000000000000)⟩
theorem valid2433 : certificate2433.Valid := by decide +kernel
theorem sound2433 : certificate2433.Sound := rat_cut_bin_certificate_sound certificate2433 profilesValid2433 numericValid2433 valid2433

def retention2434 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(1/2),(9089433251966551117/500000000000000000),1,(17956326893336510942246420618732114227/18178866503933102234000000000000000000),false,MergedCutProfiles.Batch378.profile15126,(fun _ => MergedCutProfiles.Batch378.profile15126)⟩
theorem profilesValid2434 : retention2434.ProfilesValid := by
  exact MergedCutProfiles.Batch378.valid15126
theorem numericValid2434 : retention2434.NumericValid := by decide +kernel
def certificate2434 : RatCutBinCertificate := ⟨⟨retention2434,(485964531987465781/200000000000000000),(31307344283847009/250000000000000000),(13322007802705716331/1000000000000000000),(244282304990708490629/500000000000000000),(241229305587394749/250000000000000000)⟩,(995619441484230901/1000000000000000000),(122956375339992377/500000000000000000),(81806386433758669/200000000000000000),(373101685931846209/1000000000000000000)⟩
theorem valid2434 : certificate2434.Valid := by decide +kernel
theorem sound2434 : certificate2434.Sound := rat_cut_bin_certificate_sound certificate2434 profilesValid2434 numericValid2434 valid2434

def retention2435 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(857158436330646164/34872198057386390293),(848671719139253627/1000000000000000000),(61/20),(86934498471123887611/40000000000000000000),true,MergedCutProfiles.Batch378.profile15130,![MergedCutProfiles.Batch378.profile15130,MergedCutProfiles.Batch378.profile15131,MergedCutProfiles.Batch378.profile15132,MergedCutProfiles.Batch378.profile15133,MergedCutProfiles.Batch378.profile15134,MergedCutProfiles.Batch378.profile15135,MergedCutProfiles.Batch378.profile15136,MergedCutProfiles.Batch378.profile15137,MergedCutProfiles.Batch378.profile15138,MergedCutProfiles.Batch378.profile15139,MergedCutProfiles.Batch378.profile15140,MergedCutProfiles.Batch378.profile15141,MergedCutProfiles.Batch378.profile15142,MergedCutProfiles.Batch378.profile15143,MergedCutProfiles.Batch378.profile15144,MergedCutProfiles.Batch378.profile15145]⟩
theorem profilesValid2435 : retention2435.ProfilesValid := by
  change ∀ j : Fin 16, (retention2435.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch378.valid15130
  · exact MergedCutProfiles.Batch378.valid15131
  · exact MergedCutProfiles.Batch378.valid15132
  · exact MergedCutProfiles.Batch378.valid15133
  · exact MergedCutProfiles.Batch378.valid15134
  · exact MergedCutProfiles.Batch378.valid15135
  · exact MergedCutProfiles.Batch378.valid15136
  · exact MergedCutProfiles.Batch378.valid15137
  · exact MergedCutProfiles.Batch378.valid15138
  · exact MergedCutProfiles.Batch378.valid15139
  · exact MergedCutProfiles.Batch378.valid15140
  · exact MergedCutProfiles.Batch378.valid15141
  · exact MergedCutProfiles.Batch378.valid15142
  · exact MergedCutProfiles.Batch378.valid15143
  · exact MergedCutProfiles.Batch378.valid15144
  · exact MergedCutProfiles.Batch378.valid15145
theorem numericValid2435 : retention2435.NumericValid := by decide +kernel
def certificate2435 : RatCutBinCertificate := ⟨⟨retention2435,(1084425237518221649/500000000000000000),(65444215677591123/500000000000000000),(13547344760210798237/1000000000000000000),(237582768369219431269/500000000000000000),(2109444525343950967/1000000000000000000)⟩,(249001217545662629/250000000000000000),(354815754747175449/1000000000000000000),(138767240938928883/500000000000000000),(75380156167127089/500000000000000000)⟩
theorem valid2435 : certificate2435.Valid := by decide +kernel
theorem sound2435 : certificate2435.Sound := rat_cut_bin_certificate_sound certificate2435 profilesValid2435 numericValid2435 valid2435

def certificates : List RatCutBinCertificate := [certificate2424,certificate2425,certificate2426,certificate2427,certificate2428,certificate2429,certificate2430,certificate2431,certificate2432,certificate2433,certificate2434,certificate2435]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2424,List.forall_mem_cons.mpr ⟨sound2425,List.forall_mem_cons.mpr ⟨sound2426,List.forall_mem_cons.mpr ⟨sound2427,List.forall_mem_cons.mpr ⟨sound2428,List.forall_mem_cons.mpr ⟨sound2429,List.forall_mem_cons.mpr ⟨sound2430,List.forall_mem_cons.mpr ⟨sound2431,List.forall_mem_cons.mpr ⟨sound2432,List.forall_mem_cons.mpr ⟨sound2433,List.forall_mem_cons.mpr ⟨sound2434,List.forall_mem_cons.mpr ⟨sound2435,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch202
