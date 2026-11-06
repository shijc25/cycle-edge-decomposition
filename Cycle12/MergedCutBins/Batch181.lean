import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch046
import Cycle12.MergedCutProfiles.Batch047
import Cycle12.MergedCutProfiles.Batch048
import Cycle12.MergedCutProfiles.Batch335
import Cycle12.MergedCutProfiles.Batch336

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch181

def retention2172 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(54979816872264611589/109981140854760121318),(54435462249766942167/1000000000000000000),1,(1356899457220342129319396620395537173/1360886556244173554175000000000000000),false,MergedCutProfiles.Batch335.profile13410,(fun _ => MergedCutProfiles.Batch335.profile13410)⟩
theorem profilesValid2172 : retention2172.ProfilesValid := by
  exact MergedCutProfiles.Batch335.valid13410
theorem numericValid2172 : retention2172.NumericValid := by decide +kernel
def certificate2172 : RatCutBinCertificate := ⟨⟨retention2172,(987883791982608841/500000000000000000),(42146381475855499/1000000000000000000),(9796720187986996173/1000000000000000000),(1082937317681299850407/1000000000000000000),(61785642590170693/62500000000000000)⟩,(998247141596562999/1000000000000000000),(464718693130007739/1000000000000000000),(5598640758258393/31250000000000000),(86820933459773329/500000000000000000)⟩
theorem valid2172 : certificate2172.Valid := by decide +kernel
theorem sound2172 : certificate2172.Sound := rat_cut_bin_certificate_sound certificate2172 profilesValid2172 numericValid2172 valid2172

def retention2173 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(1/2),(54979816872264611589/1000000000000000000),1,(54810577052373601911621280373721183317/54979816872264611589000000000000000000),false,MergedCutProfiles.Batch046.profile1873,(fun _ => MergedCutProfiles.Batch046.profile1873)⟩
theorem profilesValid2173 : retention2173.ProfilesValid := by
  exact MergedCutProfiles.Batch046.valid1873
theorem numericValid2173 : retention2173.NumericValid := by decide +kernel
def certificate2173 : RatCutBinCertificate := ⟨⟨retention2173,(987883791982608841/500000000000000000),(42146381475855499/1000000000000000000),(9796720187986996173/1000000000000000000),(1082937317681299850407/1000000000000000000),(988421844862101363/1000000000000000000)⟩,(998247141596562999/1000000000000000000),(92942551285816603/200000000000000000),(179161053698671827/1000000000000000000),(17365135931806801/100000000000000000)⟩
theorem valid2173 : certificate2173.Valid := by decide +kernel
theorem sound2173 : certificate2173.Sound := rat_cut_bin_certificate_sound certificate2173 profilesValid2173 numericValid2173 valid2173

def retention2174 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(46934137028651695741/109981140854760121318),(2762889258877386963/500000000000000000),(21/20),(821462793078568869308256858977214282477/736770469033969856800000000000000000000),false,MergedCutProfiles.Batch335.profile13411,(fun _ => MergedCutProfiles.Batch335.profile13411)⟩
theorem profilesValid2174 : retention2174.ProfilesValid := by
  exact MergedCutProfiles.Batch335.valid13411
theorem numericValid2174 : retention2174.NumericValid := by decide +kernel
def certificate2174 : RatCutBinCertificate := ⟨⟨retention2174,(1136556487482608841/500000000000000000),(42146381475855499/1000000000000000000),(9796720187986996173/1000000000000000000),(1082937317681299850407/1000000000000000000),(552341296794781281/500000000000000000)⟩,(498991660703850109/500000000000000000),(107455447653039001/500000000000000000),(454451461608514213/1000000000000000000),(403856730623663777/1000000000000000000)⟩
theorem valid2174 : certificate2174.Valid := by decide +kernel
theorem sound2174 : certificate2174.Sound := rat_cut_bin_certificate_sound certificate2174 profilesValid2174 numericValid2174 valid2174

def retention2175 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(54489076037346126221/109981140854760121318),(46934137028651695741/1000000000000000000),1,(188708906831629226675835512794436482299/187736548114606782964000000000000000000),false,MergedCutProfiles.Batch335.profile13412,(fun _ => MergedCutProfiles.Batch335.profile13412)⟩
theorem profilesValid2175 : retention2175.ProfilesValid := by
  exact MergedCutProfiles.Batch335.valid13412
theorem numericValid2175 : retention2175.NumericValid := by decide +kernel
def certificate2175 : RatCutBinCertificate := ⟨⟨retention2175,(1136556487482608841/500000000000000000),(42146381475855499/1000000000000000000),(9796720187986996173/1000000000000000000),(1082937317681299850407/1000000000000000000),(497700115994083989/500000000000000000)⟩,(498991660703850109/500000000000000000),(238505394702575471/1000000000000000000),(209758023971925547/500000000000000000),(102020270946750513/250000000000000000)⟩
theorem valid2175 : certificate2175.Valid := by decide +kernel
theorem sound2175 : certificate2175.Sound := rat_cut_bin_certificate_sound certificate2175 profilesValid2175 numericValid2175 valid2175

def retention2176 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(1/2),(54489076037346126221/1000000000000000000),1,(10863821748920405671326747581400959937/10897815207469225244200000000000000000),false,MergedCutProfiles.Batch046.profile1873,(fun _ => MergedCutProfiles.Batch046.profile1873)⟩
theorem profilesValid2176 : retention2176.ProfilesValid := by
  exact MergedCutProfiles.Batch046.valid1873
theorem numericValid2176 : retention2176.NumericValid := by decide +kernel
def certificate2176 : RatCutBinCertificate := ⟨⟨retention2176,(1136556487482608841/500000000000000000),(42146381475855499/1000000000000000000),(9796720187986996173/1000000000000000000),(1082937317681299850407/1000000000000000000),(987101563055745913/1000000000000000000)⟩,(498991660703850109/500000000000000000),(120255267594974781/500000000000000000),(208327990349972103/500000000000000000),(201571029091384609/500000000000000000)⟩
theorem valid2176 : certificate2176.Valid := by decide +kernel
theorem sound2176 : certificate2176.Sound := rat_cut_bin_certificate_sound certificate2176 profilesValid2176 numericValid2176 valid2176

def retention2177 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(710741255670095442/102689025408210014927),(351852106767373981/500000000000000000),(19/5),(1462500334720242848697/640000000000000000000),true,MergedCutProfiles.Batch335.profile13413,![MergedCutProfiles.Batch335.profile13413,MergedCutProfiles.Batch335.profile13414,MergedCutProfiles.Batch335.profile13415,MergedCutProfiles.Batch335.profile13416,MergedCutProfiles.Batch335.profile13417,MergedCutProfiles.Batch335.profile13418,MergedCutProfiles.Batch335.profile13419,MergedCutProfiles.Batch335.profile13420,MergedCutProfiles.Batch335.profile13421,MergedCutProfiles.Batch335.profile13422,MergedCutProfiles.Batch335.profile13423,MergedCutProfiles.Batch335.profile13424,MergedCutProfiles.Batch335.profile13425,MergedCutProfiles.Batch335.profile13426,MergedCutProfiles.Batch335.profile13427,MergedCutProfiles.Batch335.profile13428]⟩
theorem profilesValid2177 : retention2177.ProfilesValid := by
  change ∀ j : Fin 16, (retention2177.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch335.valid13413
  · exact MergedCutProfiles.Batch335.valid13414
  · exact MergedCutProfiles.Batch335.valid13415
  · exact MergedCutProfiles.Batch335.valid13416
  · exact MergedCutProfiles.Batch335.valid13417
  · exact MergedCutProfiles.Batch335.valid13418
  · exact MergedCutProfiles.Batch335.valid13419
  · exact MergedCutProfiles.Batch335.valid13420
  · exact MergedCutProfiles.Batch335.valid13421
  · exact MergedCutProfiles.Batch335.valid13422
  · exact MergedCutProfiles.Batch335.valid13423
  · exact MergedCutProfiles.Batch335.valid13424
  · exact MergedCutProfiles.Batch335.valid13425
  · exact MergedCutProfiles.Batch335.valid13426
  · exact MergedCutProfiles.Batch335.valid13427
  · exact MergedCutProfiles.Batch335.valid13428
theorem numericValid2177 : retention2177.NumericValid := by decide +kernel
def certificate2177 : RatCutBinCertificate := ⟨⟨retention2177,(247890140746105133/125000000000000000),(9018985876591161/200000000000000000),(9937081155939274967/1000000000000000000),(1025653079030248895453/1000000000000000000),(450191626329190933/200000000000000000)⟩,(249536954702024071/250000000000000000),(457273012165216919/1000000000000000000),(18492222090746143/100000000000000000),(89481246482811367/1000000000000000000)⟩
theorem valid2177 : certificate2177.Valid := by decide +kernel
theorem sound2177 : certificate2177.Sound := rat_cut_bin_certificate_sound certificate2177 profilesValid2177 numericValid2177 valid2177

def retention2178 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(920592099714554756/102689025408210014927),(355370627835047721/500000000000000000),(15/4),(290281787928235225733/128000000000000000000),true,MergedCutProfiles.Batch335.profile13429,![MergedCutProfiles.Batch335.profile13429,MergedCutProfiles.Batch335.profile13430,MergedCutProfiles.Batch335.profile13431,MergedCutProfiles.Batch335.profile13432,MergedCutProfiles.Batch335.profile13433,MergedCutProfiles.Batch335.profile13434,MergedCutProfiles.Batch335.profile13435,MergedCutProfiles.Batch047.profile1880,MergedCutProfiles.Batch335.profile13436,MergedCutProfiles.Batch335.profile13425,MergedCutProfiles.Batch047.profile1911,MergedCutProfiles.Batch335.profile13437,MergedCutProfiles.Batch335.profile13438,MergedCutProfiles.Batch335.profile13439,MergedCutProfiles.Batch336.profile13440,MergedCutProfiles.Batch336.profile13441]⟩
theorem profilesValid2178 : retention2178.ProfilesValid := by
  change ∀ j : Fin 16, (retention2178.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch335.valid13429
  · exact MergedCutProfiles.Batch335.valid13430
  · exact MergedCutProfiles.Batch335.valid13431
  · exact MergedCutProfiles.Batch335.valid13432
  · exact MergedCutProfiles.Batch335.valid13433
  · exact MergedCutProfiles.Batch335.valid13434
  · exact MergedCutProfiles.Batch335.valid13435
  · exact MergedCutProfiles.Batch047.valid1880
  · exact MergedCutProfiles.Batch335.valid13436
  · exact MergedCutProfiles.Batch335.valid13425
  · exact MergedCutProfiles.Batch047.valid1911
  · exact MergedCutProfiles.Batch335.valid13437
  · exact MergedCutProfiles.Batch335.valid13438
  · exact MergedCutProfiles.Batch335.valid13439
  · exact MergedCutProfiles.Batch336.valid13440
  · exact MergedCutProfiles.Batch336.valid13441
theorem numericValid2178 : retention2178.NumericValid := by decide +kernel
def certificate2178 : RatCutBinCertificate := ⟨⟨retention2178,(247890140746105133/125000000000000000),(9018985876591161/200000000000000000),(9937081155939274967/1000000000000000000),(1025653079030248895453/1000000000000000000),(446815561425338871/200000000000000000)⟩,(249536954702024071/250000000000000000),(458170019206795923/1000000000000000000),(92110610638718783/500000000000000000),(44753099925360117/500000000000000000)⟩
theorem valid2178 : certificate2178.Valid := by decide +kernel
theorem sound2178 : certificate2178.Sound := rat_cut_bin_certificate_sound certificate2178 profilesValid2178 numericValid2178 valid2178

def retention2179 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(1123988252000000000/102689025408210014927),(230148024928638689/250000000000000000),3,(143442425263063784301/64000000000000000000),true,MergedCutProfiles.Batch336.profile13442,![MergedCutProfiles.Batch336.profile13442,MergedCutProfiles.Batch336.profile13443,MergedCutProfiles.Batch336.profile13444,MergedCutProfiles.Batch048.profile1930,MergedCutProfiles.Batch336.profile13445,MergedCutProfiles.Batch048.profile1931,MergedCutProfiles.Batch335.profile13423,MergedCutProfiles.Batch336.profile13446,MergedCutProfiles.Batch047.profile1911,MergedCutProfiles.Batch048.profile1933,MergedCutProfiles.Batch336.profile13447,MergedCutProfiles.Batch336.profile13448,MergedCutProfiles.Batch336.profile13441,MergedCutProfiles.Batch047.profile1900,MergedCutProfiles.Batch336.profile13449,MergedCutProfiles.Batch047.profile1915]⟩
theorem profilesValid2179 : retention2179.ProfilesValid := by
  change ∀ j : Fin 16, (retention2179.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch336.valid13442
  · exact MergedCutProfiles.Batch336.valid13443
  · exact MergedCutProfiles.Batch336.valid13444
  · exact MergedCutProfiles.Batch048.valid1930
  · exact MergedCutProfiles.Batch336.valid13445
  · exact MergedCutProfiles.Batch048.valid1931
  · exact MergedCutProfiles.Batch335.valid13423
  · exact MergedCutProfiles.Batch336.valid13446
  · exact MergedCutProfiles.Batch047.valid1911
  · exact MergedCutProfiles.Batch048.valid1933
  · exact MergedCutProfiles.Batch336.valid13447
  · exact MergedCutProfiles.Batch336.valid13448
  · exact MergedCutProfiles.Batch336.valid13441
  · exact MergedCutProfiles.Batch047.valid1900
  · exact MergedCutProfiles.Batch336.valid13449
  · exact MergedCutProfiles.Batch047.valid1915
theorem numericValid2179 : retention2179.NumericValid := by decide +kernel
def certificate2179 : RatCutBinCertificate := ⟨⟨retention2179,(247890140746105133/125000000000000000),(9018985876591161/200000000000000000),(9937081155939274967/1000000000000000000),(1025653079030248895453/1000000000000000000),(2214288981446606933/1000000000000000000)⟩,(249536954702024071/250000000000000000),(787952569834787/1953125000000000),(92141090276933/400000000000000),(66939255613614449/500000000000000000)⟩
theorem valid2179 : certificate2179.Valid := by decide +kernel
theorem sound2179 : certificate2179.Sound := rat_cut_bin_certificate_sound certificate2179 profilesValid2179 numericValid2179 valid2179

def retention2180 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(1357065535339437368/102689025408210014927),(280997063/250000000),(51/20),(17731990385214120331/8000000000000000000),true,MergedCutProfiles.Batch336.profile13450,![MergedCutProfiles.Batch336.profile13450,MergedCutProfiles.Batch335.profile13431,MergedCutProfiles.Batch047.profile1908,MergedCutProfiles.Batch336.profile13451,MergedCutProfiles.Batch048.profile1931,MergedCutProfiles.Batch336.profile13452,MergedCutProfiles.Batch336.profile13453,MergedCutProfiles.Batch336.profile13454,MergedCutProfiles.Batch047.profile1898,MergedCutProfiles.Batch048.profile1934,MergedCutProfiles.Batch336.profile13455,MergedCutProfiles.Batch047.profile1886,MergedCutProfiles.Batch047.profile1887,MergedCutProfiles.Batch336.profile13456,MergedCutProfiles.Batch048.profile1923,MergedCutProfiles.Batch336.profile13457]⟩
theorem profilesValid2180 : retention2180.ProfilesValid := by
  change ∀ j : Fin 16, (retention2180.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch336.valid13450
  · exact MergedCutProfiles.Batch335.valid13431
  · exact MergedCutProfiles.Batch047.valid1908
  · exact MergedCutProfiles.Batch336.valid13451
  · exact MergedCutProfiles.Batch048.valid1931
  · exact MergedCutProfiles.Batch336.valid13452
  · exact MergedCutProfiles.Batch336.valid13453
  · exact MergedCutProfiles.Batch336.valid13454
  · exact MergedCutProfiles.Batch047.valid1898
  · exact MergedCutProfiles.Batch048.valid1934
  · exact MergedCutProfiles.Batch336.valid13455
  · exact MergedCutProfiles.Batch047.valid1886
  · exact MergedCutProfiles.Batch047.valid1887
  · exact MergedCutProfiles.Batch336.valid13456
  · exact MergedCutProfiles.Batch048.valid1923
  · exact MergedCutProfiles.Batch336.valid13457
theorem numericValid2180 : retention2180.NumericValid := by decide +kernel
def certificate2180 : RatCutBinCertificate := ⟨⟨retention2180,(247890140746105133/125000000000000000),(9018985876591161/200000000000000000),(9937081155939274967/1000000000000000000),(1025653079030248895453/1000000000000000000),(548387433790747433/250000000000000000)⟩,(249536954702024071/250000000000000000),(185423532969721989/500000000000000000),(261282236552376653/1000000000000000000),(172507213214923669/1000000000000000000)⟩
theorem valid2180 : certificate2180.Valid := by decide +kernel
theorem sound2180 : certificate2180.Sound := rat_cut_bin_certificate_sound certificate2180 profilesValid2180 numericValid2180 valid2180

def retention2181 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(6939147538377215645/102689025408210014927),(169633191917429671/125000000000000000),(11/5),(318643626273321717371/160000000000000000000),true,MergedCutProfiles.Batch047.profile1895,![MergedCutProfiles.Batch047.profile1895,MergedCutProfiles.Batch047.profile1899,MergedCutProfiles.Batch336.profile13458,MergedCutProfiles.Batch336.profile13459,MergedCutProfiles.Batch048.profile1948,MergedCutProfiles.Batch336.profile13460,MergedCutProfiles.Batch336.profile13461,MergedCutProfiles.Batch336.profile13462,MergedCutProfiles.Batch336.profile13463,MergedCutProfiles.Batch048.profile1954,MergedCutProfiles.Batch336.profile13464,MergedCutProfiles.Batch336.profile13465,MergedCutProfiles.Batch336.profile13466,MergedCutProfiles.Batch336.profile13467,MergedCutProfiles.Batch336.profile13468,MergedCutProfiles.Batch336.profile13469]⟩
theorem profilesValid2181 : retention2181.ProfilesValid := by
  change ∀ j : Fin 16, (retention2181.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch047.valid1895
  · exact MergedCutProfiles.Batch047.valid1899
  · exact MergedCutProfiles.Batch336.valid13458
  · exact MergedCutProfiles.Batch336.valid13459
  · exact MergedCutProfiles.Batch048.valid1948
  · exact MergedCutProfiles.Batch336.valid13460
  · exact MergedCutProfiles.Batch336.valid13461
  · exact MergedCutProfiles.Batch336.valid13462
  · exact MergedCutProfiles.Batch336.valid13463
  · exact MergedCutProfiles.Batch048.valid1954
  · exact MergedCutProfiles.Batch336.valid13464
  · exact MergedCutProfiles.Batch336.valid13465
  · exact MergedCutProfiles.Batch336.valid13466
  · exact MergedCutProfiles.Batch336.valid13467
  · exact MergedCutProfiles.Batch336.valid13468
  · exact MergedCutProfiles.Batch336.valid13469
theorem numericValid2181 : retention2181.NumericValid := by decide +kernel
def certificate2181 : RatCutBinCertificate := ⟨⟨retention2181,(247890140746105133/125000000000000000),(9018985876591161/200000000000000000),(9937081155939274967/1000000000000000000),(1025653079030248895453/1000000000000000000),(61616358898557851/31250000000000000)⟩,(249536954702024071/250000000000000000),(381090244248883877/1000000000000000000),(251262363868943117/1000000000000000000),(86415927149699089/500000000000000000)⟩
theorem valid2181 : certificate2181.Valid := by decide +kernel
theorem sound2181 : certificate2181.Sound := rat_cut_bin_certificate_sound certificate2181 profilesValid2181 numericValid2181 valid2181

def retention2182 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(43295114990391947747/102689025408210014927),(1387829507675443129/200000000000000000),(21/20),(504560163873263184669946219420874934759/444105442456141801280000000000000000000),false,MergedCutProfiles.Batch336.profile13470,(fun _ => MergedCutProfiles.Batch336.profile13470)⟩
theorem profilesValid2182 : retention2182.ProfilesValid := by
  exact MergedCutProfiles.Batch336.valid13470
theorem numericValid2182 : retention2182.NumericValid := by decide +kernel
def certificate2182 : RatCutBinCertificate := ⟨⟨retention2182,(247890140746105133/125000000000000000),(9018985876591161/200000000000000000),(9937081155939274967/1000000000000000000),(1025653079030248895453/1000000000000000000),(11266774283935607/10000000000000000)⟩,(249536954702024071/250000000000000000),(453216914847472007/1000000000000000000),(18811402547650673/100000000000000000),(175593158590525657/1000000000000000000)⟩
theorem valid2182 : certificate2182.Valid := by decide +kernel
theorem sound2182 : certificate2182.Sound := rat_cut_bin_certificate_sound certificate2182 profilesValid2182 numericValid2182 valid2182

def retention2183 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(50766927267249496787/102689025408210014927),(43295114990391947747/1000000000000000000),1,(34055485804552909801125232135376283/33824308586243709177343750000000000),false,MergedCutProfiles.Batch336.profile13471,(fun _ => MergedCutProfiles.Batch336.profile13471)⟩
theorem profilesValid2183 : retention2183.ProfilesValid := by
  exact MergedCutProfiles.Batch336.valid13471
theorem numericValid2183 : retention2183.NumericValid := by decide +kernel
def certificate2183 : RatCutBinCertificate := ⟨⟨retention2183,(247890140746105133/125000000000000000),(9018985876591161/200000000000000000),(9937081155939274967/1000000000000000000),(1025653079030248895453/1000000000000000000),(124729392954695833/125000000000000000)⟩,(249536954702024071/250000000000000000),(462477085462217911/1000000000000000000),(90439850739470093/500000000000000000),(11005703009635649/62500000000000000)⟩
theorem valid2183 : certificate2183.Valid := by decide +kernel
theorem sound2183 : certificate2183.Sound := rat_cut_bin_certificate_sound certificate2183 profilesValid2183 numericValid2183 valid2183

def certificates : List RatCutBinCertificate := [certificate2172,certificate2173,certificate2174,certificate2175,certificate2176,certificate2177,certificate2178,certificate2179,certificate2180,certificate2181,certificate2182,certificate2183]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2172,List.forall_mem_cons.mpr ⟨sound2173,List.forall_mem_cons.mpr ⟨sound2174,List.forall_mem_cons.mpr ⟨sound2175,List.forall_mem_cons.mpr ⟨sound2176,List.forall_mem_cons.mpr ⟨sound2177,List.forall_mem_cons.mpr ⟨sound2178,List.forall_mem_cons.mpr ⟨sound2179,List.forall_mem_cons.mpr ⟨sound2180,List.forall_mem_cons.mpr ⟨sound2181,List.forall_mem_cons.mpr ⟨sound2182,List.forall_mem_cons.mpr ⟨sound2183,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch181
