import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch044
import Cycle12.MergedCutProfiles.Batch045
import Cycle12.MergedCutProfiles.Batch046
import Cycle12.MergedCutProfiles.Batch333
import Cycle12.MergedCutProfiles.Batch334
import Cycle12.MergedCutProfiles.Batch335

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch180

def retention2160 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(1/2),(58960489229286458433/1000000000000000000),1,(78396013546268275827039144679648636977/78613985639048611244000000000000000000),false,MergedCutProfiles.Batch044.profile1794,(fun _ => MergedCutProfiles.Batch044.profile1794)⟩
theorem profilesValid2160 : retention2160.ProfilesValid := by
  exact MergedCutProfiles.Batch044.valid1794
theorem numericValid2160 : retention2160.NumericValid := by decide +kernel
def certificate2160 : RatCutBinCertificate := ⟨⟨retention2160,(983015305491488317/500000000000000000),(39310593322721927/1000000000000000000),(603711306359428117/62500000000000000),(143236628970677986199/125000000000000000),(989226190576986953/1000000000000000000)⟩,(998346947772430521/1000000000000000000),(463950752082635769/1000000000000000000),(35949125111569387/200000000000000000),(87291670870352791/500000000000000000)⟩
theorem valid2160 : certificate2160.Valid := by decide +kernel
theorem sound2160 : certificate2160.Sound := rat_cut_bin_certificate_sound certificate2160 profilesValid2160 numericValid2160 valid2160

def retention2161 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(49788730645417125709/118033013126607082996),(5467465790997523211/1000000000000000000),(11/10),(2498226766066847906061903135892280239279/2186986316399009284400000000000000000000),false,MergedCutProfiles.Batch333.profile13343,(fun _ => MergedCutProfiles.Batch333.profile13343)⟩
theorem profilesValid2161 : retention2161.ProfilesValid := by
  exact MergedCutProfiles.Batch333.valid13343
theorem numericValid2161 : retention2161.NumericValid := by decide +kernel
def certificate2161 : RatCutBinCertificate := ⟨⟨retention2161,(1133758561991488317/500000000000000000),(39310593322721927/1000000000000000000),(603711306359428117/62500000000000000),(143236628970677986199/125000000000000000),(566081916396475473/500000000000000000)⟩,(998093437459750057/1000000000000000000),(52842074327490331/250000000000000000),(28744300321721049/62500000000000000),(50420447153403581/125000000000000000)⟩
theorem valid2161 : certificate2161.Valid := by decide +kernel
theorem sound2161 : certificate2161.Sound := rat_cut_bin_certificate_sound certificate2161 profilesValid2161 numericValid2161 valid2161

def retention2162 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(14595300578168558731/29508253281651770749),(49788730645417125709/1000000000000000000),1,(8022927274472914709473508129831887827/7966196903266740113440000000000000000),false,MergedCutProfiles.Batch333.profile13344,(fun _ => MergedCutProfiles.Batch333.profile13344)⟩
theorem profilesValid2162 : retention2162.ProfilesValid := by
  exact MergedCutProfiles.Batch333.valid13344
theorem numericValid2162 : retention2162.NumericValid := by decide +kernel
def certificate2162 : RatCutBinCertificate := ⟨⟨retention2162,(1133758561991488317/500000000000000000),(39310593322721927/1000000000000000000),(603711306359428117/62500000000000000),(143236628970677986199/125000000000000000),(498946655309137609/500000000000000000)⟩,(998093437459750057/1000000000000000000),(239808744148307791/1000000000000000000),(13051722352927699/31250000000000000),(203899922440726867/500000000000000000)⟩
theorem valid2162 : certificate2162.Valid := by decide +kernel
theorem sound2162 : certificate2162.Sound := rat_cut_bin_certificate_sound certificate2162 profilesValid2162 numericValid2162 valid2162

def retention2163 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(29482507167900488637/59016506563303541498),(14595300578168558731/250000000000000000),1,(58267443639489436403603795508209370207/58381202312674234924000000000000000000),false,MergedCutProfiles.Batch333.profile13345,(fun _ => MergedCutProfiles.Batch333.profile13345)⟩
theorem profilesValid2163 : retention2163.ProfilesValid := by
  exact MergedCutProfiles.Batch333.valid13345
theorem numericValid2163 : retention2163.NumericValid := by decide +kernel
def certificate2163 : RatCutBinCertificate := ⟨⟨retention2163,(1133758561991488317/500000000000000000),(39310593322721927/1000000000000000000),(603711306359428117/62500000000000000),(143236628970677986199/125000000000000000),(988823374854820537/1000000000000000000)⟩,(998093437459750057/1000000000000000000),(60502094635581517/250000000000000000),(20726512225025537/50000000000000000),(402295614126145891/1000000000000000000)⟩
theorem valid2163 : certificate2163.Valid := by decide +kernel
theorem sound2163 : certificate2163.Sound := rat_cut_bin_certificate_sound certificate2163 profilesValid2163 numericValid2163 valid2163

def retention2164 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(1/2),(29482507167900488637/500000000000000000),1,(125443289521855579933682957782607877/125792030583042084851200000000000000),false,MergedCutProfiles.Batch044.profile1794,(fun _ => MergedCutProfiles.Batch044.profile1794)⟩
theorem profilesValid2164 : retention2164.ProfilesValid := by
  exact MergedCutProfiles.Batch044.valid1794
theorem numericValid2164 : retention2164.NumericValid := by decide +kernel
def certificate2164 : RatCutBinCertificate := ⟨⟨retention2164,(1133758561991488317/500000000000000000),(39310593322721927/1000000000000000000),(603711306359428117/62500000000000000),(143236628970677986199/125000000000000000),(197599912493091577/200000000000000000)⟩,(998093437459750057/1000000000000000000),(60552542406042879/250000000000000000),(207122280829239431/500000000000000000),(200877631066258821/500000000000000000)⟩
theorem valid2164 : certificate2164.Valid := by decide +kernel
theorem sound2164 : certificate2164.Sound := rat_cut_bin_certificate_sound certificate2164 profilesValid2164 numericValid2164 valid2164

def retention2165 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(351893768726869613/54990570427380060659),(348409672006801597/500000000000000000),(77/20),(1466120642600398399573/640000000000000000000),true,MergedCutProfiles.Batch333.profile13346,![MergedCutProfiles.Batch333.profile13346,MergedCutProfiles.Batch333.profile13347,MergedCutProfiles.Batch333.profile13348,MergedCutProfiles.Batch333.profile13349,MergedCutProfiles.Batch046.profile1856,MergedCutProfiles.Batch046.profile1842,MergedCutProfiles.Batch333.profile13350,MergedCutProfiles.Batch333.profile13351,MergedCutProfiles.Batch333.profile13352,MergedCutProfiles.Batch046.profile1857,MergedCutProfiles.Batch333.profile13353,MergedCutProfiles.Batch333.profile13354,MergedCutProfiles.Batch333.profile13355,MergedCutProfiles.Batch333.profile13356,MergedCutProfiles.Batch046.profile1858,MergedCutProfiles.Batch333.profile13357]⟩
theorem profilesValid2165 : retention2165.ProfilesValid := by
  change ∀ j : Fin 16, (retention2165.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch333.valid13346
  · exact MergedCutProfiles.Batch333.valid13347
  · exact MergedCutProfiles.Batch333.valid13348
  · exact MergedCutProfiles.Batch333.valid13349
  · exact MergedCutProfiles.Batch046.valid1856
  · exact MergedCutProfiles.Batch046.valid1842
  · exact MergedCutProfiles.Batch333.valid13350
  · exact MergedCutProfiles.Batch333.valid13351
  · exact MergedCutProfiles.Batch333.valid13352
  · exact MergedCutProfiles.Batch046.valid1857
  · exact MergedCutProfiles.Batch333.valid13353
  · exact MergedCutProfiles.Batch333.valid13354
  · exact MergedCutProfiles.Batch333.valid13355
  · exact MergedCutProfiles.Batch333.valid13356
  · exact MergedCutProfiles.Batch046.valid1858
  · exact MergedCutProfiles.Batch333.valid13357
theorem numericValid2165 : retention2165.NumericValid := by decide +kernel
def certificate2165 : RatCutBinCertificate := ⟨⟨retention2165,(987883791982608841/500000000000000000),(42146381475855499/1000000000000000000),(9796720187986996173/1000000000000000000),(1082937317681299850407/1000000000000000000),(2258088291567008951/1000000000000000000)⟩,(998247141596562999/1000000000000000000),(461636480257990787/1000000000000000000),(181528700292792161/1000000000000000000),(87189772796092639/1000000000000000000)⟩
theorem valid2165 : certificate2165.Valid := by decide +kernel
theorem sound2165 : certificate2165.Sound := rat_cut_bin_certificate_sound certificate2165 profilesValid2165 numericValid2165 valid2165

def retention2166 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(920701104805138633/109981140854760121318),(351893768726869613/500000000000000000),(19/5),(1455107391235525661121/640000000000000000000),true,MergedCutProfiles.Batch333.profile13358,![MergedCutProfiles.Batch333.profile13358,MergedCutProfiles.Batch333.profile13359,MergedCutProfiles.Batch333.profile13349,MergedCutProfiles.Batch334.profile13360,MergedCutProfiles.Batch334.profile13361,MergedCutProfiles.Batch334.profile13362,MergedCutProfiles.Batch046.profile1843,MergedCutProfiles.Batch334.profile13363,MergedCutProfiles.Batch334.profile13364,MergedCutProfiles.Batch334.profile13365,MergedCutProfiles.Batch045.profile1803,MergedCutProfiles.Batch334.profile13366,MergedCutProfiles.Batch334.profile13367,MergedCutProfiles.Batch334.profile13368,MergedCutProfiles.Batch045.profile1820,MergedCutProfiles.Batch334.profile13369]⟩
theorem profilesValid2166 : retention2166.ProfilesValid := by
  change ∀ j : Fin 16, (retention2166.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch333.valid13358
  · exact MergedCutProfiles.Batch333.valid13359
  · exact MergedCutProfiles.Batch333.valid13349
  · exact MergedCutProfiles.Batch334.valid13360
  · exact MergedCutProfiles.Batch334.valid13361
  · exact MergedCutProfiles.Batch334.valid13362
  · exact MergedCutProfiles.Batch046.valid1843
  · exact MergedCutProfiles.Batch334.valid13363
  · exact MergedCutProfiles.Batch334.valid13364
  · exact MergedCutProfiles.Batch334.valid13365
  · exact MergedCutProfiles.Batch045.valid1803
  · exact MergedCutProfiles.Batch334.valid13366
  · exact MergedCutProfiles.Batch334.valid13367
  · exact MergedCutProfiles.Batch334.valid13368
  · exact MergedCutProfiles.Batch045.valid1820
  · exact MergedCutProfiles.Batch334.valid13369
theorem numericValid2166 : retention2166.NumericValid := by decide +kernel
def certificate2166 : RatCutBinCertificate := ⟨⟨retention2166,(987883791982608841/500000000000000000),(42146381475855499/1000000000000000000),(9796720187986996173/1000000000000000000),(1082937317681299850407/1000000000000000000),(140081567975252421/62500000000000000)⟩,(998247141596562999/1000000000000000000),(462484434972755019/1000000000000000000),(36174806789363537/200000000000000000),(10903365455971889/125000000000000000)⟩
theorem valid2166 : certificate2166.Valid := by decide +kernel
theorem sound2166 : certificate2166.Sound := rat_cut_bin_certificate_sound certificate2166 profilesValid2166 numericValid2166 valid2166

def retention2167 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(569463988000000000/54990570427380060659),(920701104805138633/1000000000000000000),3,(574558949472498447121/256000000000000000000),true,MergedCutProfiles.Batch334.profile13370,![MergedCutProfiles.Batch334.profile13370,MergedCutProfiles.Batch334.profile13371,MergedCutProfiles.Batch045.profile1814,MergedCutProfiles.Batch334.profile13361,MergedCutProfiles.Batch334.profile13372,MergedCutProfiles.Batch334.profile13373,MergedCutProfiles.Batch334.profile13374,MergedCutProfiles.Batch333.profile13355,MergedCutProfiles.Batch334.profile13375,MergedCutProfiles.Batch334.profile13376,MergedCutProfiles.Batch334.profile13377,MergedCutProfiles.Batch334.profile13378,MergedCutProfiles.Batch334.profile13369,MergedCutProfiles.Batch334.profile13379,MergedCutProfiles.Batch046.profile1848,MergedCutProfiles.Batch334.profile13380]⟩
theorem profilesValid2167 : retention2167.ProfilesValid := by
  change ∀ j : Fin 16, (retention2167.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch334.valid13370
  · exact MergedCutProfiles.Batch334.valid13371
  · exact MergedCutProfiles.Batch045.valid1814
  · exact MergedCutProfiles.Batch334.valid13361
  · exact MergedCutProfiles.Batch334.valid13372
  · exact MergedCutProfiles.Batch334.valid13373
  · exact MergedCutProfiles.Batch334.valid13374
  · exact MergedCutProfiles.Batch333.valid13355
  · exact MergedCutProfiles.Batch334.valid13375
  · exact MergedCutProfiles.Batch334.valid13376
  · exact MergedCutProfiles.Batch334.valid13377
  · exact MergedCutProfiles.Batch334.valid13378
  · exact MergedCutProfiles.Batch334.valid13369
  · exact MergedCutProfiles.Batch334.valid13379
  · exact MergedCutProfiles.Batch046.valid1848
  · exact MergedCutProfiles.Batch334.valid13380
theorem numericValid2167 : retention2167.NumericValid := by decide +kernel
def certificate2167 : RatCutBinCertificate := ⟨⟨retention2167,(987883791982608841/500000000000000000),(42146381475855499/1000000000000000000),(9796720187986996173/1000000000000000000),(1082937317681299850407/1000000000000000000),(554717685355656663/250000000000000000)⟩,(998247141596562999/1000000000000000000),(405075714058671367/1000000000000000000),(57215948446991861/250000000000000000),(133249021365127759/1000000000000000000)⟩
theorem valid2167 : certificate2167.Valid := by decide +kernel
theorem sound2167 : certificate2167.Sound := rat_cut_bin_certificate_sound certificate2167 profilesValid2167 numericValid2167 valid2167

def retention2168 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(1499222114227079241/109981140854760121318),(142365997/125000000),(51/20),(35494596762746366997/16000000000000000000),true,MergedCutProfiles.Batch334.profile13381,![MergedCutProfiles.Batch334.profile13381,MergedCutProfiles.Batch334.profile13382,MergedCutProfiles.Batch334.profile13383,MergedCutProfiles.Batch334.profile13384,MergedCutProfiles.Batch334.profile13385,MergedCutProfiles.Batch334.profile13386,MergedCutProfiles.Batch046.profile1858,MergedCutProfiles.Batch045.profile1819,MergedCutProfiles.Batch334.profile13387,MergedCutProfiles.Batch334.profile13388,MergedCutProfiles.Batch334.profile13389,MergedCutProfiles.Batch334.profile13390,MergedCutProfiles.Batch334.profile13391,MergedCutProfiles.Batch046.profile1860,MergedCutProfiles.Batch045.profile1824,MergedCutProfiles.Batch334.profile13392]⟩
theorem profilesValid2168 : retention2168.ProfilesValid := by
  change ∀ j : Fin 16, (retention2168.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch334.valid13381
  · exact MergedCutProfiles.Batch334.valid13382
  · exact MergedCutProfiles.Batch334.valid13383
  · exact MergedCutProfiles.Batch334.valid13384
  · exact MergedCutProfiles.Batch334.valid13385
  · exact MergedCutProfiles.Batch334.valid13386
  · exact MergedCutProfiles.Batch046.valid1858
  · exact MergedCutProfiles.Batch045.valid1819
  · exact MergedCutProfiles.Batch334.valid13387
  · exact MergedCutProfiles.Batch334.valid13388
  · exact MergedCutProfiles.Batch334.valid13389
  · exact MergedCutProfiles.Batch334.valid13390
  · exact MergedCutProfiles.Batch334.valid13391
  · exact MergedCutProfiles.Batch046.valid1860
  · exact MergedCutProfiles.Batch045.valid1824
  · exact MergedCutProfiles.Batch334.valid13392
theorem numericValid2168 : retention2168.NumericValid := by decide +kernel
def certificate2168 : RatCutBinCertificate := ⟨⟨retention2168,(987883791982608841/500000000000000000),(42146381475855499/1000000000000000000),(9796720187986996173/1000000000000000000),(1082937317681299850407/1000000000000000000),(2196737180909845693/1000000000000000000)⟩,(998247141596562999/1000000000000000000),(185085689082726179/500000000000000000),(130976524025758849/500000000000000000),(43422552377285459/250000000000000000)⟩
theorem valid2168 : certificate2168.Valid := by decide +kernel
theorem sound2168 : certificate2168.Sound := rat_cut_bin_certificate_sound certificate2168 profilesValid2168 numericValid2168 valid2168

def retention2169 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(5166334216704979402/54990570427380060659),(1499222114227079241/1000000000000000000),(21/10),(2446957972153088471013/1280000000000000000000),true,MergedCutProfiles.Batch334.profile13375,![MergedCutProfiles.Batch334.profile13375,MergedCutProfiles.Batch334.profile13393,MergedCutProfiles.Batch334.profile13394,MergedCutProfiles.Batch334.profile13395,MergedCutProfiles.Batch334.profile13396,MergedCutProfiles.Batch334.profile13397,MergedCutProfiles.Batch334.profile13398,MergedCutProfiles.Batch334.profile13399,MergedCutProfiles.Batch335.profile13400,MergedCutProfiles.Batch335.profile13401,MergedCutProfiles.Batch335.profile13402,MergedCutProfiles.Batch335.profile13403,MergedCutProfiles.Batch335.profile13404,MergedCutProfiles.Batch335.profile13405,MergedCutProfiles.Batch335.profile13406,MergedCutProfiles.Batch335.profile13407]⟩
theorem profilesValid2169 : retention2169.ProfilesValid := by
  change ∀ j : Fin 16, (retention2169.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch334.valid13375
  · exact MergedCutProfiles.Batch334.valid13393
  · exact MergedCutProfiles.Batch334.valid13394
  · exact MergedCutProfiles.Batch334.valid13395
  · exact MergedCutProfiles.Batch334.valid13396
  · exact MergedCutProfiles.Batch334.valid13397
  · exact MergedCutProfiles.Batch334.valid13398
  · exact MergedCutProfiles.Batch334.valid13399
  · exact MergedCutProfiles.Batch335.valid13400
  · exact MergedCutProfiles.Batch335.valid13401
  · exact MergedCutProfiles.Batch335.valid13402
  · exact MergedCutProfiles.Batch335.valid13403
  · exact MergedCutProfiles.Batch335.valid13404
  · exact MergedCutProfiles.Batch335.valid13405
  · exact MergedCutProfiles.Batch335.valid13406
  · exact MergedCutProfiles.Batch335.valid13407
theorem numericValid2169 : retention2169.NumericValid := by decide +kernel
def certificate2169 : RatCutBinCertificate := ⟨⟨retention2169,(987883791982608841/500000000000000000),(42146381475855499/1000000000000000000),(9796720187986996173/1000000000000000000),(1082937317681299850407/1000000000000000000),(1893835838133296907/1000000000000000000)⟩,(998247141596562999/1000000000000000000),(19176321228405903/50000000000000000),(248920068904827823/1000000000000000000),(17415150244426507/100000000000000000)⟩
theorem valid2169 : certificate2169.Valid := by decide +kernel
theorem sound2169 : certificate2169.Sound := rat_cut_bin_certificate_sound certificate2169 profilesValid2169 numericValid2169 valid2169

def retention2170 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(24886255492935165766/54990570427380060659),(2583167108352489701/250000000000000000),(21/20),(40181348771637849322093841589615402173/36902387262178424300000000000000000000),false,MergedCutProfiles.Batch335.profile13408,(fun _ => MergedCutProfiles.Batch335.profile13408)⟩
theorem profilesValid2170 : retention2170.ProfilesValid := by
  exact MergedCutProfiles.Batch335.valid13408
theorem numericValid2170 : retention2170.NumericValid := by decide +kernel
def certificate2170 : RatCutBinCertificate := ⟨⟨retention2170,(987883791982608841/500000000000000000),(42146381475855499/1000000000000000000),(9796720187986996173/1000000000000000000),(1082937317681299850407/1000000000000000000),(1079930036504125279/1000000000000000000)⟩,(998247141596562999/1000000000000000000),(227641766080110137/500000000000000000),(11655203615613537/62500000000000000),(174869690478001889/1000000000000000000)⟩
theorem valid2170 : certificate2170.Valid := by decide +kernel
theorem sound2170 : certificate2170.Sound := rat_cut_bin_certificate_sound certificate2170 profilesValid2170 numericValid2170 valid2170

def retention2171 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(54435462249766942167/109981140854760121318),(12443127746467582883/250000000000000000),1,(200375578397094877236158516806337706871/199090043943481326128000000000000000000),false,MergedCutProfiles.Batch335.profile13409,(fun _ => MergedCutProfiles.Batch335.profile13409)⟩
theorem profilesValid2171 : retention2171.ProfilesValid := by
  exact MergedCutProfiles.Batch335.valid13409
theorem numericValid2171 : retention2171.NumericValid := by decide +kernel
def certificate2171 : RatCutBinCertificate := ⟨⟨retention2171,(987883791982608841/500000000000000000),(42146381475855499/1000000000000000000),(9796720187986996173/1000000000000000000),(1082937317681299850407/1000000000000000000),(997957111896719419/1000000000000000000)⟩,(998247141596562999/1000000000000000000),(230528608388828387/500000000000000000),(181976817833512989/1000000000000000000),(35543987930015643/200000000000000000)⟩
theorem valid2171 : certificate2171.Valid := by decide +kernel
theorem sound2171 : certificate2171.Sound := rat_cut_bin_certificate_sound certificate2171 profilesValid2171 numericValid2171 valid2171

def certificates : List RatCutBinCertificate := [certificate2160,certificate2161,certificate2162,certificate2163,certificate2164,certificate2165,certificate2166,certificate2167,certificate2168,certificate2169,certificate2170,certificate2171]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2160,List.forall_mem_cons.mpr ⟨sound2161,List.forall_mem_cons.mpr ⟨sound2162,List.forall_mem_cons.mpr ⟨sound2163,List.forall_mem_cons.mpr ⟨sound2164,List.forall_mem_cons.mpr ⟨sound2165,List.forall_mem_cons.mpr ⟨sound2166,List.forall_mem_cons.mpr ⟨sound2167,List.forall_mem_cons.mpr ⟨sound2168,List.forall_mem_cons.mpr ⟨sound2169,List.forall_mem_cons.mpr ⟨sound2170,List.forall_mem_cons.mpr ⟨sound2171,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch180
