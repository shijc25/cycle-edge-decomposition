import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch384
import Cycle12.MergedCutProfiles.Batch385
import Cycle12.MergedCutProfiles.Batch504
import Cycle12.MergedCutProfiles.Batch505
import Cycle12.MergedCutProfiles.Batch506

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch274

def retention3288 : RatCutRetentionCertificate := ⟨(107/2000),(27/500),(19752490509163505693/39951799204571019746),(1602776670512362679/50000000000000000),1,(80521966482445267286413421327253441/80138833525618133950000000000000000),false,MergedCutProfiles.Batch504.profile20184,(fun _ => MergedCutProfiles.Batch504.profile20184)⟩
theorem profilesValid3288 : retention3288.ProfilesValid := by
  exact MergedCutProfiles.Batch504.valid20184
theorem numericValid3288 : retention3288.NumericValid := by decide +kernel
def certificate3288 : RatCutBinCertificate := ⟨⟨retention3288,(2126774859921381717/1000000000000000000),(142705547327693923/1000000000000000000),(7068853974728153609/500000000000000000),(1132973115748863439211/1000000000000000000),(983313187079955009/1000000000000000000)⟩,(998384627483786401/1000000000000000000),(109974167012040467/250000000000000000),(1553539184926279/7812500000000000),(189402969874294657/1000000000000000000)⟩
theorem valid3288 : certificate3288.Valid := by decide +kernel
theorem sound3288 : certificate3288.Sound := rat_cut_bin_certificate_sound certificate3288 profilesValid3288 numericValid3288 valid3288

def retention3289 : RatCutRetentionCertificate := ⟨(107/2000),(27/500),(9975007707127570375/19975899602285509873),(19752490509163505693/500000000000000000),1,(157467484989170643722391484018092339759/158019924073308045544000000000000000000),false,MergedCutProfiles.Batch504.profile20185,(fun _ => MergedCutProfiles.Batch504.profile20185)⟩
theorem profilesValid3289 : retention3289.ProfilesValid := by
  exact MergedCutProfiles.Batch504.valid20185
theorem numericValid3289 : retention3289.NumericValid := by decide +kernel
def certificate3289 : RatCutBinCertificate := ⟨⟨retention3289,(2126774859921381717/1000000000000000000),(142705547327693923/1000000000000000000),(7068853974728153609/500000000000000000),(1132973115748863439211/1000000000000000000),(975036328783834197/1000000000000000000)⟩,(998384627483786401/1000000000000000000),(110373357394638143/250000000000000000),(197544644380121473/1000000000000000000),(1172908926902229/6250000000000000)⟩
theorem valid3289 : certificate3289.Valid := by decide +kernel
theorem sound3289 : certificate3289.Sound := rat_cut_bin_certificate_sound certificate3289 profilesValid3289 numericValid3289 valid3289

def retention3290 : RatCutRetentionCertificate := ⟨(107/2000),(27/500),(1/2),(79800061657020563/2000000000000000),1,(254156274339095819344363091784829791/255360197302465801600000000000000000),false,MergedCutProfiles.Batch504.profile20186,(fun _ => MergedCutProfiles.Batch504.profile20186)⟩
theorem profilesValid3290 : retention3290.ProfilesValid := by
  exact MergedCutProfiles.Batch504.valid20186
theorem numericValid3290 : retention3290.NumericValid := by decide +kernel
def certificate3290 : RatCutBinCertificate := ⟨⟨retention3290,(2126774859921381717/1000000000000000000),(142705547327693923/1000000000000000000),(7068853974728153609/500000000000000000),(1132973115748863439211/1000000000000000000),(194763546309777079/200000000000000000)⟩,(998384627483786401/1000000000000000000),(88390943802542429/200000000000000000),(98583872048506921/500000000000000000),(5847610277815169/31250000000000000)⟩
theorem valid3290 : certificate3290.Valid := by decide +kernel
theorem sound3290 : certificate3290.Sound := rat_cut_bin_certificate_sound certificate3290 profilesValid3290 numericValid3290 valid3290

def retention3291 : RatCutRetentionCertificate := ⟨(107/2000),(27/500),(9223320516042493858/19975899602285509873),(9822105150003026189/1000000000000000000),1,(10303802370475668449676720436173215337/9822105150003026189000000000000000000),false,MergedCutProfiles.Batch504.profile20187,(fun _ => MergedCutProfiles.Batch504.profile20187)⟩
theorem profilesValid3291 : retention3291.ProfilesValid := by
  exact MergedCutProfiles.Batch504.valid20187
theorem numericValid3291 : retention3291.NumericValid := by decide +kernel
def certificate3291 : RatCutBinCertificate := ⟨⟨retention3291,(2225137201921381717/1000000000000000000),(142705547327693923/1000000000000000000),(7068853974728153609/500000000000000000),(1132973115748863439211/1000000000000000000),(1026581408844837039/1000000000000000000)⟩,(249577474189789627/250000000000000000),(30061465661990203/250000000000000000),(622988592098313543/1000000000000000000),(577997352671237877/1000000000000000000)⟩
theorem valid3291 : certificate3291.Valid := by decide +kernel
theorem sound3291 : certificate3291.Sound := rat_cut_bin_certificate_sound certificate3291 profilesValid3291 numericValid3291 valid3291

def retention3292 : RatCutRetentionCertificate := ⟨(107/2000),(27/500),(19777295978126056657/39951799204571019746),(4611660258021246929/125000000000000000),1,(29650436373152145871337687521251829131/29514625651335980345600000000000000000),false,MergedCutProfiles.Batch504.profile20188,(fun _ => MergedCutProfiles.Batch504.profile20188)⟩
theorem profilesValid3292 : retention3292.ProfilesValid := by
  exact MergedCutProfiles.Batch504.valid20188
theorem numericValid3292 : retention3292.NumericValid := by decide +kernel
def certificate3292 : RatCutBinCertificate := ⟨⟨retention3292,(2225137201921381717/1000000000000000000),(142705547327693923/1000000000000000000),(7068853974728153609/500000000000000000),(1132973115748863439211/1000000000000000000),(982140935374198351/1000000000000000000)⟩,(249577474189789627/250000000000000000),(62843408027725969/500000000000000000),(611838520663626419/1000000000000000000),(584324672001715411/1000000000000000000)⟩
theorem valid3292 : certificate3292.Valid := by decide +kernel
theorem sound3292 : certificate3292.Sound := rat_cut_bin_certificate_sound certificate3292 profilesValid3292 numericValid3292 valid3292

def retention3293 : RatCutRetentionCertificate := ⟨(107/2000),(27/500),(9987534468953658612/19975899602285509873),(19777295978126056657/500000000000000000),1,(39367562936692712600096989772298796971/39554591956252113314000000000000000000),false,MergedCutProfiles.Batch504.profile20189,(fun _ => MergedCutProfiles.Batch504.profile20189)⟩
theorem profilesValid3293 : retention3293.ProfilesValid := by
  exact MergedCutProfiles.Batch504.valid20189
theorem numericValid3293 : retention3293.NumericValid := by decide +kernel
def certificate3293 : RatCutBinCertificate := ⟨⟨retention3293,(2225137201921381717/1000000000000000000),(142705547327693923/1000000000000000000),(7068853974728153609/500000000000000000),(1132973115748863439211/1000000000000000000),(972811091674603673/1000000000000000000)⟩,(249577474189789627/250000000000000000),(126892228245889123/1000000000000000000),(152349029208407593/250000000000000000),(288802458661313469/500000000000000000)⟩
theorem valid3293 : certificate3293.Valid := by decide +kernel
theorem sound3293 : certificate3293.Sound := rat_cut_bin_certificate_sound certificate3293 profilesValid3293 numericValid3293 valid3293

def retention3294 : RatCutRetentionCertificate := ⟨(107/2000),(27/500),(1/2),(2496883617238414653/62500000000000000),1,(706881842106720675263341511295692799/710224673347815723520000000000000000),false,MergedCutProfiles.Batch504.profile20186,(fun _ => MergedCutProfiles.Batch504.profile20186)⟩
theorem profilesValid3294 : retention3294.ProfilesValid := by
  exact MergedCutProfiles.Batch504.valid20186
theorem numericValid3294 : retention3294.NumericValid := by decide +kernel
def certificate3294 : RatCutBinCertificate := ⟨⟨retention3294,(2225137201921381717/1000000000000000000),(142705547327693923/1000000000000000000),(7068853974728153609/500000000000000000),(1132973115748863439211/1000000000000000000),(972832745685824859/1000000000000000000)⟩,(249577474189789627/250000000000000000),(12688940378737197/100000000000000000),(304700914042650029/500000000000000000),(288880166264573297/500000000000000000)⟩
theorem valid3294 : certificate3294.Valid := by decide +kernel
theorem sound3294 : certificate3294.Sound := rat_cut_bin_certificate_sound certificate3294 profilesValid3294 numericValid3294 valid3294

def retention3295 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(830866188573211517/76571538888968188262),(102829973833318257/125000000000000000),(33/10),(1422525876665020797/625000000000000000),true,MergedCutProfiles.Batch504.profile20190,![MergedCutProfiles.Batch504.profile20190,MergedCutProfiles.Batch504.profile20191,MergedCutProfiles.Batch504.profile20192,MergedCutProfiles.Batch504.profile20193,MergedCutProfiles.Batch504.profile20194,MergedCutProfiles.Batch504.profile20195,MergedCutProfiles.Batch504.profile20196,MergedCutProfiles.Batch384.profile15394,MergedCutProfiles.Batch504.profile20197,MergedCutProfiles.Batch504.profile20198,MergedCutProfiles.Batch504.profile20199,MergedCutProfiles.Batch505.profile20200,MergedCutProfiles.Batch385.profile15427,MergedCutProfiles.Batch505.profile20201,MergedCutProfiles.Batch505.profile20202,MergedCutProfiles.Batch505.profile20203]⟩
theorem profilesValid3295 : retention3295.ProfilesValid := by
  change ∀ j : Fin 16, (retention3295.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch504.valid20190
  · exact MergedCutProfiles.Batch504.valid20191
  · exact MergedCutProfiles.Batch504.valid20192
  · exact MergedCutProfiles.Batch504.valid20193
  · exact MergedCutProfiles.Batch504.valid20194
  · exact MergedCutProfiles.Batch504.valid20195
  · exact MergedCutProfiles.Batch504.valid20196
  · exact MergedCutProfiles.Batch384.valid15394
  · exact MergedCutProfiles.Batch504.valid20197
  · exact MergedCutProfiles.Batch504.valid20198
  · exact MergedCutProfiles.Batch504.valid20199
  · exact MergedCutProfiles.Batch505.valid20200
  · exact MergedCutProfiles.Batch385.valid15427
  · exact MergedCutProfiles.Batch505.valid20201
  · exact MergedCutProfiles.Batch505.valid20202
  · exact MergedCutProfiles.Batch505.valid20203
theorem numericValid3295 : retention3295.NumericValid := by decide +kernel
def certificate3295 : RatCutBinCertificate := ⟨⟨retention3295,(2133392551677267859/1000000000000000000),(14887102204219317/100000000000000000),(1426033585491067991/100000000000000000),(1098394204114735108467/1000000000000000000),(88101659671766207/40000000000000000)⟩,(998334426507043657/1000000000000000000),(38169573086775277/100000000000000000),(250678762041211017/1000000000000000000),(67014733794562117/500000000000000000)⟩
theorem valid3295 : certificate3295.Valid := by decide +kernel
theorem sound3295 : certificate3295.Sound := rat_cut_bin_certificate_sound certificate3295 profilesValid3295 numericValid3295 valid3295

def retention3296 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(1023952794304827529/76571538888968188262),(830866188573211517/1000000000000000000),(13/4),(577858802690284339601/256000000000000000000),true,MergedCutProfiles.Batch505.profile20204,![MergedCutProfiles.Batch505.profile20204,MergedCutProfiles.Batch505.profile20205,MergedCutProfiles.Batch505.profile20206,MergedCutProfiles.Batch505.profile20207,MergedCutProfiles.Batch505.profile20208,MergedCutProfiles.Batch505.profile20209,MergedCutProfiles.Batch505.profile20210,MergedCutProfiles.Batch505.profile20211,MergedCutProfiles.Batch505.profile20212,MergedCutProfiles.Batch505.profile20213,MergedCutProfiles.Batch505.profile20214,MergedCutProfiles.Batch385.profile15412,MergedCutProfiles.Batch505.profile20203,MergedCutProfiles.Batch505.profile20215,MergedCutProfiles.Batch384.profile15398,MergedCutProfiles.Batch385.profile15429]⟩
theorem profilesValid3296 : retention3296.ProfilesValid := by
  change ∀ j : Fin 16, (retention3296.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch505.valid20204
  · exact MergedCutProfiles.Batch505.valid20205
  · exact MergedCutProfiles.Batch505.valid20206
  · exact MergedCutProfiles.Batch505.valid20207
  · exact MergedCutProfiles.Batch505.valid20208
  · exact MergedCutProfiles.Batch505.valid20209
  · exact MergedCutProfiles.Batch505.valid20210
  · exact MergedCutProfiles.Batch505.valid20211
  · exact MergedCutProfiles.Batch505.valid20212
  · exact MergedCutProfiles.Batch505.valid20213
  · exact MergedCutProfiles.Batch505.valid20214
  · exact MergedCutProfiles.Batch385.valid15412
  · exact MergedCutProfiles.Batch505.valid20203
  · exact MergedCutProfiles.Batch505.valid20215
  · exact MergedCutProfiles.Batch384.valid15398
  · exact MergedCutProfiles.Batch385.valid15429
theorem numericValid3296 : retention3296.NumericValid := by decide +kernel
def certificate3296 : RatCutBinCertificate := ⟨⟨retention3296,(2133392551677267859/1000000000000000000),(14887102204219317/100000000000000000),(1426033585491067991/100000000000000000),(1098394204114735108467/1000000000000000000),(1747899722308817/800000000000000)⟩,(998334426507043657/1000000000000000000),(95716771083246859/250000000000000000),(249552469186261401/1000000000000000000),(67029791028318401/500000000000000000)⟩
theorem valid3296 : certificate3296.Valid := by decide +kernel
theorem sound3296 : certificate3296.Sound := rat_cut_bin_certificate_sound certificate3296 profilesValid3296 numericValid3296 valid3296

def retention3297 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(552562095500000000/38285769444484094131),(1023952794304827529/1000000000000000000),(11/4),(574274764951341948037/256000000000000000000),true,MergedCutProfiles.Batch505.profile20216,![MergedCutProfiles.Batch505.profile20216,MergedCutProfiles.Batch384.profile15392,MergedCutProfiles.Batch504.profile20193,MergedCutProfiles.Batch505.profile20217,MergedCutProfiles.Batch505.profile20218,MergedCutProfiles.Batch384.profile15394,MergedCutProfiles.Batch505.profile20219,MergedCutProfiles.Batch384.profile15395,MergedCutProfiles.Batch505.profile20200,MergedCutProfiles.Batch384.profile15396,MergedCutProfiles.Batch505.profile20220,MergedCutProfiles.Batch505.profile20203,MergedCutProfiles.Batch505.profile20215,MergedCutProfiles.Batch505.profile20221,MergedCutProfiles.Batch505.profile20222,MergedCutProfiles.Batch505.profile20223]⟩
theorem profilesValid3297 : retention3297.ProfilesValid := by
  change ∀ j : Fin 16, (retention3297.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch505.valid20216
  · exact MergedCutProfiles.Batch384.valid15392
  · exact MergedCutProfiles.Batch504.valid20193
  · exact MergedCutProfiles.Batch505.valid20217
  · exact MergedCutProfiles.Batch505.valid20218
  · exact MergedCutProfiles.Batch384.valid15394
  · exact MergedCutProfiles.Batch505.valid20219
  · exact MergedCutProfiles.Batch384.valid15395
  · exact MergedCutProfiles.Batch505.valid20200
  · exact MergedCutProfiles.Batch384.valid15396
  · exact MergedCutProfiles.Batch505.valid20220
  · exact MergedCutProfiles.Batch505.valid20203
  · exact MergedCutProfiles.Batch505.valid20215
  · exact MergedCutProfiles.Batch505.valid20221
  · exact MergedCutProfiles.Batch505.valid20222
  · exact MergedCutProfiles.Batch505.valid20223
theorem numericValid3297 : retention3297.NumericValid := by decide +kernel
def certificate3297 : RatCutBinCertificate := ⟨⟨retention3297,(2133392551677267859/1000000000000000000),(14887102204219317/100000000000000000),(1426033585491067991/100000000000000000),(1098394204114735108467/1000000000000000000),(2182010984717158847/1000000000000000000)⟩,(998334426507043657/1000000000000000000),(34721051189885157/100000000000000000),(285495579246149779/1000000000000000000),(22048033447741487/125000000000000000)⟩
theorem valid3297 : certificate3297.Valid := by decide +kernel
theorem sound3297 : certificate3297.Sound := rat_cut_bin_certificate_sound certificate3297 profilesValid3297 numericValid3297 valid3297

def retention3298 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(1509431861729482265/76571538888968188262),(1105124191/1000000000),(51/20),(275594065180144211/125000000000000000),true,MergedCutProfiles.Batch505.profile20224,![MergedCutProfiles.Batch505.profile20224,MergedCutProfiles.Batch505.profile20225,MergedCutProfiles.Batch505.profile20226,MergedCutProfiles.Batch505.profile20227,MergedCutProfiles.Batch504.profile20197,MergedCutProfiles.Batch504.profile20199,MergedCutProfiles.Batch385.profile15439,MergedCutProfiles.Batch505.profile20228,MergedCutProfiles.Batch385.profile15428,MergedCutProfiles.Batch505.profile20229,MergedCutProfiles.Batch505.profile20222,MergedCutProfiles.Batch505.profile20230,MergedCutProfiles.Batch385.profile15415,MergedCutProfiles.Batch505.profile20231,MergedCutProfiles.Batch505.profile20232,MergedCutProfiles.Batch385.profile15402]⟩
theorem profilesValid3298 : retention3298.ProfilesValid := by
  change ∀ j : Fin 16, (retention3298.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch505.valid20224
  · exact MergedCutProfiles.Batch505.valid20225
  · exact MergedCutProfiles.Batch505.valid20226
  · exact MergedCutProfiles.Batch505.valid20227
  · exact MergedCutProfiles.Batch504.valid20197
  · exact MergedCutProfiles.Batch504.valid20199
  · exact MergedCutProfiles.Batch385.valid15439
  · exact MergedCutProfiles.Batch505.valid20228
  · exact MergedCutProfiles.Batch385.valid15428
  · exact MergedCutProfiles.Batch505.valid20229
  · exact MergedCutProfiles.Batch505.valid20222
  · exact MergedCutProfiles.Batch505.valid20230
  · exact MergedCutProfiles.Batch385.valid15415
  · exact MergedCutProfiles.Batch505.valid20231
  · exact MergedCutProfiles.Batch505.valid20232
  · exact MergedCutProfiles.Batch385.valid15402
theorem numericValid3298 : retention3298.NumericValid := by decide +kernel
def certificate3298 : RatCutBinCertificate := ⟨⟨retention3298,(2133392551677267859/1000000000000000000),(14887102204219317/100000000000000000),(1426033585491067991/100000000000000000),(1098394204114735108467/1000000000000000000),(2147957239761343489/1000000000000000000)⟩,(998334426507043657/1000000000000000000),(341105541895761429/1000000000000000000),(18250398340513877/62500000000000000),(94497855345472807/500000000000000000)⟩
theorem valid3298 : certificate3298.Valid := by decide +kernel
theorem sound3298 : certificate3298.Sound := rat_cut_bin_certificate_sound certificate3298 profilesValid3298 numericValid3298 valid3298

def retention3299 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(111472647361041454/933799254743514491),(301886372345896453/200000000000000000),2,(94651936276273457621/51200000000000000000),true,MergedCutProfiles.Batch504.profile20199,![MergedCutProfiles.Batch504.profile20199,MergedCutProfiles.Batch505.profile20233,MergedCutProfiles.Batch505.profile20234,MergedCutProfiles.Batch505.profile20235,MergedCutProfiles.Batch505.profile20236,MergedCutProfiles.Batch505.profile20237,MergedCutProfiles.Batch505.profile20238,MergedCutProfiles.Batch505.profile20239,MergedCutProfiles.Batch506.profile20240,MergedCutProfiles.Batch506.profile20241,MergedCutProfiles.Batch506.profile20242,MergedCutProfiles.Batch506.profile20243,MergedCutProfiles.Batch506.profile20244,MergedCutProfiles.Batch506.profile20245,MergedCutProfiles.Batch506.profile20246,MergedCutProfiles.Batch506.profile20247]⟩
theorem profilesValid3299 : retention3299.ProfilesValid := by
  change ∀ j : Fin 16, (retention3299.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch504.valid20199
  · exact MergedCutProfiles.Batch505.valid20233
  · exact MergedCutProfiles.Batch505.valid20234
  · exact MergedCutProfiles.Batch505.valid20235
  · exact MergedCutProfiles.Batch505.valid20236
  · exact MergedCutProfiles.Batch505.valid20237
  · exact MergedCutProfiles.Batch505.valid20238
  · exact MergedCutProfiles.Batch505.valid20239
  · exact MergedCutProfiles.Batch506.valid20240
  · exact MergedCutProfiles.Batch506.valid20241
  · exact MergedCutProfiles.Batch506.valid20242
  · exact MergedCutProfiles.Batch506.valid20243
  · exact MergedCutProfiles.Batch506.valid20244
  · exact MergedCutProfiles.Batch506.valid20245
  · exact MergedCutProfiles.Batch506.valid20246
  · exact MergedCutProfiles.Batch506.valid20247
theorem numericValid3299 : retention3299.NumericValid := by decide +kernel
def certificate3299 : RatCutBinCertificate := ⟨⟨retention3299,(2133392551677267859/1000000000000000000),(14887102204219317/100000000000000000),(1426033585491067991/100000000000000000),(1098394204114735108467/1000000000000000000),(1804125453925103647/1000000000000000000)⟩,(998334426507043657/1000000000000000000),(359409800475117801/1000000000000000000),(27280456848667001/100000000000000000),(189105095619374211/1000000000000000000)⟩
theorem valid3299 : certificate3299.Valid := by decide +kernel
theorem sound3299 : certificate3299.Sound := rat_cut_bin_certificate_sound certificate3299 profilesValid3299 numericValid3299 valid3299

def certificates : List RatCutBinCertificate := [certificate3288,certificate3289,certificate3290,certificate3291,certificate3292,certificate3293,certificate3294,certificate3295,certificate3296,certificate3297,certificate3298,certificate3299]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3288,List.forall_mem_cons.mpr ⟨sound3289,List.forall_mem_cons.mpr ⟨sound3290,List.forall_mem_cons.mpr ⟨sound3291,List.forall_mem_cons.mpr ⟨sound3292,List.forall_mem_cons.mpr ⟨sound3293,List.forall_mem_cons.mpr ⟨sound3294,List.forall_mem_cons.mpr ⟨sound3295,List.forall_mem_cons.mpr ⟨sound3296,List.forall_mem_cons.mpr ⟨sound3297,List.forall_mem_cons.mpr ⟨sound3298,List.forall_mem_cons.mpr ⟨sound3299,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch274
