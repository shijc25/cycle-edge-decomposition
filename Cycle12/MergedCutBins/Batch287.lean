import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch407
import Cycle12.MergedCutProfiles.Batch408
import Cycle12.MergedCutProfiles.Batch409
import Cycle12.MergedCutProfiles.Batch410
import Cycle12.MergedCutProfiles.Batch411
import Cycle12.MergedCutProfiles.Batch528
import Cycle12.MergedCutProfiles.Batch529
import Cycle12.MergedCutProfiles.Batch530

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch287

def retention3444 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(483895263084225781/19626931697362334880),(111205979/100000000),(5/2),(2184449031104205841/1000000000000000000),true,MergedCutProfiles.Batch529.profile21166,![MergedCutProfiles.Batch529.profile21166,MergedCutProfiles.Batch529.profile21167,MergedCutProfiles.Batch529.profile21168,MergedCutProfiles.Batch529.profile21169,MergedCutProfiles.Batch528.profile21130,MergedCutProfiles.Batch529.profile21170,MergedCutProfiles.Batch529.profile21171,MergedCutProfiles.Batch407.profile16284,MergedCutProfiles.Batch529.profile21172,MergedCutProfiles.Batch407.profile16301,MergedCutProfiles.Batch528.profile21150,MergedCutProfiles.Batch529.profile21173,MergedCutProfiles.Batch529.profile21174,MergedCutProfiles.Batch529.profile21175,MergedCutProfiles.Batch407.profile16304,MergedCutProfiles.Batch529.profile21176]⟩
theorem profilesValid3444 : retention3444.ProfilesValid := by
  change ∀ j : Fin 16, (retention3444.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch529.valid21166
  · exact MergedCutProfiles.Batch529.valid21167
  · exact MergedCutProfiles.Batch529.valid21168
  · exact MergedCutProfiles.Batch529.valid21169
  · exact MergedCutProfiles.Batch528.valid21130
  · exact MergedCutProfiles.Batch529.valid21170
  · exact MergedCutProfiles.Batch529.valid21171
  · exact MergedCutProfiles.Batch407.valid16284
  · exact MergedCutProfiles.Batch529.valid21172
  · exact MergedCutProfiles.Batch407.valid16301
  · exact MergedCutProfiles.Batch528.valid21150
  · exact MergedCutProfiles.Batch529.valid21173
  · exact MergedCutProfiles.Batch529.valid21174
  · exact MergedCutProfiles.Batch529.valid21175
  · exact MergedCutProfiles.Batch407.valid16304
  · exact MergedCutProfiles.Batch529.valid21176
theorem numericValid3444 : retention3444.NumericValid := by decide +kernel
def certificate3444 : RatCutBinCertificate := ⟨⟨retention3444,(2224789110314203867/1000000000000000000),(19343761517970331/100000000000000000),(16162259592362227201/1000000000000000000),(477293369344536448549/500000000000000000),(105893792083574391/50000000000000000)⟩,(249527671863175091/250000000000000000),(299088005896758877/1000000000000000000),(84970996392334229/250000000000000000),(220193599085372101/1000000000000000000)⟩
theorem valid3444 : certificate3444.Valid := by decide +kernel
theorem sound3444 : certificate3444.Sound := rat_cut_bin_certificate_sound certificate3444 profilesValid3444 numericValid3444 valid3444

def retention3445 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(67940514851881213/613341615542572965),(1451685789252677343/1000000000000000000),(41/20),(2406456447759963397527/1280000000000000000000),true,MergedCutProfiles.Batch408.profile16344,![MergedCutProfiles.Batch408.profile16344,MergedCutProfiles.Batch408.profile16345,MergedCutProfiles.Batch529.profile21177,MergedCutProfiles.Batch408.profile16346,MergedCutProfiles.Batch407.profile16293,MergedCutProfiles.Batch529.profile21178,MergedCutProfiles.Batch408.profile16349,MergedCutProfiles.Batch408.profile16350,MergedCutProfiles.Batch529.profile21179,MergedCutProfiles.Batch408.profile16352,MergedCutProfiles.Batch529.profile21180,MergedCutProfiles.Batch529.profile21181,MergedCutProfiles.Batch529.profile21182,MergedCutProfiles.Batch529.profile21183,MergedCutProfiles.Batch408.profile16357,MergedCutProfiles.Batch529.profile21184]⟩
theorem profilesValid3445 : retention3445.ProfilesValid := by
  change ∀ j : Fin 16, (retention3445.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch408.valid16344
  · exact MergedCutProfiles.Batch408.valid16345
  · exact MergedCutProfiles.Batch529.valid21177
  · exact MergedCutProfiles.Batch408.valid16346
  · exact MergedCutProfiles.Batch407.valid16293
  · exact MergedCutProfiles.Batch529.valid21178
  · exact MergedCutProfiles.Batch408.valid16349
  · exact MergedCutProfiles.Batch408.valid16350
  · exact MergedCutProfiles.Batch529.valid21179
  · exact MergedCutProfiles.Batch408.valid16352
  · exact MergedCutProfiles.Batch529.valid21180
  · exact MergedCutProfiles.Batch529.valid21181
  · exact MergedCutProfiles.Batch529.valid21182
  · exact MergedCutProfiles.Batch529.valid21183
  · exact MergedCutProfiles.Batch408.valid16357
  · exact MergedCutProfiles.Batch529.valid21184
theorem numericValid3445 : retention3445.NumericValid := by decide +kernel
def certificate3445 : RatCutBinCertificate := ⟨⟨retention3445,(2224789110314203867/1000000000000000000),(19343761517970331/100000000000000000),(16162259592362227201/1000000000000000000),(477293369344536448549/500000000000000000),(182545434625937009/100000000000000000)⟩,(249527671863175091/250000000000000000),(313810146858864979/1000000000000000000),(80619589805422593/250000000000000000),(220532736633195951/1000000000000000000)⟩
theorem valid3445 : certificate3445.Valid := by decide +kernel
theorem sound3445 : certificate3445.Sound := rat_cut_bin_certificate_sound certificate3445 profilesValid3445 numericValid3445 valid3445

def retention3446 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(25493430209104712069/58880795092087004640),(203821544555643639/31250000000000000),(21/20),(725366956152192550959966976144687387631/652228942578059644800000000000000000000),false,MergedCutProfiles.Batch529.profile21185,(fun _ => MergedCutProfiles.Batch529.profile21185)⟩
theorem profilesValid3446 : retention3446.ProfilesValid := by
  exact MergedCutProfiles.Batch529.valid21185
theorem numericValid3446 : retention3446.NumericValid := by decide +kernel
def certificate3446 : RatCutBinCertificate := ⟨⟨retention3446,(2224789110314203867/1000000000000000000),(19343761517970331/100000000000000000),(16162259592362227201/1000000000000000000),(477293369344536448549/500000000000000000),(1084175963326175331/1000000000000000000)⟩,(249527671863175091/250000000000000000),(193059846748728457/500000000000000000),(24644372868325111/100000000000000000),(55168175500563913/250000000000000000)⟩
theorem valid3446 : certificate3446.Valid := by decide +kernel
theorem sound3446 : certificate3446.Sound := rat_cut_bin_certificate_sound certificate3446 profilesValid3446 numericValid3446 valid3446

def retention3447 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(29013901616177101163/58880795092087004640),(25493430209104712069/1000000000000000000),1,(25646722574813780827367697293317100761/25493430209104712069000000000000000000),false,MergedCutProfiles.Batch529.profile21186,(fun _ => MergedCutProfiles.Batch529.profile21186)⟩
theorem profilesValid3447 : retention3447.ProfilesValid := by
  exact MergedCutProfiles.Batch529.valid21186
theorem numericValid3447 : retention3447.NumericValid := by decide +kernel
def certificate3447 : RatCutBinCertificate := ⟨⟨retention3447,(2224789110314203867/1000000000000000000),(19343761517970331/100000000000000000),(16162259592362227201/1000000000000000000),(477293369344536448549/500000000000000000),(979385467901007533/1000000000000000000)⟩,(249527671863175091/250000000000000000),(393884176576648057/1000000000000000000),(2391329573450851/10000000000000000),(225102020533796307/1000000000000000000)⟩
theorem valid3447 : certificate3447.Valid := by decide +kernel
theorem sound3447 : certificate3447.Sound := rat_cut_bin_certificate_sound certificate3447 profilesValid3447 numericValid3447 valid3447

def retention3448 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(5860808126467774435/11776159018417400928),(29013901616177101163/1000000000000000000),1,(5788442842551527603177727667075375889/5802780323235420232600000000000000000),false,MergedCutProfiles.Batch529.profile21187,(fun _ => MergedCutProfiles.Batch529.profile21187)⟩
theorem profilesValid3448 : retention3448.ProfilesValid := by
  exact MergedCutProfiles.Batch529.valid21187
theorem numericValid3448 : retention3448.NumericValid := by decide +kernel
def certificate3448 : RatCutBinCertificate := ⟨⟨retention3448,(2224789110314203867/1000000000000000000),(19343761517970331/100000000000000000),(16162259592362227201/1000000000000000000),(477293369344536448549/500000000000000000),(970901684061394981/1000000000000000000)⟩,(249527671863175091/250000000000000000),(395914206375347299/1000000000000000000),(118623449951663773/500000000000000000),(222454553621182697/1000000000000000000)⟩
theorem valid3448 : certificate3448.Valid := by decide +kernel
theorem sound3448 : certificate3448.Sound := rat_cut_bin_certificate_sound certificate3448 profilesValid3448 numericValid3448 valid3448

def retention3449 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(1/2),(1172161625293554887/40000000000000000),1,(116402031424643165159734478949541035099/117216162529355488700000000000000000000),false,MergedCutProfiles.Batch409.profile16377,(fun _ => MergedCutProfiles.Batch409.profile16377)⟩
theorem profilesValid3449 : retention3449.ProfilesValid := by
  exact MergedCutProfiles.Batch409.valid16377
theorem numericValid3449 : retention3449.NumericValid := by decide +kernel
def certificate3449 : RatCutBinCertificate := ⟨⟨retention3449,(2224789110314203867/1000000000000000000),(19343761517970331/100000000000000000),(16162259592362227201/1000000000000000000),(477293369344536448549/500000000000000000),(966426927613574649/1000000000000000000)⟩,(249527671863175091/250000000000000000),(15905827320608661/40000000000000000),(4712928897265321/20000000000000000),(220038681429538929/1000000000000000000)⟩
theorem valid3449 : certificate3449.Valid := by decide +kernel
theorem sound3449 : certificate3449.Sound := rat_cut_bin_certificate_sound certificate3449 profilesValid3449 numericValid3449 valid3449

def retention3450 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(3387011183476886489/7360099386510875580),(9159607737915775943/1000000000000000000),1,(1923361113965346434052191618834677257/1831921547583155188600000000000000000),false,MergedCutProfiles.Batch529.profile21188,(fun _ => MergedCutProfiles.Batch529.profile21188)⟩
theorem profilesValid3450 : retention3450.ProfilesValid := by
  exact MergedCutProfiles.Batch529.valid21188
theorem numericValid3450 : retention3450.NumericValid := by decide +kernel
def certificate3450 : RatCutBinCertificate := ⟨⟨retention3450,(2290313073314203867/1000000000000000000),(19343761517970331/100000000000000000),(16162259592362227201/1000000000000000000),(477293369344536448549/500000000000000000),(1022502401213145827/1000000000000000000)⟩,(199611003705399347/200000000000000000),(23585537136109543/200000000000000000),(627802693294797141/1000000000000000000),(72034025107385737/125000000000000000)⟩
theorem valid3450 : certificate3450.Valid := by decide +kernel
theorem sound3450 : certificate3450.Sound := rat_cut_bin_certificate_sound certificate3450 profilesValid3450 numericValid3450 valid3450

def retention3451 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(815032838236721349/1635577641446861240),(3387011183476886489/125000000000000000),1,(26978785278739820494382686595886094903/27096089467815091912000000000000000000),false,MergedCutProfiles.Batch529.profile21189,(fun _ => MergedCutProfiles.Batch529.profile21189)⟩
theorem profilesValid3451 : retention3451.ProfilesValid := by
  exact MergedCutProfiles.Batch529.valid21189
theorem numericValid3451 : retention3451.NumericValid := by decide +kernel
def certificate3451 : RatCutBinCertificate := ⟨⟨retention3451,(2290313073314203867/1000000000000000000),(19343761517970331/100000000000000000),(16162259592362227201/1000000000000000000),(477293369344536448549/500000000000000000),(242064761376556557/250000000000000000)⟩,(199611003705399347/200000000000000000),(124534175371247563/1000000000000000000),(76772921098463731/125000000000000000),(573028697737926957/1000000000000000000)⟩
theorem valid3451 : certificate3451.Valid := by decide +kernel
theorem sound3451 : certificate3451.Sound := rat_cut_bin_certificate_sound certificate3451 profilesValid3451 numericValid3451 valid3451

def retention3452 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(1/2),(7335295544130492141/250000000000000000),1,(12950093030500131669332698209520667327/13040525411787541584000000000000000000),false,MergedCutProfiles.Batch409.profile16377,(fun _ => MergedCutProfiles.Batch409.profile16377)⟩
theorem profilesValid3452 : retention3452.ProfilesValid := by
  exact MergedCutProfiles.Batch409.valid16377
theorem numericValid3452 : retention3452.NumericValid := by decide +kernel
def certificate3452 : RatCutBinCertificate := ⟨⟨retention3452,(2290313073314203867/1000000000000000000),(19343761517970331/100000000000000000),(16162259592362227201/1000000000000000000),(477293369344536448549/500000000000000000),(241413383652104009/250000000000000000)⟩,(199611003705399347/200000000000000000),(124870191488261177/1000000000000000000),(153374713192631749/250000000000000000),(71551485385660871/125000000000000000)⟩
theorem valid3452 : certificate3452.Valid := by decide +kernel
theorem sound3452 : certificate3452.Sound := rat_cut_bin_certificate_sound certificate3452 profilesValid3452 numericValid3452 valid3452

def retention3453 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(181004365273737965/11551178452882143772),(896061214226425569/1000000000000000000),(59/20),(22306023939830773647/10000000000000000000),true,MergedCutProfiles.Batch529.profile21190,![MergedCutProfiles.Batch529.profile21190,MergedCutProfiles.Batch529.profile21191,MergedCutProfiles.Batch529.profile21192,MergedCutProfiles.Batch529.profile21193,MergedCutProfiles.Batch529.profile21194,MergedCutProfiles.Batch529.profile21195,MergedCutProfiles.Batch529.profile21196,MergedCutProfiles.Batch529.profile21197,MergedCutProfiles.Batch529.profile21198,MergedCutProfiles.Batch529.profile21199,MergedCutProfiles.Batch410.profile16416,MergedCutProfiles.Batch530.profile21200,MergedCutProfiles.Batch410.profile16432,MergedCutProfiles.Batch530.profile21201,MergedCutProfiles.Batch530.profile21202,MergedCutProfiles.Batch530.profile21203]⟩
theorem profilesValid3453 : retention3453.ProfilesValid := by
  change ∀ j : Fin 16, (retention3453.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch529.valid21190
  · exact MergedCutProfiles.Batch529.valid21191
  · exact MergedCutProfiles.Batch529.valid21192
  · exact MergedCutProfiles.Batch529.valid21193
  · exact MergedCutProfiles.Batch529.valid21194
  · exact MergedCutProfiles.Batch529.valid21195
  · exact MergedCutProfiles.Batch529.valid21196
  · exact MergedCutProfiles.Batch529.valid21197
  · exact MergedCutProfiles.Batch529.valid21198
  · exact MergedCutProfiles.Batch529.valid21199
  · exact MergedCutProfiles.Batch410.valid16416
  · exact MergedCutProfiles.Batch530.valid21200
  · exact MergedCutProfiles.Batch410.valid16432
  · exact MergedCutProfiles.Batch530.valid21201
  · exact MergedCutProfiles.Batch530.valid21202
  · exact MergedCutProfiles.Batch530.valid21203
theorem numericValid3453 : retention3453.NumericValid := by decide +kernel
def certificate3453 : RatCutBinCertificate := ⟨⟨retention3453,(2231784678733447707/1000000000000000000),(24651154762240763/125000000000000000),(16312639462881190313/1000000000000000000),(945071694641299341683/1000000000000000000),(2151002661590096871/1000000000000000000)⟩,(499047212973280453/500000000000000000),(159764441359435443/500000000000000000),(157952307253510579/500000000000000000),(36026039722606179/200000000000000000)⟩
theorem valid3453 : certificate3453.Valid := by decide +kernel
theorem sound3453 : certificate3453.Sound := rat_cut_bin_certificate_sound certificate3453 profilesValid3453 numericValid3453 valid3453

def retention3454 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(541269786526121723/28877946132205359430),(36200873054747593/40000000000000000),(29/10),(35367847529873914259/16000000000000000000),true,MergedCutProfiles.Batch530.profile21204,![MergedCutProfiles.Batch530.profile21204,MergedCutProfiles.Batch530.profile21205,MergedCutProfiles.Batch530.profile21206,MergedCutProfiles.Batch530.profile21207,MergedCutProfiles.Batch529.profile21195,MergedCutProfiles.Batch530.profile21208,MergedCutProfiles.Batch530.profile21209,MergedCutProfiles.Batch530.profile21210,MergedCutProfiles.Batch410.profile16400,MergedCutProfiles.Batch530.profile21211,MergedCutProfiles.Batch530.profile21212,MergedCutProfiles.Batch530.profile21213,MergedCutProfiles.Batch409.profile16386,MergedCutProfiles.Batch530.profile21214,MergedCutProfiles.Batch530.profile21215,MergedCutProfiles.Batch410.profile16419]⟩
theorem profilesValid3454 : retention3454.ProfilesValid := by
  change ∀ j : Fin 16, (retention3454.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch530.valid21204
  · exact MergedCutProfiles.Batch530.valid21205
  · exact MergedCutProfiles.Batch530.valid21206
  · exact MergedCutProfiles.Batch530.valid21207
  · exact MergedCutProfiles.Batch529.valid21195
  · exact MergedCutProfiles.Batch530.valid21208
  · exact MergedCutProfiles.Batch530.valid21209
  · exact MergedCutProfiles.Batch530.valid21210
  · exact MergedCutProfiles.Batch410.valid16400
  · exact MergedCutProfiles.Batch530.valid21211
  · exact MergedCutProfiles.Batch530.valid21212
  · exact MergedCutProfiles.Batch530.valid21213
  · exact MergedCutProfiles.Batch409.valid16386
  · exact MergedCutProfiles.Batch530.valid21214
  · exact MergedCutProfiles.Batch530.valid21215
  · exact MergedCutProfiles.Batch410.valid16419
theorem numericValid3454 : retention3454.NumericValid := by decide +kernel
def certificate3454 : RatCutBinCertificate := ⟨⟨retention3454,(2231784678733447707/1000000000000000000),(24651154762240763/125000000000000000),(16312639462881190313/1000000000000000000),(945071694641299341683/1000000000000000000),(2132239841945862529/1000000000000000000)⟩,(499047212973280453/500000000000000000),(64174087691692137/200000000000000000),(31437732463405159/100000000000000000),(180151618353333673/1000000000000000000)⟩
theorem valid3454 : certificate3454.Valid := by decide +kernel
theorem sound3454 : certificate3454.Sound := rat_cut_bin_certificate_sound certificate3454 profilesValid3454 numericValid3454 valid3454

def retention3455 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(54580121150000000/2887794613220535943),(541269786526121723/500000000000000000),(5/2),(17575972721926997927/8000000000000000000),true,MergedCutProfiles.Batch530.profile21204,![MergedCutProfiles.Batch530.profile21204,MergedCutProfiles.Batch530.profile21205,MergedCutProfiles.Batch530.profile21206,MergedCutProfiles.Batch530.profile21207,MergedCutProfiles.Batch530.profile21216,MergedCutProfiles.Batch411.profile16445,MergedCutProfiles.Batch530.profile21217,MergedCutProfiles.Batch530.profile21218,MergedCutProfiles.Batch530.profile21219,MergedCutProfiles.Batch530.profile21200,MergedCutProfiles.Batch530.profile21220,MergedCutProfiles.Batch530.profile21221,MergedCutProfiles.Batch530.profile21222,MergedCutProfiles.Batch530.profile21223,MergedCutProfiles.Batch409.profile16387,MergedCutProfiles.Batch530.profile21224]⟩
theorem profilesValid3455 : retention3455.ProfilesValid := by
  change ∀ j : Fin 16, (retention3455.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch530.valid21204
  · exact MergedCutProfiles.Batch530.valid21205
  · exact MergedCutProfiles.Batch530.valid21206
  · exact MergedCutProfiles.Batch530.valid21207
  · exact MergedCutProfiles.Batch530.valid21216
  · exact MergedCutProfiles.Batch411.valid16445
  · exact MergedCutProfiles.Batch530.valid21217
  · exact MergedCutProfiles.Batch530.valid21218
  · exact MergedCutProfiles.Batch530.valid21219
  · exact MergedCutProfiles.Batch530.valid21200
  · exact MergedCutProfiles.Batch530.valid21220
  · exact MergedCutProfiles.Batch530.valid21221
  · exact MergedCutProfiles.Batch530.valid21222
  · exact MergedCutProfiles.Batch530.valid21223
  · exact MergedCutProfiles.Batch409.valid16387
  · exact MergedCutProfiles.Batch530.valid21224
theorem numericValid3455 : retention3455.NumericValid := by decide +kernel
def certificate3455 : RatCutBinCertificate := ⟨⟨retention3455,(2231784678733447707/1000000000000000000),(24651154762240763/125000000000000000),(16312639462881190313/1000000000000000000),(945071694641299341683/1000000000000000000),(2129539313797953653/1000000000000000000)⟩,(499047212973280453/500000000000000000),(37142326486364913/125000000000000000),(171121022468037641/500000000000000000),(27654357243682193/125000000000000000)⟩
theorem valid3455 : certificate3455.Valid := by decide +kernel
theorem sound3455 : certificate3455.Sound := rat_cut_bin_certificate_sound certificate3455 profilesValid3455 numericValid3455 valid3455

def certificates : List RatCutBinCertificate := [certificate3444,certificate3445,certificate3446,certificate3447,certificate3448,certificate3449,certificate3450,certificate3451,certificate3452,certificate3453,certificate3454,certificate3455]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3444,List.forall_mem_cons.mpr ⟨sound3445,List.forall_mem_cons.mpr ⟨sound3446,List.forall_mem_cons.mpr ⟨sound3447,List.forall_mem_cons.mpr ⟨sound3448,List.forall_mem_cons.mpr ⟨sound3449,List.forall_mem_cons.mpr ⟨sound3450,List.forall_mem_cons.mpr ⟨sound3451,List.forall_mem_cons.mpr ⟨sound3452,List.forall_mem_cons.mpr ⟨sound3453,List.forall_mem_cons.mpr ⟨sound3454,List.forall_mem_cons.mpr ⟨sound3455,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch287
