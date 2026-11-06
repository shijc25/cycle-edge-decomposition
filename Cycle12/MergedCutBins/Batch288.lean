import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch410
import Cycle12.MergedCutProfiles.Batch411
import Cycle12.MergedCutProfiles.Batch530
import Cycle12.MergedCutProfiles.Batch531
import Cycle12.MergedCutProfiles.Batch532

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch288

def retention3456 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(55214930923529677/2887794613220535943),(1091602423/1000000000),(5/2),(8798598433330644901/4000000000000000000),true,MergedCutProfiles.Batch530.profile21204,![MergedCutProfiles.Batch530.profile21204,MergedCutProfiles.Batch530.profile21225,MergedCutProfiles.Batch530.profile21226,MergedCutProfiles.Batch530.profile21227,MergedCutProfiles.Batch530.profile21228,MergedCutProfiles.Batch530.profile21229,MergedCutProfiles.Batch530.profile21230,MergedCutProfiles.Batch410.profile16431,MergedCutProfiles.Batch410.profile16416,MergedCutProfiles.Batch530.profile21231,MergedCutProfiles.Batch530.profile21232,MergedCutProfiles.Batch530.profile21233,MergedCutProfiles.Batch530.profile21234,MergedCutProfiles.Batch530.profile21235,MergedCutProfiles.Batch530.profile21236,MergedCutProfiles.Batch410.profile16434]⟩
theorem profilesValid3456 : retention3456.ProfilesValid := by
  change ∀ j : Fin 16, (retention3456.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch530.valid21204
  · exact MergedCutProfiles.Batch530.valid21225
  · exact MergedCutProfiles.Batch530.valid21226
  · exact MergedCutProfiles.Batch530.valid21227
  · exact MergedCutProfiles.Batch530.valid21228
  · exact MergedCutProfiles.Batch530.valid21229
  · exact MergedCutProfiles.Batch530.valid21230
  · exact MergedCutProfiles.Batch410.valid16431
  · exact MergedCutProfiles.Batch410.valid16416
  · exact MergedCutProfiles.Batch530.valid21231
  · exact MergedCutProfiles.Batch530.valid21232
  · exact MergedCutProfiles.Batch530.valid21233
  · exact MergedCutProfiles.Batch530.valid21234
  · exact MergedCutProfiles.Batch530.valid21235
  · exact MergedCutProfiles.Batch530.valid21236
  · exact MergedCutProfiles.Batch410.valid16434
theorem numericValid3456 : retention3456.NumericValid := by decide +kernel
def certificate3456 : RatCutBinCertificate := ⟨⟨retention3456,(2231784678733447707/1000000000000000000),(24651154762240763/125000000000000000),(16312639462881190313/1000000000000000000),(945071694641299341683/1000000000000000000),(266524046883614213/125000000000000000)⟩,(499047212973280453/500000000000000000),(147874218463611833/500000000000000000),(85982855057751177/250000000000000000),(111490831575293009/500000000000000000)⟩
theorem valid3456 : certificate3456.Valid := by decide +kernel
theorem sound3456 : certificate3456.Sound := rat_cut_bin_certificate_sound certificate3456 profilesValid3456 numericValid3456 valid3456

def retention3457 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(653912873706867273/28877946132205359430),(55214930923529677/50000000000000000),(5/2),(8762893094199368069/4000000000000000000),true,MergedCutProfiles.Batch530.profile21237,![MergedCutProfiles.Batch530.profile21237,MergedCutProfiles.Batch530.profile21238,MergedCutProfiles.Batch530.profile21239,MergedCutProfiles.Batch531.profile21240,MergedCutProfiles.Batch411.profile16445,MergedCutProfiles.Batch531.profile21241,MergedCutProfiles.Batch531.profile21242,MergedCutProfiles.Batch531.profile21243,MergedCutProfiles.Batch410.profile16432,MergedCutProfiles.Batch530.profile21221,MergedCutProfiles.Batch530.profile21234,MergedCutProfiles.Batch531.profile21244,MergedCutProfiles.Batch531.profile21245,MergedCutProfiles.Batch531.profile21246,MergedCutProfiles.Batch531.profile21247,MergedCutProfiles.Batch531.profile21248]⟩
theorem profilesValid3457 : retention3457.ProfilesValid := by
  change ∀ j : Fin 16, (retention3457.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch530.valid21237
  · exact MergedCutProfiles.Batch530.valid21238
  · exact MergedCutProfiles.Batch530.valid21239
  · exact MergedCutProfiles.Batch531.valid21240
  · exact MergedCutProfiles.Batch411.valid16445
  · exact MergedCutProfiles.Batch531.valid21241
  · exact MergedCutProfiles.Batch531.valid21242
  · exact MergedCutProfiles.Batch531.valid21243
  · exact MergedCutProfiles.Batch410.valid16432
  · exact MergedCutProfiles.Batch530.valid21221
  · exact MergedCutProfiles.Batch530.valid21234
  · exact MergedCutProfiles.Batch531.valid21244
  · exact MergedCutProfiles.Batch531.valid21245
  · exact MergedCutProfiles.Batch531.valid21246
  · exact MergedCutProfiles.Batch531.valid21247
  · exact MergedCutProfiles.Batch531.valid21248
theorem numericValid3457 : retention3457.NumericValid := by decide +kernel
def certificate3457 : RatCutBinCertificate := ⟨⟨retention3457,(2231784678733447707/1000000000000000000),(24651154762240763/125000000000000000),(16312639462881190313/1000000000000000000),(945071694641299341683/1000000000000000000),(2123266099584141359/1000000000000000000)⟩,(499047212973280453/500000000000000000),(147792248136045079/500000000000000000),(344131072936158027/1000000000000000000),(223007918455474213/1000000000000000000)⟩
theorem valid3457 : certificate3457.Valid := by decide +kernel
theorem sound3457 : certificate3457.Sound := rat_cut_bin_certificate_sound certificate3457 profilesValid3457 numericValid3457 valid3457

def retention3458 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(4447120101482909089/57755892264410718860),(653912873706867273/500000000000000000),(11/5),(1271508749343713300973/640000000000000000000),true,MergedCutProfiles.Batch531.profile21249,![MergedCutProfiles.Batch531.profile21249,MergedCutProfiles.Batch410.profile16431,MergedCutProfiles.Batch531.profile21250,MergedCutProfiles.Batch531.profile21251,MergedCutProfiles.Batch531.profile21252,MergedCutProfiles.Batch410.profile16407,MergedCutProfiles.Batch531.profile21253,MergedCutProfiles.Batch531.profile21254,MergedCutProfiles.Batch531.profile21255,MergedCutProfiles.Batch531.profile21256,MergedCutProfiles.Batch531.profile21257,MergedCutProfiles.Batch531.profile21258,MergedCutProfiles.Batch531.profile21259,MergedCutProfiles.Batch531.profile21260,MergedCutProfiles.Batch531.profile21261,MergedCutProfiles.Batch531.profile21262]⟩
theorem profilesValid3458 : retention3458.ProfilesValid := by
  change ∀ j : Fin 16, (retention3458.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch531.valid21249
  · exact MergedCutProfiles.Batch410.valid16431
  · exact MergedCutProfiles.Batch531.valid21250
  · exact MergedCutProfiles.Batch531.valid21251
  · exact MergedCutProfiles.Batch531.valid21252
  · exact MergedCutProfiles.Batch410.valid16407
  · exact MergedCutProfiles.Batch531.valid21253
  · exact MergedCutProfiles.Batch531.valid21254
  · exact MergedCutProfiles.Batch531.valid21255
  · exact MergedCutProfiles.Batch531.valid21256
  · exact MergedCutProfiles.Batch531.valid21257
  · exact MergedCutProfiles.Batch531.valid21258
  · exact MergedCutProfiles.Batch531.valid21259
  · exact MergedCutProfiles.Batch531.valid21260
  · exact MergedCutProfiles.Batch531.valid21261
  · exact MergedCutProfiles.Batch531.valid21262
theorem numericValid3458 : retention3458.NumericValid := by decide +kernel
def certificate3458 : RatCutBinCertificate := ⟨⟨retention3458,(2231784678733447707/1000000000000000000),(24651154762240763/125000000000000000),(16312639462881190313/1000000000000000000),(945071694641299341683/1000000000000000000),(240921286172056999/125000000000000000)⟩,(499047212973280453/500000000000000000),(152441944108900141/500000000000000000),(10404607711360773/31250000000000000),(223101752764892971/1000000000000000000)⟩
theorem valid3458 : certificate3458.Valid := by decide +kernel
theorem sound3458 : certificate3458.Sound := rat_cut_bin_certificate_sound certificate3458 profilesValid3458 numericValid3458 valid3458

def retention3459 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(22514524798498268101/57755892264410718860),(4447120101482909089/1000000000000000000),(11/10),(1529356544683942452157/1280000000000000000000),true,MergedCutProfiles.Batch531.profile21263,![MergedCutProfiles.Batch531.profile21263,MergedCutProfiles.Batch531.profile21264,MergedCutProfiles.Batch531.profile21265,MergedCutProfiles.Batch531.profile21266,MergedCutProfiles.Batch531.profile21267,MergedCutProfiles.Batch531.profile21268,MergedCutProfiles.Batch531.profile21269,MergedCutProfiles.Batch531.profile21270,MergedCutProfiles.Batch411.profile16470,MergedCutProfiles.Batch531.profile21271,MergedCutProfiles.Batch531.profile21272,MergedCutProfiles.Batch531.profile21273,MergedCutProfiles.Batch531.profile21274,MergedCutProfiles.Batch531.profile21275,MergedCutProfiles.Batch531.profile21276,MergedCutProfiles.Batch531.profile21277]⟩
theorem profilesValid3459 : retention3459.ProfilesValid := by
  change ∀ j : Fin 16, (retention3459.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch531.valid21263
  · exact MergedCutProfiles.Batch531.valid21264
  · exact MergedCutProfiles.Batch531.valid21265
  · exact MergedCutProfiles.Batch531.valid21266
  · exact MergedCutProfiles.Batch531.valid21267
  · exact MergedCutProfiles.Batch531.valid21268
  · exact MergedCutProfiles.Batch531.valid21269
  · exact MergedCutProfiles.Batch531.valid21270
  · exact MergedCutProfiles.Batch411.valid16470
  · exact MergedCutProfiles.Batch531.valid21271
  · exact MergedCutProfiles.Batch531.valid21272
  · exact MergedCutProfiles.Batch531.valid21273
  · exact MergedCutProfiles.Batch531.valid21274
  · exact MergedCutProfiles.Batch531.valid21275
  · exact MergedCutProfiles.Batch531.valid21276
  · exact MergedCutProfiles.Batch531.valid21277
theorem numericValid3459 : retention3459.NumericValid := by decide +kernel
def certificate3459 : RatCutBinCertificate := ⟨⟨retention3459,(2231784678733447707/1000000000000000000),(24651154762240763/125000000000000000),(16312639462881190313/1000000000000000000),(945071694641299341683/1000000000000000000),(233025924251314157/200000000000000000)⟩,(499047212973280453/500000000000000000),(372913594902640207/1000000000000000000),(129619122458679/500000000000000),(112618124793533207/500000000000000000)⟩
theorem valid3459 : certificate3459.Valid := by decide +kernel
theorem sound3459 : certificate3459.Sound := rat_cut_bin_certificate_sound certificate3459 profilesValid3459 numericValid3459 valid3459

def retention3460 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(28304427952360664247/57755892264410718860),(22514524798498268101/1000000000000000000),1,(18190835160245009978667746352349153791/18011619838798614480800000000000000000),false,MergedCutProfiles.Batch531.profile21278,(fun _ => MergedCutProfiles.Batch531.profile21278)⟩
theorem profilesValid3460 : retention3460.ProfilesValid := by
  exact MergedCutProfiles.Batch531.valid21278
theorem numericValid3460 : retention3460.NumericValid := by decide +kernel
def certificate3460 : RatCutBinCertificate := ⟨⟨retention3460,(2231784678733447707/1000000000000000000),(24651154762240763/125000000000000000),(16312639462881190313/1000000000000000000),(945071694641299341683/1000000000000000000),(982968903264133019/1000000000000000000)⟩,(499047212973280453/500000000000000000),(389940230284398089/1000000000000000000),(242827134570460387/1000000000000000000),(57064553788908413/250000000000000000)⟩
theorem valid3460 : certificate3460.Valid := by decide +kernel
theorem sound3460 : certificate3460.Sound := rat_cut_bin_certificate_sound certificate3460 profilesValid3460 numericValid3460 valid3460

def retention3461 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(2858747223188427089/5775589226441071886),(28304427952360664247/1000000000000000000),1,(22703733640269397990026093259139607319/22643542361888531397600000000000000000),false,MergedCutProfiles.Batch531.profile21279,(fun _ => MergedCutProfiles.Batch531.profile21279)⟩
theorem profilesValid3461 : retention3461.ProfilesValid := by
  exact MergedCutProfiles.Batch531.valid21279
theorem numericValid3461 : retention3461.NumericValid := by decide +kernel
def certificate3461 : RatCutBinCertificate := ⟨⟨retention3461,(2231784678733447707/1000000000000000000),(24651154762240763/125000000000000000),(16312639462881190313/1000000000000000000),(945071694641299341683/1000000000000000000),(243919295075594813/250000000000000000)⟩,(499047212973280453/500000000000000000),(390212592394634181/1000000000000000000),(121285372087392447/500000000000000000),(228338492463971239/1000000000000000000)⟩
theorem valid3461 : certificate3461.Valid := by decide +kernel
theorem sound3461 : certificate3461.Sound := rat_cut_bin_certificate_sound certificate3461 profilesValid3461 numericValid3461 valid3461

def retention3462 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(28873346954203113599/57755892264410718860),(2858747223188427089/100000000000000000),1,(28387351300891287066178851972637852651/28587472231884270890000000000000000000),false,MergedCutProfiles.Batch532.profile21280,(fun _ => MergedCutProfiles.Batch532.profile21280)⟩
theorem profilesValid3462 : retention3462.ProfilesValid := by
  exact MergedCutProfiles.Batch532.valid21280
theorem numericValid3462 : retention3462.NumericValid := by decide +kernel
def certificate3462 : RatCutBinCertificate := ⟨⟨retention3462,(2231784678733447707/1000000000000000000),(24651154762240763/125000000000000000),(16312639462881190313/1000000000000000000),(945071694641299341683/1000000000000000000),(966018671099188737/1000000000000000000)⟩,(499047212973280453/500000000000000000),(19700565504683387/50000000000000000),(239014533928930227/1000000000000000000),(222910119065471353/1000000000000000000)⟩
theorem valid3462 : certificate3462.Valid := by decide +kernel
theorem sound3462 : certificate3462.Sound := rat_cut_bin_certificate_sound certificate3462 profilesValid3462 numericValid3462 valid3462

def retention3463 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(1/2),(28873346954203113599/1000000000000000000),1,(924813150536544078708752996285056227/931398288845261729000000000000000000),false,MergedCutProfiles.Batch411.profile16479,(fun _ => MergedCutProfiles.Batch411.profile16479)⟩
theorem profilesValid3463 : retention3463.ProfilesValid := by
  exact MergedCutProfiles.Batch411.valid16479
theorem numericValid3463 : retention3463.NumericValid := by decide +kernel
def certificate3463 : RatCutBinCertificate := ⟨⟨retention3463,(2231784678733447707/1000000000000000000),(24651154762240763/125000000000000000),(16312639462881190313/1000000000000000000),(945071694641299341683/1000000000000000000),(482974405567813723/500000000000000000)⟩,(499047212973280453/500000000000000000),(196969042597209037/500000000000000000),(5977068426928787/25000000000000000),(44606079201074069/200000000000000000)⟩
theorem valid3463 : certificate3463.Valid := by decide +kernel
theorem sound3463 : certificate3463.Sound := rat_cut_bin_certificate_sound certificate3463 profilesValid3463 numericValid3463 valid3463

def retention3464 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(13272367510661229517/28877946132205359430),(141608737833819783/15625000000000000),1,(9522387520085936953279088200465455143/9062959221364466112000000000000000000),false,MergedCutProfiles.Batch532.profile21281,(fun _ => MergedCutProfiles.Batch532.profile21281)⟩
theorem profilesValid3464 : retention3464.ProfilesValid := by
  exact MergedCutProfiles.Batch532.valid21281
theorem numericValid3464 : retention3464.NumericValid := by decide +kernel
def certificate3464 : RatCutBinCertificate := ⟨⟨retention3464,(2296346003733447707/1000000000000000000),(24651154762240763/125000000000000000),(16312639462881190313/1000000000000000000),(945071694641299341683/1000000000000000000),(1022930993654247231/1000000000000000000)⟩,(99803927535897663/100000000000000000),(118151868554957623/1000000000000000000),(627335458619670987/1000000000000000000),(57543326074063883/100000000000000000)⟩
theorem valid3464 : certificate3464.Valid := by decide +kernel
theorem sound3464 : certificate3464.Sound := rat_cut_bin_certificate_sound certificate3464 profilesValid3464 numericValid3464 valid3464

def retention3465 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(28744144316959562563/57755892264410718860),(13272367510661229517/500000000000000000),1,(26457732598911332999118989318821509507/26544735021322459034000000000000000000),false,MergedCutProfiles.Batch532.profile21282,(fun _ => MergedCutProfiles.Batch532.profile21282)⟩
theorem profilesValid3465 : retention3465.ProfilesValid := by
  exact MergedCutProfiles.Batch532.valid21282
theorem numericValid3465 : retention3465.NumericValid := by decide +kernel
def certificate3465 : RatCutBinCertificate := ⟨⟨retention3465,(2296346003733447707/1000000000000000000),(24651154762240763/125000000000000000),(16312639462881190313/1000000000000000000),(945071694641299341683/1000000000000000000),(484480434798509827/500000000000000000)⟩,(99803927535897663/100000000000000000),(15591600767285587/125000000000000000),(613778633085111323/1000000000000000000),(286315641691948247/500000000000000000)⟩
theorem valid3465 : certificate3465.Valid := by decide +kernel
theorem sound3465 : certificate3465.Sound := rat_cut_bin_certificate_sound certificate3465 profilesValid3465 numericValid3465 valid3465

def retention3466 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(1/2),(28744144316959562563/1000000000000000000),1,(28539796192222870422051064394124456933/28744144316959562563000000000000000000),false,MergedCutProfiles.Batch411.profile16479,(fun _ => MergedCutProfiles.Batch411.profile16479)⟩
theorem profilesValid3466 : retention3466.ProfilesValid := by
  exact MergedCutProfiles.Batch411.valid16479
theorem numericValid3466 : retention3466.NumericValid := by decide +kernel
def certificate3466 : RatCutBinCertificate := ⟨⟨retention3466,(2296346003733447707/1000000000000000000),(24651154762240763/125000000000000000),(16312639462881190313/1000000000000000000),(945071694641299341683/1000000000000000000),(241282313703981257/250000000000000000)⟩,(99803927535897663/100000000000000000),(125228002052512801/1000000000000000000),(612770797745779201/1000000000000000000),(22841781223976493/40000000000000000)⟩
theorem valid3466 : certificate3466.Valid := by decide +kernel
theorem sound3466 : certificate3466.Sound := rat_cut_bin_certificate_sound certificate3466 profilesValid3466 numericValid3466 valid3466

def retention3467 : RatCutRetentionCertificate := ⟨(31/500),(249/4000),(909316059867196595/57204096836931725928),(900312930561580787/1000000000000000000),(59/20),(44661686025755979457/20000000000000000000),true,MergedCutProfiles.Batch532.profile21283,![MergedCutProfiles.Batch532.profile21283,MergedCutProfiles.Batch532.profile21284,MergedCutProfiles.Batch532.profile21285,MergedCutProfiles.Batch532.profile21286,MergedCutProfiles.Batch532.profile21287,MergedCutProfiles.Batch532.profile21288,MergedCutProfiles.Batch532.profile21289,MergedCutProfiles.Batch532.profile21290,MergedCutProfiles.Batch532.profile21291,MergedCutProfiles.Batch532.profile21292,MergedCutProfiles.Batch532.profile21293,MergedCutProfiles.Batch532.profile21294,MergedCutProfiles.Batch532.profile21295,MergedCutProfiles.Batch532.profile21296,MergedCutProfiles.Batch532.profile21297,MergedCutProfiles.Batch532.profile21298]⟩
theorem profilesValid3467 : retention3467.ProfilesValid := by
  change ∀ j : Fin 16, (retention3467.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch532.valid21283
  · exact MergedCutProfiles.Batch532.valid21284
  · exact MergedCutProfiles.Batch532.valid21285
  · exact MergedCutProfiles.Batch532.valid21286
  · exact MergedCutProfiles.Batch532.valid21287
  · exact MergedCutProfiles.Batch532.valid21288
  · exact MergedCutProfiles.Batch532.valid21289
  · exact MergedCutProfiles.Batch532.valid21290
  · exact MergedCutProfiles.Batch532.valid21291
  · exact MergedCutProfiles.Batch532.valid21292
  · exact MergedCutProfiles.Batch532.valid21293
  · exact MergedCutProfiles.Batch532.valid21294
  · exact MergedCutProfiles.Batch532.valid21295
  · exact MergedCutProfiles.Batch532.valid21296
  · exact MergedCutProfiles.Batch532.valid21297
  · exact MergedCutProfiles.Batch532.valid21298
theorem numericValid3467 : retention3467.NumericValid := by decide +kernel
def certificate3467 : RatCutBinCertificate := ⟨⟨retention3467,(1118732903210718603/500000000000000000),(99557273866218649/500000000000000000),(823257618475654671/50000000000000000),(11791708434151031007/12500000000000000),(1076628617026696969/500000000000000000)⟩,(499047495099218751/500000000000000000),(31610076331814241/100000000000000000),(39979113433617439/125000000000000000),(182706756696224289/1000000000000000000)⟩
theorem valid3467 : certificate3467.Valid := by decide +kernel
theorem sound3467 : certificate3467.Sound := rat_cut_bin_certificate_sound certificate3467 profilesValid3467 numericValid3467 valid3467

def certificates : List RatCutBinCertificate := [certificate3456,certificate3457,certificate3458,certificate3459,certificate3460,certificate3461,certificate3462,certificate3463,certificate3464,certificate3465,certificate3466,certificate3467]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3456,List.forall_mem_cons.mpr ⟨sound3457,List.forall_mem_cons.mpr ⟨sound3458,List.forall_mem_cons.mpr ⟨sound3459,List.forall_mem_cons.mpr ⟨sound3460,List.forall_mem_cons.mpr ⟨sound3461,List.forall_mem_cons.mpr ⟨sound3462,List.forall_mem_cons.mpr ⟨sound3463,List.forall_mem_cons.mpr ⟨sound3464,List.forall_mem_cons.mpr ⟨sound3465,List.forall_mem_cons.mpr ⟨sound3466,List.forall_mem_cons.mpr ⟨sound3467,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch288
