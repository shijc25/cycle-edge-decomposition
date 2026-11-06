import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch386
import Cycle12.MergedCutProfiles.Batch506
import Cycle12.MergedCutProfiles.Batch507
import Cycle12.MergedCutProfiles.Batch508

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch275

def retention3300 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(34677378164604959977/76571538888968188262),(2285189270901349807/250000000000000000),(21/20),(992156121997423620154622537324719905191/914075708360539922800000000000000000000),false,MergedCutProfiles.Batch506.profile20248,(fun _ => MergedCutProfiles.Batch506.profile20248)⟩
theorem profilesValid3300 : retention3300.ProfilesValid := by
  exact MergedCutProfiles.Batch506.valid20248
theorem numericValid3300 : retention3300.NumericValid := by decide +kernel
def certificate3300 : RatCutBinCertificate := ⟨⟨retention3300,(2133392551677267859/1000000000000000000),(14887102204219317/100000000000000000),(1426033585491067991/100000000000000000),(1098394204114735108467/1000000000000000000),(1699255319861939/1600000000000000)⟩,(998334426507043657/1000000000000000000),(214747747397435761/500000000000000000),(20751841374514351/100000000000000000),(47387707043352667/250000000000000000)⟩
theorem valid3300 : certificate3300.Valid := by decide +kernel
theorem sound3300 : certificate3300.Sound := rat_cut_bin_certificate_sound certificate3300 profilesValid3300 numericValid3300 valid3300

def retention3301 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(18963068896967339097/38285769444484094131),(34677378164604959977/1000000000000000000),1,(139211438687829471278036041133846423787/138709512658419839908000000000000000000),false,MergedCutProfiles.Batch506.profile20249,(fun _ => MergedCutProfiles.Batch506.profile20249)⟩
theorem profilesValid3301 : retention3301.ProfilesValid := by
  exact MergedCutProfiles.Batch506.valid20249
theorem numericValid3301 : retention3301.NumericValid := by decide +kernel
def certificate3301 : RatCutBinCertificate := ⟨⟨retention3301,(2133392551677267859/1000000000000000000),(14887102204219317/100000000000000000),(1426033585491067991/100000000000000000),(1098394204114735108467/1000000000000000000),(981346865413214983/1000000000000000000)⟩,(998334426507043657/1000000000000000000),(436269787140767361/1000000000000000000),(25230801408630069/125000000000000000),(24037943983157973/125000000000000000)⟩
theorem valid3301 : certificate3301.Valid := by decide +kernel
theorem sound3301 : certificate3301.Sound := rat_cut_bin_certificate_sound certificate3301 profilesValid3301 numericValid3301 valid3301

def retention3302 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(1/2),(18963068896967339097/500000000000000000),1,(1118074541110877719293049526073198393/1123737416116583057600000000000000000),false,MergedCutProfiles.Batch386.profile15456,(fun _ => MergedCutProfiles.Batch386.profile15456)⟩
theorem profilesValid3302 : retention3302.ProfilesValid := by
  exact MergedCutProfiles.Batch386.valid15456
theorem numericValid3302 : retention3302.NumericValid := by decide +kernel
def certificate3302 : RatCutBinCertificate := ⟨⟨retention3302,(2133392551677267859/1000000000000000000),(14887102204219317/100000000000000000),(1426033585491067991/100000000000000000),(1098394204114735108467/1000000000000000000),(972689009793551667/1000000000000000000)⟩,(998334426507043657/1000000000000000000),(439270143165889739/1000000000000000000),(49841991517554573/250000000000000000),(47188466514408231/250000000000000000)⟩
theorem valid3302 : certificate3302.Valid := by decide +kernel
theorem sound3302 : certificate3302.Sound := rat_cut_bin_certificate_sound certificate3302 profilesValid3302 numericValid3302 valid3302

def retention3303 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(17699994988166725826/38285769444484094131),(153237813697088227/15625000000000000),1,(2163519258644274582053271591817507453/2064677910866030848000000000000000000),false,MergedCutProfiles.Batch506.profile20250,(fun _ => MergedCutProfiles.Batch506.profile20250)⟩
theorem profilesValid3303 : retention3303.ProfilesValid := by
  exact MergedCutProfiles.Batch506.valid20250
theorem numericValid3303 : retention3303.NumericValid := by decide +kernel
def certificate3303 : RatCutBinCertificate := ⟨⟨retention3303,(2228911576677267859/1000000000000000000),(14887102204219317/100000000000000000),(1426033585491067991/100000000000000000),(1098394204114735108467/1000000000000000000),(1024603443982013189/1000000000000000000)⟩,(998259831683907101/1000000000000000000),(15011974757080729/125000000000000000),(623299067527462987/1000000000000000000),(577162667237915293/1000000000000000000)⟩
theorem valid3303 : certificate3303.Valid := by decide +kernel
theorem sound3303 : certificate3303.Sound := rat_cut_bin_certificate_sound certificate3303 profilesValid3303 numericValid3303 valid3303

def retention3304 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(37953580717860889787/76571538888968188262),(8849997494083362913/250000000000000000),1,(35508329425174947934467252310680717543/35399989976333451652000000000000000000),false,MergedCutProfiles.Batch506.profile20251,(fun _ => MergedCutProfiles.Batch506.profile20251)⟩
theorem profilesValid3304 : retention3304.ProfilesValid := by
  exact MergedCutProfiles.Batch506.valid20251
theorem numericValid3304 : retention3304.NumericValid := by decide +kernel
def certificate3304 : RatCutBinCertificate := ⟨⟨retention3304,(2228911576677267859/1000000000000000000),(14887102204219317/100000000000000000),(1426033585491067991/100000000000000000),(1098394204114735108467/1000000000000000000),(979791587349056247/1000000000000000000)⟩,(998259831683907101/1000000000000000000),(125588512787230363/1000000000000000000),(612038143537233917/1000000000000000000),(72810891960935887/125000000000000000)⟩
theorem valid3304 : certificate3304.Valid := by decide +kernel
theorem sound3304 : certificate3304.Sound := rat_cut_bin_certificate_sound certificate3304 profilesValid3304 numericValid3304 valid3304

def retention3305 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(1/2),(37953580717860889787/1000000000000000000),1,(30210001487576242368259969239765163263/30362864574288711829600000000000000000),false,MergedCutProfiles.Batch386.profile15456,(fun _ => MergedCutProfiles.Batch386.profile15456)⟩
theorem profilesValid3305 : retention3305.ProfilesValid := by
  exact MergedCutProfiles.Batch386.valid15456
theorem numericValid3305 : retention3305.NumericValid := by decide +kernel
def certificate3305 : RatCutBinCertificate := ⟨⟨retention3305,(2228911576677267859/1000000000000000000),(14887102204219317/100000000000000000),(1426033585491067991/100000000000000000),(1098394204114735108467/1000000000000000000),(242924153766027451/250000000000000000)⟩,(998259831683907101/1000000000000000000),(63317380337117443/500000000000000000),(15247923971932757/25000000000000000),(1802620764907559/3125000000000000)⟩
theorem valid3305 : certificate3305.Valid := by decide +kernel
theorem sound3305 : certificate3305.Sound := rat_cut_bin_certificate_sound certificate3305 profilesValid3305 numericValid3305 valid3305

def retention3306 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(840202160190600603/73424105109331892356),(166376665384277347/200000000000000000),(13/4),(18158257089704999527/8000000000000000000),true,MergedCutProfiles.Batch506.profile20252,![MergedCutProfiles.Batch506.profile20252,MergedCutProfiles.Batch506.profile20253,MergedCutProfiles.Batch506.profile20254,MergedCutProfiles.Batch506.profile20255,MergedCutProfiles.Batch506.profile20256,MergedCutProfiles.Batch506.profile20257,MergedCutProfiles.Batch506.profile20258,MergedCutProfiles.Batch506.profile20259,MergedCutProfiles.Batch506.profile20260,MergedCutProfiles.Batch506.profile20261,MergedCutProfiles.Batch506.profile20262,MergedCutProfiles.Batch506.profile20263,MergedCutProfiles.Batch506.profile20264,MergedCutProfiles.Batch506.profile20265,MergedCutProfiles.Batch506.profile20266,MergedCutProfiles.Batch506.profile20267]⟩
theorem profilesValid3306 : retention3306.ProfilesValid := by
  change ∀ j : Fin 16, (retention3306.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch506.valid20252
  · exact MergedCutProfiles.Batch506.valid20253
  · exact MergedCutProfiles.Batch506.valid20254
  · exact MergedCutProfiles.Batch506.valid20255
  · exact MergedCutProfiles.Batch506.valid20256
  · exact MergedCutProfiles.Batch506.valid20257
  · exact MergedCutProfiles.Batch506.valid20258
  · exact MergedCutProfiles.Batch506.valid20259
  · exact MergedCutProfiles.Batch506.valid20260
  · exact MergedCutProfiles.Batch506.valid20261
  · exact MergedCutProfiles.Batch506.valid20262
  · exact MergedCutProfiles.Batch506.valid20263
  · exact MergedCutProfiles.Batch506.valid20264
  · exact MergedCutProfiles.Batch506.valid20265
  · exact MergedCutProfiles.Batch506.valid20266
  · exact MergedCutProfiles.Batch506.valid20267
theorem numericValid3306 : retention3306.NumericValid := by decide +kernel
def certificate3306 : RatCutBinCertificate := ⟨⟨retention3306,(10728847932270571/5000000000000000),(155212952940275013/1000000000000000000),(14510522890331406119/1000000000000000000),(535882737577125299899/500000000000000000),(548795715263395359/250000000000000000)⟩,(998295452455399649/1000000000000000000),(373647570313020979/1000000000000000000),(129257515455690077/500000000000000000),(69712905586339377/500000000000000000)⟩
theorem valid3306 : certificate3306.Valid := by decide +kernel
theorem sound3306 : certificate3306.Sound := rat_cut_bin_certificate_sound certificate3306 profilesValid3306 numericValid3306 valid3306

def retention3307 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(1025206307407336983/73424105109331892356),(840202160190600603/1000000000000000000),(16/5),(180084101489439045147/80000000000000000000),true,MergedCutProfiles.Batch506.profile20268,![MergedCutProfiles.Batch506.profile20268,MergedCutProfiles.Batch506.profile20269,MergedCutProfiles.Batch506.profile20270,MergedCutProfiles.Batch506.profile20271,MergedCutProfiles.Batch506.profile20272,MergedCutProfiles.Batch506.profile20273,MergedCutProfiles.Batch506.profile20274,MergedCutProfiles.Batch506.profile20275,MergedCutProfiles.Batch506.profile20262,MergedCutProfiles.Batch506.profile20276,MergedCutProfiles.Batch506.profile20277,MergedCutProfiles.Batch506.profile20278,MergedCutProfiles.Batch506.profile20279,MergedCutProfiles.Batch507.profile20280,MergedCutProfiles.Batch507.profile20281,MergedCutProfiles.Batch507.profile20282]⟩
theorem profilesValid3307 : retention3307.ProfilesValid := by
  change ∀ j : Fin 16, (retention3307.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch506.valid20268
  · exact MergedCutProfiles.Batch506.valid20269
  · exact MergedCutProfiles.Batch506.valid20270
  · exact MergedCutProfiles.Batch506.valid20271
  · exact MergedCutProfiles.Batch506.valid20272
  · exact MergedCutProfiles.Batch506.valid20273
  · exact MergedCutProfiles.Batch506.valid20274
  · exact MergedCutProfiles.Batch506.valid20275
  · exact MergedCutProfiles.Batch506.valid20262
  · exact MergedCutProfiles.Batch506.valid20276
  · exact MergedCutProfiles.Batch506.valid20277
  · exact MergedCutProfiles.Batch506.valid20278
  · exact MergedCutProfiles.Batch506.valid20279
  · exact MergedCutProfiles.Batch507.valid20280
  · exact MergedCutProfiles.Batch507.valid20281
  · exact MergedCutProfiles.Batch507.valid20282
theorem numericValid3307 : retention3307.NumericValid := by decide +kernel
def certificate3307 : RatCutBinCertificate := ⟨⟨retention3307,(10728847932270571/5000000000000000),(155212952940275013/1000000000000000000),(14510522890331406119/1000000000000000000),(535882737577125299899/500000000000000000),(1063281080421767/488281250000000)⟩,(998295452455399649/1000000000000000000),(93702502955227359/250000000000000000),(32171572384311877/125000000000000000),(139483919284663183/1000000000000000000)⟩
theorem valid3307 : certificate3307.Valid := by decide +kernel
theorem sound3307 : certificate3307.Sound := rat_cut_bin_certificate_sound certificate3307 profilesValid3307 numericValid3307 valid3307

def retention3308 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(272825384500000000/18356026277332973089),(1025206307407336983/1000000000000000000),(27/10),(178537895235367071477/80000000000000000000),true,MergedCutProfiles.Batch507.profile20283,![MergedCutProfiles.Batch507.profile20283,MergedCutProfiles.Batch507.profile20284,MergedCutProfiles.Batch507.profile20285,MergedCutProfiles.Batch507.profile20286,MergedCutProfiles.Batch507.profile20287,MergedCutProfiles.Batch507.profile20288,MergedCutProfiles.Batch507.profile20289,MergedCutProfiles.Batch507.profile20290,MergedCutProfiles.Batch507.profile20291,MergedCutProfiles.Batch506.profile20264,MergedCutProfiles.Batch507.profile20292,MergedCutProfiles.Batch507.profile20293,MergedCutProfiles.Batch507.profile20294,MergedCutProfiles.Batch507.profile20295,MergedCutProfiles.Batch507.profile20296,MergedCutProfiles.Batch507.profile20297]⟩
theorem profilesValid3308 : retention3308.ProfilesValid := by
  change ∀ j : Fin 16, (retention3308.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch507.valid20283
  · exact MergedCutProfiles.Batch507.valid20284
  · exact MergedCutProfiles.Batch507.valid20285
  · exact MergedCutProfiles.Batch507.valid20286
  · exact MergedCutProfiles.Batch507.valid20287
  · exact MergedCutProfiles.Batch507.valid20288
  · exact MergedCutProfiles.Batch507.valid20289
  · exact MergedCutProfiles.Batch507.valid20290
  · exact MergedCutProfiles.Batch507.valid20291
  · exact MergedCutProfiles.Batch506.valid20264
  · exact MergedCutProfiles.Batch507.valid20292
  · exact MergedCutProfiles.Batch507.valid20293
  · exact MergedCutProfiles.Batch507.valid20294
  · exact MergedCutProfiles.Batch507.valid20295
  · exact MergedCutProfiles.Batch507.valid20296
  · exact MergedCutProfiles.Batch507.valid20297
theorem numericValid3308 : retention3308.NumericValid := by decide +kernel
def certificate3308 : RatCutBinCertificate := ⟨⟨retention3308,(10728847932270571/5000000000000000),(155212952940275013/1000000000000000000),(14510522890331406119/1000000000000000000),(535882737577125299899/500000000000000000),(13560931157969381/6250000000000000)⟩,(998295452455399649/1000000000000000000),(34257766748336093/100000000000000000),(145213241697334663/500000000000000000),(180515202403840499/1000000000000000000)⟩
theorem valid3308 : certificate3308.Valid := by decide +kernel
theorem sound3308 : certificate3308.Sound := rat_cut_bin_certificate_sound certificate3308 profilesValid3308 numericValid3308 valid3308

def retention3309 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(309640229007491604/18356026277332973089),(545650769/500000000),(13/5),(7123101672219711737/3200000000000000000),true,MergedCutProfiles.Batch507.profile20298,![MergedCutProfiles.Batch507.profile20298,MergedCutProfiles.Batch506.profile20254,MergedCutProfiles.Batch507.profile20299,MergedCutProfiles.Batch507.profile20300,MergedCutProfiles.Batch506.profile20273,MergedCutProfiles.Batch507.profile20301,MergedCutProfiles.Batch507.profile20302,MergedCutProfiles.Batch507.profile20303,MergedCutProfiles.Batch507.profile20304,MergedCutProfiles.Batch507.profile20305,MergedCutProfiles.Batch507.profile20306,MergedCutProfiles.Batch507.profile20307,MergedCutProfiles.Batch507.profile20308,MergedCutProfiles.Batch507.profile20309,MergedCutProfiles.Batch507.profile20310,MergedCutProfiles.Batch507.profile20311]⟩
theorem profilesValid3309 : retention3309.ProfilesValid := by
  change ∀ j : Fin 16, (retention3309.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch507.valid20298
  · exact MergedCutProfiles.Batch506.valid20254
  · exact MergedCutProfiles.Batch507.valid20299
  · exact MergedCutProfiles.Batch507.valid20300
  · exact MergedCutProfiles.Batch506.valid20273
  · exact MergedCutProfiles.Batch507.valid20301
  · exact MergedCutProfiles.Batch507.valid20302
  · exact MergedCutProfiles.Batch507.valid20303
  · exact MergedCutProfiles.Batch507.valid20304
  · exact MergedCutProfiles.Batch507.valid20305
  · exact MergedCutProfiles.Batch507.valid20306
  · exact MergedCutProfiles.Batch507.valid20307
  · exact MergedCutProfiles.Batch507.valid20308
  · exact MergedCutProfiles.Batch507.valid20309
  · exact MergedCutProfiles.Batch507.valid20310
  · exact MergedCutProfiles.Batch507.valid20311
theorem numericValid3309 : retention3309.NumericValid := by decide +kernel
def certificate3309 : RatCutBinCertificate := ⟨⟨retention3309,(10728847932270571/5000000000000000),(155212952940275013/1000000000000000000),(14510522890331406119/1000000000000000000),(535882737577125299899/500000000000000000),(433258000627440769/200000000000000000)⟩,(998295452455399649/1000000000000000000),(333871062906284463/1000000000000000000),(74965777216068123/250000000000000000),(48186124868350123/250000000000000000)⟩
theorem valid3309 : certificate3309.Valid := by decide +kernel
theorem sound3309 : certificate3309.Sound := rat_cut_bin_certificate_sound certificate3309 profilesValid3309 numericValid3309 valid3309

def retention3310 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(141696809801783823/2622289468190424727),(77410057251872901/62500000000000000),(47/20),(41312225716737895947/20000000000000000000),true,MergedCutProfiles.Batch507.profile20312,![MergedCutProfiles.Batch507.profile20312,MergedCutProfiles.Batch507.profile20313,MergedCutProfiles.Batch507.profile20314,MergedCutProfiles.Batch507.profile20315,MergedCutProfiles.Batch507.profile20316,MergedCutProfiles.Batch507.profile20317,MergedCutProfiles.Batch507.profile20318,MergedCutProfiles.Batch507.profile20319,MergedCutProfiles.Batch508.profile20320,MergedCutProfiles.Batch508.profile20321,MergedCutProfiles.Batch508.profile20322,MergedCutProfiles.Batch508.profile20323,MergedCutProfiles.Batch508.profile20324,MergedCutProfiles.Batch508.profile20325,MergedCutProfiles.Batch508.profile20326,MergedCutProfiles.Batch508.profile20327]⟩
theorem profilesValid3310 : retention3310.ProfilesValid := by
  change ∀ j : Fin 16, (retention3310.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch507.valid20312
  · exact MergedCutProfiles.Batch507.valid20313
  · exact MergedCutProfiles.Batch507.valid20314
  · exact MergedCutProfiles.Batch507.valid20315
  · exact MergedCutProfiles.Batch507.valid20316
  · exact MergedCutProfiles.Batch507.valid20317
  · exact MergedCutProfiles.Batch507.valid20318
  · exact MergedCutProfiles.Batch507.valid20319
  · exact MergedCutProfiles.Batch508.valid20320
  · exact MergedCutProfiles.Batch508.valid20321
  · exact MergedCutProfiles.Batch508.valid20322
  · exact MergedCutProfiles.Batch508.valid20323
  · exact MergedCutProfiles.Batch508.valid20324
  · exact MergedCutProfiles.Batch508.valid20325
  · exact MergedCutProfiles.Batch508.valid20326
  · exact MergedCutProfiles.Batch508.valid20327
theorem numericValid3310 : retention3310.NumericValid := by decide +kernel
def certificate3310 : RatCutBinCertificate := ⟨⟨retention3310,(10728847932270571/5000000000000000),(155212952940275013/1000000000000000000),(14510522890331406119/1000000000000000000),(535882737577125299899/500000000000000000),(502917619241299651/250000000000000000)⟩,(998295452455399649/1000000000000000000),(6823113711796703/20000000000000000),(72988113726093451/250000000000000000),(19273737586786441/100000000000000000)⟩
theorem valid3310 : certificate3310.Valid := by decide +kernel
theorem sound3310 : certificate3310.Sound := rat_cut_bin_certificate_sound certificate3310 profilesValid3310 numericValid3310 valid3310

def retention3311 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(26805373943513364641/73424105109331892356),(991877668612486761/250000000000000000),(6/5),(501264945211963567262751217715778686399/396751067444994704400000000000000000000),false,MergedCutProfiles.Batch508.profile20328,(fun _ => MergedCutProfiles.Batch508.profile20328)⟩
theorem profilesValid3311 : retention3311.ProfilesValid := by
  exact MergedCutProfiles.Batch508.valid20328
theorem numericValid3311 : retention3311.NumericValid := by decide +kernel
def certificate3311 : RatCutBinCertificate := ⟨⟨retention3311,(10728847932270571/5000000000000000),(155212952940275013/1000000000000000000),(14510522890331406119/1000000000000000000),(535882737577125299899/500000000000000000),(1235880603782768749/1000000000000000000)⟩,(998295452455399649/1000000000000000000),(80566447915017969/200000000000000000),(230897322335444187/1000000000000000000),(24392404415378307/125000000000000000)⟩
theorem valid3311 : certificate3311.Valid := by decide +kernel
theorem sound3311 : certificate3311.Sound := rat_cut_bin_certificate_sound certificate3311 profilesValid3311 numericValid3311 valid3311

def certificates : List RatCutBinCertificate := [certificate3300,certificate3301,certificate3302,certificate3303,certificate3304,certificate3305,certificate3306,certificate3307,certificate3308,certificate3309,certificate3310,certificate3311]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3300,List.forall_mem_cons.mpr ⟨sound3301,List.forall_mem_cons.mpr ⟨sound3302,List.forall_mem_cons.mpr ⟨sound3303,List.forall_mem_cons.mpr ⟨sound3304,List.forall_mem_cons.mpr ⟨sound3305,List.forall_mem_cons.mpr ⟨sound3306,List.forall_mem_cons.mpr ⟨sound3307,List.forall_mem_cons.mpr ⟨sound3308,List.forall_mem_cons.mpr ⟨sound3309,List.forall_mem_cons.mpr ⟨sound3310,List.forall_mem_cons.mpr ⟨sound3311,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch275
