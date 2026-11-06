import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch208
import Cycle12.MergedCutProfiles.Batch209
import Cycle12.MergedCutProfiles.Batch210

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch106

def retention1272 : RatCutRetentionCertificate := ⟨(231/4000),(29/500),(1343651757092000401/13526363696142142574),(920607525381927631/1000000000000000000),(13/5),(2438202726326744048923/1280000000000000000000),true,MergedCutProfiles.Batch208.profile8351,![MergedCutProfiles.Batch208.profile8351,MergedCutProfiles.Batch208.profile8352,MergedCutProfiles.Batch208.profile8353,MergedCutProfiles.Batch208.profile8354,MergedCutProfiles.Batch208.profile8355,MergedCutProfiles.Batch208.profile8356,MergedCutProfiles.Batch208.profile8357,MergedCutProfiles.Batch208.profile8358,MergedCutProfiles.Batch208.profile8359,MergedCutProfiles.Batch209.profile8360,MergedCutProfiles.Batch209.profile8361,MergedCutProfiles.Batch209.profile8362,MergedCutProfiles.Batch209.profile8363,MergedCutProfiles.Batch209.profile8364,MergedCutProfiles.Batch209.profile8365,MergedCutProfiles.Batch209.profile8366]⟩
theorem profilesValid1272 : retention1272.ProfilesValid := by
  change ∀ j : Fin 16, (retention1272.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch208.valid8351
  · exact MergedCutProfiles.Batch208.valid8352
  · exact MergedCutProfiles.Batch208.valid8353
  · exact MergedCutProfiles.Batch208.valid8354
  · exact MergedCutProfiles.Batch208.valid8355
  · exact MergedCutProfiles.Batch208.valid8356
  · exact MergedCutProfiles.Batch208.valid8357
  · exact MergedCutProfiles.Batch208.valid8358
  · exact MergedCutProfiles.Batch208.valid8359
  · exact MergedCutProfiles.Batch209.valid8360
  · exact MergedCutProfiles.Batch209.valid8361
  · exact MergedCutProfiles.Batch209.valid8362
  · exact MergedCutProfiles.Batch209.valid8363
  · exact MergedCutProfiles.Batch209.valid8364
  · exact MergedCutProfiles.Batch209.valid8365
  · exact MergedCutProfiles.Batch209.valid8366
theorem numericValid1272 : retention1272.NumericValid := by decide +kernel
def certificate1272 : RatCutBinCertificate := ⟨⟨retention1272,(1142711195124929509/500000000000000000),(168442616661570077/1000000000000000000),(3807216807094491581/250000000000000000),(51575497878328939587/250000000000000000),(367819885506188461/200000000000000000)⟩,(495375731098478063/500000000000000000),(45169373129270319/125000000000000000),(270819572404869299/1000000000000000000),(73114639627180887/500000000000000000)⟩
theorem valid1272 : certificate1272.Valid := by decide +kernel
theorem sound1272 : certificate1272.Sound := rat_cut_bin_certificate_sound certificate1272 profilesValid1272 numericValid1272 valid1272

def retention1273 : RatCutRetentionCertificate := ⟨(231/4000),(29/500),(1596673979625524187/6763181848071071287),(1343651757092000401/1000000000000000000),(37/20),(1974677344650452566873/1280000000000000000000),true,MergedCutProfiles.Batch209.profile8367,![MergedCutProfiles.Batch209.profile8367,MergedCutProfiles.Batch209.profile8368,MergedCutProfiles.Batch209.profile8369,MergedCutProfiles.Batch209.profile8370,MergedCutProfiles.Batch209.profile8371,MergedCutProfiles.Batch209.profile8372,MergedCutProfiles.Batch209.profile8373,MergedCutProfiles.Batch209.profile8374,MergedCutProfiles.Batch209.profile8375,MergedCutProfiles.Batch209.profile8376,MergedCutProfiles.Batch209.profile8377,MergedCutProfiles.Batch209.profile8378,MergedCutProfiles.Batch209.profile8379,MergedCutProfiles.Batch209.profile8380,MergedCutProfiles.Batch209.profile8381,MergedCutProfiles.Batch209.profile8382]⟩
theorem profilesValid1273 : retention1273.ProfilesValid := by
  change ∀ j : Fin 16, (retention1273.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch209.valid8367
  · exact MergedCutProfiles.Batch209.valid8368
  · exact MergedCutProfiles.Batch209.valid8369
  · exact MergedCutProfiles.Batch209.valid8370
  · exact MergedCutProfiles.Batch209.valid8371
  · exact MergedCutProfiles.Batch209.valid8372
  · exact MergedCutProfiles.Batch209.valid8373
  · exact MergedCutProfiles.Batch209.valid8374
  · exact MergedCutProfiles.Batch209.valid8375
  · exact MergedCutProfiles.Batch209.valid8376
  · exact MergedCutProfiles.Batch209.valid8377
  · exact MergedCutProfiles.Batch209.valid8378
  · exact MergedCutProfiles.Batch209.valid8379
  · exact MergedCutProfiles.Batch209.valid8380
  · exact MergedCutProfiles.Batch209.valid8381
  · exact MergedCutProfiles.Batch209.valid8382
theorem numericValid1273 : retention1273.NumericValid := by decide +kernel
def certificate1273 : RatCutBinCertificate := ⟨⟨retention1273,(1142711195124929509/500000000000000000),(168442616661570077/1000000000000000000),(3807216807094491581/250000000000000000),(51575497878328939587/250000000000000000),(747968068723335881/500000000000000000)⟩,(495375731098478063/500000000000000000),(48725547403973801/125000000000000000),(48591018035009789/200000000000000000),(73305436905602377/500000000000000000)⟩
theorem valid1273 : certificate1273.Valid := by decide +kernel
theorem sound1273 : certificate1273.Sound := rat_cut_bin_certificate_sound certificate1273 profilesValid1273 numericValid1273 valid1273

def retention1274 : RatCutRetentionCertificate := ⟨(231/4000),(29/500),(2900672347468877333/6763181848071071287),(1596673979625524187/500000000000000000),(23/20),(713918674359071477979/640000000000000000000),true,MergedCutProfiles.Batch209.profile8383,![MergedCutProfiles.Batch209.profile8383,MergedCutProfiles.Batch209.profile8384,MergedCutProfiles.Batch209.profile8385,MergedCutProfiles.Batch209.profile8386,MergedCutProfiles.Batch209.profile8387,MergedCutProfiles.Batch209.profile8388,MergedCutProfiles.Batch209.profile8389,MergedCutProfiles.Batch209.profile8390,MergedCutProfiles.Batch209.profile8391,MergedCutProfiles.Batch209.profile8392,MergedCutProfiles.Batch209.profile8393,MergedCutProfiles.Batch209.profile8394,MergedCutProfiles.Batch209.profile8395,MergedCutProfiles.Batch209.profile8396,MergedCutProfiles.Batch209.profile8397,MergedCutProfiles.Batch209.profile8398]⟩
theorem profilesValid1274 : retention1274.ProfilesValid := by
  change ∀ j : Fin 16, (retention1274.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch209.valid8383
  · exact MergedCutProfiles.Batch209.valid8384
  · exact MergedCutProfiles.Batch209.valid8385
  · exact MergedCutProfiles.Batch209.valid8386
  · exact MergedCutProfiles.Batch209.valid8387
  · exact MergedCutProfiles.Batch209.valid8388
  · exact MergedCutProfiles.Batch209.valid8389
  · exact MergedCutProfiles.Batch209.valid8390
  · exact MergedCutProfiles.Batch209.valid8391
  · exact MergedCutProfiles.Batch209.valid8392
  · exact MergedCutProfiles.Batch209.valid8393
  · exact MergedCutProfiles.Batch209.valid8394
  · exact MergedCutProfiles.Batch209.valid8395
  · exact MergedCutProfiles.Batch209.valid8396
  · exact MergedCutProfiles.Batch209.valid8397
  · exact MergedCutProfiles.Batch209.valid8398
theorem numericValid1274 : retention1274.NumericValid := by decide +kernel
def certificate1274 : RatCutBinCertificate := ⟨⟨retention1274,(1142711195124929509/500000000000000000),(168442616661570077/1000000000000000000),(3807216807094491581/250000000000000000),(51575497878328939587/250000000000000000),(543210610026600211/500000000000000000)⟩,(495375731098478063/500000000000000000),(110560399903594323/250000000000000000),(196933588787286399/1000000000000000000),(146428768010056279/1000000000000000000)⟩
theorem valid1274 : certificate1274.Valid := by decide +kernel
theorem sound1274 : certificate1274.Sound := rat_cut_bin_certificate_sound certificate1274 profilesValid1274 numericValid1274 valid1274

def retention1275 : RatCutRetentionCertificate := ⟨(231/4000),(29/500),(6602471414785969877/13526363696142142574),(2900672347468877333/500000000000000000),(11/10),(147483064629062891742197542665788526229/145033617373443866650000000000000000000),false,MergedCutProfiles.Batch209.profile8399,(fun _ => MergedCutProfiles.Batch209.profile8399)⟩
theorem profilesValid1275 : retention1275.ProfilesValid := by
  exact MergedCutProfiles.Batch209.valid8399
theorem numericValid1275 : retention1275.NumericValid := by decide +kernel
def certificate1275 : RatCutBinCertificate := ⟨⟨retention1275,(1142711195124929509/500000000000000000),(168442616661570077/1000000000000000000),(3807216807094491581/250000000000000000),(51575497878328939587/250000000000000000),(989078944771517303/1000000000000000000)⟩,(495375731098478063/500000000000000000),(451870188713896137/1000000000000000000),(7567271803695541/40000000000000000),(147602465731959181/1000000000000000000)⟩
theorem valid1275 : certificate1275.Valid := by decide +kernel
theorem sound1275 : certificate1275.Sound := rat_cut_bin_certificate_sound certificate1275 profilesValid1275 numericValid1275 valid1275

def retention1276 : RatCutRetentionCertificate := ⟨(231/4000),(29/500),(3367590545111583936/6763181848071071287),(6602471414785969877/1000000000000000000),(21/20),(213102600810179326151123044455170545559/215590903339950036800000000000000000000),false,MergedCutProfiles.Batch210.profile8400,(fun _ => MergedCutProfiles.Batch210.profile8400)⟩
theorem profilesValid1276 : retention1276.ProfilesValid := by
  exact MergedCutProfiles.Batch210.valid8400
theorem numericValid1276 : retention1276.NumericValid := by decide +kernel
def certificate1276 : RatCutBinCertificate := ⟨⟨retention1276,(1142711195124929509/500000000000000000),(168442616661570077/1000000000000000000),(3807216807094491581/250000000000000000),(51575497878328939587/250000000000000000),(192382539437491431/200000000000000000)⟩,(495375731098478063/500000000000000000),(459453747704016403/1000000000000000000),(91610528812523839/500000000000000000),(7339029928821473/50000000000000000)⟩
theorem valid1276 : certificate1276.Valid := by decide +kernel
theorem sound1276 : certificate1276.Sound := rat_cut_bin_certificate_sound certificate1276 profilesValid1276 numericValid1276 valid1276

def retention1277 : RatCutRetentionCertificate := ⟨(231/4000),(29/500),(1/2),(52618602267368499/7812500000000000),(21/20),(10367836414905304460085524626759439879/10523720453473699800000000000000000000),false,MergedCutProfiles.Batch210.profile8401,(fun _ => MergedCutProfiles.Batch210.profile8401)⟩
theorem profilesValid1277 : retention1277.ProfilesValid := by
  exact MergedCutProfiles.Batch210.valid8401
theorem numericValid1277 : retention1277.NumericValid := by decide +kernel
def certificate1277 : RatCutBinCertificate := ⟨⟨retention1277,(1142711195124929509/500000000000000000),(168442616661570077/1000000000000000000),(3807216807094491581/250000000000000000),(51575497878328939587/250000000000000000),(95864190181695727/100000000000000000)⟩,(495375731098478063/500000000000000000),(460279995838642211/1000000000000000000),(22822402302904347/125000000000000000),(36540973781172419/250000000000000000)⟩
theorem valid1277 : certificate1277.Valid := by decide +kernel
theorem sound1277 : certificate1277.Sound := rat_cut_bin_certificate_sound certificate1277 profilesValid1277 numericValid1277 valid1277

def retention1278 : RatCutRetentionCertificate := ⟨(231/4000),(29/500),(1/2),64,1,(3990700969808284373058544950935189511/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch210.profile8401,(fun _ => MergedCutProfiles.Batch210.profile8401)⟩
theorem profilesValid1278 : retention1278.ProfilesValid := by
  exact MergedCutProfiles.Batch210.valid8401
theorem numericValid1278 : retention1278.NumericValid := by decide +kernel
def certificate1278 : RatCutBinCertificate := ⟨⟨retention1278,(1142711195124929509/500000000000000000),(168442616661570077/1000000000000000000),(3807216807094491581/250000000000000000),(51575497878328939587/250000000000000000),(486198222871221409/500000000000000000)⟩,(495375731098478063/500000000000000000),(42123389502260831/100000000000000000),(107290234114284991/500000000000000000),(203615672386632897/1000000000000000000)⟩
theorem valid1278 : certificate1278.Valid := by decide +kernel
theorem sound1278 : certificate1278.Sound := rat_cut_bin_certificate_sound certificate1278 profilesValid1278 numericValid1278 valid1278

def retention1279 : RatCutRetentionCertificate := ⟨(231/4000),(29/500),(3136141603399192123/6763181848071071287),(177859619202131793/50000000000000000),(6/5),(236866257656024639692671353426447189/222324524002664741250000000000000000),false,MergedCutProfiles.Batch210.profile8402,(fun _ => MergedCutProfiles.Batch210.profile8402)⟩
theorem profilesValid1279 : retention1279.ProfilesValid := by
  exact MergedCutProfiles.Batch210.valid8402
theorem numericValid1279 : retention1279.NumericValid := by decide +kernel
def certificate1279 : RatCutBinCertificate := ⟨⟨retention1279,(1310504712624929509/500000000000000000),(168442616661570077/1000000000000000000),(3807216807094491581/250000000000000000),(51575497878328939587/250000000000000000),(1030612656117830001/1000000000000000000)⟩,(494695271301329829/500000000000000000),(392054465212616129/1000000000000000000),(240841861646663901/1000000000000000000),(170182608588726291/1000000000000000000)⟩
theorem valid1279 : certificate1279.Valid := by decide +kernel
theorem sound1279 : certificate1279.Sound := rat_cut_bin_certificate_sound certificate1279 profilesValid1279 numericValid1279 valid1279

def retention1280 : RatCutRetentionCertificate := ⟨(231/4000),(29/500),(3329077507146372037/6763181848071071287),(3136141603399192123/500000000000000000),(21/20),(2502479570655565258537647916400672734791/2508913282719353698400000000000000000000),false,MergedCutProfiles.Batch210.profile8403,(fun _ => MergedCutProfiles.Batch210.profile8403)⟩
theorem profilesValid1280 : retention1280.ProfilesValid := by
  exact MergedCutProfiles.Batch210.valid8403
theorem numericValid1280 : retention1280.NumericValid := by decide +kernel
def certificate1280 : RatCutBinCertificate := ⟨⟨retention1280,(1310504712624929509/500000000000000000),(168442616661570077/1000000000000000000),(3807216807094491581/250000000000000000),(51575497878328939587/250000000000000000),(483496025706909019/500000000000000000)⟩,(494695271301329829/500000000000000000),(208924309742188561/500000000000000000),(54380206897836347/250000000000000000),(173751808176475751/1000000000000000000)⟩
theorem valid1280 : certificate1280.Valid := by decide +kernel
theorem sound1280 : certificate1280.Sound := rat_cut_bin_certificate_sound certificate1280 profilesValid1280 numericValid1280 valid1280

def retention1281 : RatCutRetentionCertificate := ⟨(231/4000),(29/500),(6724736564435671515/13526363696142142574),(3329077507146372037/500000000000000000),(21/20),(376742481315701148513614515526437003193/380466000816728232800000000000000000000),false,MergedCutProfiles.Batch210.profile8404,(fun _ => MergedCutProfiles.Batch210.profile8404)⟩
theorem profilesValid1281 : retention1281.ProfilesValid := by
  exact MergedCutProfiles.Batch210.valid8404
theorem numericValid1281 : retention1281.NumericValid := by decide +kernel
def certificate1281 : RatCutBinCertificate := ⟨⟨retention1281,(1310504712624929509/500000000000000000),(168442616661570077/1000000000000000000),(3807216807094491581/250000000000000000),(51575497878328939587/250000000000000000),(191953975676640607/200000000000000000)⟩,(494695271301329829/500000000000000000),(210496444427017087/500000000000000000),(107394448943595871/500000000000000000),(42915851441286983/250000000000000000)⟩
theorem valid1281 : certificate1281.Valid := by decide +kernel
theorem sound1281 : certificate1281.Sound := rat_cut_bin_certificate_sound certificate1281 profilesValid1281 numericValid1281 valid1281

def retention1282 : RatCutRetentionCertificate := ⟨(231/4000),(29/500),(1/2),(1344947312887134303/200000000000000000),(21/20),(423985949845410464575198829528342753279/430383140123882976960000000000000000000),false,MergedCutProfiles.Batch210.profile8401,(fun _ => MergedCutProfiles.Batch210.profile8401)⟩
theorem profilesValid1282 : retention1282.ProfilesValid := by
  exact MergedCutProfiles.Batch210.valid8401
theorem numericValid1282 : retention1282.NumericValid := by decide +kernel
def certificate1282 : RatCutBinCertificate := ⟨⟨retention1282,(1310504712624929509/500000000000000000),(168442616661570077/1000000000000000000),(3807216807094491581/250000000000000000),(51575497878328939587/250000000000000000),(238673176223058571/250000000000000000)⟩,(494695271301329829/500000000000000000),(105807945233340703/250000000000000000),(106428967394250531/500000000000000000),(169517943450858477/1000000000000000000)⟩
theorem valid1282 : certificate1282.Valid := by decide +kernel
theorem sound1282 : certificate1282.Sound := rat_cut_bin_certificate_sound certificate1282 profilesValid1282 numericValid1282 valid1282

def retention1283 : RatCutRetentionCertificate := ⟨(29/500),(233/4000),(890109966273599438/13390269966443149833),(846909091106130267/1000000000000000000),(11/4),(7969604860762939911/4000000000000000000),true,MergedCutProfiles.Batch210.profile8405,![MergedCutProfiles.Batch210.profile8405,MergedCutProfiles.Batch210.profile8406,MergedCutProfiles.Batch210.profile8407,MergedCutProfiles.Batch210.profile8408,MergedCutProfiles.Batch210.profile8409,MergedCutProfiles.Batch210.profile8410,MergedCutProfiles.Batch210.profile8411,MergedCutProfiles.Batch210.profile8412,MergedCutProfiles.Batch210.profile8413,MergedCutProfiles.Batch210.profile8414,MergedCutProfiles.Batch210.profile8415,MergedCutProfiles.Batch210.profile8416,MergedCutProfiles.Batch210.profile8417,MergedCutProfiles.Batch210.profile8418,MergedCutProfiles.Batch210.profile8419,MergedCutProfiles.Batch210.profile8420]⟩
theorem profilesValid1283 : retention1283.ProfilesValid := by
  change ∀ j : Fin 16, (retention1283.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch210.valid8405
  · exact MergedCutProfiles.Batch210.valid8406
  · exact MergedCutProfiles.Batch210.valid8407
  · exact MergedCutProfiles.Batch210.valid8408
  · exact MergedCutProfiles.Batch210.valid8409
  · exact MergedCutProfiles.Batch210.valid8410
  · exact MergedCutProfiles.Batch210.valid8411
  · exact MergedCutProfiles.Batch210.valid8412
  · exact MergedCutProfiles.Batch210.valid8413
  · exact MergedCutProfiles.Batch210.valid8414
  · exact MergedCutProfiles.Batch210.valid8415
  · exact MergedCutProfiles.Batch210.valid8416
  · exact MergedCutProfiles.Batch210.valid8417
  · exact MergedCutProfiles.Batch210.valid8418
  · exact MergedCutProfiles.Batch210.valid8419
  · exact MergedCutProfiles.Batch210.valid8420
theorem numericValid1283 : retention1283.NumericValid := by decide +kernel
def certificate1283 : RatCutBinCertificate := ⟨⟨retention1283,(2290464292249505967/1000000000000000000),(17014879615267021/100000000000000000),(15297248449517538051/1000000000000000000),(12821490825172820533/62500000000000000),(961157999700042017/500000000000000000)⟩,(990697354959467891/1000000000000000000),(89306948804018843/250000000000000000),(275043747515788519/1000000000000000000),(73112420412593711/500000000000000000)⟩
theorem valid1283 : certificate1283.Valid := by decide +kernel
theorem sound1283 : certificate1283.Sound := rat_cut_bin_certificate_sound certificate1283 profilesValid1283 numericValid1283 valid1283

def certificates : List RatCutBinCertificate := [certificate1272,certificate1273,certificate1274,certificate1275,certificate1276,certificate1277,certificate1278,certificate1279,certificate1280,certificate1281,certificate1282,certificate1283]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1272,List.forall_mem_cons.mpr ⟨sound1273,List.forall_mem_cons.mpr ⟨sound1274,List.forall_mem_cons.mpr ⟨sound1275,List.forall_mem_cons.mpr ⟨sound1276,List.forall_mem_cons.mpr ⟨sound1277,List.forall_mem_cons.mpr ⟨sound1278,List.forall_mem_cons.mpr ⟨sound1279,List.forall_mem_cons.mpr ⟨sound1280,List.forall_mem_cons.mpr ⟨sound1281,List.forall_mem_cons.mpr ⟨sound1282,List.forall_mem_cons.mpr ⟨sound1283,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch106
