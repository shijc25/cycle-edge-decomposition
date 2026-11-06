import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch005
import Cycle12.MergedCutProfiles.Batch006
import Cycle12.MergedCutProfiles.Batch007
import Cycle12.MergedCutProfiles.Batch308
import Cycle12.MergedCutProfiles.Batch309
import Cycle12.MergedCutProfiles.Batch441
import Cycle12.MergedCutProfiles.Batch562
import Cycle12.MergedCutProfiles.Batch644

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch361

def retention4332 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(32000000000000000000/82624014196148766232829),(15215789724397044897/1000000000000000000),1,(11685515540632883791906871838259491003/5071929908132348299000000000000000000),false,MergedCutProfiles.Batch644.profile25790,(fun _ => MergedCutProfiles.Batch644.profile25790)⟩
theorem profilesValid4332 : retention4332.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25790
theorem numericValid4332 : retention4332.NumericValid := by decide +kernel
def certificate4332 : RatCutBinCertificate := ⟨⟨retention4332,(1627222038509417263/1000000000000000000),(721626522366223/500000000000000000),(110674435016275059/15625000000000000),(587816181513631838837573/500000000000000000),(2303626844936861857/1000000000000000000)⟩,(124999827157246951/125000000000000000),(35043784335496437/1000000000000000000),(829727822805065931/1000000000000000000),(1660053257364161973/1000000000000000000)⟩
theorem valid4332 : certificate4332.Valid := by decide +kernel
theorem sound4332 : certificate4332.Sound := rat_cut_bin_certificate_sound certificate4332 profilesValid4332 numericValid4332 valid4332

def retention4333 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(1/2),64,1,(63842211595158023048219618863822294719/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch005.profile236,(fun _ => MergedCutProfiles.Batch005.profile236)⟩
theorem profilesValid4333 : retention4333.ProfilesValid := by
  exact MergedCutProfiles.Batch005.valid236
theorem numericValid4333 : retention4333.NumericValid := by decide +kernel
def certificate4333 : RatCutBinCertificate := ⟨⟨retention4333,(1627222038509417263/1000000000000000000),(721626522366223/500000000000000000),(110674435016275059/15625000000000000),(587816181513631838837573/500000000000000000),(249300749066229731/250000000000000000)⟩,(124999827157246951/125000000000000000),(80954231631671883/1000000000000000000),(355079813709666761/500000000000000000),(697307366733337503/1000000000000000000)⟩
theorem valid4333 : certificate4333.Valid := by decide +kernel
theorem sound4333 : certificate4333.Sound := rat_cut_bin_certificate_sound certificate4333 profilesValid4333 numericValid4333 valid4333

def retention4334 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(705200327357687599/165248028392297532465658),(698218145898700593/1000000000000000000),4,(555658934599789913779018824610183809/232739381966233531000000000000000000),false,MergedCutProfiles.Batch644.profile25791,(fun _ => MergedCutProfiles.Batch644.profile25791)⟩
theorem profilesValid4334 : retention4334.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25791
theorem numericValid4334 : retention4334.NumericValid := by decide +kernel
def certificate4334 : RatCutBinCertificate := ⟨⟨retention4334,(1776321414509417263/1000000000000000000),(721626522366223/500000000000000000),(110674435016275059/15625000000000000),(587816181513631838837573/500000000000000000),(74563281229675251/31250000000000000)⟩,(249999622639963869/250000000000000000),(663470104625009669/1000000000000000000),(32163515685869791/500000000000000000),(31618317270780213/1000000000000000000)⟩
theorem valid4334 : certificate4334.Valid := by decide +kernel
theorem sound4334 : certificate4334.Sound := rat_cut_bin_certificate_sound certificate4334 profilesValid4334 numericValid4334 valid4334

def retention4335 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(4458952276022075430/82624014196148766232829),(705200327357687599/1000000000000000000),4,(6730296144288576910283199133116630327/2820801309430750396000000000000000000),false,MergedCutProfiles.Batch644.profile25792,(fun _ => MergedCutProfiles.Batch644.profile25792)⟩
theorem profilesValid4335 : retention4335.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25792
theorem numericValid4335 : retention4335.NumericValid := by decide +kernel
def certificate4335 : RatCutBinCertificate := ⟨⟨retention4335,(1776321414509417263/1000000000000000000),(721626522366223/500000000000000000),(110674435016275059/15625000000000000),(587816181513631838837573/500000000000000000),(2384504104188890441/1000000000000000000)⟩,(249999622639963869/250000000000000000),(661695729593997049/1000000000000000000),(2033043176336089/31250000000000000),(32016264029488007/1000000000000000000)⟩
theorem valid4335 : certificate4335.Valid := by decide +kernel
theorem sound4335 : certificate4335.Sound := rat_cut_bin_certificate_sound certificate4335 profilesValid4335 numericValid4335 valid4335

def retention4336 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(1/40),(445895227602207543/50000000000000000),(23/20),(76742026501097594445237005756000028359/35671618208176603440000000000000000000),false,MergedCutProfiles.Batch644.profile25793,(fun _ => MergedCutProfiles.Batch644.profile25793)⟩
theorem profilesValid4336 : retention4336.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25793
theorem numericValid4336 : retention4336.NumericValid := by decide +kernel
def certificate4336 : RatCutBinCertificate := ⟨⟨retention4336,(1776321414509417263/1000000000000000000),(721626522366223/500000000000000000),(110674435016275059/15625000000000000),(587816181513631838837573/500000000000000000),(537732675977792083/250000000000000000)⟩,(249999622639963869/250000000000000000),(101839241697713897/200000000000000000),(147136103791182561/1000000000000000000),(46550194324639141/200000000000000000)⟩
theorem valid4336 : certificate4336.Valid := by decide +kernel
theorem sound4336 : certificate4336.Sound := rat_cut_bin_certificate_sound certificate4336 profilesValid4336 numericValid4336 valid4336

def retention4337 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(229502759231037367/40290505214374806148667),(282131575882422583/500000000000000000),4,(247007175424356452894784412732923699/112852630352969033200000000000000000),true,MergedCutProfiles.Batch644.profile25794,![MergedCutProfiles.Batch644.profile25794,MergedCutProfiles.Batch644.profile25794,MergedCutProfiles.Batch562.profile22515,MergedCutProfiles.Batch562.profile22515,MergedCutProfiles.Batch562.profile22515,MergedCutProfiles.Batch562.profile22515,MergedCutProfiles.Batch562.profile22516,MergedCutProfiles.Batch562.profile22516,MergedCutProfiles.Batch562.profile22516,MergedCutProfiles.Batch562.profile22516,MergedCutProfiles.Batch562.profile22517,MergedCutProfiles.Batch562.profile22517,MergedCutProfiles.Batch562.profile22517,MergedCutProfiles.Batch562.profile22517,MergedCutProfiles.Batch562.profile22517,MergedCutProfiles.Batch562.profile22517]⟩
theorem profilesValid4337 : retention4337.ProfilesValid := by
  change ∀ j : Fin 16, (retention4337.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch644.valid25794
  · exact MergedCutProfiles.Batch644.valid25794
  · exact MergedCutProfiles.Batch562.valid22515
  · exact MergedCutProfiles.Batch562.valid22515
  · exact MergedCutProfiles.Batch562.valid22515
  · exact MergedCutProfiles.Batch562.valid22515
  · exact MergedCutProfiles.Batch562.valid22516
  · exact MergedCutProfiles.Batch562.valid22516
  · exact MergedCutProfiles.Batch562.valid22516
  · exact MergedCutProfiles.Batch562.valid22516
  · exact MergedCutProfiles.Batch562.valid22517
  · exact MergedCutProfiles.Batch562.valid22517
  · exact MergedCutProfiles.Batch562.valid22517
  · exact MergedCutProfiles.Batch562.valid22517
  · exact MergedCutProfiles.Batch562.valid22517
  · exact MergedCutProfiles.Batch562.valid22517
theorem numericValid4337 : retention4337.NumericValid := by decide +kernel
def certificate4337 : RatCutBinCertificate := ⟨⟨retention4337,(222425573155974093/125000000000000000),(1970684370264843/1000000000000000000),(1433645119237357817/200000000000000000),(87027072012813190743797/100000000000000000),(437360383797429451/200000000000000000)⟩,(999997958294564771/1000000000000000000),(600122647743457611/1000000000000000000),(46720992844093947/500000000000000000),(41123717371185671/1000000000000000000)⟩
theorem valid4337 : certificate4337.Valid := by decide +kernel
theorem sound4337 : certificate4337.Sound := rat_cut_bin_certificate_sound certificate4337 profilesValid4337 numericValid4337 valid4337

def retention4338 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(3867560000000000/367390625055089417769),(688508277693112101/1000000000000000000),4,(6552014976907550128749106241597253191/2754033110772448404000000000000000000),true,MergedCutProfiles.Batch644.profile25794,![MergedCutProfiles.Batch644.profile25794,MergedCutProfiles.Batch562.profile22515,MergedCutProfiles.Batch562.profile22515,MergedCutProfiles.Batch562.profile22516,MergedCutProfiles.Batch562.profile22516,MergedCutProfiles.Batch562.profile22517,MergedCutProfiles.Batch562.profile22517,MergedCutProfiles.Batch562.profile22517,MergedCutProfiles.Batch562.profile22517,MergedCutProfiles.Batch441.profile17670,MergedCutProfiles.Batch441.profile17670,MergedCutProfiles.Batch441.profile17670,MergedCutProfiles.Batch441.profile17670,MergedCutProfiles.Batch562.profile22518,MergedCutProfiles.Batch562.profile22518,MergedCutProfiles.Batch562.profile22518]⟩
theorem profilesValid4338 : retention4338.ProfilesValid := by
  change ∀ j : Fin 16, (retention4338.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch644.valid25794
  · exact MergedCutProfiles.Batch562.valid22515
  · exact MergedCutProfiles.Batch562.valid22515
  · exact MergedCutProfiles.Batch562.valid22516
  · exact MergedCutProfiles.Batch562.valid22516
  · exact MergedCutProfiles.Batch562.valid22517
  · exact MergedCutProfiles.Batch562.valid22517
  · exact MergedCutProfiles.Batch562.valid22517
  · exact MergedCutProfiles.Batch562.valid22517
  · exact MergedCutProfiles.Batch441.valid17670
  · exact MergedCutProfiles.Batch441.valid17670
  · exact MergedCutProfiles.Batch441.valid17670
  · exact MergedCutProfiles.Batch441.valid17670
  · exact MergedCutProfiles.Batch562.valid22518
  · exact MergedCutProfiles.Batch562.valid22518
  · exact MergedCutProfiles.Batch562.valid22518
theorem numericValid4338 : retention4338.NumericValid := by decide +kernel
def certificate4338 : RatCutBinCertificate := ⟨⟨retention4338,(222425573155974093/125000000000000000),(1970684370264843/1000000000000000000),(1433645119237357817/200000000000000000),(87027072012813190743797/100000000000000000),(297138128891906667/125000000000000000)⟩,(999997958294564771/1000000000000000000),(48352468073392049/100000000000000000),(165120608023111321/1000000000000000000),(20177725567263891/250000000000000000)⟩
theorem valid4338 : certificate4338.Valid := by decide +kernel
theorem sound4338 : certificate4338.Sound := rat_cut_bin_certificate_sound certificate4338 profilesValid4338 numericValid4338 valid4338

def retention4339 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(699490426478243007/40290505214374806148667),(31810681/25000000),(5/2),(12074895825224097958956844216025154399/5089708960000000000000000000000000000),true,MergedCutProfiles.Batch562.profile22515,![MergedCutProfiles.Batch562.profile22515,MergedCutProfiles.Batch562.profile22516,MergedCutProfiles.Batch562.profile22516,MergedCutProfiles.Batch562.profile22517,MergedCutProfiles.Batch562.profile22517,MergedCutProfiles.Batch441.profile17670,MergedCutProfiles.Batch441.profile17670,MergedCutProfiles.Batch562.profile22518,MergedCutProfiles.Batch562.profile22518,MergedCutProfiles.Batch562.profile22518,MergedCutProfiles.Batch441.profile17671,MergedCutProfiles.Batch441.profile17671,MergedCutProfiles.Batch441.profile17671,MergedCutProfiles.Batch441.profile17671,MergedCutProfiles.Batch308.profile12358,MergedCutProfiles.Batch308.profile12358]⟩
theorem profilesValid4339 : retention4339.ProfilesValid := by
  change ∀ j : Fin 16, (retention4339.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch562.valid22515
  · exact MergedCutProfiles.Batch562.valid22516
  · exact MergedCutProfiles.Batch562.valid22516
  · exact MergedCutProfiles.Batch562.valid22517
  · exact MergedCutProfiles.Batch562.valid22517
  · exact MergedCutProfiles.Batch441.valid17670
  · exact MergedCutProfiles.Batch441.valid17670
  · exact MergedCutProfiles.Batch562.valid22518
  · exact MergedCutProfiles.Batch562.valid22518
  · exact MergedCutProfiles.Batch562.valid22518
  · exact MergedCutProfiles.Batch441.valid17671
  · exact MergedCutProfiles.Batch441.valid17671
  · exact MergedCutProfiles.Batch441.valid17671
  · exact MergedCutProfiles.Batch441.valid17671
  · exact MergedCutProfiles.Batch308.valid12358
  · exact MergedCutProfiles.Batch308.valid12358
theorem numericValid4339 : retention4339.NumericValid := by decide +kernel
def certificate4339 : RatCutBinCertificate := ⟨⟨retention4339,(222425573155974093/125000000000000000),(1970684370264843/1000000000000000000),(1433645119237357817/200000000000000000),(87027072012813190743797/100000000000000000),(1185595413884950977/500000000000000000)⟩,(999997958294564771/1000000000000000000),(341499512409455383/1000000000000000000),(291582942670824451/1000000000000000000),(106519331490107481/500000000000000000)⟩
theorem valid4339 : certificate4339.Valid := by decide +kernel
theorem sound4339 : certificate4339.Sound := rat_cut_bin_certificate_sound certificate4339 profilesValid4339 numericValid4339 valid4339

def retention4340 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(64000000000000000000/120871515643124418446001),(2098471279434729021/1000000000000000000),(9/5),(13606609505655255932277869344693386269/5829086887318691725000000000000000000),true,MergedCutProfiles.Batch005.profile238,![MergedCutProfiles.Batch005.profile238,MergedCutProfiles.Batch006.profile254,MergedCutProfiles.Batch309.profile12367,MergedCutProfiles.Batch006.profile255,MergedCutProfiles.Batch309.profile12363,MergedCutProfiles.Batch309.profile12364,MergedCutProfiles.Batch006.profile245,MergedCutProfiles.Batch006.profile246,MergedCutProfiles.Batch006.profile247,MergedCutProfiles.Batch006.profile248,MergedCutProfiles.Batch006.profile249,MergedCutProfiles.Batch006.profile250,MergedCutProfiles.Batch006.profile251,MergedCutProfiles.Batch006.profile257,MergedCutProfiles.Batch006.profile253,MergedCutProfiles.Batch006.profile258]⟩
theorem profilesValid4340 : retention4340.ProfilesValid := by
  change ∀ j : Fin 16, (retention4340.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch005.valid238
  · exact MergedCutProfiles.Batch006.valid254
  · exact MergedCutProfiles.Batch309.valid12367
  · exact MergedCutProfiles.Batch006.valid255
  · exact MergedCutProfiles.Batch309.valid12363
  · exact MergedCutProfiles.Batch309.valid12364
  · exact MergedCutProfiles.Batch006.valid245
  · exact MergedCutProfiles.Batch006.valid246
  · exact MergedCutProfiles.Batch006.valid247
  · exact MergedCutProfiles.Batch006.valid248
  · exact MergedCutProfiles.Batch006.valid249
  · exact MergedCutProfiles.Batch006.valid250
  · exact MergedCutProfiles.Batch006.valid251
  · exact MergedCutProfiles.Batch006.valid257
  · exact MergedCutProfiles.Batch006.valid253
  · exact MergedCutProfiles.Batch006.valid258
theorem numericValid4340 : retention4340.NumericValid := by decide +kernel
def certificate4340 : RatCutBinCertificate := ⟨⟨retention4340,(222425573155974093/125000000000000000),(1970684370264843/1000000000000000000),(1433645119237357817/200000000000000000),(87027072012813190743797/100000000000000000),(1166690168006698411/500000000000000000)⟩,(999997958294564771/1000000000000000000),(279475463250320531/1000000000000000000),(91049550057339457/250000000000000000),(175744466634126151/500000000000000000)⟩
theorem valid4340 : certificate4340.Valid := by decide +kernel
theorem sound4340 : certificate4340.Sound := rat_cut_bin_certificate_sound certificate4340 profilesValid4340 numericValid4340 valid4340

def retention4341 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(1/2),64,1,(255368860549321472084694123425840443671/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch007.profile295,(fun _ => MergedCutProfiles.Batch007.profile295)⟩
theorem profilesValid4341 : retention4341.ProfilesValid := by
  exact MergedCutProfiles.Batch007.valid295
theorem numericValid4341 : retention4341.NumericValid := by decide +kernel
def certificate4341 : RatCutBinCertificate := ⟨⟨retention4341,(222425573155974093/125000000000000000),(1970684370264843/1000000000000000000),(1433645119237357817/200000000000000000),(87027072012813190743797/100000000000000000),(997045418657421359/1000000000000000000)⟩,(999997958294564771/1000000000000000000),(418497461836630997/1000000000000000000),(13559696461920023/62500000000000000),(106497732577042499/500000000000000000)⟩
theorem valid4341 : certificate4341.Valid := by decide +kernel
theorem sound4341 : certificate4341.Sound := rat_cut_bin_certificate_sound certificate4341 profilesValid4341 numericValid4341 valid4341

def retention4342 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(64000000000000000000/120871515643124418446001),(384483422764000587/25000000000000000),1,(11794004096386171341305115456870086397/5126445636853341160000000000000000000),false,MergedCutProfiles.Batch644.profile25795,(fun _ => MergedCutProfiles.Batch644.profile25795)⟩
theorem profilesValid4342 : retention4342.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25795
theorem numericValid4342 : retention4342.NumericValid := by decide +kernel
def certificate4342 : RatCutBinCertificate := ⟨⟨retention4342,(202418550530974093/125000000000000000),(1970684370264843/1000000000000000000),(1433645119237357817/200000000000000000),(87027072012813190743797/100000000000000000),(9200699812504589/4000000000000000)⟩,(249999535486130443/250000000000000000),(17454183508450657/500000000000000000),(415057003218853263/500000000000000000),(415245683261850979/250000000000000000)⟩
theorem valid4342 : certificate4342.Valid := by decide +kernel
theorem sound4342 : certificate4342.Sound := rat_cut_bin_certificate_sound certificate4342 profilesValid4342 numericValid4342 valid4342

def retention4343 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(1/2),64,1,(255368860549321472084694123425840443671/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch007.profile295,(fun _ => MergedCutProfiles.Batch007.profile295)⟩
theorem profilesValid4343 : retention4343.ProfilesValid := by
  exact MergedCutProfiles.Batch007.valid295
theorem numericValid4343 : retention4343.NumericValid := by decide +kernel
def certificate4343 : RatCutBinCertificate := ⟨⟨retention4343,(202418550530974093/125000000000000000),(1970684370264843/1000000000000000000),(1433645119237357817/200000000000000000),(87027072012813190743797/100000000000000000),(997089421208685919/1000000000000000000)⟩,(249999535486130443/250000000000000000),(503310872618853/6250000000000000),(711170844406364927/1000000000000000000),(69822163603643967/100000000000000000)⟩
theorem valid4343 : certificate4343.Valid := by decide +kernel
theorem sound4343 : certificate4343.Sound := rat_cut_bin_certificate_sound certificate4343 profilesValid4343 numericValid4343 valid4343

def certificates : List RatCutBinCertificate := [certificate4332,certificate4333,certificate4334,certificate4335,certificate4336,certificate4337,certificate4338,certificate4339,certificate4340,certificate4341,certificate4342,certificate4343]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4332,List.forall_mem_cons.mpr ⟨sound4333,List.forall_mem_cons.mpr ⟨sound4334,List.forall_mem_cons.mpr ⟨sound4335,List.forall_mem_cons.mpr ⟨sound4336,List.forall_mem_cons.mpr ⟨sound4337,List.forall_mem_cons.mpr ⟨sound4338,List.forall_mem_cons.mpr ⟨sound4339,List.forall_mem_cons.mpr ⟨sound4340,List.forall_mem_cons.mpr ⟨sound4341,List.forall_mem_cons.mpr ⟨sound4342,List.forall_mem_cons.mpr ⟨sound4343,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch361
