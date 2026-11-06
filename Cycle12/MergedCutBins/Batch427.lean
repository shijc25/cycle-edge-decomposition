import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch631
import Cycle12.MergedCutProfiles.Batch632
import Cycle12.MergedCutProfiles.Batch711
import Cycle12.MergedCutProfiles.Batch712
import Cycle12.MergedCutProfiles.Batch713

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch427

def retention5124 : RatCutRetentionCertificate := ⟨(61/1000),(31/500),(124832448282221648/165016835041173482459),(767799224368385911/1000000000000000000),4,(94302609204687588651804229667636621/38389961218419295550000000000000000),false,MergedCutProfiles.Batch711.profile28471,(fun _ => MergedCutProfiles.Batch711.profile28471)⟩
theorem profilesValid5124 : retention5124.ProfilesValid := by
  exact MergedCutProfiles.Batch711.valid28471
theorem numericValid5124 : retention5124.NumericValid := by decide +kernel
def certificate5124 : RatCutBinCertificate := ⟨⟨retention5124,(997797158768336193/500000000000000000),(24651154762240763/125000000000000000),(8081272758122984273/500000000000000000),(18785377548995781000869/1000000000000000000),(589760256617871819/250000000000000000)⟩,(249978480232172581/250000000000000000),(192902784711783073/250000000000000000),(14164860540588283/500000000000000000),(3503691649294679/250000000000000000)⟩
theorem valid5124 : certificate5124.Valid := by decide +kernel
theorem sound5124 : certificate5124.Sound := rat_cut_bin_certificate_sound certificate5124 profilesValid5124 numericValid5124 valid5124

def retention5125 : RatCutRetentionCertificate := ⟨(61/1000),(31/500),(2459508918043606658/1155117845288214377213),(54614196123471971/62500000000000000),(73/20),(212269641001983386484981035231633738911/87382713797555153600000000000000000000),false,MergedCutProfiles.Batch711.profile28472,(fun _ => MergedCutProfiles.Batch711.profile28472)⟩
theorem profilesValid5125 : retention5125.ProfilesValid := by
  exact MergedCutProfiles.Batch711.valid28472
theorem numericValid5125 : retention5125.NumericValid := by decide +kernel
def certificate5125 : RatCutBinCertificate := ⟨⟨retention5125,(997797158768336193/500000000000000000),(24651154762240763/125000000000000000),(8081272758122984273/500000000000000000),(18785377548995781000869/1000000000000000000),(585079743326260189/250000000000000000)⟩,(249978480232172581/250000000000000000),(379282845280790097/500000000000000000),(15911489463251121/500000000000000000),(8493644280980093/500000000000000000)⟩
theorem valid5125 : certificate5125.Valid := by decide +kernel
theorem sound5125 : certificate5125.Sound := rat_cut_bin_certificate_sound certificate5125 profilesValid5125 numericValid5125 valid5125

def retention5126 : RatCutRetentionCertificate := ⟨(61/1000),(31/500),(24740422913511558844/1155117845288214377213),(1229754459021803329/500000000000000000),(37/20),(2217314814144699477733828071850654139191/983803567217442663200000000000000000000),false,MergedCutProfiles.Batch711.profile28473,(fun _ => MergedCutProfiles.Batch711.profile28473)⟩
theorem profilesValid5126 : retention5126.ProfilesValid := by
  exact MergedCutProfiles.Batch711.valid28473
theorem numericValid5126 : retention5126.NumericValid := by decide +kernel
def certificate5126 : RatCutBinCertificate := ⟨⟨retention5126,(997797158768336193/500000000000000000),(24651154762240763/125000000000000000),(8081272758122984273/500000000000000000),(18785377548995781000869/1000000000000000000),(552192996958672577/250000000000000000)⟩,(249978480232172581/250000000000000000),(70867595366636467/100000000000000000),(9457317805291703/200000000000000000),(2235882402566451/50000000000000000)⟩
theorem valid5126 : certificate5126.Valid := by decide +kernel
theorem sound5126 : certificate5126.Sound := rat_cut_bin_certificate_sound certificate5126 profilesValid5126 numericValid5126 valid5126

def retention5127 : RatCutRetentionCertificate := ⟨(61/1000),(31/500),(1/40),(6185105728377889711/250000000000000000),(21/20),(1376283899668620987137484526046227429811/618510572837788971100000000000000000000),false,MergedCutProfiles.Batch711.profile28474,(fun _ => MergedCutProfiles.Batch711.profile28474)⟩
theorem profilesValid5127 : retention5127.ProfilesValid := by
  exact MergedCutProfiles.Batch711.valid28474
theorem numericValid5127 : retention5127.NumericValid := by decide +kernel
def certificate5127 : RatCutBinCertificate := ⟨⟨retention5127,(997797158768336193/500000000000000000),(24651154762240763/125000000000000000),(8081272758122984273/500000000000000000),(18785377548995781000869/1000000000000000000),(2199591275242046699/1000000000000000000)⟩,(249978480232172581/250000000000000000),(41515997741505571/62500000000000000),(64005080966952061/1000000000000000000),(62032217364204219/500000000000000000)⟩
theorem valid5127 : certificate5127.Valid := by decide +kernel
theorem sound5127 : certificate5127.Sound := rat_cut_bin_certificate_sound certificate5127 profilesValid5127 numericValid5127 valid5127

def retention5128 : RatCutRetentionCertificate := ⟨(31/500),(63/1000),(13247274721619008/24169545643253642081),(74670943681314867/125000000000000000),4,(73107282985881948373/32000000000000000000),true,MergedCutProfiles.Batch711.profile28475,![MergedCutProfiles.Batch711.profile28475,MergedCutProfiles.Batch711.profile28476,MergedCutProfiles.Batch711.profile28477,MergedCutProfiles.Batch711.profile28478,MergedCutProfiles.Batch711.profile28479,MergedCutProfiles.Batch712.profile28480,MergedCutProfiles.Batch712.profile28481,MergedCutProfiles.Batch712.profile28482,MergedCutProfiles.Batch712.profile28483,MergedCutProfiles.Batch712.profile28484,MergedCutProfiles.Batch712.profile28485,MergedCutProfiles.Batch712.profile28486,MergedCutProfiles.Batch631.profile25255,MergedCutProfiles.Batch712.profile28487,MergedCutProfiles.Batch712.profile28488,MergedCutProfiles.Batch712.profile28489]⟩
theorem profilesValid5128 : retention5128.ProfilesValid := by
  change ∀ j : Fin 16, (retention5128.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch711.valid28475
  · exact MergedCutProfiles.Batch711.valid28476
  · exact MergedCutProfiles.Batch711.valid28477
  · exact MergedCutProfiles.Batch711.valid28478
  · exact MergedCutProfiles.Batch711.valid28479
  · exact MergedCutProfiles.Batch712.valid28480
  · exact MergedCutProfiles.Batch712.valid28481
  · exact MergedCutProfiles.Batch712.valid28482
  · exact MergedCutProfiles.Batch712.valid28483
  · exact MergedCutProfiles.Batch712.valid28484
  · exact MergedCutProfiles.Batch712.valid28485
  · exact MergedCutProfiles.Batch712.valid28486
  · exact MergedCutProfiles.Batch631.valid25255
  · exact MergedCutProfiles.Batch712.valid28487
  · exact MergedCutProfiles.Batch712.valid28488
  · exact MergedCutProfiles.Batch712.valid28489
theorem numericValid5128 : retention5128.NumericValid := by decide +kernel
def certificate5128 : RatCutBinCertificate := ⟨⟨retention5128,(973171758537087533/500000000000000000),(204909449857824037/1000000000000000000),(8232728109168444141/500000000000000000),(9210269669224913247457/500000000000000000),(136732165794301489/62500000000000000)⟩,(999915174081267131/1000000000000000000),(761589858391604551/1000000000000000000),(968541978547369/31250000000000000),(13792378493219031/1000000000000000000)⟩
theorem valid5128 : certificate5128.Valid := by decide +kernel
theorem sound5128 : certificate5128.Sound := rat_cut_bin_certificate_sound certificate5128 profilesValid5128 numericValid5128 valid5128

def retention5129 : RatCutRetentionCertificate := ⟨(31/500),(63/1000),(525945823000000000/555899549794833767863),(4760739353081831/7812500000000000),4,(1151757416644897073/500000000000000000),true,MergedCutProfiles.Batch712.profile28490,![MergedCutProfiles.Batch712.profile28490,MergedCutProfiles.Batch712.profile28491,MergedCutProfiles.Batch712.profile28492,MergedCutProfiles.Batch712.profile28481,MergedCutProfiles.Batch712.profile28483,MergedCutProfiles.Batch712.profile28493,MergedCutProfiles.Batch712.profile28486,MergedCutProfiles.Batch712.profile28487,MergedCutProfiles.Batch712.profile28489,MergedCutProfiles.Batch712.profile28494,MergedCutProfiles.Batch631.profile25256,MergedCutProfiles.Batch712.profile28495,MergedCutProfiles.Batch712.profile28496,MergedCutProfiles.Batch712.profile28497,MergedCutProfiles.Batch631.profile25257,MergedCutProfiles.Batch631.profile25272]⟩
theorem profilesValid5129 : retention5129.ProfilesValid := by
  change ∀ j : Fin 16, (retention5129.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch712.valid28490
  · exact MergedCutProfiles.Batch712.valid28491
  · exact MergedCutProfiles.Batch712.valid28492
  · exact MergedCutProfiles.Batch712.valid28481
  · exact MergedCutProfiles.Batch712.valid28483
  · exact MergedCutProfiles.Batch712.valid28493
  · exact MergedCutProfiles.Batch712.valid28486
  · exact MergedCutProfiles.Batch712.valid28487
  · exact MergedCutProfiles.Batch712.valid28489
  · exact MergedCutProfiles.Batch712.valid28494
  · exact MergedCutProfiles.Batch631.valid25256
  · exact MergedCutProfiles.Batch712.valid28495
  · exact MergedCutProfiles.Batch712.valid28496
  · exact MergedCutProfiles.Batch712.valid28497
  · exact MergedCutProfiles.Batch631.valid25257
  · exact MergedCutProfiles.Batch631.valid25272
theorem numericValid5129 : retention5129.NumericValid := by decide +kernel
def certificate5129 : RatCutBinCertificate := ⟨⟨retention5129,(973171758537087533/500000000000000000),(204909449857824037/1000000000000000000),(8232728109168444141/500000000000000000),(9210269669224913247457/500000000000000000),(441325380315459069/200000000000000000)⟩,(999915174081267131/1000000000000000000),(372647618007559709/500000000000000000),(17803354701804097/500000000000000000),(16015861427952621/1000000000000000000)⟩
theorem valid5129 : certificate5129.Valid := by decide +kernel
theorem sound5129 : certificate5129.Sound := rat_cut_bin_certificate_sound certificate5129 profilesValid5129 numericValid5129 valid5129

def retention5130 : RatCutRetentionCertificate := ⟨(31/500),(63/1000),(1527273905471031881/555899549794833767863),(525945823/500000000),3,(19227815276117412143/8000000000000000000),true,MergedCutProfiles.Batch711.profile28479,![MergedCutProfiles.Batch711.profile28479,MergedCutProfiles.Batch712.profile28484,MergedCutProfiles.Batch712.profile28488,MergedCutProfiles.Batch712.profile28498,MergedCutProfiles.Batch631.profile25257,MergedCutProfiles.Batch712.profile28499,MergedCutProfiles.Batch712.profile28500,MergedCutProfiles.Batch712.profile28501,MergedCutProfiles.Batch631.profile25260,MergedCutProfiles.Batch632.profile25296,MergedCutProfiles.Batch632.profile25286,MergedCutProfiles.Batch712.profile28502,MergedCutProfiles.Batch631.profile25263,MergedCutProfiles.Batch712.profile28503,MergedCutProfiles.Batch632.profile25287,MergedCutProfiles.Batch712.profile28504]⟩
theorem profilesValid5130 : retention5130.ProfilesValid := by
  change ∀ j : Fin 16, (retention5130.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch711.valid28479
  · exact MergedCutProfiles.Batch712.valid28484
  · exact MergedCutProfiles.Batch712.valid28488
  · exact MergedCutProfiles.Batch712.valid28498
  · exact MergedCutProfiles.Batch631.valid25257
  · exact MergedCutProfiles.Batch712.valid28499
  · exact MergedCutProfiles.Batch712.valid28500
  · exact MergedCutProfiles.Batch712.valid28501
  · exact MergedCutProfiles.Batch631.valid25260
  · exact MergedCutProfiles.Batch632.valid25296
  · exact MergedCutProfiles.Batch632.valid25286
  · exact MergedCutProfiles.Batch712.valid28502
  · exact MergedCutProfiles.Batch631.valid25263
  · exact MergedCutProfiles.Batch712.valid28503
  · exact MergedCutProfiles.Batch632.valid25287
  · exact MergedCutProfiles.Batch712.valid28504
theorem numericValid5130 : retention5130.NumericValid := by decide +kernel
def certificate5130 : RatCutBinCertificate := ⟨⟨retention5130,(973171758537087533/500000000000000000),(204909449857824037/1000000000000000000),(8232728109168444141/500000000000000000),(9210269669224913247457/500000000000000000),(2330811036201824461/1000000000000000000)⟩,(999915174081267131/1000000000000000000),(512051592039666109/1000000000000000000),(72608468825876047/500000000000000000),(45262672248447541/500000000000000000)⟩
theorem valid5130 : certificate5130.Valid := by decide +kernel
theorem sound5130 : certificate5130.Sound := rat_cut_bin_certificate_sound certificate5130 profilesValid5130 numericValid5130 valid5130

def retention5131 : RatCutRetentionCertificate := ⟨(31/500),(63/1000),(32000000000000000000/555899549794833767863),(1527273905471031881/500000000000000000),(3/2),(263714709190829634609/128000000000000000000),true,MergedCutProfiles.Batch712.profile28505,![MergedCutProfiles.Batch712.profile28505,MergedCutProfiles.Batch712.profile28506,MergedCutProfiles.Batch712.profile28507,MergedCutProfiles.Batch712.profile28508,MergedCutProfiles.Batch712.profile28509,MergedCutProfiles.Batch712.profile28510,MergedCutProfiles.Batch712.profile28511,MergedCutProfiles.Batch712.profile28512,MergedCutProfiles.Batch712.profile28513,MergedCutProfiles.Batch712.profile28514,MergedCutProfiles.Batch712.profile28515,MergedCutProfiles.Batch712.profile28516,MergedCutProfiles.Batch712.profile28517,MergedCutProfiles.Batch712.profile28518,MergedCutProfiles.Batch712.profile28519,MergedCutProfiles.Batch713.profile28520]⟩
theorem profilesValid5131 : retention5131.ProfilesValid := by
  change ∀ j : Fin 16, (retention5131.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch712.valid28505
  · exact MergedCutProfiles.Batch712.valid28506
  · exact MergedCutProfiles.Batch712.valid28507
  · exact MergedCutProfiles.Batch712.valid28508
  · exact MergedCutProfiles.Batch712.valid28509
  · exact MergedCutProfiles.Batch712.valid28510
  · exact MergedCutProfiles.Batch712.valid28511
  · exact MergedCutProfiles.Batch712.valid28512
  · exact MergedCutProfiles.Batch712.valid28513
  · exact MergedCutProfiles.Batch712.valid28514
  · exact MergedCutProfiles.Batch712.valid28515
  · exact MergedCutProfiles.Batch712.valid28516
  · exact MergedCutProfiles.Batch712.valid28517
  · exact MergedCutProfiles.Batch712.valid28518
  · exact MergedCutProfiles.Batch712.valid28519
  · exact MergedCutProfiles.Batch713.valid28520
theorem numericValid5131 : retention5131.NumericValid := by decide +kernel
def certificate5131 : RatCutBinCertificate := ⟨⟨retention5131,(973171758537087533/500000000000000000),(204909449857824037/1000000000000000000),(8232728109168444141/500000000000000000),(9210269669224913247457/500000000000000000),(404787653752397591/200000000000000000)⟩,(999915174081267131/1000000000000000000),(388464316577431539/1000000000000000000),(6105495212741987/25000000000000000),(254534807913450149/1000000000000000000)⟩
theorem valid5131 : certificate5131.Valid := by decide +kernel
theorem sound5131 : certificate5131.Sound := rat_cut_bin_certificate_sound certificate5131 profilesValid5131 numericValid5131 valid5131

def retention5132 : RatCutRetentionCertificate := ⟨(31/500),(63/1000),(1/2),64,1,(255411314097293059585699365940977515079/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch632.profile25310,(fun _ => MergedCutProfiles.Batch632.profile25310)⟩
theorem profilesValid5132 : retention5132.ProfilesValid := by
  exact MergedCutProfiles.Batch632.valid25310
theorem numericValid5132 : retention5132.NumericValid := by decide +kernel
def certificate5132 : RatCutBinCertificate := ⟨⟨retention5132,(973171758537087533/500000000000000000),(204909449857824037/1000000000000000000),(8232728109168444141/500000000000000000),(9210269669224913247457/500000000000000000),(12168482113690923/12500000000000000)⟩,(999915174081267131/1000000000000000000),(598390998463147527/1000000000000000000),(18865740647289029/200000000000000000),(90443390820501849/1000000000000000000)⟩
theorem valid5132 : certificate5132.Valid := by decide +kernel
theorem sound5132 : certificate5132.Sound := rat_cut_bin_certificate_sound certificate5132 profilesValid5132 numericValid5132 valid5132

def retention5133 : RatCutRetentionCertificate := ⟨(31/500),(63/1000),(32000000000000000000/555899549794833767863),(50287791709272955471/1000000000000000000),1,(1296222538614599305819190402719137099/628597396365911943387500000000000000),false,MergedCutProfiles.Batch713.profile28521,(fun _ => MergedCutProfiles.Batch713.profile28521)⟩
theorem profilesValid5133 : retention5133.ProfilesValid := by
  exact MergedCutProfiles.Batch713.valid28521
theorem numericValid5133 : retention5133.NumericValid := by decide +kernel
def certificate5133 : RatCutBinCertificate := ⟨⟨retention5133,(856756783537087533/500000000000000000),(204909449857824037/1000000000000000000),(8232728109168444141/500000000000000000),(9210269669224913247457/500000000000000000),(2040762677799867951/1000000000000000000)⟩,(999925321507227799/1000000000000000000),(15150380441659853/1000000000000000000),(888890161212939483/1000000000000000000),(87156836355887527/50000000000000000)⟩
theorem valid5133 : certificate5133.Valid := by decide +kernel
theorem sound5133 : certificate5133.Sound := rat_cut_bin_certificate_sound certificate5133 profilesValid5133 numericValid5133 valid5133

def retention5134 : RatCutRetentionCertificate := ⟨(31/500),(63/1000),(1/2),64,1,(255411314097293059585699365940977515079/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch632.profile25310,(fun _ => MergedCutProfiles.Batch632.profile25310)⟩
theorem profilesValid5134 : retention5134.ProfilesValid := by
  exact MergedCutProfiles.Batch632.valid25310
theorem numericValid5134 : retention5134.NumericValid := by decide +kernel
def certificate5134 : RatCutBinCertificate := ⟨⟨retention5134,(856756783537087533/500000000000000000),(204909449857824037/1000000000000000000),(8232728109168444141/500000000000000000),(9210269669224913247457/500000000000000000),(488188046872369777/500000000000000000)⟩,(999925321507227799/1000000000000000000),(31666415388383823/1000000000000000000),(41971232699166259/50000000000000000),(807217325723402501/1000000000000000000)⟩
theorem valid5134 : certificate5134.Valid := by decide +kernel
theorem sound5134 : certificate5134.Sound := rat_cut_bin_certificate_sound certificate5134 profilesValid5134 numericValid5134 valid5134

def retention5135 : RatCutRetentionCertificate := ⟨(31/500),(63/1000),(772048579720785847/1111799099589667535726),(76440453437701569/100000000000000000),4,(2506364739370234837907208235720117917/1019206045836020920000000000000000000),false,MergedCutProfiles.Batch713.profile28522,(fun _ => MergedCutProfiles.Batch713.profile28522)⟩
theorem profilesValid5135 : retention5135.ProfilesValid := by
  exact MergedCutProfiles.Batch713.valid28522
theorem numericValid5135 : retention5135.NumericValid := by decide +kernel
def certificate5135 : RatCutBinCertificate := ⟨⟨retention5135,(1002207365037087533/500000000000000000),(204909449857824037/1000000000000000000),(8232728109168444141/500000000000000000),(9210269669224913247457/500000000000000000),(147459743536625271/62500000000000000)⟩,(15623635049314767/15625000000000000),(768152798117794101/1000000000000000000),(29234142559524347/1000000000000000000),(14453437501505129/1000000000000000000)⟩
theorem valid5135 : certificate5135.Valid := by decide +kernel
theorem sound5135 : certificate5135.Sound := rat_cut_bin_certificate_sound certificate5135 profilesValid5135 numericValid5135 valid5135

def certificates : List RatCutBinCertificate := [certificate5124,certificate5125,certificate5126,certificate5127,certificate5128,certificate5129,certificate5130,certificate5131,certificate5132,certificate5133,certificate5134,certificate5135]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound5124,List.forall_mem_cons.mpr ⟨sound5125,List.forall_mem_cons.mpr ⟨sound5126,List.forall_mem_cons.mpr ⟨sound5127,List.forall_mem_cons.mpr ⟨sound5128,List.forall_mem_cons.mpr ⟨sound5129,List.forall_mem_cons.mpr ⟨sound5130,List.forall_mem_cons.mpr ⟨sound5131,List.forall_mem_cons.mpr ⟨sound5132,List.forall_mem_cons.mpr ⟨sound5133,List.forall_mem_cons.mpr ⟨sound5134,List.forall_mem_cons.mpr ⟨sound5135,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch427
