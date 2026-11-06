import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch040
import Cycle12.MergedCutProfiles.Batch041
import Cycle12.MergedCutProfiles.Batch042
import Cycle12.MergedCutProfiles.Batch330
import Cycle12.MergedCutProfiles.Batch331
import Cycle12.MergedCutProfiles.Batch462
import Cycle12.MergedCutProfiles.Batch593
import Cycle12.MergedCutProfiles.Batch594
import Cycle12.MergedCutProfiles.Batch654

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch381

def retention4572 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(1/40),(23653300126867139171/1000000000000000000),(21/20),(82383244999724162202255159642839174896599/37845280202987422673600000000000000000000),false,MergedCutProfiles.Batch654.profile26165,(fun _ => MergedCutProfiles.Batch654.profile26165)⟩
theorem profilesValid4572 : retention4572.ProfilesValid := by
  exact MergedCutProfiles.Batch654.valid26165
theorem numericValid4572 : retention4572.NumericValid := by decide +kernel
def certificate4572 : RatCutBinCertificate := ⟨⟨retention4572,(1776840848995079283/1000000000000000000),(1358828718451041/40000000000000000),(2348368801580123351/250000000000000000),(64604278686172635417061/1000000000000000000),(2170096222950624321/1000000000000000000)⟩,(999973361876516047/1000000000000000000),(13500855023293973/20000000000000000),(59679451325392483/1000000000000000000),(14233034228016141/125000000000000000)⟩
theorem valid4572 : certificate4572.Valid := by decide +kernel
theorem sound4572 : certificate4572.Sound := rat_cut_bin_certificate_sound certificate4572 profilesValid4572 numericValid4572 valid4572

def retention4573 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(711459189593676700/6347625620013930963373),(657020625070622909/1000000000000000000),4,(6189524111909980943359383946225899271/2628082500282491636000000000000000000),true,MergedCutProfiles.Batch654.profile26166,![MergedCutProfiles.Batch654.profile26166,MergedCutProfiles.Batch654.profile26167,MergedCutProfiles.Batch654.profile26168,MergedCutProfiles.Batch654.profile26169,MergedCutProfiles.Batch654.profile26170,MergedCutProfiles.Batch654.profile26171,MergedCutProfiles.Batch654.profile26172,MergedCutProfiles.Batch593.profile23743,MergedCutProfiles.Batch654.profile26173,MergedCutProfiles.Batch654.profile26174,MergedCutProfiles.Batch654.profile26174,MergedCutProfiles.Batch654.profile26175,MergedCutProfiles.Batch593.profile23744,MergedCutProfiles.Batch654.profile26176,MergedCutProfiles.Batch654.profile26176,MergedCutProfiles.Batch654.profile26177]⟩
theorem profilesValid4573 : retention4573.ProfilesValid := by
  change ∀ j : Fin 16, (retention4573.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch654.valid26166
  · exact MergedCutProfiles.Batch654.valid26167
  · exact MergedCutProfiles.Batch654.valid26168
  · exact MergedCutProfiles.Batch654.valid26169
  · exact MergedCutProfiles.Batch654.valid26170
  · exact MergedCutProfiles.Batch654.valid26171
  · exact MergedCutProfiles.Batch654.valid26172
  · exact MergedCutProfiles.Batch593.valid23743
  · exact MergedCutProfiles.Batch654.valid26173
  · exact MergedCutProfiles.Batch654.valid26174
  · exact MergedCutProfiles.Batch654.valid26174
  · exact MergedCutProfiles.Batch654.valid26175
  · exact MergedCutProfiles.Batch593.valid23744
  · exact MergedCutProfiles.Batch654.valid26176
  · exact MergedCutProfiles.Batch654.valid26176
  · exact MergedCutProfiles.Batch654.valid26177
theorem numericValid4573 : retention4573.NumericValid := by decide +kernel
def certificate4573 : RatCutBinCertificate := ⟨⟨retention4573,(967992187110864181/500000000000000000),(36585906920747501/1000000000000000000),(9525037663980445463/1000000000000000000),(60765393535420988496591/1000000000000000000),(2325403666472771939/1000000000000000000)⟩,(999969222290672767/1000000000000000000),(467813605855388517/1000000000000000000),(44198775300780779/250000000000000000),(42079787875604511/500000000000000000)⟩
theorem valid4573 : certificate4573.Valid := by decide +kernel
theorem sound4573 : certificate4573.Sound := rat_cut_bin_certificate_sound certificate4573 profilesValid4573 numericValid4573 valid4573

def retention4574 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(1246107423000000000/6347625620013930963373),(7114591895936767/10000000000000000),4,(153623930123866645103/64000000000000000000),true,MergedCutProfiles.Batch654.profile26167,![MergedCutProfiles.Batch654.profile26167,MergedCutProfiles.Batch654.profile26169,MergedCutProfiles.Batch654.profile26170,MergedCutProfiles.Batch654.profile26172,MergedCutProfiles.Batch654.profile26173,MergedCutProfiles.Batch654.profile26174,MergedCutProfiles.Batch654.profile26175,MergedCutProfiles.Batch654.profile26176,MergedCutProfiles.Batch654.profile26177,MergedCutProfiles.Batch462.profile18491,MergedCutProfiles.Batch593.profile23759,MergedCutProfiles.Batch593.profile23745,MergedCutProfiles.Batch654.profile26178,MergedCutProfiles.Batch593.profile23746,MergedCutProfiles.Batch593.profile23753,MergedCutProfiles.Batch654.profile26179]⟩
theorem profilesValid4574 : retention4574.ProfilesValid := by
  change ∀ j : Fin 16, (retention4574.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch654.valid26167
  · exact MergedCutProfiles.Batch654.valid26169
  · exact MergedCutProfiles.Batch654.valid26170
  · exact MergedCutProfiles.Batch654.valid26172
  · exact MergedCutProfiles.Batch654.valid26173
  · exact MergedCutProfiles.Batch654.valid26174
  · exact MergedCutProfiles.Batch654.valid26175
  · exact MergedCutProfiles.Batch654.valid26176
  · exact MergedCutProfiles.Batch654.valid26177
  · exact MergedCutProfiles.Batch462.valid18491
  · exact MergedCutProfiles.Batch593.valid23759
  · exact MergedCutProfiles.Batch593.valid23745
  · exact MergedCutProfiles.Batch654.valid26178
  · exact MergedCutProfiles.Batch593.valid23746
  · exact MergedCutProfiles.Batch593.valid23753
  · exact MergedCutProfiles.Batch654.valid26179
theorem numericValid4574 : retention4574.NumericValid := by decide +kernel
def certificate4574 : RatCutBinCertificate := ⟨⟨retention4574,(967992187110864181/500000000000000000),(36585906920747501/1000000000000000000),(9525037663980445463/1000000000000000000),(60765393535420988496591/1000000000000000000),(2370629245077839243/1000000000000000000)⟩,(999969222290672767/1000000000000000000),(54562285280723811/125000000000000000),(201656938840609753/1000000000000000000),(98910637334254067/1000000000000000000)⟩
theorem valid4574 : certificate4574.Valid := by decide +kernel
theorem sound4574 : certificate4574.Sound := rat_cut_bin_certificate_sound certificate4574 profilesValid4574 numericValid4574 valid4574

def retention4575 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(3260770115312804117/6347625620013930963373),(1246107423/1000000000),(5/2),(5565754414357682995617153334259967/2360051937500000000000000000000000),true,MergedCutProfiles.Batch593.profile23742,![MergedCutProfiles.Batch593.profile23742,MergedCutProfiles.Batch654.profile26173,MergedCutProfiles.Batch654.profile26176,MergedCutProfiles.Batch593.profile23759,MergedCutProfiles.Batch654.profile26178,MergedCutProfiles.Batch654.profile26179,MergedCutProfiles.Batch654.profile26180,MergedCutProfiles.Batch462.profile18492,MergedCutProfiles.Batch593.profile23749,MergedCutProfiles.Batch593.profile23750,MergedCutProfiles.Batch462.profile18508,MergedCutProfiles.Batch654.profile26181,MergedCutProfiles.Batch593.profile23751,MergedCutProfiles.Batch330.profile13232,MergedCutProfiles.Batch462.profile18505,MergedCutProfiles.Batch654.profile26182]⟩
theorem profilesValid4575 : retention4575.ProfilesValid := by
  change ∀ j : Fin 16, (retention4575.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch593.valid23742
  · exact MergedCutProfiles.Batch654.valid26173
  · exact MergedCutProfiles.Batch654.valid26176
  · exact MergedCutProfiles.Batch593.valid23759
  · exact MergedCutProfiles.Batch654.valid26178
  · exact MergedCutProfiles.Batch654.valid26179
  · exact MergedCutProfiles.Batch654.valid26180
  · exact MergedCutProfiles.Batch462.valid18492
  · exact MergedCutProfiles.Batch593.valid23749
  · exact MergedCutProfiles.Batch593.valid23750
  · exact MergedCutProfiles.Batch462.valid18508
  · exact MergedCutProfiles.Batch654.valid26181
  · exact MergedCutProfiles.Batch593.valid23751
  · exact MergedCutProfiles.Batch330.valid13232
  · exact MergedCutProfiles.Batch462.valid18505
  · exact MergedCutProfiles.Batch654.valid26182
theorem numericValid4575 : retention4575.NumericValid := by decide +kernel
def certificate4575 : RatCutBinCertificate := ⟨⟨retention4575,(967992187110864181/500000000000000000),(36585906920747501/1000000000000000000),(9525037663980445463/1000000000000000000),(60765393535420988496591/1000000000000000000),(584932049989807079/250000000000000000)⟩,(999969222290672767/1000000000000000000),(324787062124925471/1000000000000000000),(15497518410855591/50000000000000000),(22305834476067983/100000000000000000)⟩
theorem valid4575 : certificate4575.Valid := by decide +kernel
theorem sound4575 : certificate4575.Sound := rat_cut_bin_certificate_sound certificate4575 profilesValid4575 numericValid4575 valid4575

def retention4576 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(64000000000000000000/6347625620013930963373),(3260770115312804117/1000000000000000000),(7/5),(709993377065911278977/320000000000000000000),true,MergedCutProfiles.Batch462.profile18495,![MergedCutProfiles.Batch462.profile18495,MergedCutProfiles.Batch462.profile18499,MergedCutProfiles.Batch654.profile26183,MergedCutProfiles.Batch462.profile18511,MergedCutProfiles.Batch041.profile1657,MergedCutProfiles.Batch042.profile1683,MergedCutProfiles.Batch330.profile13230,MergedCutProfiles.Batch331.profile13241,MergedCutProfiles.Batch040.profile1631,MergedCutProfiles.Batch594.profile23762,MergedCutProfiles.Batch654.profile26184,MergedCutProfiles.Batch654.profile26185,MergedCutProfiles.Batch654.profile26186,MergedCutProfiles.Batch654.profile26187,MergedCutProfiles.Batch041.profile1676,MergedCutProfiles.Batch331.profile13263]⟩
theorem profilesValid4576 : retention4576.ProfilesValid := by
  change ∀ j : Fin 16, (retention4576.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch462.valid18495
  · exact MergedCutProfiles.Batch462.valid18499
  · exact MergedCutProfiles.Batch654.valid26183
  · exact MergedCutProfiles.Batch462.valid18511
  · exact MergedCutProfiles.Batch041.valid1657
  · exact MergedCutProfiles.Batch042.valid1683
  · exact MergedCutProfiles.Batch330.valid13230
  · exact MergedCutProfiles.Batch331.valid13241
  · exact MergedCutProfiles.Batch040.valid1631
  · exact MergedCutProfiles.Batch594.valid23762
  · exact MergedCutProfiles.Batch654.valid26184
  · exact MergedCutProfiles.Batch654.valid26185
  · exact MergedCutProfiles.Batch654.valid26186
  · exact MergedCutProfiles.Batch654.valid26187
  · exact MergedCutProfiles.Batch041.valid1676
  · exact MergedCutProfiles.Batch331.valid13263
theorem numericValid4576 : retention4576.NumericValid := by decide +kernel
def certificate4576 : RatCutBinCertificate := ⟨⟨retention4576,(967992187110864181/500000000000000000),(36585906920747501/1000000000000000000),(9525037663980445463/1000000000000000000),(60765393535420988496591/1000000000000000000),(2208318672072814627/1000000000000000000)⟩,(999969222290672767/1000000000000000000),(241780681264475849/1000000000000000000),(414852802556145309/1000000000000000000),(486317444327196667/1000000000000000000)⟩
theorem valid4576 : certificate4576.Valid := by decide +kernel
theorem sound4576 : certificate4576.Sound := rat_cut_bin_certificate_sound certificate4576 profilesValid4576 numericValid4576 valid4576

def retention4577 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(1/2),64,1,(255375334696131669987701620024329127359/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch042.profile1701,(fun _ => MergedCutProfiles.Batch042.profile1701)⟩
theorem profilesValid4577 : retention4577.ProfilesValid := by
  exact MergedCutProfiles.Batch042.valid1701
theorem numericValid4577 : retention4577.NumericValid := by decide +kernel
def certificate4577 : RatCutBinCertificate := ⟨⟨retention4577,(967992187110864181/500000000000000000),(36585906920747501/1000000000000000000),(9525037663980445463/1000000000000000000),(60765393535420988496591/1000000000000000000),(990123736883159311/1000000000000000000)⟩,(999969222290672767/1000000000000000000),(101319274118835491/250000000000000000),(22868186537602131/100000000000000000),(222966865103215409/1000000000000000000)⟩
theorem valid4577 : certificate4577.Valid := by decide +kernel
theorem sound4577 : certificate4577.Sound := rat_cut_bin_certificate_sound certificate4577 profilesValid4577 numericValid4577 valid4577

def retention4578 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(64000000000000000000/6347625620013930963373),(19915793403484897453/1000000000000000000),1,(44230631655302097892649701473690872809/19915793403484897453000000000000000000),false,MergedCutProfiles.Batch654.profile26188,(fun _ => MergedCutProfiles.Batch654.profile26188)⟩
theorem profilesValid4578 : retention4578.ProfilesValid := by
  exact MergedCutProfiles.Batch654.valid26188
theorem numericValid4578 : retention4578.NumericValid := by decide +kernel
def certificate4578 : RatCutBinCertificate := ⟨⟨retention4578,(899984291610864181/500000000000000000),(36585906920747501/1000000000000000000),(9525037663980445463/1000000000000000000),(60765393535420988496591/1000000000000000000),(442793701016754971/200000000000000000)⟩,(249992846157957457/250000000000000000),(4912952884018247/200000000000000000),(215067001913287719/250000000000000000),(1714009873737755437/1000000000000000000)⟩
theorem valid4578 : certificate4578.Valid := by decide +kernel
theorem sound4578 : certificate4578.Sound := rat_cut_bin_certificate_sound certificate4578 profilesValid4578 numericValid4578 valid4578

def retention4579 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(1/2),64,1,(255375334696131669987701620024329127359/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch042.profile1701,(fun _ => MergedCutProfiles.Batch042.profile1701)⟩
theorem profilesValid4579 : retention4579.ProfilesValid := by
  exact MergedCutProfiles.Batch042.valid1701
theorem numericValid4579 : retention4579.NumericValid := by decide +kernel
def certificate4579 : RatCutBinCertificate := ⟨⟨retention4579,(899984291610864181/500000000000000000),(36585906920747501/1000000000000000000),(9525037663980445463/1000000000000000000),(60765393535420988496591/1000000000000000000),(30957693029038757/31250000000000000)⟩,(249992846157957457/250000000000000000),(274495657619487/5000000000000000),(193838463814114821/250000000000000000),(756371394637305073/1000000000000000000)⟩
theorem valid4579 : certificate4579.Valid := by decide +kernel
theorem sound4579 : certificate4579.Sound := rat_cut_bin_certificate_sound certificate4579 profilesValid4579 numericValid4579 valid4579

def retention4580 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(674712012930311956/6347625620013930963373),(668031695970605897/1000000000000000000),4,(6322181921679326974118374233067613703/2672126783882423588000000000000000000),false,MergedCutProfiles.Batch654.profile26189,(fun _ => MergedCutProfiles.Batch654.profile26189)⟩
theorem profilesValid4580 : retention4580.ProfilesValid := by
  exact MergedCutProfiles.Batch654.valid26189
theorem numericValid4580 : retention4580.NumericValid := by decide +kernel
def certificate4580 : RatCutBinCertificate := ⟨⟨retention4580,(891967213610864181/500000000000000000),(36585906920747501/1000000000000000000),(9525037663980445463/1000000000000000000),(60765393535420988496591/1000000000000000000),(2338565232850495561/1000000000000000000)⟩,(999971639538353809/1000000000000000000),(865092387229784343/1000000000000000000),(9539313580781711/1000000000000000000),(4575749666469911/1000000000000000000)⟩
theorem valid4580 : certificate4580.Valid := by decide +kernel
theorem sound4580 : certificate4580.Sound := rat_cut_bin_certificate_sound certificate4580 profilesValid4580 numericValid4580 valid4580

def retention4581 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(1055796609118963344/6347625620013930963373),(168678003232577989/250000000000000000),4,(6396196582385077978041519109034042367/2698848051721247824000000000000000000),false,MergedCutProfiles.Batch654.profile26190,(fun _ => MergedCutProfiles.Batch654.profile26190)⟩
theorem profilesValid4581 : retention4581.ProfilesValid := by
  exact MergedCutProfiles.Batch654.valid26190
theorem numericValid4581 : retention4581.NumericValid := by decide +kernel
def certificate4581 : RatCutBinCertificate := ⟨⟨retention4581,(891967213610864181/500000000000000000),(36585906920747501/1000000000000000000),(9525037663980445463/1000000000000000000),(60765393535420988496591/1000000000000000000),(14641026798737921/6250000000000000)⟩,(999971639538353809/1000000000000000000),(861166185191688191/1000000000000000000),(1264652217645563/125000000000000000),(4868426940790443/1000000000000000000)⟩
theorem valid4581 : certificate4581.Valid := by decide +kernel
theorem sound4581 : certificate4581.Sound := rat_cut_bin_certificate_sound certificate4581 profilesValid4581 numericValid4581 valid4581

def retention4582 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(21740918738820643918/6347625620013930963373),(65987288069935209/62500000000000000),(63/20),(82864347777954438869865483656524794957/35193220303965444800000000000000000000),false,MergedCutProfiles.Batch654.profile26191,(fun _ => MergedCutProfiles.Batch654.profile26191)⟩
theorem profilesValid4582 : retention4582.ProfilesValid := by
  exact MergedCutProfiles.Batch654.valid26191
theorem numericValid4582 : retention4582.NumericValid := by decide +kernel
def certificate4582 : RatCutBinCertificate := ⟨⟨retention4582,(891967213610864181/500000000000000000),(36585906920747501/1000000000000000000),(9525037663980445463/1000000000000000000),(60765393535420988496591/1000000000000000000),(583242513493667703/250000000000000000)⟩,(999971639538353809/1000000000000000000),(193983742111379199/250000000000000000),(13610377039318729/500000000000000000),(3297592371056153/200000000000000000)⟩
theorem valid4582 : certificate4582.Valid := by decide +kernel
theorem sound4582 : certificate4582.Sound := rat_cut_bin_certificate_sound certificate4582 profilesValid4582 numericValid4582 valid4582

def retention4583 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(1/40),(10870459369410321959/500000000000000000),(21/20),(18910716216006960543308472635522275818959/8696367495528257567200000000000000000000),false,MergedCutProfiles.Batch654.profile26192,(fun _ => MergedCutProfiles.Batch654.profile26192)⟩
theorem profilesValid4583 : retention4583.ProfilesValid := by
  exact MergedCutProfiles.Batch654.valid26192
theorem numericValid4583 : retention4583.NumericValid := by decide +kernel
def certificate4583 : RatCutBinCertificate := ⟨⟨retention4583,(891967213610864181/500000000000000000),(36585906920747501/1000000000000000000),(9525037663980445463/1000000000000000000),(60765393535420988496591/1000000000000000000),(2167358738165115519/1000000000000000000)⟩,(999971639538353809/1000000000000000000),(674259017986791377/1000000000000000000),(59987897342939893/1000000000000000000),(11355281506656071/100000000000000000)⟩
theorem valid4583 : certificate4583.Valid := by decide +kernel
theorem sound4583 : certificate4583.Sound := rat_cut_bin_certificate_sound certificate4583 profilesValid4583 numericValid4583 valid4583

def certificates : List RatCutBinCertificate := [certificate4572,certificate4573,certificate4574,certificate4575,certificate4576,certificate4577,certificate4578,certificate4579,certificate4580,certificate4581,certificate4582,certificate4583]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4572,List.forall_mem_cons.mpr ⟨sound4573,List.forall_mem_cons.mpr ⟨sound4574,List.forall_mem_cons.mpr ⟨sound4575,List.forall_mem_cons.mpr ⟨sound4576,List.forall_mem_cons.mpr ⟨sound4577,List.forall_mem_cons.mpr ⟨sound4578,List.forall_mem_cons.mpr ⟨sound4579,List.forall_mem_cons.mpr ⟨sound4580,List.forall_mem_cons.mpr ⟨sound4581,List.forall_mem_cons.mpr ⟨sound4582,List.forall_mem_cons.mpr ⟨sound4583,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch381
