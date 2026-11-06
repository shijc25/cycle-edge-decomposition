import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch045
import Cycle12.MergedCutProfiles.Batch046
import Cycle12.MergedCutProfiles.Batch333
import Cycle12.MergedCutProfiles.Batch334
import Cycle12.MergedCutProfiles.Batch463
import Cycle12.MergedCutProfiles.Batch464
import Cycle12.MergedCutProfiles.Batch595
import Cycle12.MergedCutProfiles.Batch596
import Cycle12.MergedCutProfiles.Batch655
import Cycle12.MergedCutProfiles.Batch656

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch383

def retention4596 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(587885098000000000/2749528521369003032971),(586442270897867269/1000000000000000000),4,(573846609915778574341/256000000000000000000),true,MergedCutProfiles.Batch655.profile26216,![MergedCutProfiles.Batch655.profile26216,MergedCutProfiles.Batch655.profile26218,MergedCutProfiles.Batch655.profile26219,MergedCutProfiles.Batch655.profile26221,MergedCutProfiles.Batch595.profile23817,MergedCutProfiles.Batch655.profile26224,MergedCutProfiles.Batch595.profile23831,MergedCutProfiles.Batch655.profile26225,MergedCutProfiles.Batch655.profile26226,MergedCutProfiles.Batch595.profile23819,MergedCutProfiles.Batch655.profile26227,MergedCutProfiles.Batch463.profile18552,MergedCutProfiles.Batch595.profile23820,MergedCutProfiles.Batch595.profile23821,MergedCutProfiles.Batch595.profile23821,MergedCutProfiles.Batch655.profile26228]⟩
theorem profilesValid4596 : retention4596.ProfilesValid := by
  change ∀ j : Fin 16, (retention4596.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch655.valid26216
  · exact MergedCutProfiles.Batch655.valid26218
  · exact MergedCutProfiles.Batch655.valid26219
  · exact MergedCutProfiles.Batch655.valid26221
  · exact MergedCutProfiles.Batch595.valid23817
  · exact MergedCutProfiles.Batch655.valid26224
  · exact MergedCutProfiles.Batch595.valid23831
  · exact MergedCutProfiles.Batch655.valid26225
  · exact MergedCutProfiles.Batch655.valid26226
  · exact MergedCutProfiles.Batch595.valid23819
  · exact MergedCutProfiles.Batch655.valid26227
  · exact MergedCutProfiles.Batch463.valid18552
  · exact MergedCutProfiles.Batch595.valid23820
  · exact MergedCutProfiles.Batch595.valid23821
  · exact MergedCutProfiles.Batch595.valid23821
  · exact MergedCutProfiles.Batch655.valid26228
theorem numericValid4596 : retention4596.NumericValid := by decide +kernel
def certificate4596 : RatCutBinCertificate := ⟨⟨retention4596,(929398518179652177/500000000000000000),(42146381475855499/1000000000000000000),(9796801993206856219/1000000000000000000),(54147318024800195909169/1000000000000000000),(2209601720670818869/1000000000000000000)⟩,(999967020914476037/1000000000000000000),(663027140108628219/1000000000000000000),(32254457492467527/500000000000000000),(28841511232389789/1000000000000000000)⟩
theorem valid4596 : certificate4596.Valid := by decide +kernel
theorem sound4596 : certificate4596.Sound := rat_cut_bin_certificate_sound certificate4596 profilesValid4596 numericValid4596 valid4596

def retention4597 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(624625454742029608/2749528521369003032971),(293942549/250000000),(27/10),(1757795018071657222937149319712959/734856372500000000000000000000000),true,MergedCutProfiles.Batch655.profile26216,![MergedCutProfiles.Batch655.profile26216,MergedCutProfiles.Batch655.profile26218,MergedCutProfiles.Batch655.profile26220,MergedCutProfiles.Batch655.profile26222,MergedCutProfiles.Batch655.profile26223,MergedCutProfiles.Batch655.profile26224,MergedCutProfiles.Batch595.profile23818,MergedCutProfiles.Batch655.profile26225,MergedCutProfiles.Batch595.profile23819,MergedCutProfiles.Batch655.profile26227,MergedCutProfiles.Batch463.profile18552,MergedCutProfiles.Batch595.profile23820,MergedCutProfiles.Batch595.profile23832,MergedCutProfiles.Batch595.profile23821,MergedCutProfiles.Batch655.profile26228,MergedCutProfiles.Batch655.profile26229]⟩
theorem profilesValid4597 : retention4597.ProfilesValid := by
  change ∀ j : Fin 16, (retention4597.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch655.valid26216
  · exact MergedCutProfiles.Batch655.valid26218
  · exact MergedCutProfiles.Batch655.valid26220
  · exact MergedCutProfiles.Batch655.valid26222
  · exact MergedCutProfiles.Batch655.valid26223
  · exact MergedCutProfiles.Batch655.valid26224
  · exact MergedCutProfiles.Batch595.valid23818
  · exact MergedCutProfiles.Batch655.valid26225
  · exact MergedCutProfiles.Batch595.valid23819
  · exact MergedCutProfiles.Batch655.valid26227
  · exact MergedCutProfiles.Batch463.valid18552
  · exact MergedCutProfiles.Batch595.valid23820
  · exact MergedCutProfiles.Batch595.valid23832
  · exact MergedCutProfiles.Batch595.valid23821
  · exact MergedCutProfiles.Batch655.valid26228
  · exact MergedCutProfiles.Batch655.valid26229
theorem numericValid4597 : retention4597.NumericValid := by decide +kernel
def certificate4597 : RatCutBinCertificate := ⟨⟨retention4597,(929398518179652177/500000000000000000),(42146381475855499/1000000000000000000),(9796801993206856219/1000000000000000000),(54147318024800195909169/1000000000000000000),(1185217162226459353/500000000000000000)⟩,(999967020914476037/1000000000000000000),(81872354802003949/200000000000000000),(112506649439643871/500000000000000000),(38686301660624893/250000000000000000)⟩
theorem valid4597 : certificate4597.Valid := by decide +kernel
theorem sound4597 : certificate4597.Sound := rat_cut_bin_certificate_sound certificate4597 profilesValid4597 numericValid4597 valid4597

def retention4598 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(16009859910394415804/2749528521369003032971),(78078181842753701/62500000000000000),(13/5),(92417441857734136703/40000000000000000000),true,MergedCutProfiles.Batch595.profile23824,![MergedCutProfiles.Batch595.profile23824,MergedCutProfiles.Batch463.profile18556,MergedCutProfiles.Batch464.profile18565,MergedCutProfiles.Batch655.profile26230,MergedCutProfiles.Batch655.profile26231,MergedCutProfiles.Batch655.profile26232,MergedCutProfiles.Batch334.profile13383,MergedCutProfiles.Batch655.profile26233,MergedCutProfiles.Batch045.profile1800,MergedCutProfiles.Batch046.profile1843,MergedCutProfiles.Batch046.profile1857,MergedCutProfiles.Batch333.profile13353,MergedCutProfiles.Batch334.profile13364,MergedCutProfiles.Batch334.profile13386,MergedCutProfiles.Batch464.profile18575,MergedCutProfiles.Batch334.profile13375]⟩
theorem profilesValid4598 : retention4598.ProfilesValid := by
  change ∀ j : Fin 16, (retention4598.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch595.valid23824
  · exact MergedCutProfiles.Batch463.valid18556
  · exact MergedCutProfiles.Batch464.valid18565
  · exact MergedCutProfiles.Batch655.valid26230
  · exact MergedCutProfiles.Batch655.valid26231
  · exact MergedCutProfiles.Batch655.valid26232
  · exact MergedCutProfiles.Batch334.valid13383
  · exact MergedCutProfiles.Batch655.valid26233
  · exact MergedCutProfiles.Batch045.valid1800
  · exact MergedCutProfiles.Batch046.valid1843
  · exact MergedCutProfiles.Batch046.valid1857
  · exact MergedCutProfiles.Batch333.valid13353
  · exact MergedCutProfiles.Batch334.valid13364
  · exact MergedCutProfiles.Batch334.valid13386
  · exact MergedCutProfiles.Batch464.valid18575
  · exact MergedCutProfiles.Batch334.valid13375
theorem numericValid4598 : retention4598.NumericValid := by decide +kernel
def certificate4598 : RatCutBinCertificate := ⟨⟨retention4598,(929398518179652177/500000000000000000),(42146381475855499/1000000000000000000),(9796801993206856219/1000000000000000000),(54147318024800195909169/1000000000000000000),(572411189701640481/250000000000000000)⟩,(999967020914476037/1000000000000000000),(411160644516665777/1000000000000000000),(55852656981697457/250000000000000000),(7738619991523757/50000000000000000)⟩
theorem valid4598 : certificate4598.Valid := by decide +kernel
theorem sound4598 : certificate4598.Sound := rat_cut_bin_certificate_sound certificate4598 profilesValid4598 numericValid4598 valid4598

def retention4599 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(32000000000000000000/2749528521369003032971),(4002464977598603951/125000000000000000),1,(71588267063653223432332032830360796639/32019719820788831608000000000000000000),false,MergedCutProfiles.Batch655.profile26234,(fun _ => MergedCutProfiles.Batch655.profile26234)⟩
theorem profilesValid4599 : retention4599.ProfilesValid := by
  exact MergedCutProfiles.Batch655.valid26234
theorem numericValid4599 : retention4599.NumericValid := by decide +kernel
def certificate4599 : RatCutBinCertificate := ⟨⟨retention4599,(929398518179652177/500000000000000000),(42146381475855499/1000000000000000000),(9796801993206856219/1000000000000000000),(54147318024800195909169/1000000000000000000),(1113879463259311913/500000000000000000)⟩,(999967020914476037/1000000000000000000),(222735815006641641/1000000000000000000),(442597525276711589/1000000000000000000),(460915734214501697/500000000000000000)⟩
theorem valid4599 : certificate4599.Valid := by decide +kernel
theorem sound4599 : certificate4599.Sound := rat_cut_bin_certificate_sound certificate4599 profilesValid4599 numericValid4599 valid4599

def retention4600 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(1/2),64,1,(63844131674568793248260656909441386031/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch046.profile1873,(fun _ => MergedCutProfiles.Batch046.profile1873)⟩
theorem profilesValid4600 : retention4600.ProfilesValid := by
  exact MergedCutProfiles.Batch046.valid1873
theorem numericValid4600 : retention4600.NumericValid := by decide +kernel
def certificate4600 : RatCutBinCertificate := ⟨⟨retention4600,(929398518179652177/500000000000000000),(42146381475855499/1000000000000000000),(9796801993206856219/1000000000000000000),(54147318024800195909169/1000000000000000000),(989567910143129871/1000000000000000000)⟩,(999967020914476037/1000000000000000000),(24615274864605017/50000000000000000),(3970481936562001/25000000000000000),(154764266007840821/1000000000000000000)⟩
theorem valid4600 : certificate4600.Valid := by decide +kernel
theorem sound4600 : certificate4600.Sound := rat_cut_bin_certificate_sound certificate4600 profilesValid4600 numericValid4600 valid4600

def retention4601 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(32000000000000000000/2749528521369003032971),(24821787527572240607/1000000000000000000),1,(55204274743979184915098766072207839233/24821787527572240607000000000000000000),false,MergedCutProfiles.Batch655.profile26234,(fun _ => MergedCutProfiles.Batch655.profile26234)⟩
theorem profilesValid4601 : retention4601.ProfilesValid := by
  exact MergedCutProfiles.Batch655.valid26234
theorem numericValid4601 : retention4601.NumericValid := by decide +kernel
def certificate4601 : RatCutBinCertificate := ⟨⟨retention4601,(879620931179652177/500000000000000000),(42146381475855499/1000000000000000000),(9796801993206856219/1000000000000000000),(54147318024800195909169/1000000000000000000),(1108228296791610953/500000000000000000)⟩,(999968787241152283/1000000000000000000),(1490038420568847/62500000000000000),(862428801900963279/1000000000000000000),(877391031613128223/500000000000000000)⟩
theorem valid4601 : certificate4601.Valid := by decide +kernel
theorem sound4601 : certificate4601.Sound := rat_cut_bin_certificate_sound certificate4601 profilesValid4601 numericValid4601 valid4601

def retention4602 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(1/2),64,1,(63844131674568793248260656909441386031/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch046.profile1873,(fun _ => MergedCutProfiles.Batch046.profile1873)⟩
theorem profilesValid4602 : retention4602.ProfilesValid := by
  exact MergedCutProfiles.Batch046.valid1873
theorem numericValid4602 : retention4602.NumericValid := by decide +kernel
def certificate4602 : RatCutBinCertificate := ⟨⟨retention4602,(879620931179652177/500000000000000000),(42146381475855499/1000000000000000000),(9796801993206856219/1000000000000000000),(54147318024800195909169/1000000000000000000),(989996201987268279/1000000000000000000)⟩,(999968787241152283/1000000000000000000),(53375646901798897/1000000000000000000),(155874760064550091/200000000000000000),(759799684420223567/1000000000000000000)⟩
theorem valid4602 : certificate4602.Valid := by decide +kernel
theorem sound4602 : certificate4602.Sound := rat_cut_bin_certificate_sound certificate4602 profilesValid4602 numericValid4602 valid4602

def retention4603 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(672773734059867507/5499057042738006065942),(333056303990033419/500000000000000000),4,(15752070634218680048909485045068691/6661126079800668380000000000000000),false,MergedCutProfiles.Batch655.profile26235,(fun _ => MergedCutProfiles.Batch655.profile26235)⟩
theorem profilesValid4603 : retention4603.ProfilesValid := by
  exact MergedCutProfiles.Batch655.valid26235
theorem numericValid4603 : retention4603.NumericValid := by decide +kernel
def certificate4603 : RatCutBinCertificate := ⟨⟨retention4603,(892844859179652177/500000000000000000),(42146381475855499/1000000000000000000),(9796801993206856219/1000000000000000000),(54147318024800195909169/1000000000000000000),(291755922656703663/125000000000000000)⟩,(199993663599665433/200000000000000000),(880807788026105713/1000000000000000000),(7403741441917959/1000000000000000000),(3543898345074243/1000000000000000000)⟩
theorem valid4603 : certificate4603.Valid := by decide +kernel
theorem sound4603 : certificate4603.Sound := rat_cut_bin_certificate_sound certificate4603 profilesValid4603 numericValid4603 valid4603

def retention4604 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(495875452253694633/2749528521369003032971),(672773734059867507/1000000000000000000),4,(2125225326615467365755840670772030901/897031645413156676000000000000000000),false,MergedCutProfiles.Batch655.profile26236,(fun _ => MergedCutProfiles.Batch655.profile26236)⟩
theorem profilesValid4604 : retention4604.ProfilesValid := by
  exact MergedCutProfiles.Batch655.valid26236
theorem numericValid4604 : retention4604.NumericValid := by decide +kernel
def certificate4604 : RatCutBinCertificate := ⟨⟨retention4604,(892844859179652177/500000000000000000),(42146381475855499/1000000000000000000),(9796801993206856219/1000000000000000000),(54147318024800195909169/1000000000000000000),(1169223435366734531/500000000000000000)⟩,(199993663599665433/200000000000000000),(876698410975403737/1000000000000000000),(3967443774024131/500000000000000000),(381079860110537/100000000000000000)⟩
theorem valid4604 : certificate4604.Valid := by decide +kernel
theorem sound4604 : certificate4604.Sound := rat_cut_bin_certificate_sound certificate4604 profilesValid4604 numericValid4604 valid4604

def retention4605 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(576984703823688075/211502193951461771767),(495875452253694633/500000000000000000),(33/10),(234768697597190028689040726038074668239/99175090450738926600000000000000000000),false,MergedCutProfiles.Batch655.profile26237,(fun _ => MergedCutProfiles.Batch655.profile26237)⟩
theorem profilesValid4605 : retention4605.ProfilesValid := by
  exact MergedCutProfiles.Batch655.valid26237
theorem numericValid4605 : retention4605.NumericValid := by decide +kernel
def certificate4605 : RatCutBinCertificate := ⟨⟨retention4605,(892844859179652177/500000000000000000),(42146381475855499/1000000000000000000),(9796801993206856219/1000000000000000000),(54147318024800195909169/1000000000000000000),(2341863300148633751/1000000000000000000)⟩,(199993663599665433/200000000000000000),(199165679359719833/250000000000000000),(22236822639983621/1000000000000000000),(12967984531458373/1000000000000000000)⟩
theorem valid4605 : certificate4605.Valid := by decide +kernel
theorem sound4605 : certificate4605.Sound := rat_cut_bin_certificate_sound certificate4605 profilesValid4605 numericValid4605 valid4605

def retention4606 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(1/40),(300032045988317799/20000000000000000),(11/10),(32742554443870969630950230207126591741/15001602299415889950000000000000000000),false,MergedCutProfiles.Batch655.profile26238,(fun _ => MergedCutProfiles.Batch655.profile26238)⟩
theorem profilesValid4606 : retention4606.ProfilesValid := by
  exact MergedCutProfiles.Batch655.valid26238
theorem numericValid4606 : retention4606.NumericValid := by decide +kernel
def certificate4606 : RatCutBinCertificate := ⟨⟨retention4606,(892844859179652177/500000000000000000),(42146381475855499/1000000000000000000),(9796801993206856219/1000000000000000000),(54147318024800195909169/1000000000000000000),(434830693571258219/200000000000000000)⟩,(199993663599665433/200000000000000000),(345510181193819053/500000000000000000),(53588194482827027/1000000000000000000),(47292421822250701/500000000000000000)⟩
theorem valid4606 : certificate4606.Valid := by decide +kernel
theorem sound4606 : certificate4606.Sound := rat_cut_bin_certificate_sound certificate4606 profilesValid4606 numericValid4606 valid4606

def retention4607 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(636570874548685086/5134451270410500746393),(564924329444591919/1000000000000000000),4,(39698382367958171288153580543643579/18077578542226941408000000000000000),true,MergedCutProfiles.Batch655.profile26239,![MergedCutProfiles.Batch655.profile26239,MergedCutProfiles.Batch656.profile26240,MergedCutProfiles.Batch656.profile26241,MergedCutProfiles.Batch656.profile26242,MergedCutProfiles.Batch595.profile23838,MergedCutProfiles.Batch656.profile26243,MergedCutProfiles.Batch656.profile26244,MergedCutProfiles.Batch656.profile26245,MergedCutProfiles.Batch595.profile23839,MergedCutProfiles.Batch656.profile26246,MergedCutProfiles.Batch656.profile26246,MergedCutProfiles.Batch656.profile26247,MergedCutProfiles.Batch596.profile23840,MergedCutProfiles.Batch656.profile26248,MergedCutProfiles.Batch656.profile26249,MergedCutProfiles.Batch656.profile26249]⟩
theorem profilesValid4607 : retention4607.ProfilesValid := by
  change ∀ j : Fin 16, (retention4607.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch655.valid26239
  · exact MergedCutProfiles.Batch656.valid26240
  · exact MergedCutProfiles.Batch656.valid26241
  · exact MergedCutProfiles.Batch656.valid26242
  · exact MergedCutProfiles.Batch595.valid23838
  · exact MergedCutProfiles.Batch656.valid26243
  · exact MergedCutProfiles.Batch656.valid26244
  · exact MergedCutProfiles.Batch656.valid26245
  · exact MergedCutProfiles.Batch595.valid23839
  · exact MergedCutProfiles.Batch656.valid26246
  · exact MergedCutProfiles.Batch656.valid26246
  · exact MergedCutProfiles.Batch656.valid26247
  · exact MergedCutProfiles.Batch596.valid23840
  · exact MergedCutProfiles.Batch656.valid26248
  · exact MergedCutProfiles.Batch656.valid26249
  · exact MergedCutProfiles.Batch656.valid26249
theorem numericValid4607 : retention4607.NumericValid := by decide +kernel
def certificate4607 : RatCutBinCertificate := ⟨⟨retention4607,(928424619889688411/500000000000000000),(9018985876591161/200000000000000000),(4968587493102325573/500000000000000000),(2051325527390199155699/40000000000000000),(2162295537802160779/1000000000000000000)⟩,(999965318181749223/1000000000000000000),(712162229648253229/1000000000000000000),(11523656756921347/250000000000000000),(5026634730479581/250000000000000000)⟩
theorem valid4607 : certificate4607.Valid := by decide +kernel
theorem sound4607 : certificate4607.Sound := rat_cut_bin_certificate_sound certificate4607 profilesValid4607 numericValid4607 valid4607

def certificates : List RatCutBinCertificate := [certificate4596,certificate4597,certificate4598,certificate4599,certificate4600,certificate4601,certificate4602,certificate4603,certificate4604,certificate4605,certificate4606,certificate4607]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4596,List.forall_mem_cons.mpr ⟨sound4597,List.forall_mem_cons.mpr ⟨sound4598,List.forall_mem_cons.mpr ⟨sound4599,List.forall_mem_cons.mpr ⟨sound4600,List.forall_mem_cons.mpr ⟨sound4601,List.forall_mem_cons.mpr ⟨sound4602,List.forall_mem_cons.mpr ⟨sound4603,List.forall_mem_cons.mpr ⟨sound4604,List.forall_mem_cons.mpr ⟨sound4605,List.forall_mem_cons.mpr ⟨sound4606,List.forall_mem_cons.mpr ⟨sound4607,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch383
