import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch022
import Cycle12.MergedCutProfiles.Batch023
import Cycle12.MergedCutProfiles.Batch319
import Cycle12.MergedCutProfiles.Batch454
import Cycle12.MergedCutProfiles.Batch455
import Cycle12.MergedCutProfiles.Batch579
import Cycle12.MergedCutProfiles.Batch580

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch317

def retention3804 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(1/2),64,1,(63842651577774958124598119296594031199/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch022.profile888,(fun _ => MergedCutProfiles.Batch022.profile888)⟩
theorem profilesValid3804 : retention3804.ProfilesValid := by
  exact MergedCutProfiles.Batch022.valid888
theorem numericValid3804 : retention3804.NumericValid := by decide +kernel
def certificate3804 : RatCutBinCertificate := ⟨⟨retention3804,(1780549791027474153/1000000000000000000),(13522397103991873/1000000000000000000),(8218234299472071169/1000000000000000000),(14353424855149524330681/500000000000000000),(497305844735983197/500000000000000000)⟩,(19998774403633457/20000000000000000),(34923485145013/500000000000000),(368578868332153757/500000000000000000),(2887684546351701/4000000000000000)⟩
theorem valid3804 : certificate3804.Valid := by decide +kernel
theorem sound3804 : certificate3804.Sound := rat_cut_bin_certificate_sound certificate3804 profilesValid3804 numericValid3804 valid3804

def retention3805 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(33248186379999813/182683193381119038518),(559622939069303783/1000000000000000000),4,(1218429985019810777837322682576220907/559622939069303783000000000000000000),true,MergedCutProfiles.Batch579.profile23177,![MergedCutProfiles.Batch579.profile23177,MergedCutProfiles.Batch579.profile23178,MergedCutProfiles.Batch579.profile23179,MergedCutProfiles.Batch579.profile23180,MergedCutProfiles.Batch579.profile23181,MergedCutProfiles.Batch579.profile23182,MergedCutProfiles.Batch579.profile23183,MergedCutProfiles.Batch579.profile23184,MergedCutProfiles.Batch454.profile18189,MergedCutProfiles.Batch579.profile23185,MergedCutProfiles.Batch579.profile23186,MergedCutProfiles.Batch319.profile12772,MergedCutProfiles.Batch454.profile18190,MergedCutProfiles.Batch455.profile18204,MergedCutProfiles.Batch579.profile23187,MergedCutProfiles.Batch579.profile23188]⟩
theorem profilesValid3805 : retention3805.ProfilesValid := by
  change ∀ j : Fin 16, (retention3805.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch579.valid23177
  · exact MergedCutProfiles.Batch579.valid23178
  · exact MergedCutProfiles.Batch579.valid23179
  · exact MergedCutProfiles.Batch579.valid23180
  · exact MergedCutProfiles.Batch579.valid23181
  · exact MergedCutProfiles.Batch579.valid23182
  · exact MergedCutProfiles.Batch579.valid23183
  · exact MergedCutProfiles.Batch579.valid23184
  · exact MergedCutProfiles.Batch454.valid18189
  · exact MergedCutProfiles.Batch579.valid23185
  · exact MergedCutProfiles.Batch579.valid23186
  · exact MergedCutProfiles.Batch319.valid12772
  · exact MergedCutProfiles.Batch454.valid18190
  · exact MergedCutProfiles.Batch455.valid18204
  · exact MergedCutProfiles.Batch579.valid23187
  · exact MergedCutProfiles.Batch579.valid23188
theorem numericValid3805 : retention3805.NumericValid := by decide +kernel
def certificate3805 : RatCutBinCertificate := ⟨⟨retention3805,(1809857969488236619/1000000000000000000),(15120529320228081/1000000000000000000),(8325289875112082173/1000000000000000000),(12988872207026718218203/500000000000000000),(432817086545317433/200000000000000000)⟩,(999931272476733191/1000000000000000000),(21494957965565093/31250000000000000),(54771445119309171/1000000000000000000),(23862691511526469/1000000000000000000)⟩
theorem valid3805 : certificate3805.Valid := by decide +kernel
theorem sound3805 : certificate3805.Sound := rat_cut_bin_certificate_sound certificate3805 profilesValid3805 numericValid3805 valid3805

def retention3806 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(616471386000000000/1552807143739511827403),(565219168459996821/1000000000000000000),4,(28006659617845314393/12800000000000000000),true,MergedCutProfiles.Batch579.profile23189,![MergedCutProfiles.Batch579.profile23189,MergedCutProfiles.Batch454.profile18188,MergedCutProfiles.Batch579.profile23190,MergedCutProfiles.Batch454.profile18189,MergedCutProfiles.Batch579.profile23186,MergedCutProfiles.Batch454.profile18190,MergedCutProfiles.Batch579.profile23187,MergedCutProfiles.Batch454.profile18191,MergedCutProfiles.Batch579.profile23191,MergedCutProfiles.Batch319.profile12773,MergedCutProfiles.Batch022.profile889,MergedCutProfiles.Batch454.profile18199,MergedCutProfiles.Batch455.profile18205,MergedCutProfiles.Batch579.profile23192,MergedCutProfiles.Batch579.profile23193,MergedCutProfiles.Batch319.profile12774]⟩
theorem profilesValid3806 : retention3806.ProfilesValid := by
  change ∀ j : Fin 16, (retention3806.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch579.valid23189
  · exact MergedCutProfiles.Batch454.valid18188
  · exact MergedCutProfiles.Batch579.valid23190
  · exact MergedCutProfiles.Batch454.valid18189
  · exact MergedCutProfiles.Batch579.valid23186
  · exact MergedCutProfiles.Batch454.valid18190
  · exact MergedCutProfiles.Batch579.valid23187
  · exact MergedCutProfiles.Batch454.valid18191
  · exact MergedCutProfiles.Batch579.valid23191
  · exact MergedCutProfiles.Batch319.valid12773
  · exact MergedCutProfiles.Batch022.valid889
  · exact MergedCutProfiles.Batch454.valid18199
  · exact MergedCutProfiles.Batch455.valid18205
  · exact MergedCutProfiles.Batch579.valid23192
  · exact MergedCutProfiles.Batch579.valid23193
  · exact MergedCutProfiles.Batch319.valid12774
theorem numericValid3806 : retention3806.NumericValid := by decide +kernel
def certificate3806 : RatCutBinCertificate := ⟨⟨retention3806,(1809857969488236619/1000000000000000000),(15120529320228081/1000000000000000000),(8325289875112082173/1000000000000000000),(12988872207026718218203/500000000000000000),(67964746975401693/31250000000000000)⟩,(999931272476733191/1000000000000000000),(169936260060522977/250000000000000000),(57847889243803677/1000000000000000000),(25353158992012061/1000000000000000000)⟩
theorem valid3806 : certificate3806.Valid := by decide +kernel
theorem sound3806 : certificate3806.Sound := rat_cut_bin_certificate_sound certificate3806 profilesValid3806 numericValid3806 valid3806

def retention3807 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(671655236784586110/1552807143739511827403),(308235693/250000000),(13/5),(243590433067418497120627651503788253/102745231000000000000000000000000000),true,MergedCutProfiles.Batch579.profile23189,![MergedCutProfiles.Batch579.profile23189,MergedCutProfiles.Batch579.profile23181,MergedCutProfiles.Batch579.profile23183,MergedCutProfiles.Batch579.profile23185,MergedCutProfiles.Batch319.profile12772,MergedCutProfiles.Batch579.profile23187,MergedCutProfiles.Batch454.profile18191,MergedCutProfiles.Batch579.profile23191,MergedCutProfiles.Batch454.profile18192,MergedCutProfiles.Batch022.profile889,MergedCutProfiles.Batch454.profile18199,MergedCutProfiles.Batch455.profile18205,MergedCutProfiles.Batch579.profile23192,MergedCutProfiles.Batch579.profile23193,MergedCutProfiles.Batch022.profile905,MergedCutProfiles.Batch454.profile18195]⟩
theorem profilesValid3807 : retention3807.ProfilesValid := by
  change ∀ j : Fin 16, (retention3807.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch579.valid23189
  · exact MergedCutProfiles.Batch579.valid23181
  · exact MergedCutProfiles.Batch579.valid23183
  · exact MergedCutProfiles.Batch579.valid23185
  · exact MergedCutProfiles.Batch319.valid12772
  · exact MergedCutProfiles.Batch579.valid23187
  · exact MergedCutProfiles.Batch454.valid18191
  · exact MergedCutProfiles.Batch579.valid23191
  · exact MergedCutProfiles.Batch454.valid18192
  · exact MergedCutProfiles.Batch022.valid889
  · exact MergedCutProfiles.Batch454.valid18199
  · exact MergedCutProfiles.Batch455.valid18205
  · exact MergedCutProfiles.Batch579.valid23192
  · exact MergedCutProfiles.Batch579.valid23193
  · exact MergedCutProfiles.Batch022.valid905
  · exact MergedCutProfiles.Batch454.valid18195
theorem numericValid3807 : retention3807.NumericValid := by decide +kernel
def certificate3807 : RatCutBinCertificate := ⟨⟨retention3807,(1809857969488236619/1000000000000000000),(15120529320228081/1000000000000000000),(8325289875112082173/1000000000000000000),(12988872207026718218203/500000000000000000),(11811367016186883/5000000000000000)⟩,(999931272476733191/1000000000000000000),(78472419083026379/200000000000000000),(240553947048921759/1000000000000000000),(85140129657349659/500000000000000000)⟩
theorem valid3807 : certificate3807.Valid := by decide +kernel
theorem sound3807 : certificate3807.Sound := rat_cut_bin_certificate_sound certificate3807 profilesValid3807 numericValid3807 valid3807

def retention3808 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(34430573289540523509/3105614287479023654806),(67165523678458611/50000000000000000),(49/20),(144212901880161682491/64000000000000000000),true,MergedCutProfiles.Batch454.profile18198,![MergedCutProfiles.Batch454.profile18198,MergedCutProfiles.Batch319.profile12781,MergedCutProfiles.Batch022.profile896,MergedCutProfiles.Batch319.profile12794,MergedCutProfiles.Batch319.profile12796,MergedCutProfiles.Batch022.profile904,MergedCutProfiles.Batch022.profile915,MergedCutProfiles.Batch579.profile23194,MergedCutProfiles.Batch023.profile930,MergedCutProfiles.Batch579.profile23195,MergedCutProfiles.Batch579.profile23196,MergedCutProfiles.Batch579.profile23197,MergedCutProfiles.Batch579.profile23198,MergedCutProfiles.Batch579.profile23199,MergedCutProfiles.Batch580.profile23200,MergedCutProfiles.Batch580.profile23201]⟩
theorem profilesValid3808 : retention3808.ProfilesValid := by
  change ∀ j : Fin 16, (retention3808.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch454.valid18198
  · exact MergedCutProfiles.Batch319.valid12781
  · exact MergedCutProfiles.Batch022.valid896
  · exact MergedCutProfiles.Batch319.valid12794
  · exact MergedCutProfiles.Batch319.valid12796
  · exact MergedCutProfiles.Batch022.valid904
  · exact MergedCutProfiles.Batch022.valid915
  · exact MergedCutProfiles.Batch579.valid23194
  · exact MergedCutProfiles.Batch023.valid930
  · exact MergedCutProfiles.Batch579.valid23195
  · exact MergedCutProfiles.Batch579.valid23196
  · exact MergedCutProfiles.Batch579.valid23197
  · exact MergedCutProfiles.Batch579.valid23198
  · exact MergedCutProfiles.Batch579.valid23199
  · exact MergedCutProfiles.Batch580.valid23200
  · exact MergedCutProfiles.Batch580.valid23201
theorem numericValid3808 : retention3808.NumericValid := by decide +kernel
def certificate3808 : RatCutBinCertificate := ⟨⟨retention3808,(1809857969488236619/1000000000000000000),(15120529320228081/1000000000000000000),(8325289875112082173/1000000000000000000),(12988872207026718218203/500000000000000000),(2245273210124871581/1000000000000000000)⟩,(999931272476733191/1000000000000000000),(197862622205998917/500000000000000000),(237422020496118733/1000000000000000000),(170178055662116277/1000000000000000000)⟩
theorem valid3808 : certificate3808.Valid := by decide +kernel
theorem sound3808 : certificate3808.Sound := rat_cut_bin_certificate_sound certificate3808 profilesValid3808 numericValid3808 valid3808

def retention3809 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(32000000000000000000/1552807143739511827403),(34430573289540523509/1000000000000000000),1,(2987131308433191812927304815062672253/1377222931581620940360000000000000000),false,MergedCutProfiles.Batch580.profile23202,(fun _ => MergedCutProfiles.Batch580.profile23202)⟩
theorem profilesValid3809 : retention3809.ProfilesValid := by
  exact MergedCutProfiles.Batch580.valid23202
theorem numericValid3809 : retention3809.NumericValid := by decide +kernel
def certificate3809 : RatCutBinCertificate := ⟨⟨retention3809,(1809857969488236619/1000000000000000000),(15120529320228081/1000000000000000000),(8325289875112082173/1000000000000000000),(12988872207026718218203/500000000000000000),(2165665542382739003/1000000000000000000)⟩,(999931272476733191/1000000000000000000),(220141562735829261/1000000000000000000),(89299471388809739/200000000000000000),(454839078929719799/500000000000000000)⟩
theorem valid3809 : certificate3809.Valid := by decide +kernel
theorem sound3809 : certificate3809.Sound := rat_cut_bin_certificate_sound certificate3809 profilesValid3809 numericValid3809 valid3809

def retention3810 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(1/2),64,1,(255370911039032911357452645744173379951/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch023.profile947,(fun _ => MergedCutProfiles.Batch023.profile947)⟩
theorem profilesValid3810 : retention3810.ProfilesValid := by
  exact MergedCutProfiles.Batch023.valid947
theorem numericValid3810 : retention3810.NumericValid := by decide +kernel
def certificate3810 : RatCutBinCertificate := ⟨⟨retention3810,(1809857969488236619/1000000000000000000),(15120529320228081/1000000000000000000),(8325289875112082173/1000000000000000000),(12988872207026718218203/500000000000000000),(994255527204753757/1000000000000000000)⟩,(999931272476733191/1000000000000000000),(58967408902694109/125000000000000000),(17382927522008299/100000000000000000),(170175025235778367/1000000000000000000)⟩
theorem valid3810 : certificate3810.Valid := by decide +kernel
theorem sound3810 : certificate3810.Sound := rat_cut_bin_certificate_sound certificate3810 profilesValid3810 numericValid3810 valid3810

def retention3811 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(32000000000000000000/1552807143739511827403),(9176165193320450901/500000000000000000),1,(1569524768296905323192680791734434859/734093215465636072080000000000000000),false,MergedCutProfiles.Batch580.profile23202,(fun _ => MergedCutProfiles.Batch580.profile23202)⟩
theorem profilesValid3811 : retention3811.ProfilesValid := by
  exact MergedCutProfiles.Batch580.valid23202
theorem numericValid3811 : retention3811.NumericValid := by decide +kernel
def certificate3811 : RatCutBinCertificate := ⟨⟨retention3811,(1782928220488236619/1000000000000000000),(15120529320228081/1000000000000000000),(8325289875112082173/1000000000000000000),(12988872207026718218203/500000000000000000),(208477286597003/97656250000000)⟩,(31247884222113269/31250000000000000),(32350291305605167/1000000000000000000),(837450127429602751/1000000000000000000),(400347721652594303/250000000000000000)⟩
theorem valid3811 : certificate3811.Valid := by decide +kernel
theorem sound3811 : certificate3811.Sound := rat_cut_bin_certificate_sound certificate3811 profilesValid3811 numericValid3811 valid3811

def retention3812 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(1/2),64,1,(255370911039032911357452645744173379951/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch023.profile947,(fun _ => MergedCutProfiles.Batch023.profile947)⟩
theorem profilesValid3812 : retention3812.ProfilesValid := by
  exact MergedCutProfiles.Batch023.valid947
theorem numericValid3812 : retention3812.NumericValid := by decide +kernel
def certificate3812 : RatCutBinCertificate := ⟨⟨retention3812,(1782928220488236619/1000000000000000000),(15120529320228081/1000000000000000000),(8325289875112082173/1000000000000000000),(12988872207026718218203/500000000000000000),(994304437461231603/1000000000000000000)⟩,(31247884222113269/31250000000000000),(34728619900848133/500000000000000000),(29525033598236001/40000000000000000),(28905786177221081/40000000000000000)⟩
theorem valid3812 : certificate3812.Valid := by decide +kernel
theorem sound3812 : certificate3812.Sound := rat_cut_bin_certificate_sound certificate3812 profilesValid3812 numericValid3812 valid3812

def retention3813 : RatCutRetentionCertificate := ⟨(19/1000),(39/2000),(600300726506529479/2941397753709211052194),(55991132586645027/100000000000000000),4,(1625989782367074911140881776454612453/746548434488600360000000000000000000),true,MergedCutProfiles.Batch580.profile23203,![MergedCutProfiles.Batch580.profile23203,MergedCutProfiles.Batch580.profile23204,MergedCutProfiles.Batch580.profile23205,MergedCutProfiles.Batch580.profile23206,MergedCutProfiles.Batch580.profile23207,MergedCutProfiles.Batch580.profile23208,MergedCutProfiles.Batch580.profile23209,MergedCutProfiles.Batch580.profile23210,MergedCutProfiles.Batch580.profile23211,MergedCutProfiles.Batch580.profile23212,MergedCutProfiles.Batch580.profile23213,MergedCutProfiles.Batch580.profile23214,MergedCutProfiles.Batch580.profile23215,MergedCutProfiles.Batch580.profile23216,MergedCutProfiles.Batch580.profile23217,MergedCutProfiles.Batch580.profile23218]⟩
theorem profilesValid3813 : retention3813.ProfilesValid := by
  change ∀ j : Fin 16, (retention3813.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch580.valid23203
  · exact MergedCutProfiles.Batch580.valid23204
  · exact MergedCutProfiles.Batch580.valid23205
  · exact MergedCutProfiles.Batch580.valid23206
  · exact MergedCutProfiles.Batch580.valid23207
  · exact MergedCutProfiles.Batch580.valid23208
  · exact MergedCutProfiles.Batch580.valid23209
  · exact MergedCutProfiles.Batch580.valid23210
  · exact MergedCutProfiles.Batch580.valid23211
  · exact MergedCutProfiles.Batch580.valid23212
  · exact MergedCutProfiles.Batch580.valid23213
  · exact MergedCutProfiles.Batch580.valid23214
  · exact MergedCutProfiles.Batch580.valid23215
  · exact MergedCutProfiles.Batch580.valid23216
  · exact MergedCutProfiles.Batch580.valid23217
  · exact MergedCutProfiles.Batch580.valid23218
theorem numericValid3813 : retention3813.NumericValid := by decide +kernel
def certificate3813 : RatCutBinCertificate := ⟨⟨retention3813,(1812427699421595639/1000000000000000000),(3988876601543201/250000000000000000),(8434505002173129721/1000000000000000000),(24868242594516611726429/1000000000000000000),(216429552598710663/100000000000000000)⟩,(999928220709849401/1000000000000000000),(345680204182501943/500000000000000000),(53462601907967941/1000000000000000000),(11648264426615469/500000000000000000)⟩
theorem valid3813 : certificate3813.Valid := by decide +kernel
theorem sound3813 : certificate3813.Sound := rat_cut_bin_certificate_sound certificate3813 profilesValid3813 numericValid3813 valid3813

def retention3814 : RatCutRetentionCertificate := ⟨(19/1000),(39/2000),(616736110000000000/1470698876854605526097),(600300726506529479/1000000000000000000),4,(9035849710084751747/4000000000000000000),true,MergedCutProfiles.Batch580.profile23204,![MergedCutProfiles.Batch580.profile23204,MergedCutProfiles.Batch580.profile23206,MergedCutProfiles.Batch580.profile23219,MergedCutProfiles.Batch580.profile23210,MergedCutProfiles.Batch580.profile23212,MergedCutProfiles.Batch580.profile23214,MergedCutProfiles.Batch580.profile23216,MergedCutProfiles.Batch580.profile23218,MergedCutProfiles.Batch580.profile23220,MergedCutProfiles.Batch580.profile23221,MergedCutProfiles.Batch580.profile23222,MergedCutProfiles.Batch580.profile23223,MergedCutProfiles.Batch580.profile23224,MergedCutProfiles.Batch580.profile23225,MergedCutProfiles.Batch580.profile23226,MergedCutProfiles.Batch580.profile23227]⟩
theorem profilesValid3814 : retention3814.ProfilesValid := by
  change ∀ j : Fin 16, (retention3814.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch580.valid23204
  · exact MergedCutProfiles.Batch580.valid23206
  · exact MergedCutProfiles.Batch580.valid23219
  · exact MergedCutProfiles.Batch580.valid23210
  · exact MergedCutProfiles.Batch580.valid23212
  · exact MergedCutProfiles.Batch580.valid23214
  · exact MergedCutProfiles.Batch580.valid23216
  · exact MergedCutProfiles.Batch580.valid23218
  · exact MergedCutProfiles.Batch580.valid23220
  · exact MergedCutProfiles.Batch580.valid23221
  · exact MergedCutProfiles.Batch580.valid23222
  · exact MergedCutProfiles.Batch580.valid23223
  · exact MergedCutProfiles.Batch580.valid23224
  · exact MergedCutProfiles.Batch580.valid23225
  · exact MergedCutProfiles.Batch580.valid23226
  · exact MergedCutProfiles.Batch580.valid23227
theorem numericValid3814 : retention3814.NumericValid := by decide +kernel
def certificate3814 : RatCutBinCertificate := ⟨⟨retention3814,(1812427699421595639/1000000000000000000),(3988876601543201/250000000000000000),(8434505002173129721/1000000000000000000),(24868242594516611726429/1000000000000000000),(1122624093043173711/500000000000000000)⟩,(999928220709849401/1000000000000000000),(31773772367979259/50000000000000000),(76411534855528069/1000000000000000000),(1086286677565071/31250000000000000)⟩
theorem valid3814 : certificate3814.Valid := by decide +kernel
theorem sound3814 : certificate3814.Sound := rat_cut_bin_certificate_sound certificate3814 profilesValid3814 numericValid3814 valid3814

def retention3815 : RatCutRetentionCertificate := ⟨(19/1000),(39/2000),(1000518448535425975/1470698876854605526097),(61673611/50000000),(13/5),(11669792438668686084686057219015260639/4933888880000000000000000000000000000),true,MergedCutProfiles.Batch580.profile23228,![MergedCutProfiles.Batch580.profile23228,MergedCutProfiles.Batch580.profile23219,MergedCutProfiles.Batch580.profile23212,MergedCutProfiles.Batch580.profile23215,MergedCutProfiles.Batch580.profile23218,MergedCutProfiles.Batch580.profile23229,MergedCutProfiles.Batch580.profile23230,MergedCutProfiles.Batch580.profile23224,MergedCutProfiles.Batch580.profile23226,MergedCutProfiles.Batch580.profile23231,MergedCutProfiles.Batch580.profile23232,MergedCutProfiles.Batch580.profile23233,MergedCutProfiles.Batch580.profile23234,MergedCutProfiles.Batch580.profile23235,MergedCutProfiles.Batch580.profile23236,MergedCutProfiles.Batch580.profile23237]⟩
theorem profilesValid3815 : retention3815.ProfilesValid := by
  change ∀ j : Fin 16, (retention3815.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch580.valid23228
  · exact MergedCutProfiles.Batch580.valid23219
  · exact MergedCutProfiles.Batch580.valid23212
  · exact MergedCutProfiles.Batch580.valid23215
  · exact MergedCutProfiles.Batch580.valid23218
  · exact MergedCutProfiles.Batch580.valid23229
  · exact MergedCutProfiles.Batch580.valid23230
  · exact MergedCutProfiles.Batch580.valid23224
  · exact MergedCutProfiles.Batch580.valid23226
  · exact MergedCutProfiles.Batch580.valid23231
  · exact MergedCutProfiles.Batch580.valid23232
  · exact MergedCutProfiles.Batch580.valid23233
  · exact MergedCutProfiles.Batch580.valid23234
  · exact MergedCutProfiles.Batch580.valid23235
  · exact MergedCutProfiles.Batch580.valid23236
  · exact MergedCutProfiles.Batch580.valid23237
theorem numericValid3815 : retention3815.NumericValid := by decide +kernel
def certificate3815 : RatCutBinCertificate := ⟨⟨retention3815,(1812427699421595639/1000000000000000000),(3988876601543201/250000000000000000),(8434505002173129721/1000000000000000000),(24868242594516611726429/1000000000000000000),(2356317860257148927/1000000000000000000)⟩,(999928220709849401/1000000000000000000),(395605017149866227/1000000000000000000),(23753348811152739/100000000000000000),(33565398474993893/200000000000000000)⟩
theorem valid3815 : certificate3815.Valid := by decide +kernel
theorem sound3815 : certificate3815.Sound := rat_cut_bin_certificate_sound certificate3815 profilesValid3815 numericValid3815 valid3815

def certificates : List RatCutBinCertificate := [certificate3804,certificate3805,certificate3806,certificate3807,certificate3808,certificate3809,certificate3810,certificate3811,certificate3812,certificate3813,certificate3814,certificate3815]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3804,List.forall_mem_cons.mpr ⟨sound3805,List.forall_mem_cons.mpr ⟨sound3806,List.forall_mem_cons.mpr ⟨sound3807,List.forall_mem_cons.mpr ⟨sound3808,List.forall_mem_cons.mpr ⟨sound3809,List.forall_mem_cons.mpr ⟨sound3810,List.forall_mem_cons.mpr ⟨sound3811,List.forall_mem_cons.mpr ⟨sound3812,List.forall_mem_cons.mpr ⟨sound3813,List.forall_mem_cons.mpr ⟨sound3814,List.forall_mem_cons.mpr ⟨sound3815,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch317
