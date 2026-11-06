import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch019
import Cycle12.MergedCutProfiles.Batch020
import Cycle12.MergedCutProfiles.Batch317
import Cycle12.MergedCutProfiles.Batch452
import Cycle12.MergedCutProfiles.Batch453
import Cycle12.MergedCutProfiles.Batch578
import Cycle12.MergedCutProfiles.Batch647
import Cycle12.MergedCutProfiles.Batch648

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch370

def retention4440 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(667634885055258995/19580518535939935226393),(604401151938475349/1000000000000000000),4,(68712266152476246236998821580153509/30220057596923767450000000000000000),true,MergedCutProfiles.Batch647.profile25912,![MergedCutProfiles.Batch647.profile25912,MergedCutProfiles.Batch647.profile25913,MergedCutProfiles.Batch647.profile25914,MergedCutProfiles.Batch647.profile25914,MergedCutProfiles.Batch647.profile25915,MergedCutProfiles.Batch647.profile25916,MergedCutProfiles.Batch647.profile25916,MergedCutProfiles.Batch647.profile25917,MergedCutProfiles.Batch647.profile25917,MergedCutProfiles.Batch647.profile25918,MergedCutProfiles.Batch647.profile25918,MergedCutProfiles.Batch647.profile25919,MergedCutProfiles.Batch647.profile25919,MergedCutProfiles.Batch648.profile25920,MergedCutProfiles.Batch648.profile25920,MergedCutProfiles.Batch648.profile25920]⟩
theorem profilesValid4440 : retention4440.ProfilesValid := by
  change ∀ j : Fin 16, (retention4440.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch647.valid25912
  · exact MergedCutProfiles.Batch647.valid25913
  · exact MergedCutProfiles.Batch647.valid25914
  · exact MergedCutProfiles.Batch647.valid25914
  · exact MergedCutProfiles.Batch647.valid25915
  · exact MergedCutProfiles.Batch647.valid25916
  · exact MergedCutProfiles.Batch647.valid25916
  · exact MergedCutProfiles.Batch647.valid25917
  · exact MergedCutProfiles.Batch647.valid25917
  · exact MergedCutProfiles.Batch647.valid25918
  · exact MergedCutProfiles.Batch647.valid25918
  · exact MergedCutProfiles.Batch647.valid25919
  · exact MergedCutProfiles.Batch647.valid25919
  · exact MergedCutProfiles.Batch648.valid25920
  · exact MergedCutProfiles.Batch648.valid25920
  · exact MergedCutProfiles.Batch648.valid25920
theorem numericValid4440 : retention4440.NumericValid := by decide +kernel
def certificate4440 : RatCutBinCertificate := ⟨⟨retention4440,(1868424475170467959/1000000000000000000),(12019078477736559/1000000000000000000),(4056640817141112331/500000000000000000),(39901735358418733875897/250000000000000000),(1131329444185288537/500000000000000000)⟩,(999988417786166947/1000000000000000000),(264971497684996131/500000000000000000),(26710138551640237/200000000000000000),(61219827006040607/1000000000000000000)⟩
theorem valid4440 : certificate4440.Valid := by decide +kernel
theorem sound4440 : certificate4440.Sound := rat_cut_bin_certificate_sound certificate4440 profilesValid4440 numericValid4440 valid4440

def retention4441 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(1266866319000000000/19580518535939935226393),(133526977011051799/200000000000000000),4,(604157500259608468619/256000000000000000000),true,MergedCutProfiles.Batch647.profile25913,![MergedCutProfiles.Batch647.profile25913,MergedCutProfiles.Batch647.profile25914,MergedCutProfiles.Batch647.profile25916,MergedCutProfiles.Batch647.profile25917,MergedCutProfiles.Batch647.profile25918,MergedCutProfiles.Batch647.profile25919,MergedCutProfiles.Batch647.profile25919,MergedCutProfiles.Batch648.profile25920,MergedCutProfiles.Batch452.profile18113,MergedCutProfiles.Batch648.profile25921,MergedCutProfiles.Batch648.profile25921,MergedCutProfiles.Batch648.profile25922,MergedCutProfiles.Batch648.profile25922,MergedCutProfiles.Batch648.profile25923,MergedCutProfiles.Batch648.profile25923,MergedCutProfiles.Batch648.profile25924]⟩
theorem profilesValid4441 : retention4441.ProfilesValid := by
  change ∀ j : Fin 16, (retention4441.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch647.valid25913
  · exact MergedCutProfiles.Batch647.valid25914
  · exact MergedCutProfiles.Batch647.valid25916
  · exact MergedCutProfiles.Batch647.valid25917
  · exact MergedCutProfiles.Batch647.valid25918
  · exact MergedCutProfiles.Batch647.valid25919
  · exact MergedCutProfiles.Batch647.valid25919
  · exact MergedCutProfiles.Batch648.valid25920
  · exact MergedCutProfiles.Batch452.valid18113
  · exact MergedCutProfiles.Batch648.valid25921
  · exact MergedCutProfiles.Batch648.valid25921
  · exact MergedCutProfiles.Batch648.valid25922
  · exact MergedCutProfiles.Batch648.valid25922
  · exact MergedCutProfiles.Batch648.valid25923
  · exact MergedCutProfiles.Batch648.valid25923
  · exact MergedCutProfiles.Batch648.valid25924
theorem numericValid4441 : retention4441.NumericValid := by decide +kernel
def certificate4441 : RatCutBinCertificate := ⟨⟨retention4441,(1868424475170467959/1000000000000000000),(12019078477736559/1000000000000000000),(4056640817141112331/500000000000000000),(39901735358418733875897/250000000000000000),(146807415057100891/62500000000000000)⟩,(999988417786166947/1000000000000000000),(239134556265951481/500000000000000000),(6758729210359543/40000000000000000),(81336571593129751/1000000000000000000)⟩
theorem valid4441 : certificate4441.Valid := by decide +kernel
theorem sound4441 : certificate4441.Sound := rat_cut_bin_certificate_sound certificate4441 profilesValid4441 numericValid4441 valid4441

def retention4442 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(3885278731779363486/19580518535939935226393),(1266866319/1000000000),(5/2),(2996208952456560475858260083915366639/1266866319000000000000000000000000000),true,MergedCutProfiles.Batch647.profile25916,![MergedCutProfiles.Batch647.profile25916,MergedCutProfiles.Batch647.profile25919,MergedCutProfiles.Batch452.profile18113,MergedCutProfiles.Batch648.profile25922,MergedCutProfiles.Batch648.profile25924,MergedCutProfiles.Batch452.profile18114,MergedCutProfiles.Batch648.profile25925,MergedCutProfiles.Batch317.profile12704,MergedCutProfiles.Batch452.profile18115,MergedCutProfiles.Batch648.profile25926,MergedCutProfiles.Batch648.profile25927,MergedCutProfiles.Batch648.profile25928,MergedCutProfiles.Batch453.profile18123,MergedCutProfiles.Batch453.profile18123,MergedCutProfiles.Batch648.profile25929,MergedCutProfiles.Batch317.profile12705]⟩
theorem profilesValid4442 : retention4442.ProfilesValid := by
  change ∀ j : Fin 16, (retention4442.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch647.valid25916
  · exact MergedCutProfiles.Batch647.valid25919
  · exact MergedCutProfiles.Batch452.valid18113
  · exact MergedCutProfiles.Batch648.valid25922
  · exact MergedCutProfiles.Batch648.valid25924
  · exact MergedCutProfiles.Batch452.valid18114
  · exact MergedCutProfiles.Batch648.valid25925
  · exact MergedCutProfiles.Batch317.valid12704
  · exact MergedCutProfiles.Batch452.valid18115
  · exact MergedCutProfiles.Batch648.valid25926
  · exact MergedCutProfiles.Batch648.valid25927
  · exact MergedCutProfiles.Batch648.valid25928
  · exact MergedCutProfiles.Batch453.valid18123
  · exact MergedCutProfiles.Batch453.valid18123
  · exact MergedCutProfiles.Batch648.valid25929
  · exact MergedCutProfiles.Batch317.valid12705
theorem numericValid4442 : retention4442.NumericValid := by decide +kernel
def certificate4442 : RatCutBinCertificate := ⟨⟨retention4442,(1868424475170467959/1000000000000000000),(12019078477736559/1000000000000000000),(4056640817141112331/500000000000000000),(39901735358418733875897/250000000000000000),(2358135593198834063/1000000000000000000)⟩,(999988417786166947/1000000000000000000),(331333475207489963/1000000000000000000),(151327922437572201/500000000000000000),(219966591478309369/1000000000000000000)⟩
theorem valid4442 : certificate4442.Valid := by decide +kernel
theorem sound4442 : certificate4442.Sound := rat_cut_bin_certificate_sound certificate4442 profilesValid4442 numericValid4442 valid4442

def retention4443 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(64000000000000000000/19580518535939935226393),(1942639365889681743/500000000000000000),(13/10),(21427987525396761429629244426081654919/9476289589705764600000000000000000000),true,MergedCutProfiles.Batch019.profile764,![MergedCutProfiles.Batch019.profile764,MergedCutProfiles.Batch019.profile765,MergedCutProfiles.Batch019.profile766,MergedCutProfiles.Batch019.profile767,MergedCutProfiles.Batch019.profile768,MergedCutProfiles.Batch019.profile769,MergedCutProfiles.Batch019.profile770,MergedCutProfiles.Batch019.profile771,MergedCutProfiles.Batch019.profile772,MergedCutProfiles.Batch019.profile773,MergedCutProfiles.Batch019.profile798,MergedCutProfiles.Batch019.profile775,MergedCutProfiles.Batch019.profile776,MergedCutProfiles.Batch019.profile777,MergedCutProfiles.Batch019.profile799,MergedCutProfiles.Batch648.profile25930]⟩
theorem profilesValid4443 : retention4443.ProfilesValid := by
  change ∀ j : Fin 16, (retention4443.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch019.valid764
  · exact MergedCutProfiles.Batch019.valid765
  · exact MergedCutProfiles.Batch019.valid766
  · exact MergedCutProfiles.Batch019.valid767
  · exact MergedCutProfiles.Batch019.valid768
  · exact MergedCutProfiles.Batch019.valid769
  · exact MergedCutProfiles.Batch019.valid770
  · exact MergedCutProfiles.Batch019.valid771
  · exact MergedCutProfiles.Batch019.valid772
  · exact MergedCutProfiles.Batch019.valid773
  · exact MergedCutProfiles.Batch019.valid798
  · exact MergedCutProfiles.Batch019.valid775
  · exact MergedCutProfiles.Batch019.valid776
  · exact MergedCutProfiles.Batch019.valid777
  · exact MergedCutProfiles.Batch019.valid799
  · exact MergedCutProfiles.Batch648.valid25930
theorem numericValid4443 : retention4443.NumericValid := by decide +kernel
def certificate4443 : RatCutBinCertificate := ⟨⟨retention4443,(1868424475170467959/1000000000000000000),(12019078477736559/1000000000000000000),(4056640817141112331/500000000000000000),(39901735358418733875897/250000000000000000),(2257622995983873611/1000000000000000000)⟩,(999988417786166947/1000000000000000000),(46462123994495607/200000000000000000),(107114336465963851/250000000000000000),(34605587421474823/62500000000000000)⟩
theorem valid4443 : certificate4443.Valid := by decide +kernel
theorem sound4443 : certificate4443.Sound := rat_cut_bin_certificate_sound certificate4443 profilesValid4443 numericValid4443 valid4443

def retention4444 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(1/2),64,1,(408592521868712119380352324506759031/409600000000000000000000000000000000),false,MergedCutProfiles.Batch020.profile830,(fun _ => MergedCutProfiles.Batch020.profile830)⟩
theorem profilesValid4444 : retention4444.ProfilesValid := by
  exact MergedCutProfiles.Batch020.valid830
theorem numericValid4444 : retention4444.NumericValid := by decide +kernel
def certificate4444 : RatCutBinCertificate := ⟨⟨retention4444,(1868424475170467959/1000000000000000000),(12019078477736559/1000000000000000000),(4056640817141112331/500000000000000000),(39901735358418733875897/250000000000000000),(62173277378091119/62500000000000000)⟩,(999988417786166947/1000000000000000000),(25617542305431599/62500000000000000),(112275091193204467/500000000000000000),(10997744712494591/50000000000000000)⟩
theorem valid4444 : certificate4444.Valid := by decide +kernel
theorem sound4444 : certificate4444.Sound := rat_cut_bin_certificate_sound certificate4444 profilesValid4444 numericValid4444 valid4444

def retention4445 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(64000000000000000000/19580518535939935226393),(17195704096029440333/1000000000000000000),1,(155866092833856456754985646261292582747/68782816384117761332000000000000000000),false,MergedCutProfiles.Batch648.profile25931,(fun _ => MergedCutProfiles.Batch648.profile25931)⟩
theorem profilesValid4445 : retention4445.ProfilesValid := by
  exact MergedCutProfiles.Batch648.valid25931
theorem numericValid4445 : retention4445.NumericValid := by decide +kernel
def certificate4445 : RatCutBinCertificate := ⟨⟨retention4445,(1791108653170467959/1000000000000000000),(12019078477736559/1000000000000000000),(4056640817141112331/500000000000000000),(39901735358418733875897/250000000000000000),(2263408148818133189/1000000000000000000)⟩,(999988897060818719/1000000000000000000),(28245474594000647/1000000000000000000),(849387201922624297/1000000000000000000),(1698871632444771143/1000000000000000000)⟩
theorem valid4445 : certificate4445.Valid := by decide +kernel
theorem sound4445 : certificate4445.Sound := rat_cut_bin_certificate_sound certificate4445 profilesValid4445 numericValid4445 valid4445

def retention4446 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(1/2),64,1,(408592521868712119380352324506759031/409600000000000000000000000000000000),false,MergedCutProfiles.Batch020.profile830,(fun _ => MergedCutProfiles.Batch020.profile830)⟩
theorem profilesValid4446 : retention4446.ProfilesValid := by
  exact MergedCutProfiles.Batch020.valid830
theorem numericValid4446 : retention4446.NumericValid := by decide +kernel
def certificate4446 : RatCutBinCertificate := ⟨⟨retention4446,(1791108653170467959/1000000000000000000),(12019078477736559/1000000000000000000),(4056640817141112331/500000000000000000),(39901735358418733875897/250000000000000000),(994886974309281001/1000000000000000000)⟩,(999988897060818719/1000000000000000000),(6425959834048681/100000000000000000),(375588183208990167/500000000000000000),(91985969557811057/125000000000000000)⟩
theorem valid4446 : certificate4446.Valid := by decide +kernel
theorem sound4446 : certificate4446.Sound := rat_cut_bin_certificate_sound certificate4446 profilesValid4446 numericValid4446 valid4446

def retention4447 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(677887506952654026/19580518535939935226393),(671175749458073293/1000000000000000000),4,(1587507127735049637706969913675160627/671175749458073293000000000000000000),false,MergedCutProfiles.Batch648.profile25932,(fun _ => MergedCutProfiles.Batch648.profile25932)⟩
theorem profilesValid4447 : retention4447.ProfilesValid := by
  exact MergedCutProfiles.Batch648.valid25932
theorem numericValid4447 : retention4447.NumericValid := by decide +kernel
def certificate4447 : RatCutBinCertificate := ⟨⟨retention4447,(1758462553170467959/1000000000000000000),(12019078477736559/1000000000000000000),(4056640817141112331/500000000000000000),(39901735358418733875897/250000000000000000),(94193717651514151/40000000000000000)⟩,(999989099431403291/1000000000000000000),(99971573261316853/125000000000000000),(10767968611122327/500000000000000000),(10398136260270533/1000000000000000000)⟩
theorem valid4447 : certificate4447.Valid := by decide +kernel
theorem sound4447 : certificate4447.Sound := rat_cut_bin_certificate_sound certificate4447 profilesValid4447 numericValid4447 valid4447

def retention4448 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(1870414049619931772/19580518535939935226393),(338943753476327013/500000000000000000),4,(1283886364534889610821558090238461299/542310005562123220800000000000000000),false,MergedCutProfiles.Batch648.profile25933,(fun _ => MergedCutProfiles.Batch648.profile25933)⟩
theorem profilesValid4448 : retention4448.ProfilesValid := by
  exact MergedCutProfiles.Batch648.valid25933
theorem numericValid4448 : retention4448.NumericValid := by decide +kernel
def certificate4448 : RatCutBinCertificate := ⟨⟨retention4448,(1758462553170467959/1000000000000000000),(12019078477736559/1000000000000000000),(4056640817141112331/500000000000000000),(39901735358418733875897/250000000000000000),(589254983682877929/250000000000000000)⟩,(999989099431403291/1000000000000000000),(398284433712719639/500000000000000000),(1391135157333629/62500000000000000),(10774193141008841/1000000000000000000)⟩
theorem valid4448 : certificate4448.Valid := by decide +kernel
theorem sound4448 : certificate4448.Sound := rat_cut_bin_certificate_sound certificate4448 profilesValid4448 numericValid4448 valid4448

def retention4449 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(64000000000000000000/19580518535939935226393),(467603512404982943/250000000000000000),(43/20),(27366437449244943348492115850127814279/11690087810124573575000000000000000000),false,MergedCutProfiles.Batch648.profile25931,(fun _ => MergedCutProfiles.Batch648.profile25931)⟩
theorem profilesValid4449 : retention4449.ProfilesValid := by
  exact MergedCutProfiles.Batch648.valid25931
theorem numericValid4449 : retention4449.NumericValid := by decide +kernel
def certificate4449 : RatCutBinCertificate := ⟨⟨retention4449,(1758462553170467959/1000000000000000000),(12019078477736559/1000000000000000000),(4056640817141112331/500000000000000000),(39901735358418733875897/250000000000000000),(1167697139224563899/500000000000000000)⟩,(999989099431403291/1000000000000000000),(645325821852296401/1000000000000000000),(9002688381479747/125000000000000000),(61593702601611221/1000000000000000000)⟩
theorem valid4449 : certificate4449.Valid := by decide +kernel
theorem sound4449 : certificate4449.Sound := rat_cut_bin_certificate_sound certificate4449 profilesValid4449 numericValid4449 valid4449

def retention4450 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(1/40),64,1,(34551488668056805389986143622115878679/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch648.profile25934,(fun _ => MergedCutProfiles.Batch648.profile25934)⟩
theorem profilesValid4450 : retention4450.ProfilesValid := by
  exact MergedCutProfiles.Batch648.valid25934
theorem numericValid4450 : retention4450.NumericValid := by decide +kernel
def certificate4450 : RatCutBinCertificate := ⟨⟨retention4450,(1758462553170467959/1000000000000000000),(12019078477736559/1000000000000000000),(4056640817141112331/500000000000000000),(39901735358418733875897/250000000000000000),(17254904333245213/8000000000000000)⟩,(999989099431403291/1000000000000000000),(301982520619389333/500000000000000000),(91492252780712563/1000000000000000000),(95450275992920643/500000000000000000)⟩
theorem valid4450 : certificate4450.Valid := by decide +kernel
theorem sound4450 : certificate4450.Sound := rat_cut_bin_certificate_sound certificate4450 profilesValid4450 numericValid4450 valid4450

def retention4451 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(221670462604383020/5794460636957674161301),(608046395450615409/1000000000000000000),4,(9121116682088436003/4000000000000000000),true,MergedCutProfiles.Batch648.profile25935,![MergedCutProfiles.Batch648.profile25935,MergedCutProfiles.Batch648.profile25936,MergedCutProfiles.Batch648.profile25937,MergedCutProfiles.Batch578.profile23155,MergedCutProfiles.Batch648.profile25938,MergedCutProfiles.Batch648.profile25938,MergedCutProfiles.Batch648.profile25939,MergedCutProfiles.Batch648.profile25939,MergedCutProfiles.Batch578.profile23156,MergedCutProfiles.Batch648.profile25940,MergedCutProfiles.Batch648.profile25940,MergedCutProfiles.Batch648.profile25940,MergedCutProfiles.Batch578.profile23157,MergedCutProfiles.Batch578.profile23157,MergedCutProfiles.Batch648.profile25941,MergedCutProfiles.Batch648.profile25941]⟩
theorem profilesValid4451 : retention4451.ProfilesValid := by
  change ∀ j : Fin 16, (retention4451.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch648.valid25935
  · exact MergedCutProfiles.Batch648.valid25936
  · exact MergedCutProfiles.Batch648.valid25937
  · exact MergedCutProfiles.Batch578.valid23155
  · exact MergedCutProfiles.Batch648.valid25938
  · exact MergedCutProfiles.Batch648.valid25938
  · exact MergedCutProfiles.Batch648.valid25939
  · exact MergedCutProfiles.Batch648.valid25939
  · exact MergedCutProfiles.Batch578.valid23156
  · exact MergedCutProfiles.Batch648.valid25940
  · exact MergedCutProfiles.Batch648.valid25940
  · exact MergedCutProfiles.Batch648.valid25940
  · exact MergedCutProfiles.Batch578.valid23157
  · exact MergedCutProfiles.Batch578.valid23157
  · exact MergedCutProfiles.Batch648.valid25941
  · exact MergedCutProfiles.Batch648.valid25941
theorem numericValid4451 : retention4451.NumericValid := by decide +kernel
def certificate4451 : RatCutBinCertificate := ⟨⟨retention4451,(1878427048205494831/1000000000000000000),(13522397103991873/1000000000000000000),(4109117189075387729/500000000000000000),(71767124962822745430191/500000000000000000),(1133958005059803017/500000000000000000)⟩,(999987070330746971/1000000000000000000),(104878802240506949/200000000000000000),(68551684283355011/500000000000000000),(31519177643879593/500000000000000000)⟩
theorem valid4451 : certificate4451.Valid := by decide +kernel
theorem sound4451 : certificate4451.Sound := rat_cut_bin_certificate_sound certificate4451 profilesValid4451 numericValid4451 valid4451

def certificates : List RatCutBinCertificate := [certificate4440,certificate4441,certificate4442,certificate4443,certificate4444,certificate4445,certificate4446,certificate4447,certificate4448,certificate4449,certificate4450,certificate4451]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4440,List.forall_mem_cons.mpr ⟨sound4441,List.forall_mem_cons.mpr ⟨sound4442,List.forall_mem_cons.mpr ⟨sound4443,List.forall_mem_cons.mpr ⟨sound4444,List.forall_mem_cons.mpr ⟨sound4445,List.forall_mem_cons.mpr ⟨sound4446,List.forall_mem_cons.mpr ⟨sound4447,List.forall_mem_cons.mpr ⟨sound4448,List.forall_mem_cons.mpr ⟨sound4449,List.forall_mem_cons.mpr ⟨sound4450,List.forall_mem_cons.mpr ⟨sound4451,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch370
