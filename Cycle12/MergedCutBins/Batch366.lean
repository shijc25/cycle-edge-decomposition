import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch013
import Cycle12.MergedCutProfiles.Batch014
import Cycle12.MergedCutProfiles.Batch015
import Cycle12.MergedCutProfiles.Batch314
import Cycle12.MergedCutProfiles.Batch449
import Cycle12.MergedCutProfiles.Batch646

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch366

def retention4392 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(1/2),64,1,(63842322836766415695342227016481542439/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch013.profile555,(fun _ => MergedCutProfiles.Batch013.profile555)⟩
theorem profilesValid4392 : retention4392.ProfilesValid := by
  exact MergedCutProfiles.Batch013.valid555
theorem numericValid4392 : retention4392.NumericValid := by decide +kernel
def certificate4392 : RatCutBinCertificate := ⟨⟨retention4392,(442724114423632951/250000000000000000),(5886872707676009/1000000000000000000),(7618207346444008837/1000000000000000000),(76942453293967764291679/250000000000000000),(199233571327815767/200000000000000000)⟩,(999994274403652617/1000000000000000000),(34468884886366827/500000000000000000),(7394184662306253/10000000000000000),(145058280897980207/200000000000000000)⟩
theorem valid4392 : certificate4392.Valid := by decide +kernel
theorem sound4392 : certificate4392.Sound := rat_cut_bin_certificate_sound certificate4392 profilesValid4392 numericValid4392 valid4392

def retention4393 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(693670172115345303/40216049413821108156326),(27472086024370111/40000000000000000),4,(522839771740387125229235746383111/219776688194960888000000000000000),false,MergedCutProfiles.Batch646.profile25853,(fun _ => MergedCutProfiles.Batch646.profile25853)⟩
theorem profilesValid4393 : retention4393.ProfilesValid := by
  exact MergedCutProfiles.Batch646.valid25853
theorem numericValid4393 : retention4393.NumericValid := by decide +kernel
def certificate4393 : RatCutBinCertificate := ⟨⟨retention4393,(442398704673632951/250000000000000000),(5886872707676009/1000000000000000000),(7618207346444008837/1000000000000000000),(76942453293967764291679/250000000000000000),(148343091297052133/62500000000000000)⟩,(499997139306031691/500000000000000000),(726934009012289673/1000000000000000000),(10308126042062827/250000000000000000),(4024053528250561/200000000000000000)⟩
theorem valid4393 : certificate4393.Valid := by decide +kernel
theorem sound4393 : certificate4393.Sound := rat_cut_bin_certificate_sound certificate4393 profilesValid4393 numericValid4393 valid4393

def retention4394 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(3085738275931008625/40216049413821108156326),(693670172115345303/1000000000000000000),4,(1320263890066190707068970247060257243/554936137692276242400000000000000000),false,MergedCutProfiles.Batch646.profile25854,(fun _ => MergedCutProfiles.Batch646.profile25854)⟩
theorem profilesValid4394 : retention4394.ProfilesValid := by
  exact MergedCutProfiles.Batch646.valid25854
theorem numericValid4394 : retention4394.NumericValid := by decide +kernel
def certificate4394 : RatCutBinCertificate := ⟨⟨retention4394,(442398704673632951/250000000000000000),(5886872707676009/1000000000000000000),(7618207346444008837/1000000000000000000),(76942453293967764291679/250000000000000000),(2373657888100728867/1000000000000000000)⟩,(499997139306031691/500000000000000000),(28982546794191609/40000000000000000),(41992320461185431/1000000000000000000),(10264168286966753/500000000000000000)⟩
theorem valid4394 : certificate4394.Valid := by decide +kernel
theorem sound4394 : certificate4394.Sound := rat_cut_bin_certificate_sound certificate4394 profilesValid4394 numericValid4394 valid4394

def retention4395 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(1/40),(24685906207448069/8000000000000000),(33/20),(428971148254882030992036273172311229079/197487249659584552000000000000000000000),false,MergedCutProfiles.Batch646.profile25855,(fun _ => MergedCutProfiles.Batch646.profile25855)⟩
theorem profilesValid4395 : retention4395.ProfilesValid := by
  exact MergedCutProfiles.Batch646.valid25855
theorem numericValid4395 : retention4395.NumericValid := by decide +kernel
def certificate4395 : RatCutBinCertificate := ⟨⟨retention4395,(442398704673632951/250000000000000000),(5886872707676009/1000000000000000000),(7618207346444008837/1000000000000000000),(76942453293967764291679/250000000000000000),(2169889782264939467/1000000000000000000)⟩,(499997139306031691/500000000000000000),(595975094549963119/1000000000000000000),(4778708979077023/50000000000000000),(19977457515463833/200000000000000000)⟩
theorem valid4395 : certificate4395.Valid := by decide +kernel
theorem sound4395 : certificate4395.Sound := rat_cut_bin_certificate_sound certificate4395 profilesValid4395 numericValid4395 valid4395

def retention4396 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(132550395350259116/6822131672314993651691),(147039682077721603/250000000000000000),4,(143477838271753993963/64000000000000000000),true,MergedCutProfiles.Batch646.profile25856,![MergedCutProfiles.Batch646.profile25856,MergedCutProfiles.Batch646.profile25857,MergedCutProfiles.Batch646.profile25857,MergedCutProfiles.Batch646.profile25858,MergedCutProfiles.Batch646.profile25859,MergedCutProfiles.Batch646.profile25859,MergedCutProfiles.Batch646.profile25859,MergedCutProfiles.Batch646.profile25860,MergedCutProfiles.Batch646.profile25860,MergedCutProfiles.Batch646.profile25861,MergedCutProfiles.Batch646.profile25861,MergedCutProfiles.Batch646.profile25861,MergedCutProfiles.Batch646.profile25862,MergedCutProfiles.Batch646.profile25862,MergedCutProfiles.Batch646.profile25862,MergedCutProfiles.Batch449.profile17979]⟩
theorem profilesValid4396 : retention4396.ProfilesValid := by
  change ∀ j : Fin 16, (retention4396.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch646.valid25856
  · exact MergedCutProfiles.Batch646.valid25857
  · exact MergedCutProfiles.Batch646.valid25857
  · exact MergedCutProfiles.Batch646.valid25858
  · exact MergedCutProfiles.Batch646.valid25859
  · exact MergedCutProfiles.Batch646.valid25859
  · exact MergedCutProfiles.Batch646.valid25859
  · exact MergedCutProfiles.Batch646.valid25860
  · exact MergedCutProfiles.Batch646.valid25860
  · exact MergedCutProfiles.Batch646.valid25861
  · exact MergedCutProfiles.Batch646.valid25861
  · exact MergedCutProfiles.Batch646.valid25861
  · exact MergedCutProfiles.Batch646.valid25862
  · exact MergedCutProfiles.Batch646.valid25862
  · exact MergedCutProfiles.Batch646.valid25862
  · exact MergedCutProfiles.Batch449.valid17979
theorem numericValid4396 : retention4396.NumericValid := by decide +kernel
def certificate4396 : RatCutBinCertificate := ⟨⟨retention4396,(1843928283350021743/1000000000000000000),(21663071517499/3125000000000000),(1928357821217704129/250000000000000000),(26431560741512952229391/100000000000000000),(2235212552689243001/1000000000000000000)⟩,(499996532415536349/500000000000000000),(277162647554225381/500000000000000000),(29655196140901009/250000000000000000),(53562770468962827/1000000000000000000)⟩
theorem valid4396 : certificate4396.Valid := by decide +kernel
theorem sound4396 : certificate4396.Sound := rat_cut_bin_certificate_sound certificate4396 profilesValid4396 numericValid4396 valid4396

def retention4397 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(259146439000000000/6822131672314993651691),(33137598837564779/50000000000000000),4,(6241604648623866839153368840075299799/2651007907005182320000000000000000000),true,MergedCutProfiles.Batch646.profile25857,![MergedCutProfiles.Batch646.profile25857,MergedCutProfiles.Batch646.profile25858,MergedCutProfiles.Batch646.profile25859,MergedCutProfiles.Batch646.profile25860,MergedCutProfiles.Batch646.profile25861,MergedCutProfiles.Batch646.profile25861,MergedCutProfiles.Batch646.profile25862,MergedCutProfiles.Batch646.profile25862,MergedCutProfiles.Batch449.profile17979,MergedCutProfiles.Batch449.profile17979,MergedCutProfiles.Batch646.profile25863,MergedCutProfiles.Batch646.profile25863,MergedCutProfiles.Batch646.profile25864,MergedCutProfiles.Batch646.profile25864,MergedCutProfiles.Batch646.profile25865,MergedCutProfiles.Batch646.profile25865]⟩
theorem profilesValid4397 : retention4397.ProfilesValid := by
  change ∀ j : Fin 16, (retention4397.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch646.valid25857
  · exact MergedCutProfiles.Batch646.valid25858
  · exact MergedCutProfiles.Batch646.valid25859
  · exact MergedCutProfiles.Batch646.valid25860
  · exact MergedCutProfiles.Batch646.valid25861
  · exact MergedCutProfiles.Batch646.valid25861
  · exact MergedCutProfiles.Batch646.valid25862
  · exact MergedCutProfiles.Batch646.valid25862
  · exact MergedCutProfiles.Batch449.valid17979
  · exact MergedCutProfiles.Batch449.valid17979
  · exact MergedCutProfiles.Batch646.valid25863
  · exact MergedCutProfiles.Batch646.valid25863
  · exact MergedCutProfiles.Batch646.valid25864
  · exact MergedCutProfiles.Batch646.valid25864
  · exact MergedCutProfiles.Batch646.valid25865
  · exact MergedCutProfiles.Batch646.valid25865
theorem numericValid4397 : retention4397.NumericValid := by decide +kernel
def certificate4397 : RatCutBinCertificate := ⟨⟨retention4397,(1843928283350021743/1000000000000000000),(21663071517499/3125000000000000),(1928357821217704129/250000000000000000),(26431560741512952229391/100000000000000000),(2347798350507594707/1000000000000000000)⟩,(499996532415536349/500000000000000000),(121910396086511163/250000000000000000),(162146536901560993/1000000000000000000),(19479815752719703/250000000000000000)⟩
theorem valid4397 : certificate4397.Valid := by decide +kernel
theorem sound4397 : certificate4397.Sound := rat_cut_bin_certificate_sound certificate4397 profilesValid4397 numericValid4397 valid4397

def retention4398 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(35473214483665136861/34110658361574968258455),(259146439/200000000),(49/20),(37390624461410032053/16000000000000000000),true,MergedCutProfiles.Batch449.profile17981,![MergedCutProfiles.Batch449.profile17981,MergedCutProfiles.Batch449.profile17983,MergedCutProfiles.Batch449.profile17985,MergedCutProfiles.Batch449.profile17986,MergedCutProfiles.Batch449.profile17988,MergedCutProfiles.Batch314.profile12568,MergedCutProfiles.Batch013.profile559,MergedCutProfiles.Batch014.profile582,MergedCutProfiles.Batch314.profile12577,MergedCutProfiles.Batch449.profile17993,MergedCutProfiles.Batch314.profile12578,MergedCutProfiles.Batch014.profile562,MergedCutProfiles.Batch314.profile12572,MergedCutProfiles.Batch014.profile563,MergedCutProfiles.Batch646.profile25866,MergedCutProfiles.Batch314.profile12581]⟩
theorem profilesValid4398 : retention4398.ProfilesValid := by
  change ∀ j : Fin 16, (retention4398.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch449.valid17981
  · exact MergedCutProfiles.Batch449.valid17983
  · exact MergedCutProfiles.Batch449.valid17985
  · exact MergedCutProfiles.Batch449.valid17986
  · exact MergedCutProfiles.Batch449.valid17988
  · exact MergedCutProfiles.Batch314.valid12568
  · exact MergedCutProfiles.Batch013.valid559
  · exact MergedCutProfiles.Batch014.valid582
  · exact MergedCutProfiles.Batch314.valid12577
  · exact MergedCutProfiles.Batch449.valid17993
  · exact MergedCutProfiles.Batch314.valid12578
  · exact MergedCutProfiles.Batch014.valid562
  · exact MergedCutProfiles.Batch314.valid12572
  · exact MergedCutProfiles.Batch014.valid563
  · exact MergedCutProfiles.Batch646.valid25866
  · exact MergedCutProfiles.Batch314.valid12581
theorem numericValid4398 : retention4398.NumericValid := by decide +kernel
def certificate4398 : RatCutBinCertificate := ⟨⟨retention4398,(1843928283350021743/1000000000000000000),(21663071517499/3125000000000000),(1928357821217704129/250000000000000000),(26431560741512952229391/100000000000000000),(93314158731474443/40000000000000000)⟩,(499996532415536349/500000000000000000),(335309921846302337/1000000000000000000),(298288134574399179/1000000000000000000),(21848891144110813/100000000000000000)⟩
theorem valid4398 : certificate4398.Valid := by decide +kernel
theorem sound4398 : certificate4398.Sound := rat_cut_bin_certificate_sound certificate4398 profilesValid4398 numericValid4398 valid4398

def retention4399 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(12800000000000000000/6822131672314993651691),(35473214483665136861/1000000000000000000),1,(128916212001324310538063948355260709/55426897630726776345312500000000000),false,MergedCutProfiles.Batch646.profile25867,(fun _ => MergedCutProfiles.Batch646.profile25867)⟩
theorem profilesValid4399 : retention4399.ProfilesValid := by
  exact MergedCutProfiles.Batch646.valid25867
theorem numericValid4399 : retention4399.NumericValid := by decide +kernel
def certificate4399 : RatCutBinCertificate := ⟨⟨retention4399,(1843928283350021743/1000000000000000000),(21663071517499/3125000000000000),(1928357821217704129/250000000000000000),(26431560741512952229391/100000000000000000),(464844203270840311/200000000000000000)⟩,(499996532415536349/500000000000000000),(2799235020848893/15625000000000000),(512299329152568101/1000000000000000000),(1117471268161118253/1000000000000000000)⟩
theorem valid4399 : certificate4399.Valid := by decide +kernel
theorem sound4399 : certificate4399.Sound := rat_cut_bin_certificate_sound certificate4399 profilesValid4399 numericValid4399 valid4399

def retention4400 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(1/2),64,1,(63842362441861810878166029772824077959/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch015.profile610,(fun _ => MergedCutProfiles.Batch015.profile610)⟩
theorem profilesValid4400 : retention4400.ProfilesValid := by
  exact MergedCutProfiles.Batch015.valid610
theorem numericValid4400 : retention4400.NumericValid := by decide +kernel
def certificate4400 : RatCutBinCertificate := ⟨⟨retention4400,(1843928283350021743/1000000000000000000),(21663071517499/3125000000000000),(1928357821217704129/250000000000000000),(26431560741512952229391/100000000000000000),(995879745595157327/1000000000000000000)⟩,(499996532415536349/500000000000000000),(82380313453998631/200000000000000000),(55688201453891497/250000000000000000),(218434479959197089/1000000000000000000)⟩
theorem valid4400 : certificate4400.Valid := by decide +kernel
theorem sound4400 : certificate4400.Sound := rat_cut_bin_certificate_sound certificate4400 profilesValid4400 numericValid4400 valid4400

def retention4401 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(12800000000000000000/6822131672314993651691),(8213594690952650247/500000000000000000),1,(9754343183336085497268140508938661/4277913901537838670312500000000000),false,MergedCutProfiles.Batch646.profile25867,(fun _ => MergedCutProfiles.Batch646.profile25867)⟩
theorem profilesValid4401 : retention4401.ProfilesValid := by
  exact MergedCutProfiles.Batch646.valid25867
theorem numericValid4401 : retention4401.NumericValid := by decide +kernel
def certificate4401 : RatCutBinCertificate := ⟨⟨retention4401,(1743828563350021743/1000000000000000000),(21663071517499/3125000000000000),(1928357821217704129/250000000000000000),(26431560741512952229391/100000000000000000),(455719261015145283/200000000000000000)⟩,(499996720657264893/500000000000000000),(30217883148718077/1000000000000000000),(843625646021473901/1000000000000000000),(1688113081506126163/1000000000000000000)⟩
theorem valid4401 : certificate4401.Valid := by decide +kernel
theorem sound4401 : certificate4401.Sound := rat_cut_bin_certificate_sound certificate4401 profilesValid4401 numericValid4401 valid4401

def retention4402 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(1/2),64,1,(63842362441861810878166029772824077959/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch015.profile610,(fun _ => MergedCutProfiles.Batch015.profile610)⟩
theorem profilesValid4402 : retention4402.ProfilesValid := by
  exact MergedCutProfiles.Batch015.valid610
theorem numericValid4402 : retention4402.NumericValid := by decide +kernel
def certificate4402 : RatCutBinCertificate := ⟨⟨retention4402,(1743828563350021743/1000000000000000000),(21663071517499/3125000000000000),(1928357821217704129/250000000000000000),(26431560741512952229391/100000000000000000),(497984853399628151/500000000000000000)⟩,(499996720657264893/500000000000000000),(34566491540769863/500000000000000000),(738932404641067939/1000000000000000000),(724672054527289703/1000000000000000000)⟩
theorem valid4402 : certificate4402.Valid := by decide +kernel
theorem sound4402 : certificate4402.Sound := rat_cut_bin_certificate_sound certificate4402 profilesValid4402 numericValid4402 valid4402

def retention4403 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(666020743038781502/34110658361574968258455),(164856619564054827/250000000000000000),4,(6203154410231617934012543204124039743/2637705913024877232000000000000000000),false,MergedCutProfiles.Batch646.profile25868,(fun _ => MergedCutProfiles.Batch646.profile25868)⟩
theorem profilesValid4403 : retention4403.ProfilesValid := by
  exact MergedCutProfiles.Batch646.valid25868
theorem numericValid4403 : retention4403.NumericValid := by decide +kernel
def certificate4403 : RatCutBinCertificate := ⟨⟨retention4403,(1732693739350021743/1000000000000000000),(21663071517499/3125000000000000),(1928357821217704129/250000000000000000),(26431560741512952229391/100000000000000000),(146593405376238547/62500000000000000)⟩,(999993483193538271/1000000000000000000),(821294723926718987/1000000000000000000),(17014312670539499/1000000000000000000),(8162179045112929/1000000000000000000)⟩
theorem valid4403 : certificate4403.Valid := by decide +kernel
theorem sound4403 : certificate4403.Sound := rat_cut_bin_certificate_sound certificate4403 profilesValid4403 numericValid4403 valid4403

def certificates : List RatCutBinCertificate := [certificate4392,certificate4393,certificate4394,certificate4395,certificate4396,certificate4397,certificate4398,certificate4399,certificate4400,certificate4401,certificate4402,certificate4403]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4392,List.forall_mem_cons.mpr ⟨sound4393,List.forall_mem_cons.mpr ⟨sound4394,List.forall_mem_cons.mpr ⟨sound4395,List.forall_mem_cons.mpr ⟨sound4396,List.forall_mem_cons.mpr ⟨sound4397,List.forall_mem_cons.mpr ⟨sound4398,List.forall_mem_cons.mpr ⟨sound4399,List.forall_mem_cons.mpr ⟨sound4400,List.forall_mem_cons.mpr ⟨sound4401,List.forall_mem_cons.mpr ⟨sound4402,List.forall_mem_cons.mpr ⟨sound4403,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch366
