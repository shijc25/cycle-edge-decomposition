import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch421
import Cycle12.MergedCutProfiles.Batch422
import Cycle12.MergedCutProfiles.Batch423
import Cycle12.MergedCutProfiles.Batch424
import Cycle12.MergedCutProfiles.Batch546
import Cycle12.MergedCutProfiles.Batch547
import Cycle12.MergedCutProfiles.Batch548

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch296

def retention3552 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(13232232091211170704/26764961125307303143),(12341941775547813027/500000000000000000),1,(3665989531786938023053332286006059789/3656871637199352008000000000000000000),false,MergedCutProfiles.Batch546.profile21864,(fun _ => MergedCutProfiles.Batch546.profile21864)⟩
theorem profilesValid3552 : retention3552.ProfilesValid := by
  exact MergedCutProfiles.Batch546.valid21864
theorem numericValid3552 : retention3552.NumericValid := by decide +kernel
def certificate3552 : RatCutBinCertificate := ⟨⟨retention3552,(578746279881922261/250000000000000000),(106411689904918233/500000000000000000),(1693583516892780107/100000000000000000),(909423140879630589347/1000000000000000000),(973401931278958599/1000000000000000000)⟩,(997984976315110531/1000000000000000000),(30668568916611131/250000000000000000),(38624154613774787/62500000000000000),(577531063137689951/1000000000000000000)⟩
theorem valid3552 : certificate3552.Valid := by decide +kernel
theorem sound3552 : certificate3552.Sound := rat_cut_bin_certificate_sound certificate3552 profilesValid3552 numericValid3552 valid3552

def retention3553 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(26729108824246564823/53529922250614606286),(827014505700698169/31250000000000000),1,(105166410307073790101220074425792490567/105857856729689365632000000000000000000),false,MergedCutProfiles.Batch546.profile21865,(fun _ => MergedCutProfiles.Batch546.profile21865)⟩
theorem profilesValid3553 : retention3553.ProfilesValid := by
  exact MergedCutProfiles.Batch546.valid21865
theorem numericValid3553 : retention3553.NumericValid := by decide +kernel
def certificate3553 : RatCutBinCertificate := ⟨⟨retention3553,(578746279881922261/250000000000000000),(106411689904918233/500000000000000000),(1693583516892780107/100000000000000000),(909423140879630589347/1000000000000000000),(48218837606834867/50000000000000000)⟩,(997984976315110531/1000000000000000000),(123822330419510437/1000000000000000000),(615636094602499703/1000000000000000000),(571648817413442607/1000000000000000000)⟩
theorem valid3553 : certificate3553.Valid := by decide +kernel
theorem sound3553 : certificate3553.Sound := rat_cut_bin_certificate_sound certificate3553 profilesValid3553 numericValid3553 valid3553

def retention3554 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(1/2),(26729108824246564823/1000000000000000000),1,(26521839801888063622121260651449666573/26729108824246564823000000000000000000),false,MergedCutProfiles.Batch421.profile16877,(fun _ => MergedCutProfiles.Batch421.profile16877)⟩
theorem profilesValid3554 : retention3554.ProfilesValid := by
  exact MergedCutProfiles.Batch421.valid16877
theorem numericValid3554 : retention3554.NumericValid := by decide +kernel
def certificate3554 : RatCutBinCertificate := ⟨⟨retention3554,(578746279881922261/250000000000000000),(106411689904918233/500000000000000000),(1693583516892780107/100000000000000000),(909423140879630589347/1000000000000000000),(963154162458015119/1000000000000000000)⟩,(997984976315110531/1000000000000000000),(12397950557283681/100000000000000000),(615315030076375261/1000000000000000000),(570850538969556277/1000000000000000000)⟩
theorem valid3554 : certificate3554.Valid := by decide +kernel
theorem sound3554 : certificate3554.Sound := rat_cut_bin_certificate_sound certificate3554 profilesValid3554 numericValid3554 valid3554

def retention3555 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(931704733392524153/52537530222601784183),(922479934052004111/1000000000000000000),(57/20),(88677366132901880121/40000000000000000000),true,MergedCutProfiles.Batch546.profile21866,![MergedCutProfiles.Batch546.profile21866,MergedCutProfiles.Batch546.profile21867,MergedCutProfiles.Batch546.profile21868,MergedCutProfiles.Batch546.profile21869,MergedCutProfiles.Batch546.profile21870,MergedCutProfiles.Batch546.profile21871,MergedCutProfiles.Batch546.profile21872,MergedCutProfiles.Batch546.profile21873,MergedCutProfiles.Batch546.profile21874,MergedCutProfiles.Batch546.profile21875,MergedCutProfiles.Batch423.profile16926,MergedCutProfiles.Batch546.profile21876,MergedCutProfiles.Batch546.profile21877,MergedCutProfiles.Batch546.profile21878,MergedCutProfiles.Batch546.profile21879,MergedCutProfiles.Batch547.profile21880]⟩
theorem profilesValid3555 : retention3555.ProfilesValid := by
  change ∀ j : Fin 16, (retention3555.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch546.valid21866
  · exact MergedCutProfiles.Batch546.valid21867
  · exact MergedCutProfiles.Batch546.valid21868
  · exact MergedCutProfiles.Batch546.valid21869
  · exact MergedCutProfiles.Batch546.valid21870
  · exact MergedCutProfiles.Batch546.valid21871
  · exact MergedCutProfiles.Batch546.valid21872
  · exact MergedCutProfiles.Batch546.valid21873
  · exact MergedCutProfiles.Batch546.valid21874
  · exact MergedCutProfiles.Batch546.valid21875
  · exact MergedCutProfiles.Batch423.valid16926
  · exact MergedCutProfiles.Batch546.valid21876
  · exact MergedCutProfiles.Batch546.valid21877
  · exact MergedCutProfiles.Batch546.valid21878
  · exact MergedCutProfiles.Batch546.valid21879
  · exact MergedCutProfiles.Batch547.valid21880
theorem numericValid3555 : retention3555.NumericValid := by decide +kernel
def certificate3555 : RatCutBinCertificate := ⟨⟨retention3555,(2266473188367216253/1000000000000000000),(216862197802423917/1000000000000000000),(17097254971987718171/1000000000000000000),(450540175640321153547/500000000000000000),(2134994774641384203/1000000000000000000)⟩,(998018955343898949/1000000000000000000),(74403874158772063/250000000000000000),(341664014862664221/1000000000000000000),(198716531729897567/1000000000000000000)⟩
theorem valid3555 : certificate3555.Valid := by decide +kernel
theorem sound3555 : certificate3555.Sound := rat_cut_bin_certificate_sound certificate3555 profilesValid3555 numericValid3555 valid3555

def retention3556 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(1096201582000000000/52537530222601784183),(931704733392524153/1000000000000000000),(14/5),(175701663929503763233/80000000000000000000),true,MergedCutProfiles.Batch547.profile21881,![MergedCutProfiles.Batch547.profile21881,MergedCutProfiles.Batch547.profile21882,MergedCutProfiles.Batch547.profile21883,MergedCutProfiles.Batch547.profile21884,MergedCutProfiles.Batch547.profile21885,MergedCutProfiles.Batch547.profile21886,MergedCutProfiles.Batch423.profile16925,MergedCutProfiles.Batch547.profile21887,MergedCutProfiles.Batch547.profile21888,MergedCutProfiles.Batch423.profile16939,MergedCutProfiles.Batch546.profile21877,MergedCutProfiles.Batch547.profile21889,MergedCutProfiles.Batch547.profile21890,MergedCutProfiles.Batch547.profile21891,MergedCutProfiles.Batch547.profile21892,MergedCutProfiles.Batch547.profile21893]⟩
theorem profilesValid3556 : retention3556.ProfilesValid := by
  change ∀ j : Fin 16, (retention3556.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch547.valid21881
  · exact MergedCutProfiles.Batch547.valid21882
  · exact MergedCutProfiles.Batch547.valid21883
  · exact MergedCutProfiles.Batch547.valid21884
  · exact MergedCutProfiles.Batch547.valid21885
  · exact MergedCutProfiles.Batch547.valid21886
  · exact MergedCutProfiles.Batch423.valid16925
  · exact MergedCutProfiles.Batch547.valid21887
  · exact MergedCutProfiles.Batch547.valid21888
  · exact MergedCutProfiles.Batch423.valid16939
  · exact MergedCutProfiles.Batch546.valid21877
  · exact MergedCutProfiles.Batch547.valid21889
  · exact MergedCutProfiles.Batch547.valid21890
  · exact MergedCutProfiles.Batch547.valid21891
  · exact MergedCutProfiles.Batch547.valid21892
  · exact MergedCutProfiles.Batch547.valid21893
theorem numericValid3556 : retention3556.NumericValid := by decide +kernel
def certificate3556 : RatCutBinCertificate := ⟨⟨retention3556,(2266473188367216253/1000000000000000000),(216862197802423917/1000000000000000000),(17097254971987718171/1000000000000000000),(450540175640321153547/500000000000000000),(1057884448037042749/500000000000000000)⟩,(998018955343898949/1000000000000000000),(298995066592292687/1000000000000000000),(339996120724645533/1000000000000000000),(24841994023974011/125000000000000000)⟩
theorem valid3556 : certificate3556.Valid := by decide +kernel
theorem sound3556 : certificate3556.Sound := rat_cut_bin_certificate_sound certificate3556 profilesValid3556 numericValid3556 valid3556

def retention3557 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(1103422044487905799/52537530222601784183),(548100791/500000000),(49/20),(8735982728916126371/4000000000000000000),true,MergedCutProfiles.Batch547.profile21894,![MergedCutProfiles.Batch547.profile21894,MergedCutProfiles.Batch547.profile21882,MergedCutProfiles.Batch547.profile21883,MergedCutProfiles.Batch547.profile21895,MergedCutProfiles.Batch547.profile21885,MergedCutProfiles.Batch547.profile21886,MergedCutProfiles.Batch547.profile21896,MergedCutProfiles.Batch547.profile21887,MergedCutProfiles.Batch547.profile21897,MergedCutProfiles.Batch547.profile21898,MergedCutProfiles.Batch422.profile16900,MergedCutProfiles.Batch547.profile21899,MergedCutProfiles.Batch422.profile16885,MergedCutProfiles.Batch423.profile16928,MergedCutProfiles.Batch547.profile21900,MergedCutProfiles.Batch547.profile21901]⟩
theorem profilesValid3557 : retention3557.ProfilesValid := by
  change ∀ j : Fin 16, (retention3557.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch547.valid21894
  · exact MergedCutProfiles.Batch547.valid21882
  · exact MergedCutProfiles.Batch547.valid21883
  · exact MergedCutProfiles.Batch547.valid21895
  · exact MergedCutProfiles.Batch547.valid21885
  · exact MergedCutProfiles.Batch547.valid21886
  · exact MergedCutProfiles.Batch547.valid21896
  · exact MergedCutProfiles.Batch547.valid21887
  · exact MergedCutProfiles.Batch547.valid21897
  · exact MergedCutProfiles.Batch547.valid21898
  · exact MergedCutProfiles.Batch422.valid16900
  · exact MergedCutProfiles.Batch547.valid21899
  · exact MergedCutProfiles.Batch422.valid16885
  · exact MergedCutProfiles.Batch423.valid16928
  · exact MergedCutProfiles.Batch547.valid21900
  · exact MergedCutProfiles.Batch547.valid21901
theorem numericValid3557 : retention3557.NumericValid := by decide +kernel
def certificate3557 : RatCutBinCertificate := ⟨⟨retention3557,(2266473188367216253/1000000000000000000),(216862197802423917/1000000000000000000),(17097254971987718171/1000000000000000000),(450540175640321153547/500000000000000000),(1056778351582035907/500000000000000000)⟩,(998018955343898949/1000000000000000000),(279406464562746763/1000000000000000000),(45535762422771133/125000000000000000),(237296474442296729/1000000000000000000)⟩
theorem valid3557 : certificate3557.Valid := by decide +kernel
theorem sound3557 : certificate3557.Sound := rat_cut_bin_certificate_sound certificate3557 profilesValid3557 numericValid3557 valid3557

def retention3558 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(1206796439611690264/52537530222601784183),(1103422044487905799/1000000000000000000),(49/20),(87164157708084930203/40000000000000000000),true,MergedCutProfiles.Batch547.profile21902,![MergedCutProfiles.Batch547.profile21902,MergedCutProfiles.Batch422.profile16880,MergedCutProfiles.Batch423.profile16938,MergedCutProfiles.Batch422.profile16897,MergedCutProfiles.Batch547.profile21903,MergedCutProfiles.Batch422.profile16898,MergedCutProfiles.Batch547.profile21904,MergedCutProfiles.Batch547.profile21905,MergedCutProfiles.Batch547.profile21906,MergedCutProfiles.Batch546.profile21877,MergedCutProfiles.Batch547.profile21899,MergedCutProfiles.Batch547.profile21907,MergedCutProfiles.Batch547.profile21908,MergedCutProfiles.Batch547.profile21909,MergedCutProfiles.Batch547.profile21910,MergedCutProfiles.Batch547.profile21911]⟩
theorem profilesValid3558 : retention3558.ProfilesValid := by
  change ∀ j : Fin 16, (retention3558.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch547.valid21902
  · exact MergedCutProfiles.Batch422.valid16880
  · exact MergedCutProfiles.Batch423.valid16938
  · exact MergedCutProfiles.Batch422.valid16897
  · exact MergedCutProfiles.Batch547.valid21903
  · exact MergedCutProfiles.Batch422.valid16898
  · exact MergedCutProfiles.Batch547.valid21904
  · exact MergedCutProfiles.Batch547.valid21905
  · exact MergedCutProfiles.Batch547.valid21906
  · exact MergedCutProfiles.Batch546.valid21877
  · exact MergedCutProfiles.Batch547.valid21899
  · exact MergedCutProfiles.Batch547.valid21907
  · exact MergedCutProfiles.Batch547.valid21908
  · exact MergedCutProfiles.Batch547.valid21909
  · exact MergedCutProfiles.Batch547.valid21910
  · exact MergedCutProfiles.Batch547.valid21911
theorem numericValid3558 : retention3558.NumericValid := by decide +kernel
def certificate3558 : RatCutBinCertificate := ⟨⟨retention3558,(2266473188367216253/1000000000000000000),(216862197802423917/1000000000000000000),(17097254971987718171/1000000000000000000),(450540175640321153547/500000000000000000),(1054332502469117673/500000000000000000)⟩,(998018955343898949/1000000000000000000),(139657652843071003/500000000000000000),(364402254889172413/1000000000000000000),(118666697673165023/500000000000000000)⟩
theorem valid3558 : certificate3558.Valid := by decide +kernel
theorem sound3558 : certificate3558.Sound := rat_cut_bin_certificate_sound certificate3558 profilesValid3558 numericValid3558 valid3558

def retention3559 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(2756182965028930971/52537530222601784183),(150849554951461283/125000000000000000),(23/10),(82833969857116988021/40000000000000000000),true,MergedCutProfiles.Batch547.profile21912,![MergedCutProfiles.Batch547.profile21912,MergedCutProfiles.Batch547.profile21885,MergedCutProfiles.Batch547.profile21913,MergedCutProfiles.Batch547.profile21898,MergedCutProfiles.Batch547.profile21914,MergedCutProfiles.Batch547.profile21900,MergedCutProfiles.Batch547.profile21911,MergedCutProfiles.Batch422.profile16916,MergedCutProfiles.Batch547.profile21915,MergedCutProfiles.Batch547.profile21916,MergedCutProfiles.Batch547.profile21917,MergedCutProfiles.Batch547.profile21918,MergedCutProfiles.Batch547.profile21919,MergedCutProfiles.Batch423.profile16936,MergedCutProfiles.Batch548.profile21920,MergedCutProfiles.Batch548.profile21921]⟩
theorem profilesValid3559 : retention3559.ProfilesValid := by
  change ∀ j : Fin 16, (retention3559.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch547.valid21912
  · exact MergedCutProfiles.Batch547.valid21885
  · exact MergedCutProfiles.Batch547.valid21913
  · exact MergedCutProfiles.Batch547.valid21898
  · exact MergedCutProfiles.Batch547.valid21914
  · exact MergedCutProfiles.Batch547.valid21900
  · exact MergedCutProfiles.Batch547.valid21911
  · exact MergedCutProfiles.Batch422.valid16916
  · exact MergedCutProfiles.Batch547.valid21915
  · exact MergedCutProfiles.Batch547.valid21916
  · exact MergedCutProfiles.Batch547.valid21917
  · exact MergedCutProfiles.Batch547.valid21918
  · exact MergedCutProfiles.Batch547.valid21919
  · exact MergedCutProfiles.Batch423.valid16936
  · exact MergedCutProfiles.Batch548.valid21920
  · exact MergedCutProfiles.Batch548.valid21921
theorem numericValid3559 : retention3559.NumericValid := by decide +kernel
def certificate3559 : RatCutBinCertificate := ⟨⟨retention3559,(2266473188367216253/1000000000000000000),(216862197802423917/1000000000000000000),(17097254971987718171/1000000000000000000),(450540175640321153547/500000000000000000),(400944609981783699/200000000000000000)⟩,(998018955343898949/1000000000000000000),(8865126526861899/31250000000000000),(358868599654462247/1000000000000000000),(237484911289335599/1000000000000000000)⟩
theorem valid3559 : certificate3559.Valid := by decide +kernel
theorem sound3559 : certificate3559.Sound := rat_cut_bin_certificate_sound certificate3559 profilesValid3559 numericValid3559 valid3559

def retention3560 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(15880706884997957452/52537530222601784183),(2756182965028930971/1000000000000000000),(7/5),(387650886089540628780359115361022880131/275618296502893097100000000000000000000),false,MergedCutProfiles.Batch548.profile21922,(fun _ => MergedCutProfiles.Batch548.profile21922)⟩
theorem profilesValid3560 : retention3560.ProfilesValid := by
  exact MergedCutProfiles.Batch548.valid21922
theorem numericValid3560 : retention3560.NumericValid := by decide +kernel
def certificate3560 : RatCutBinCertificate := ⟨⟨retention3560,(2266473188367216253/1000000000000000000),(216862197802423917/1000000000000000000),(17097254971987718171/1000000000000000000),(450540175640321153547/500000000000000000),(1366227582345813947/1000000000000000000)⟩,(998018955343898949/1000000000000000000),(327217103476289629/1000000000000000000),(76806851855993219/250000000000000000),(2984446715875751/12500000000000000)⟩
theorem valid3560 : certificate3560.Valid := by decide +kernel
theorem sound3560 : certificate3560.Sound := rat_cut_bin_certificate_sound certificate3560 profilesValid3560 numericValid3560 valid3560

def retention3561 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(25349791853490261074/52537530222601784183),(3970176721249489363/250000000000000000),1,(4048967512831228029096067928717061987/3970176721249489363000000000000000000),false,MergedCutProfiles.Batch548.profile21923,(fun _ => MergedCutProfiles.Batch548.profile21923)⟩
theorem profilesValid3561 : retention3561.ProfilesValid := by
  exact MergedCutProfiles.Batch548.valid21923
theorem numericValid3561 : retention3561.NumericValid := by decide +kernel
def certificate3561 : RatCutBinCertificate := ⟨⟨retention3561,(2266473188367216253/1000000000000000000),(216862197802423917/1000000000000000000),(17097254971987718171/1000000000000000000),(450540175640321153547/500000000000000000),(991097200368155979/1000000000000000000)⟩,(998018955343898949/1000000000000000000),(18602764454129783/50000000000000000),(10403431894846901/40000000000000000),(121064042046158121/500000000000000000)⟩
theorem valid3561 : certificate3561.Valid := by decide +kernel
theorem sound3561 : certificate3561.Sound := rat_cut_bin_certificate_sound certificate3561 profilesValid3561 numericValid3561 valid3561

def retention3562 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(26117915896442869476/52537530222601784183),(12674895926745130537/500000000000000000),1,(101133357291466436107805912092970354679/101399167413961044296000000000000000000),false,MergedCutProfiles.Batch548.profile21924,(fun _ => MergedCutProfiles.Batch548.profile21924)⟩
theorem profilesValid3562 : retention3562.ProfilesValid := by
  exact MergedCutProfiles.Batch548.valid21924
theorem numericValid3562 : retention3562.NumericValid := by decide +kernel
def certificate3562 : RatCutBinCertificate := ⟨⟨retention3562,(2266473188367216253/1000000000000000000),(216862197802423917/1000000000000000000),(17097254971987718171/1000000000000000000),(450540175640321153547/500000000000000000),(193726055279175399/200000000000000000)⟩,(998018955343898949/1000000000000000000),(374343061140205941/1000000000000000000),(10313242658456551/40000000000000000),(240062488405531949/1000000000000000000)⟩
theorem valid3562 : certificate3562.Valid := by decide +kernel
theorem sound3562 : certificate3562.Sound := rat_cut_bin_certificate_sound certificate3562 profilesValid3562 numericValid3562 valid3562

def retention3563 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(1/2),(6529478974110717369/250000000000000000),1,(8636578528751411133722181899908719069/8705971965480956492000000000000000000),false,MergedCutProfiles.Batch424.profile16984,(fun _ => MergedCutProfiles.Batch424.profile16984)⟩
theorem profilesValid3563 : retention3563.ProfilesValid := by
  exact MergedCutProfiles.Batch424.valid16984
theorem numericValid3563 : retention3563.NumericValid := by decide +kernel
def certificate3563 : RatCutBinCertificate := ⟨⟨retention3563,(2266473188367216253/1000000000000000000),(216862197802423917/1000000000000000000),(17097254971987718171/1000000000000000000),(450540175640321153547/500000000000000000),(481640460931515037/500000000000000000)⟩,(998018955343898949/1000000000000000000),(376107346343613011/1000000000000000000),(256101806699460699/1000000000000000000),(237439716534212421/1000000000000000000)⟩
theorem valid3563 : certificate3563.Valid := by decide +kernel
theorem sound3563 : certificate3563.Sound := rat_cut_bin_certificate_sound certificate3563 profilesValid3563 numericValid3563 valid3563

def certificates : List RatCutBinCertificate := [certificate3552,certificate3553,certificate3554,certificate3555,certificate3556,certificate3557,certificate3558,certificate3559,certificate3560,certificate3561,certificate3562,certificate3563]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3552,List.forall_mem_cons.mpr ⟨sound3553,List.forall_mem_cons.mpr ⟨sound3554,List.forall_mem_cons.mpr ⟨sound3555,List.forall_mem_cons.mpr ⟨sound3556,List.forall_mem_cons.mpr ⟨sound3557,List.forall_mem_cons.mpr ⟨sound3558,List.forall_mem_cons.mpr ⟨sound3559,List.forall_mem_cons.mpr ⟨sound3560,List.forall_mem_cons.mpr ⟨sound3561,List.forall_mem_cons.mpr ⟨sound3562,List.forall_mem_cons.mpr ⟨sound3563,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch296
