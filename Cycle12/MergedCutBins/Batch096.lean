import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch191
import Cycle12.MergedCutProfiles.Batch192
import Cycle12.MergedCutProfiles.Batch193

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch096

def retention1152 : RatCutRetentionCertificate := ⟨(219/4000),(11/200),(7003659167894968331/15314307777793637652),(1834026943300852141/500000000000000000),(6/5),(395797399815828464558832639731118656231/366805388660170428200000000000000000000),false,MergedCutProfiles.Batch191.profile7666,(fun _ => MergedCutProfiles.Batch191.profile7666)⟩
theorem profilesValid1152 : retention1152.ProfilesValid := by
  exact MergedCutProfiles.Batch191.valid7666
theorem numericValid1152 : retention1152.NumericValid := by decide +kernel
def certificate1152 : RatCutBinCertificate := ⟨⟨retention1152,(646823677096584823/250000000000000000),(14887102204219317/100000000000000000),(14443280455941829001/1000000000000000000),(221515985080731664567/1000000000000000000),(523516374198515467/500000000000000000)⟩,(990022997339300147/1000000000000000000),(190744650417893969/500000000000000000),(31359702866489651/125000000000000000),(90341366624877613/500000000000000000)⟩
theorem valid1152 : certificate1152.Valid := by decide +kernel
theorem sound1152 : certificate1152.Sound := rat_cut_bin_certificate_sound certificate1152 profilesValid1152 numericValid1152 valid1152

def retention1153 : RatCutRetentionCertificate := ⟨(219/4000),(11/200),(1895989823472161537/3828576944448409413),(7003659167894968331/1000000000000000000),(21/20),(11156129182805888504823538347007586975319/11205854668631949329600000000000000000000),false,MergedCutProfiles.Batch191.profile7667,(fun _ => MergedCutProfiles.Batch191.profile7667)⟩
theorem profilesValid1153 : retention1153.ProfilesValid := by
  exact MergedCutProfiles.Batch191.valid7667
theorem numericValid1153 : retention1153.NumericValid := by decide +kernel
def certificate1153 : RatCutBinCertificate := ⟨⟨retention1153,(646823677096584823/250000000000000000),(14887102204219317/100000000000000000),(14443280455941829001/1000000000000000000),(221515985080731664567/1000000000000000000),(193511719866018687/200000000000000000)⟩,(990022997339300147/1000000000000000000),(82564878533395407/200000000000000000),(110967672882749887/500000000000000000),(224762795880681/1250000000000000)⟩
theorem valid1153 : certificate1153.Valid := by decide +kernel
theorem sound1153 : certificate1153.Sound := rat_cut_bin_certificate_sound certificate1153 profilesValid1153 numericValid1153 valid1153

def retention1154 : RatCutRetentionCertificate := ⟨(219/4000),(11/200),(1/2),(1895989823472161537/250000000000000000),(21/20),(749908304470532727281819492840596310111/758395929388864614800000000000000000000),false,MergedCutProfiles.Batch191.profile7665,(fun _ => MergedCutProfiles.Batch191.profile7665)⟩
theorem profilesValid1154 : retention1154.ProfilesValid := by
  exact MergedCutProfiles.Batch191.valid7665
theorem numericValid1154 : retention1154.NumericValid := by decide +kernel
def certificate1154 : RatCutBinCertificate := ⟨⟨retention1154,(646823677096584823/250000000000000000),(14887102204219317/100000000000000000),(14443280455941829001/1000000000000000000),(221515985080731664567/1000000000000000000),(96080470240690611/100000000000000000)⟩,(990022997339300147/1000000000000000000),(83145261495399139/200000000000000000),(54844544891917871/250000000000000000),(178151133505246283/1000000000000000000)⟩
theorem valid1154 : certificate1154.Valid := by decide +kernel
theorem sound1154 : certificate1154.Sound := rat_cut_bin_certificate_sound certificate1154 profilesValid1154 numericValid1154 valid1154

def retention1155 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(423923204357467156/7497559102219071473),(103892560620886961/125000000000000000),(57/20),(10137131744596597041/5000000000000000000),true,MergedCutProfiles.Batch191.profile7668,![MergedCutProfiles.Batch191.profile7668,MergedCutProfiles.Batch191.profile7669,MergedCutProfiles.Batch191.profile7670,MergedCutProfiles.Batch191.profile7671,MergedCutProfiles.Batch191.profile7672,MergedCutProfiles.Batch191.profile7673,MergedCutProfiles.Batch191.profile7674,MergedCutProfiles.Batch191.profile7675,MergedCutProfiles.Batch191.profile7676,MergedCutProfiles.Batch191.profile7677,MergedCutProfiles.Batch191.profile7678,MergedCutProfiles.Batch191.profile7679,MergedCutProfiles.Batch192.profile7680,MergedCutProfiles.Batch192.profile7681,MergedCutProfiles.Batch192.profile7682,MergedCutProfiles.Batch192.profile7683]⟩
theorem profilesValid1155 : retention1155.ProfilesValid := by
  change ∀ j : Fin 16, (retention1155.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch191.valid7668
  · exact MergedCutProfiles.Batch191.valid7669
  · exact MergedCutProfiles.Batch191.valid7670
  · exact MergedCutProfiles.Batch191.valid7671
  · exact MergedCutProfiles.Batch191.valid7672
  · exact MergedCutProfiles.Batch191.valid7673
  · exact MergedCutProfiles.Batch191.valid7674
  · exact MergedCutProfiles.Batch191.valid7675
  · exact MergedCutProfiles.Batch191.valid7676
  · exact MergedCutProfiles.Batch191.valid7677
  · exact MergedCutProfiles.Batch191.valid7678
  · exact MergedCutProfiles.Batch191.valid7679
  · exact MergedCutProfiles.Batch192.valid7680
  · exact MergedCutProfiles.Batch192.valid7681
  · exact MergedCutProfiles.Batch192.valid7682
  · exact MergedCutProfiles.Batch192.valid7683
theorem numericValid1155 : retention1155.NumericValid := by decide +kernel
def certificate1155 : RatCutBinCertificate := ⟨⟨retention1155,(2227889042599441323/1000000000000000000),(30403935940526677/200000000000000000),(7253142565918527661/500000000000000000),(21816897607164609127/100000000000000000),(490216723545015721/250000000000000000)⟩,(495647391364660151/500000000000000000),(93794809743706599/250000000000000000),(128505227776377237/500000000000000000),(135599339207656861/1000000000000000000)⟩
theorem valid1155 : certificate1155.Valid := by decide +kernel
theorem sound1155 : certificate1155.Sound := rat_cut_bin_certificate_sound certificate1155 profilesValid1155 numericValid1155 valid1155

def retention1156 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(482464150298981530/7497559102219071473),(105980801089366789/125000000000000000),(57/20),(322016252347363092111/160000000000000000000),true,MergedCutProfiles.Batch192.profile7684,![MergedCutProfiles.Batch192.profile7684,MergedCutProfiles.Batch192.profile7685,MergedCutProfiles.Batch192.profile7686,MergedCutProfiles.Batch192.profile7687,MergedCutProfiles.Batch192.profile7688,MergedCutProfiles.Batch192.profile7689,MergedCutProfiles.Batch192.profile7690,MergedCutProfiles.Batch192.profile7691,MergedCutProfiles.Batch192.profile7692,MergedCutProfiles.Batch192.profile7693,MergedCutProfiles.Batch192.profile7694,MergedCutProfiles.Batch192.profile7695,MergedCutProfiles.Batch192.profile7696,MergedCutProfiles.Batch192.profile7697,MergedCutProfiles.Batch192.profile7698,MergedCutProfiles.Batch192.profile7699]⟩
theorem profilesValid1156 : retention1156.ProfilesValid := by
  change ∀ j : Fin 16, (retention1156.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch192.valid7684
  · exact MergedCutProfiles.Batch192.valid7685
  · exact MergedCutProfiles.Batch192.valid7686
  · exact MergedCutProfiles.Batch192.valid7687
  · exact MergedCutProfiles.Batch192.valid7688
  · exact MergedCutProfiles.Batch192.valid7689
  · exact MergedCutProfiles.Batch192.valid7690
  · exact MergedCutProfiles.Batch192.valid7691
  · exact MergedCutProfiles.Batch192.valid7692
  · exact MergedCutProfiles.Batch192.valid7693
  · exact MergedCutProfiles.Batch192.valid7694
  · exact MergedCutProfiles.Batch192.valid7695
  · exact MergedCutProfiles.Batch192.valid7696
  · exact MergedCutProfiles.Batch192.valid7697
  · exact MergedCutProfiles.Batch192.valid7698
  · exact MergedCutProfiles.Batch192.valid7699
theorem numericValid1156 : retention1156.NumericValid := by decide +kernel
def certificate1156 : RatCutBinCertificate := ⟨⟨retention1156,(2227889042599441323/1000000000000000000),(30403935940526677/200000000000000000),(7253142565918527661/500000000000000000),(21816897607164609127/100000000000000000),(1946042508107975139/1000000000000000000)⟩,(495647391364660151/500000000000000000),(374946401053968589/1000000000000000000),(64309692888078197/250000000000000000),(33881015659290179/250000000000000000)⟩
theorem valid1156 : certificate1156.Valid := by decide +kernel
theorem sound1156 : certificate1156.Sound := rat_cut_bin_certificate_sound certificate1156 profilesValid1156 numericValid1156 valid1156

def retention1157 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(1718441386185057953/14995118204438142946),(48246415029898153/50000000000000000),(5/2),(950542280617439017/512000000000000000),true,MergedCutProfiles.Batch192.profile7700,![MergedCutProfiles.Batch192.profile7700,MergedCutProfiles.Batch192.profile7701,MergedCutProfiles.Batch192.profile7702,MergedCutProfiles.Batch192.profile7703,MergedCutProfiles.Batch192.profile7704,MergedCutProfiles.Batch192.profile7705,MergedCutProfiles.Batch192.profile7706,MergedCutProfiles.Batch192.profile7707,MergedCutProfiles.Batch192.profile7699,MergedCutProfiles.Batch192.profile7708,MergedCutProfiles.Batch192.profile7709,MergedCutProfiles.Batch192.profile7710,MergedCutProfiles.Batch192.profile7711,MergedCutProfiles.Batch192.profile7712,MergedCutProfiles.Batch192.profile7713,MergedCutProfiles.Batch192.profile7714]⟩
theorem profilesValid1157 : retention1157.ProfilesValid := by
  change ∀ j : Fin 16, (retention1157.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch192.valid7700
  · exact MergedCutProfiles.Batch192.valid7701
  · exact MergedCutProfiles.Batch192.valid7702
  · exact MergedCutProfiles.Batch192.valid7703
  · exact MergedCutProfiles.Batch192.valid7704
  · exact MergedCutProfiles.Batch192.valid7705
  · exact MergedCutProfiles.Batch192.valid7706
  · exact MergedCutProfiles.Batch192.valid7707
  · exact MergedCutProfiles.Batch192.valid7699
  · exact MergedCutProfiles.Batch192.valid7708
  · exact MergedCutProfiles.Batch192.valid7709
  · exact MergedCutProfiles.Batch192.valid7710
  · exact MergedCutProfiles.Batch192.valid7711
  · exact MergedCutProfiles.Batch192.valid7712
  · exact MergedCutProfiles.Batch192.valid7713
  · exact MergedCutProfiles.Batch192.valid7714
theorem numericValid1157 : retention1157.NumericValid := by decide +kernel
def certificate1157 : RatCutBinCertificate := ⟨⟨retention1157,(2227889042599441323/1000000000000000000),(30403935940526677/200000000000000000),(7253142565918527661/500000000000000000),(21816897607164609127/100000000000000000),(1798142715331201353/1000000000000000000)⟩,(495647391364660151/500000000000000000),(192796566080611501/500000000000000000),(123472567836304127/500000000000000000),(135401050292178677/1000000000000000000)⟩
theorem valid1157 : certificate1157.Valid := by decide +kernel
theorem sound1157 : certificate1157.Sound := rat_cut_bin_certificate_sound certificate1157 profilesValid1157 numericValid1157 valid1157

def retention1158 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(2255682575482136903/7497559102219071473),(1718441386185057953/1000000000000000000),(8/5),(1790103810122118273109/1280000000000000000000),true,MergedCutProfiles.Batch192.profile7715,![MergedCutProfiles.Batch192.profile7715,MergedCutProfiles.Batch192.profile7716,MergedCutProfiles.Batch192.profile7683,MergedCutProfiles.Batch192.profile7717,MergedCutProfiles.Batch192.profile7718,MergedCutProfiles.Batch192.profile7719,MergedCutProfiles.Batch193.profile7720,MergedCutProfiles.Batch193.profile7721,MergedCutProfiles.Batch193.profile7722,MergedCutProfiles.Batch193.profile7723,MergedCutProfiles.Batch193.profile7724,MergedCutProfiles.Batch193.profile7725,MergedCutProfiles.Batch193.profile7726,MergedCutProfiles.Batch193.profile7727,MergedCutProfiles.Batch193.profile7728,MergedCutProfiles.Batch193.profile7729]⟩
theorem profilesValid1158 : retention1158.ProfilesValid := by
  change ∀ j : Fin 16, (retention1158.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch192.valid7715
  · exact MergedCutProfiles.Batch192.valid7716
  · exact MergedCutProfiles.Batch192.valid7683
  · exact MergedCutProfiles.Batch192.valid7717
  · exact MergedCutProfiles.Batch192.valid7718
  · exact MergedCutProfiles.Batch192.valid7719
  · exact MergedCutProfiles.Batch193.valid7720
  · exact MergedCutProfiles.Batch193.valid7721
  · exact MergedCutProfiles.Batch193.valid7722
  · exact MergedCutProfiles.Batch193.valid7723
  · exact MergedCutProfiles.Batch193.valid7724
  · exact MergedCutProfiles.Batch193.valid7725
  · exact MergedCutProfiles.Batch193.valid7726
  · exact MergedCutProfiles.Batch193.valid7727
  · exact MergedCutProfiles.Batch193.valid7728
  · exact MergedCutProfiles.Batch193.valid7729
theorem numericValid1158 : retention1158.NumericValid := by decide +kernel
def certificate1158 : RatCutBinCertificate := ⟨⟨retention1158,(2227889042599441323/1000000000000000000),(30403935940526677/200000000000000000),(7253142565918527661/500000000000000000),(21816897607164609127/100000000000000000),(272230682390315193/200000000000000000)⟩,(495647391364660151/500000000000000000),(424681138394830799/1000000000000000000),(21161423412193169/100000000000000000),(34021875722788397/250000000000000000)⟩
theorem valid1158 : certificate1158.Valid := by decide +kernel
theorem sound1158 : certificate1158.Sound := rat_cut_bin_certificate_sound certificate1158 profilesValid1158 numericValid1158 valid1158

def retention1159 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(6851815802285570001/14995118204438142946),(2255682575482136903/500000000000000000),1,(132762416877806770583/128000000000000000000),true,MergedCutProfiles.Batch192.profile7703,![MergedCutProfiles.Batch192.profile7703,MergedCutProfiles.Batch193.profile7730,MergedCutProfiles.Batch193.profile7731,MergedCutProfiles.Batch193.profile7732,MergedCutProfiles.Batch193.profile7733,MergedCutProfiles.Batch193.profile7734,MergedCutProfiles.Batch193.profile7735,MergedCutProfiles.Batch193.profile7736,MergedCutProfiles.Batch193.profile7737,MergedCutProfiles.Batch193.profile7738,MergedCutProfiles.Batch193.profile7739,MergedCutProfiles.Batch193.profile7740,MergedCutProfiles.Batch193.profile7741,MergedCutProfiles.Batch193.profile7742,MergedCutProfiles.Batch193.profile7743,MergedCutProfiles.Batch193.profile7744]⟩
theorem profilesValid1159 : retention1159.ProfilesValid := by
  change ∀ j : Fin 16, (retention1159.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch192.valid7703
  · exact MergedCutProfiles.Batch193.valid7730
  · exact MergedCutProfiles.Batch193.valid7731
  · exact MergedCutProfiles.Batch193.valid7732
  · exact MergedCutProfiles.Batch193.valid7733
  · exact MergedCutProfiles.Batch193.valid7734
  · exact MergedCutProfiles.Batch193.valid7735
  · exact MergedCutProfiles.Batch193.valid7736
  · exact MergedCutProfiles.Batch193.valid7737
  · exact MergedCutProfiles.Batch193.valid7738
  · exact MergedCutProfiles.Batch193.valid7739
  · exact MergedCutProfiles.Batch193.valid7740
  · exact MergedCutProfiles.Batch193.valid7741
  · exact MergedCutProfiles.Batch193.valid7742
  · exact MergedCutProfiles.Batch193.valid7743
  · exact MergedCutProfiles.Batch193.valid7744
theorem numericValid1159 : retention1159.NumericValid := by decide +kernel
def certificate1159 : RatCutBinCertificate := ⟨⟨retention1159,(2227889042599441323/1000000000000000000),(30403935940526677/200000000000000000),(7253142565918527661/500000000000000000),(21816897607164609127/100000000000000000),(1013855449038565149/1000000000000000000)⟩,(495647391364660151/500000000000000000),(19200047189024383/40000000000000000),(16769382802135287/100000000000000000),(68739487116927321/500000000000000000)⟩
theorem valid1159 : certificate1159.Valid := by decide +kernel
theorem sound1159 : certificate1159.Sound := rat_cut_bin_certificate_sound certificate1159 profilesValid1159 numericValid1159 valid1159

def retention1160 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(7419534687233372961/14995118204438142946),(6851815802285570001/1000000000000000000),(21/20),(10915309878959502810955981306716554222159/10962905283656912001600000000000000000000),false,MergedCutProfiles.Batch193.profile7745,(fun _ => MergedCutProfiles.Batch193.profile7745)⟩
theorem profilesValid1160 : retention1160.ProfilesValid := by
  exact MergedCutProfiles.Batch193.valid7745
theorem numericValid1160 : retention1160.NumericValid := by decide +kernel
def certificate1160 : RatCutBinCertificate := ⟨⟨retention1160,(2227889042599441323/1000000000000000000),(30403935940526677/200000000000000000),(7253142565918527661/500000000000000000),(21816897607164609127/100000000000000000),(30348169907715509/31250000000000000)⟩,(495647391364660151/500000000000000000),(481331960387593971/1000000000000000000),(166718926937324459/1000000000000000000),(27070895568089601/200000000000000000)⟩
theorem valid1160 : certificate1160.Valid := by decide +kernel
theorem sound1160 : certificate1160.Sound := rat_cut_bin_certificate_sound certificate1160 profilesValid1160 numericValid1160 valid1160

def retention1161 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(7493730034105706691/14995118204438142946),(7419534687233372961/1000000000000000000),(21/20),(434694325277529547557956949707093355597/439676129613829508800000000000000000000),false,MergedCutProfiles.Batch193.profile7746,(fun _ => MergedCutProfiles.Batch193.profile7746)⟩
theorem profilesValid1161 : retention1161.ProfilesValid := by
  exact MergedCutProfiles.Batch193.valid7746
theorem numericValid1161 : retention1161.NumericValid := by decide +kernel
def certificate1161 : RatCutBinCertificate := ⟨⟨retention1161,(2227889042599441323/1000000000000000000),(30403935940526677/200000000000000000),(7253142565918527661/500000000000000000),(21816897607164609127/100000000000000000),(482076245793076963/500000000000000000)⟩,(495647391364660151/500000000000000000),(120470583490813227/250000000000000000),(41579202798958077/250000000000000000),(13534437052052687/100000000000000000)⟩
theorem valid1161 : certificate1161.Valid := by decide +kernel
theorem sound1161 : certificate1161.Sound := rat_cut_bin_certificate_sound certificate1161 profilesValid1161 numericValid1161 valid1161

def retention1162 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(1/2),(7493730034105706691/1000000000000000000),(21/20),(3950566126950191075374110567474021182133/3996656018189710235200000000000000000000),false,MergedCutProfiles.Batch193.profile7747,(fun _ => MergedCutProfiles.Batch193.profile7747)⟩
theorem profilesValid1162 : retention1162.ProfilesValid := by
  exact MergedCutProfiles.Batch193.valid7747
theorem numericValid1162 : retention1162.NumericValid := by decide +kernel
def certificate1162 : RatCutBinCertificate := ⟨⟨retention1162,(2227889042599441323/1000000000000000000),(30403935940526677/200000000000000000),(7253142565918527661/500000000000000000),(21816897607164609127/100000000000000000),(481975511197172299/500000000000000000)⟩,(495647391364660151/500000000000000000),(481631814263366801/1000000000000000000),(83249884367696543/500000000000000000),(27122040787664511/200000000000000000)⟩
theorem valid1162 : certificate1162.Valid := by decide +kernel
theorem sound1162 : certificate1162.Sound := rat_cut_bin_certificate_sound certificate1162 profilesValid1162 numericValid1162 valid1162

def retention1163 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(1/2),64,1,(255400971721539503099627322418447646271/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch193.profile7747,(fun _ => MergedCutProfiles.Batch193.profile7747)⟩
theorem profilesValid1163 : retention1163.ProfilesValid := by
  exact MergedCutProfiles.Batch193.valid7747
theorem numericValid1163 : retention1163.NumericValid := by decide +kernel
def certificate1163 : RatCutBinCertificate := ⟨⟨retention1163,(2227889042599441323/1000000000000000000),(30403935940526677/200000000000000000),(7253142565918527661/500000000000000000),(21816897607164609127/100000000000000000),(194862492972011719/200000000000000000)⟩,(495647391364660151/500000000000000000),(17833149682938159/40000000000000000),(97010695688720971/500000000000000000),(23070840990120517/125000000000000000)⟩
theorem valid1163 : certificate1163.Valid := by decide +kernel
theorem sound1163 : certificate1163.Sound := rat_cut_bin_certificate_sound certificate1163 profilesValid1163 numericValid1163 valid1163

def certificates : List RatCutBinCertificate := [certificate1152,certificate1153,certificate1154,certificate1155,certificate1156,certificate1157,certificate1158,certificate1159,certificate1160,certificate1161,certificate1162,certificate1163]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1152,List.forall_mem_cons.mpr ⟨sound1153,List.forall_mem_cons.mpr ⟨sound1154,List.forall_mem_cons.mpr ⟨sound1155,List.forall_mem_cons.mpr ⟨sound1156,List.forall_mem_cons.mpr ⟨sound1157,List.forall_mem_cons.mpr ⟨sound1158,List.forall_mem_cons.mpr ⟨sound1159,List.forall_mem_cons.mpr ⟨sound1160,List.forall_mem_cons.mpr ⟨sound1161,List.forall_mem_cons.mpr ⟨sound1162,List.forall_mem_cons.mpr ⟨sound1163,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch096
