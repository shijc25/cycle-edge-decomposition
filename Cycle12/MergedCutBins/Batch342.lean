import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch616
import Cycle12.MergedCutProfiles.Batch617
import Cycle12.MergedCutProfiles.Batch618

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch342

def retention4104 : RatCutRetentionCertificate := ⟨(27/500),(109/2000),(1991233887262691662/312854493878473221417),(1111204577/1000000000),(27/10),(9273024775091062499/4000000000000000000),true,MergedCutProfiles.Batch616.profile24669,![MergedCutProfiles.Batch616.profile24669,MergedCutProfiles.Batch616.profile24670,MergedCutProfiles.Batch616.profile24671,MergedCutProfiles.Batch616.profile24672,MergedCutProfiles.Batch616.profile24662,MergedCutProfiles.Batch616.profile24673,MergedCutProfiles.Batch616.profile24674,MergedCutProfiles.Batch616.profile24675,MergedCutProfiles.Batch616.profile24668,MergedCutProfiles.Batch616.profile24676,MergedCutProfiles.Batch616.profile24677,MergedCutProfiles.Batch616.profile24678,MergedCutProfiles.Batch616.profile24679,MergedCutProfiles.Batch617.profile24680,MergedCutProfiles.Batch617.profile24681,MergedCutProfiles.Batch617.profile24682]⟩
theorem profilesValid4104 : retention4104.ProfilesValid := by
  change ∀ j : Fin 16, (retention4104.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch616.valid24669
  · exact MergedCutProfiles.Batch616.valid24670
  · exact MergedCutProfiles.Batch616.valid24671
  · exact MergedCutProfiles.Batch616.valid24672
  · exact MergedCutProfiles.Batch616.valid24662
  · exact MergedCutProfiles.Batch616.valid24673
  · exact MergedCutProfiles.Batch616.valid24674
  · exact MergedCutProfiles.Batch616.valid24675
  · exact MergedCutProfiles.Batch616.valid24668
  · exact MergedCutProfiles.Batch616.valid24676
  · exact MergedCutProfiles.Batch616.valid24677
  · exact MergedCutProfiles.Batch616.valid24678
  · exact MergedCutProfiles.Batch616.valid24679
  · exact MergedCutProfiles.Batch617.valid24680
  · exact MergedCutProfiles.Batch617.valid24681
  · exact MergedCutProfiles.Batch617.valid24682
theorem numericValid4104 : retention4104.NumericValid := by decide +kernel
def certificate4104 : RatCutBinCertificate := ⟨⟨retention4104,(1993058303095839087/1000000000000000000),(36441619022305257/250000000000000000),(14260494253622171183/1000000000000000000),(1118653101311841638807/250000000000000000),(2263250004377286999/1000000000000000000)⟩,(999618124099214697/1000000000000000000),(432764226955903191/1000000000000000000),(25596040567756059/125000000000000000),(67050760846724929/500000000000000000)⟩
theorem valid4104 : certificate4104.Valid := by decide +kernel
theorem sound4104 : certificate4104.Sound := rat_cut_bin_certificate_sound certificate4104 profilesValid4104 numericValid4104 valid4104

def retention4105 : RatCutRetentionCertificate := ⟨(27/500),(109/2000),(54177426350435397446/312854493878473221417),(995616943631345831/500000000000000000),(37/20),(1368175072834035525469813046514821106871/796493554905076664800000000000000000000),false,MergedCutProfiles.Batch617.profile24683,(fun _ => MergedCutProfiles.Batch617.profile24683)⟩
theorem profilesValid4105 : retention4105.ProfilesValid := by
  exact MergedCutProfiles.Batch617.valid24683
theorem numericValid4105 : retention4105.NumericValid := by decide +kernel
def certificate4105 : RatCutBinCertificate := ⟨⟨retention4105,(1993058303095839087/1000000000000000000),(36441619022305257/250000000000000000),(14260494253622171183/1000000000000000000),(1118653101311841638807/250000000000000000),(1680058476458051393/1000000000000000000)⟩,(999618124099214697/1000000000000000000),(91416369274023971/200000000000000000),(185071841870755771/1000000000000000000),(134772838607492151/1000000000000000000)⟩
theorem valid4105 : certificate4105.Valid := by decide +kernel
theorem sound4105 : certificate4105.Sound := rat_cut_bin_certificate_sound certificate4105 profilesValid4105 numericValid4105 valid4105

def retention4106 : RatCutRetentionCertificate := ⟨(27/500),(109/2000),(64000000000000000000/312854493878473221417),(27088713175217698723/500000000000000000),1,(88123018086699515164808444199478604691/54177426350435397446000000000000000000),false,MergedCutProfiles.Batch617.profile24684,(fun _ => MergedCutProfiles.Batch617.profile24684)⟩
theorem profilesValid4106 : retention4106.ProfilesValid := by
  exact MergedCutProfiles.Batch617.valid24684
theorem numericValid4106 : retention4106.NumericValid := by decide +kernel
def certificate4106 : RatCutBinCertificate := ⟨⟨retention4106,(1993058303095839087/1000000000000000000),(36441619022305257/250000000000000000),(14260494253622171183/1000000000000000000),(1118653101311841638807/250000000000000000),(1606190932902181437/1000000000000000000)⟩,(999618124099214697/1000000000000000000),(317922919075387993/1000000000000000000),(9929384528145897/31250000000000000),(99093073520043521/200000000000000000)⟩
theorem valid4106 : certificate4106.Valid := by decide +kernel
theorem sound4106 : certificate4106.Sound := rat_cut_bin_certificate_sound certificate4106 profilesValid4106 numericValid4106 valid4106

def retention4107 : RatCutRetentionCertificate := ⟨(27/500),(109/2000),(1/2),64,1,(255399627808886112418606522747640527911/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch617.profile24685,(fun _ => MergedCutProfiles.Batch617.profile24685)⟩
theorem profilesValid4107 : retention4107.ProfilesValid := by
  exact MergedCutProfiles.Batch617.valid24685
theorem numericValid4107 : retention4107.NumericValid := by decide +kernel
def certificate4107 : RatCutBinCertificate := ⟨⟨retention4107,(1993058303095839087/1000000000000000000),(36441619022305257/250000000000000000),(14260494253622171183/1000000000000000000),(1118653101311841638807/250000000000000000),(195456468844188041/200000000000000000)⟩,(999618124099214697/1000000000000000000),(520973542012264601/1000000000000000000),(8503570505659/61035156250000),(33514454752116569/250000000000000000)⟩
theorem valid4107 : certificate4107.Valid := by decide +kernel
theorem sound4107 : certificate4107.Sound := rat_cut_bin_certificate_sound certificate4107 profilesValid4107 numericValid4107 valid4107

def retention4108 : RatCutRetentionCertificate := ⟨(27/500),(109/2000),(64000000000000000000/312854493878473221417),(1264571813073683317/50000000000000000),1,(40780073197161895775259525319735137759/25291436261473666340000000000000000000),false,MergedCutProfiles.Batch617.profile24684,(fun _ => MergedCutProfiles.Batch617.profile24684)⟩
theorem profilesValid4108 : retention4108.ProfilesValid := by
  exact MergedCutProfiles.Batch617.valid24684
theorem numericValid4108 : retention4108.NumericValid := by decide +kernel
def certificate4108 : RatCutBinCertificate := ⟨⟨retention4108,(1883257051095839087/1000000000000000000),(36441619022305257/250000000000000000),(14260494253622171183/1000000000000000000),(1118653101311841638807/250000000000000000),(1593156269373529083/1000000000000000000)⟩,(499819581804724003/500000000000000000),(16824476003969769/500000000000000000),(833716031994494627/1000000000000000000),(312266717200071179/250000000000000000)⟩
theorem valid4108 : certificate4108.Valid := by decide +kernel
theorem sound4108 : certificate4108.Sound := rat_cut_bin_certificate_sound certificate4108 profilesValid4108 numericValid4108 valid4108

def retention4109 : RatCutRetentionCertificate := ⟨(27/500),(109/2000),(1/2),64,1,(255399627808886112418606522747640527911/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch617.profile24685,(fun _ => MergedCutProfiles.Batch617.profile24685)⟩
theorem profilesValid4109 : retention4109.ProfilesValid := by
  exact MergedCutProfiles.Batch617.valid24685
theorem numericValid4109 : retention4109.NumericValid := by decide +kernel
def certificate4109 : RatCutBinCertificate := ⟨⟨retention4109,(1883257051095839087/1000000000000000000),(36441619022305257/250000000000000000),(14260494253622171183/1000000000000000000),(1118653101311841638807/250000000000000000),(122300587513877723/125000000000000000)⟩,(499819581804724003/500000000000000000),(13697818204270393/250000000000000000),(387818829816846003/500000000000000000),(747188015484175511/1000000000000000000)⟩
theorem valid4109 : certificate4109.Valid := by decide +kernel
theorem sound4109 : certificate4109.Sound := rat_cut_bin_certificate_sound certificate4109 profilesValid4109 numericValid4109 valid4109

def retention4110 : RatCutRetentionCertificate := ⟨(109/2000),(11/200),(691427747929872700/306286155555872753049),(171145482160859579/250000000000000000),4,(4749060376438962859/2000000000000000000),true,MergedCutProfiles.Batch617.profile24686,![MergedCutProfiles.Batch617.profile24686,MergedCutProfiles.Batch617.profile24687,MergedCutProfiles.Batch617.profile24688,MergedCutProfiles.Batch617.profile24689,MergedCutProfiles.Batch617.profile24690,MergedCutProfiles.Batch617.profile24691,MergedCutProfiles.Batch617.profile24692,MergedCutProfiles.Batch617.profile24693,MergedCutProfiles.Batch617.profile24694,MergedCutProfiles.Batch617.profile24695,MergedCutProfiles.Batch617.profile24696,MergedCutProfiles.Batch617.profile24697,MergedCutProfiles.Batch617.profile24698,MergedCutProfiles.Batch617.profile24699,MergedCutProfiles.Batch617.profile24700,MergedCutProfiles.Batch617.profile24701]⟩
theorem profilesValid4110 : retention4110.ProfilesValid := by
  change ∀ j : Fin 16, (retention4110.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch617.valid24686
  · exact MergedCutProfiles.Batch617.valid24687
  · exact MergedCutProfiles.Batch617.valid24688
  · exact MergedCutProfiles.Batch617.valid24689
  · exact MergedCutProfiles.Batch617.valid24690
  · exact MergedCutProfiles.Batch617.valid24691
  · exact MergedCutProfiles.Batch617.valid24692
  · exact MergedCutProfiles.Batch617.valid24693
  · exact MergedCutProfiles.Batch617.valid24694
  · exact MergedCutProfiles.Batch617.valid24695
  · exact MergedCutProfiles.Batch617.valid24696
  · exact MergedCutProfiles.Batch617.valid24697
  · exact MergedCutProfiles.Batch617.valid24698
  · exact MergedCutProfiles.Batch617.valid24699
  · exact MergedCutProfiles.Batch617.valid24700
  · exact MergedCutProfiles.Batch617.valid24701
theorem numericValid4110 : retention4110.NumericValid := by decide +kernel
def certificate4110 : RatCutBinCertificate := ⟨⟨retention4110,(399696909933863393/200000000000000000),(14887102204219317/100000000000000000),(14384765127274286941/1000000000000000000),(2209443003729267056791/500000000000000000),(2291798188033195237/1000000000000000000)⟩,(999613638988966513/1000000000000000000),(276946337755605431/500000000000000000),(118876200426335213/1000000000000000000),(28149406256118161/500000000000000000)⟩
theorem valid4110 : certificate4110.Valid := by decide +kernel
theorem sound4110 : certificate4110.Sound := rat_cut_bin_certificate_sound certificate4110 profilesValid4110 numericValid4110 valid4110

def retention4111 : RatCutRetentionCertificate := ⟨(109/2000),(11/200),(1093773151000000000/306286155555872753049),(6914277479298727/10000000000000000),4,(30270129465047334567/12800000000000000000),true,MergedCutProfiles.Batch617.profile24702,![MergedCutProfiles.Batch617.profile24702,MergedCutProfiles.Batch617.profile24703,MergedCutProfiles.Batch617.profile24704,MergedCutProfiles.Batch617.profile24705,MergedCutProfiles.Batch617.profile24693,MergedCutProfiles.Batch617.profile24706,MergedCutProfiles.Batch617.profile24696,MergedCutProfiles.Batch617.profile24707,MergedCutProfiles.Batch617.profile24699,MergedCutProfiles.Batch617.profile24708,MergedCutProfiles.Batch617.profile24709,MergedCutProfiles.Batch617.profile24710,MergedCutProfiles.Batch617.profile24711,MergedCutProfiles.Batch617.profile24712,MergedCutProfiles.Batch617.profile24713,MergedCutProfiles.Batch617.profile24714]⟩
theorem profilesValid4111 : retention4111.ProfilesValid := by
  change ∀ j : Fin 16, (retention4111.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch617.valid24702
  · exact MergedCutProfiles.Batch617.valid24703
  · exact MergedCutProfiles.Batch617.valid24704
  · exact MergedCutProfiles.Batch617.valid24705
  · exact MergedCutProfiles.Batch617.valid24693
  · exact MergedCutProfiles.Batch617.valid24706
  · exact MergedCutProfiles.Batch617.valid24696
  · exact MergedCutProfiles.Batch617.valid24707
  · exact MergedCutProfiles.Batch617.valid24699
  · exact MergedCutProfiles.Batch617.valid24708
  · exact MergedCutProfiles.Batch617.valid24709
  · exact MergedCutProfiles.Batch617.valid24710
  · exact MergedCutProfiles.Batch617.valid24711
  · exact MergedCutProfiles.Batch617.valid24712
  · exact MergedCutProfiles.Batch617.valid24713
  · exact MergedCutProfiles.Batch617.valid24714
theorem numericValid4111 : retention4111.NumericValid := by decide +kernel
def certificate4111 : RatCutBinCertificate := ⟨⟨retention4111,(399696909933863393/200000000000000000),(14887102204219317/100000000000000000),(14384765127274286941/1000000000000000000),(2209443003729267056791/500000000000000000),(570530468587043723/250000000000000000)⟩,(999613638988966513/1000000000000000000),(552897338848837001/1000000000000000000),(11946512430627373/100000000000000000),(28238240025602733/500000000000000000)⟩
theorem valid4111 : certificate4111.Valid := by decide +kernel
theorem sound4111 : certificate4111.Sound := rat_cut_bin_certificate_sound certificate4111 profilesValid4111 numericValid4111 valid4111

def retention4112 : RatCutRetentionCertificate := ⟨(109/2000),(11/200),(418704835653267924/102095385185290917683),(1093773151/1000000000),(11/4),(37496743376156873417/16000000000000000000),true,MergedCutProfiles.Batch617.profile24715,![MergedCutProfiles.Batch617.profile24715,MergedCutProfiles.Batch617.profile24716,MergedCutProfiles.Batch617.profile24717,MergedCutProfiles.Batch617.profile24718,MergedCutProfiles.Batch617.profile24719,MergedCutProfiles.Batch617.profile24696,MergedCutProfiles.Batch617.profile24707,MergedCutProfiles.Batch618.profile24720,MergedCutProfiles.Batch618.profile24721,MergedCutProfiles.Batch618.profile24722,MergedCutProfiles.Batch618.profile24723,MergedCutProfiles.Batch618.profile24724,MergedCutProfiles.Batch617.profile24713,MergedCutProfiles.Batch617.profile24714,MergedCutProfiles.Batch618.profile24725,MergedCutProfiles.Batch618.profile24726]⟩
theorem profilesValid4112 : retention4112.ProfilesValid := by
  change ∀ j : Fin 16, (retention4112.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch617.valid24715
  · exact MergedCutProfiles.Batch617.valid24716
  · exact MergedCutProfiles.Batch617.valid24717
  · exact MergedCutProfiles.Batch617.valid24718
  · exact MergedCutProfiles.Batch617.valid24719
  · exact MergedCutProfiles.Batch617.valid24696
  · exact MergedCutProfiles.Batch617.valid24707
  · exact MergedCutProfiles.Batch618.valid24720
  · exact MergedCutProfiles.Batch618.valid24721
  · exact MergedCutProfiles.Batch618.valid24722
  · exact MergedCutProfiles.Batch618.valid24723
  · exact MergedCutProfiles.Batch618.valid24724
  · exact MergedCutProfiles.Batch617.valid24713
  · exact MergedCutProfiles.Batch617.valid24714
  · exact MergedCutProfiles.Batch618.valid24725
  · exact MergedCutProfiles.Batch618.valid24726
theorem numericValid4112 : retention4112.NumericValid := by decide +kernel
def certificate4112 : RatCutBinCertificate := ⟨⟨retention4112,(399696909933863393/200000000000000000),(14887102204219317/100000000000000000),(14384765127274286941/1000000000000000000),(2209443003729267056791/500000000000000000),(1143334136795355271/500000000000000000)⟩,(999613638988966513/1000000000000000000),(429038069672529237/1000000000000000000),(51976309916208419/250000000000000000),(13537428320122497/100000000000000000)⟩
theorem valid4112 : certificate4112.Valid := by decide +kernel
theorem sound4112 : certificate4112.Sound := rat_cut_bin_certificate_sound certificate4112 profilesValid4112 numericValid4112 valid4112

def retention4113 : RatCutRetentionCertificate := ⟨(109/2000),(11/200),(10151207978001935527/306286155555872753049),(314028626739950943/250000000000000000),(5/2),(27730723673925670767/12800000000000000000),true,MergedCutProfiles.Batch618.profile24727,![MergedCutProfiles.Batch618.profile24727,MergedCutProfiles.Batch618.profile24726,MergedCutProfiles.Batch618.profile24728,MergedCutProfiles.Batch618.profile24729,MergedCutProfiles.Batch618.profile24730,MergedCutProfiles.Batch618.profile24731,MergedCutProfiles.Batch618.profile24732,MergedCutProfiles.Batch618.profile24733,MergedCutProfiles.Batch618.profile24734,MergedCutProfiles.Batch618.profile24735,MergedCutProfiles.Batch618.profile24736,MergedCutProfiles.Batch618.profile24737,MergedCutProfiles.Batch618.profile24738,MergedCutProfiles.Batch618.profile24739,MergedCutProfiles.Batch618.profile24740,MergedCutProfiles.Batch618.profile24741]⟩
theorem profilesValid4113 : retention4113.ProfilesValid := by
  change ∀ j : Fin 16, (retention4113.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch618.valid24727
  · exact MergedCutProfiles.Batch618.valid24726
  · exact MergedCutProfiles.Batch618.valid24728
  · exact MergedCutProfiles.Batch618.valid24729
  · exact MergedCutProfiles.Batch618.valid24730
  · exact MergedCutProfiles.Batch618.valid24731
  · exact MergedCutProfiles.Batch618.valid24732
  · exact MergedCutProfiles.Batch618.valid24733
  · exact MergedCutProfiles.Batch618.valid24734
  · exact MergedCutProfiles.Batch618.valid24735
  · exact MergedCutProfiles.Batch618.valid24736
  · exact MergedCutProfiles.Batch618.valid24737
  · exact MergedCutProfiles.Batch618.valid24738
  · exact MergedCutProfiles.Batch618.valid24739
  · exact MergedCutProfiles.Batch618.valid24740
  · exact MergedCutProfiles.Batch618.valid24741
theorem numericValid4113 : retention4113.NumericValid := by decide +kernel
def certificate4113 : RatCutBinCertificate := ⟨⟨retention4113,(399696909933863393/200000000000000000),(14887102204219317/100000000000000000),(14384765127274286941/1000000000000000000),(2209443003729267056791/500000000000000000),(1057377684168358409/500000000000000000)⟩,(999613638988966513/1000000000000000000),(434434111965795493/1000000000000000000),(101686467380880303/500000000000000000),(4233295264708757/31250000000000000)⟩
theorem valid4113 : certificate4113.Valid := by decide +kernel
theorem sound4113 : certificate4113.Sound := rat_cut_bin_certificate_sound certificate4113 profilesValid4113 numericValid4113 valid4113

def retention4114 : RatCutRetentionCertificate := ⟨(109/2000),(11/200),(64000000000000000000/306286155555872753049),(10151207978001935527/1000000000000000000),(21/20),(25947058424756076856473837169702653987551/16241932764803096843200000000000000000000),false,MergedCutProfiles.Batch618.profile24742,(fun _ => MergedCutProfiles.Batch618.profile24742)⟩
theorem profilesValid4114 : retention4114.ProfilesValid := by
  exact MergedCutProfiles.Batch618.valid24742
theorem numericValid4114 : retention4114.NumericValid := by decide +kernel
def certificate4114 : RatCutBinCertificate := ⟨⟨retention4114,(399696909933863393/200000000000000000),(14887102204219317/100000000000000000),(14384765127274286941/1000000000000000000),(2209443003729267056791/500000000000000000),(49244318566383401/31250000000000000)⟩,(999613638988966513/1000000000000000000),(87358579371739569/250000000000000000),(141575336978987441/500000000000000000),(74469235972242101/200000000000000000)⟩
theorem valid4114 : certificate4114.Valid := by decide +kernel
theorem sound4114 : certificate4114.Sound := rat_cut_bin_certificate_sound certificate4114 profilesValid4114 numericValid4114 valid4114

def retention4115 : RatCutRetentionCertificate := ⟨(109/2000),(11/200),(1/2),64,1,(255400295568475156950441867733842600231/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch618.profile24743,(fun _ => MergedCutProfiles.Batch618.profile24743)⟩
theorem profilesValid4115 : retention4115.ProfilesValid := by
  exact MergedCutProfiles.Batch618.valid24743
theorem numericValid4115 : retention4115.NumericValid := by decide +kernel
def certificate4115 : RatCutBinCertificate := ⟨⟨retention4115,(399696909933863393/200000000000000000),(14887102204219317/100000000000000000),(14384765127274286941/1000000000000000000),(2209443003729267056791/500000000000000000),(39078985923628421/40000000000000000)⟩,(999613638988966513/1000000000000000000),(51885844900650883/100000000000000000),(140705955710469799/1000000000000000000),(33836599068893403/250000000000000000)⟩
theorem valid4115 : certificate4115.Valid := by decide +kernel
theorem sound4115 : certificate4115.Sound := rat_cut_bin_certificate_sound certificate4115 profilesValid4115 numericValid4115 valid4115

def certificates : List RatCutBinCertificate := [certificate4104,certificate4105,certificate4106,certificate4107,certificate4108,certificate4109,certificate4110,certificate4111,certificate4112,certificate4113,certificate4114,certificate4115]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4104,List.forall_mem_cons.mpr ⟨sound4105,List.forall_mem_cons.mpr ⟨sound4106,List.forall_mem_cons.mpr ⟨sound4107,List.forall_mem_cons.mpr ⟨sound4108,List.forall_mem_cons.mpr ⟨sound4109,List.forall_mem_cons.mpr ⟨sound4110,List.forall_mem_cons.mpr ⟨sound4111,List.forall_mem_cons.mpr ⟨sound4112,List.forall_mem_cons.mpr ⟨sound4113,List.forall_mem_cons.mpr ⟨sound4114,List.forall_mem_cons.mpr ⟨sound4115,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch342
