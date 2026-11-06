import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch502
import Cycle12.MergedCutProfiles.Batch503
import Cycle12.MergedCutProfiles.Batch504
import Cycle12.MergedCutProfiles.Batch615
import Cycle12.MergedCutProfiles.Batch616

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch341

def retention4092 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(64000000000000000000/326573202875387438003),(12661725285250508153/500000000000000000),1,(1653569379634912749589085866333660203/1012938022820040652240000000000000000),false,MergedCutProfiles.Batch615.profile24606,(fun _ => MergedCutProfiles.Batch615.profile24606)⟩
theorem profilesValid4092 : retention4092.ProfilesValid := by
  exact MergedCutProfiles.Batch615.valid24606
theorem numericValid4092 : retention4092.NumericValid := by decide +kernel
def certificate4092 : RatCutBinCertificate := ⟨⟨retention4092,(1878605482598564961/1000000000000000000),(17460968802135489/125000000000000000),(876051008877953263/62500000000000000),(4590923125678254077949/1000000000000000000),(806863515327266277/500000000000000000)⟩,(249911680762022813/250000000000000000),(33433164259710421/1000000000000000000),(208583774235384717/250000000000000000),(253054414514412037/200000000000000000)⟩
theorem valid4092 : certificate4092.Valid := by decide +kernel
theorem sound4092 : certificate4092.Sound := rat_cut_bin_certificate_sound certificate4092 profilesValid4092 numericValid4092 valid4092

def retention4093 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(1/2),64,1,(63849579314623294310930918929863576759/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch502.profile20104,(fun _ => MergedCutProfiles.Batch502.profile20104)⟩
theorem profilesValid4093 : retention4093.ProfilesValid := by
  exact MergedCutProfiles.Batch502.valid20104
theorem numericValid4093 : retention4093.NumericValid := by decide +kernel
def certificate4093 : RatCutBinCertificate := ⟨⟨retention4093,(1878605482598564961/1000000000000000000),(17460968802135489/125000000000000000),(876051008877953263/62500000000000000),(4590923125678254077949/1000000000000000000),(195785600041459209/200000000000000000)⟩,(249911680762022813/250000000000000000),(13778337343191471/250000000000000000),(774790551146863571/1000000000000000000),(18669272460097461/25000000000000000)⟩
theorem valid4093 : certificate4093.Valid := by decide +kernel
theorem sound4093 : certificate4093.Sound := rat_cut_bin_certificate_sound certificate4093 profilesValid4093 numericValid4093 valid4093

def retention4094 : RatCutRetentionCertificate := ⟨(107/2000),(27/500),(688360521531433681/319614393636568157969),(337398549912476071/500000000000000000),4,(3786077341595203397/1600000000000000000),true,MergedCutProfiles.Batch615.profile24607,![MergedCutProfiles.Batch615.profile24607,MergedCutProfiles.Batch615.profile24608,MergedCutProfiles.Batch615.profile24609,MergedCutProfiles.Batch615.profile24610,MergedCutProfiles.Batch615.profile24611,MergedCutProfiles.Batch615.profile24612,MergedCutProfiles.Batch615.profile24613,MergedCutProfiles.Batch615.profile24614,MergedCutProfiles.Batch615.profile24615,MergedCutProfiles.Batch615.profile24616,MergedCutProfiles.Batch615.profile24617,MergedCutProfiles.Batch615.profile24618,MergedCutProfiles.Batch615.profile24619,MergedCutProfiles.Batch615.profile24620,MergedCutProfiles.Batch615.profile24621,MergedCutProfiles.Batch615.profile24622]⟩
theorem profilesValid4094 : retention4094.ProfilesValid := by
  change ∀ j : Fin 16, (retention4094.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch615.valid24607
  · exact MergedCutProfiles.Batch615.valid24608
  · exact MergedCutProfiles.Batch615.valid24609
  · exact MergedCutProfiles.Batch615.valid24610
  · exact MergedCutProfiles.Batch615.valid24611
  · exact MergedCutProfiles.Batch615.valid24612
  · exact MergedCutProfiles.Batch615.valid24613
  · exact MergedCutProfiles.Batch615.valid24614
  · exact MergedCutProfiles.Batch615.valid24615
  · exact MergedCutProfiles.Batch615.valid24616
  · exact MergedCutProfiles.Batch615.valid24617
  · exact MergedCutProfiles.Batch615.valid24618
  · exact MergedCutProfiles.Batch615.valid24619
  · exact MergedCutProfiles.Batch615.valid24620
  · exact MergedCutProfiles.Batch615.valid24621
  · exact MergedCutProfiles.Batch615.valid24622
theorem numericValid4094 : retention4094.NumericValid := by decide +kernel
def certificate4094 : RatCutBinCertificate := ⟨⟨retention4094,(198764762323034543/100000000000000000),(142705547327693923/1000000000000000000),(706892696417685269/50000000000000000),(2265969628524573106277/500000000000000000),(2286045238568563629/1000000000000000000)⟩,(31238207982955139/31250000000000000),(35478214332346593/62500000000000000),(55458616936184427/500000000000000000),(52290041415504467/1000000000000000000)⟩
theorem valid4094 : certificate4094.Valid := by decide +kernel
theorem sound4094 : certificate4094.Sound := rat_cut_bin_certificate_sound certificate4094 profilesValid4094 numericValid4094 valid4094

def retention4095 : RatCutRetentionCertificate := ⟨(107/2000),(27/500),(1103833751000000000/319614393636568157969),(688360521531433681/1000000000000000000),4,(604863671315699397929/256000000000000000000),true,MergedCutProfiles.Batch615.profile24623,![MergedCutProfiles.Batch615.profile24623,MergedCutProfiles.Batch615.profile24624,MergedCutProfiles.Batch615.profile24625,MergedCutProfiles.Batch615.profile24626,MergedCutProfiles.Batch615.profile24614,MergedCutProfiles.Batch502.profile20108,MergedCutProfiles.Batch615.profile24627,MergedCutProfiles.Batch615.profile24619,MergedCutProfiles.Batch502.profile20109,MergedCutProfiles.Batch615.profile24622,MergedCutProfiles.Batch503.profile20125,MergedCutProfiles.Batch615.profile24628,MergedCutProfiles.Batch615.profile24629,MergedCutProfiles.Batch503.profile20155,MergedCutProfiles.Batch502.profile20111,MergedCutProfiles.Batch615.profile24630]⟩
theorem profilesValid4095 : retention4095.ProfilesValid := by
  change ∀ j : Fin 16, (retention4095.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch615.valid24623
  · exact MergedCutProfiles.Batch615.valid24624
  · exact MergedCutProfiles.Batch615.valid24625
  · exact MergedCutProfiles.Batch615.valid24626
  · exact MergedCutProfiles.Batch615.valid24614
  · exact MergedCutProfiles.Batch502.valid20108
  · exact MergedCutProfiles.Batch615.valid24627
  · exact MergedCutProfiles.Batch615.valid24619
  · exact MergedCutProfiles.Batch502.valid20109
  · exact MergedCutProfiles.Batch615.valid24622
  · exact MergedCutProfiles.Batch503.valid20125
  · exact MergedCutProfiles.Batch615.valid24628
  · exact MergedCutProfiles.Batch615.valid24629
  · exact MergedCutProfiles.Batch503.valid20155
  · exact MergedCutProfiles.Batch502.valid20111
  · exact MergedCutProfiles.Batch615.valid24630
theorem numericValid4095 : retention4095.NumericValid := by decide +kernel
def certificate4095 : RatCutBinCertificate := ⟨⟨retention4095,(198764762323034543/100000000000000000),(142705547327693923/1000000000000000000),(706892696417685269/50000000000000000),(2265969628524573106277/500000000000000000),(2282495634595847377/1000000000000000000)⟩,(31238207982955139/31250000000000000),(2808369568032467/5000000000000000),(28583392740013133/250000000000000000),(54017338060406351/1000000000000000000)⟩
theorem valid4095 : certificate4095.Valid := by decide +kernel
theorem sound4095 : certificate4095.Sound := rat_cut_bin_certificate_sound certificate4095 profilesValid4095 numericValid4095 valid4095

def retention4096 : RatCutRetentionCertificate := ⟨(107/2000),(27/500),(1652330227389409800/319614393636568157969),(1103833751/1000000000),(11/4),(1868331650456045809/800000000000000000),true,MergedCutProfiles.Batch615.profile24631,![MergedCutProfiles.Batch615.profile24631,MergedCutProfiles.Batch615.profile24625,MergedCutProfiles.Batch615.profile24632,MergedCutProfiles.Batch502.profile20108,MergedCutProfiles.Batch615.profile24618,MergedCutProfiles.Batch502.profile20109,MergedCutProfiles.Batch615.profile24633,MergedCutProfiles.Batch615.profile24628,MergedCutProfiles.Batch615.profile24634,MergedCutProfiles.Batch502.profile20111,MergedCutProfiles.Batch615.profile24635,MergedCutProfiles.Batch502.profile20112,MergedCutProfiles.Batch615.profile24636,MergedCutProfiles.Batch502.profile20113,MergedCutProfiles.Batch615.profile24637,MergedCutProfiles.Batch502.profile20114]⟩
theorem profilesValid4096 : retention4096.ProfilesValid := by
  change ∀ j : Fin 16, (retention4096.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch615.valid24631
  · exact MergedCutProfiles.Batch615.valid24625
  · exact MergedCutProfiles.Batch615.valid24632
  · exact MergedCutProfiles.Batch502.valid20108
  · exact MergedCutProfiles.Batch615.valid24618
  · exact MergedCutProfiles.Batch502.valid20109
  · exact MergedCutProfiles.Batch615.valid24633
  · exact MergedCutProfiles.Batch615.valid24628
  · exact MergedCutProfiles.Batch615.valid24634
  · exact MergedCutProfiles.Batch502.valid20111
  · exact MergedCutProfiles.Batch615.valid24635
  · exact MergedCutProfiles.Batch502.valid20112
  · exact MergedCutProfiles.Batch615.valid24636
  · exact MergedCutProfiles.Batch502.valid20113
  · exact MergedCutProfiles.Batch615.valid24637
  · exact MergedCutProfiles.Batch502.valid20114
theorem numericValid4096 : retention4096.NumericValid := by decide +kernel
def certificate4096 : RatCutBinCertificate := ⟨⟨retention4096,(198764762323034543/100000000000000000),(142705547327693923/1000000000000000000),(706892696417685269/50000000000000000),(2265969628524573106277/500000000000000000),(2280240628189660767/1000000000000000000)⟩,(31238207982955139/31250000000000000),(433636963937609171/1000000000000000000),(20403824576303879/100000000000000000),(1062613897301201/8000000000000000)⟩
theorem valid4096 : certificate4096.Valid := by decide +kernel
theorem sound4096 : certificate4096.Sound := rat_cut_bin_certificate_sound certificate4096 profilesValid4096 numericValid4096 valid4096

def retention4097 : RatCutRetentionCertificate := ⟨(107/2000),(27/500),(138703795640594450/1215263854131437863),(8261651136947049/5000000000000000),(21/10),(12424740210470593537775667463365560279/6609320909557639200000000000000000000),false,MergedCutProfiles.Batch615.profile24638,(fun _ => MergedCutProfiles.Batch615.profile24638)⟩
theorem profilesValid4097 : retention4097.ProfilesValid := by
  exact MergedCutProfiles.Batch615.valid24638
theorem numericValid4097 : retention4097.NumericValid := by decide +kernel
def certificate4097 : RatCutBinCertificate := ⟨⟨retention4097,(198764762323034543/100000000000000000),(142705547327693923/1000000000000000000),(706892696417685269/50000000000000000),(2265969628524573106277/500000000000000000),(367549749520175387/200000000000000000)⟩,(31238207982955139/31250000000000000),(56286902253572159/125000000000000000),(190435623379357237/1000000000000000000),(133030456814203921/1000000000000000000)⟩
theorem valid4097 : certificate4097.Valid := by decide +kernel
theorem sound4097 : certificate4097.Sound := rat_cut_bin_certificate_sound certificate4097 profilesValid4097 numericValid4097 valid4097

def retention4098 : RatCutRetentionCertificate := ⟨(107/2000),(27/500),(64000000000000000000/319614393636568157969),(729581965069526807/20000000000000000),1,(237946246331023888612696260015871879791/145916393013905361400000000000000000000),false,MergedCutProfiles.Batch615.profile24639,(fun _ => MergedCutProfiles.Batch615.profile24639)⟩
theorem profilesValid4098 : retention4098.ProfilesValid := by
  exact MergedCutProfiles.Batch615.valid24639
theorem numericValid4098 : retention4098.NumericValid := by decide +kernel
def certificate4098 : RatCutBinCertificate := ⟨⟨retention4098,(198764762323034543/100000000000000000),(142705547327693923/1000000000000000000),(706892696417685269/50000000000000000),(2265969628524573106277/500000000000000000),(402659893766690563/250000000000000000)⟩,(31238207982955139/31250000000000000),(80353831057930849/250000000000000000),(156879299675873179/500000000000000000),(120949293976150289/250000000000000000)⟩
theorem valid4098 : certificate4098.Valid := by decide +kernel
theorem sound4098 : certificate4098.Sound := rat_cut_bin_certificate_sound certificate4098 profilesValid4098 numericValid4098 valid4098

def retention4099 : RatCutRetentionCertificate := ⟨(107/2000),(27/500),(1/2),64,1,(408638349423453486626934523116689871/409600000000000000000000000000000000),false,MergedCutProfiles.Batch504.profile20186,(fun _ => MergedCutProfiles.Batch504.profile20186)⟩
theorem profilesValid4099 : retention4099.ProfilesValid := by
  exact MergedCutProfiles.Batch504.valid20186
theorem numericValid4099 : retention4099.NumericValid := by decide +kernel
def certificate4099 : RatCutBinCertificate := ⟨⟨retention4099,(198764762323034543/100000000000000000),(142705547327693923/1000000000000000000),(706892696417685269/50000000000000000),(2265969628524573106277/500000000000000000),(977589169475011747/1000000000000000000)⟩,(31238207982955139/31250000000000000),(523085655707046617/1000000000000000000),(137949560152986837/1000000000000000000),(33194604218410739/250000000000000000)⟩
theorem valid4099 : certificate4099.Valid := by decide +kernel
theorem sound4099 : certificate4099.Sound := rat_cut_bin_certificate_sound certificate4099 profilesValid4099 numericValid4099 valid4099

def retention4100 : RatCutRetentionCertificate := ⟨(107/2000),(27/500),(64000000000000000000/319614393636568157969),(2530656025904066357/100000000000000000),1,(164236732513704634304336608083958370431/101226241036162654280000000000000000000),false,MergedCutProfiles.Batch615.profile24639,(fun _ => MergedCutProfiles.Batch615.profile24639)⟩
theorem profilesValid4100 : retention4100.ProfilesValid := by
  exact MergedCutProfiles.Batch615.valid24639
theorem numericValid4100 : retention4100.NumericValid := by decide +kernel
def certificate4100 : RatCutBinCertificate := ⟨⟨retention4100,(188093945723034543/100000000000000000),(142705547327693923/1000000000000000000),(706892696417685269/50000000000000000),(2265969628524573106277/500000000000000000),(1603485941749202093/1000000000000000000)⟩,(999642914618466443/1000000000000000000),(16770206258743407/500000000000000000),(834027347143771037/1000000000000000000),(31430041407920017/25000000000000000)⟩
theorem valid4100 : certificate4100.Valid := by decide +kernel
theorem sound4100 : certificate4100.Sound := rat_cut_bin_certificate_sound certificate4100 profilesValid4100 numericValid4100 valid4100

def retention4101 : RatCutRetentionCertificate := ⟨(107/2000),(27/500),(1/2),64,1,(408638349423453486626934523116689871/409600000000000000000000000000000000),false,MergedCutProfiles.Batch504.profile20186,(fun _ => MergedCutProfiles.Batch504.profile20186)⟩
theorem profilesValid4101 : retention4101.ProfilesValid := by
  exact MergedCutProfiles.Batch504.valid20186
theorem numericValid4101 : retention4101.NumericValid := by decide +kernel
def certificate4101 : RatCutBinCertificate := ⟨⟨retention4101,(188093945723034543/100000000000000000),(142705547327693923/1000000000000000000),(706892696417685269/50000000000000000),(2265969628524573106277/500000000000000000),(244666566878215921/250000000000000000)⟩,(999642914618466443/1000000000000000000),(54953952882157717/1000000000000000000),(155041930475581427/200000000000000000),(373487595854881547/500000000000000000)⟩
theorem valid4101 : certificate4101.Valid := by decide +kernel
theorem sound4101 : certificate4101.Sound := rat_cut_bin_certificate_sound certificate4101 profilesValid4101 numericValid4101 valid4101

def retention4102 : RatCutRetentionCertificate := ⟨(27/500),(109/2000),(231172089722432874/104284831292824407139),(135970251772825923/200000000000000000),4,(37928680424211377943/16000000000000000000),true,MergedCutProfiles.Batch616.profile24640,![MergedCutProfiles.Batch616.profile24640,MergedCutProfiles.Batch616.profile24641,MergedCutProfiles.Batch616.profile24642,MergedCutProfiles.Batch616.profile24643,MergedCutProfiles.Batch616.profile24644,MergedCutProfiles.Batch616.profile24645,MergedCutProfiles.Batch616.profile24646,MergedCutProfiles.Batch616.profile24647,MergedCutProfiles.Batch616.profile24648,MergedCutProfiles.Batch616.profile24649,MergedCutProfiles.Batch616.profile24650,MergedCutProfiles.Batch616.profile24651,MergedCutProfiles.Batch616.profile24652,MergedCutProfiles.Batch616.profile24653,MergedCutProfiles.Batch616.profile24654,MergedCutProfiles.Batch616.profile24655]⟩
theorem profilesValid4102 : retention4102.ProfilesValid := by
  change ∀ j : Fin 16, (retention4102.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch616.valid24640
  · exact MergedCutProfiles.Batch616.valid24641
  · exact MergedCutProfiles.Batch616.valid24642
  · exact MergedCutProfiles.Batch616.valid24643
  · exact MergedCutProfiles.Batch616.valid24644
  · exact MergedCutProfiles.Batch616.valid24645
  · exact MergedCutProfiles.Batch616.valid24646
  · exact MergedCutProfiles.Batch616.valid24647
  · exact MergedCutProfiles.Batch616.valid24648
  · exact MergedCutProfiles.Batch616.valid24649
  · exact MergedCutProfiles.Batch616.valid24650
  · exact MergedCutProfiles.Batch616.valid24651
  · exact MergedCutProfiles.Batch616.valid24652
  · exact MergedCutProfiles.Batch616.valid24653
  · exact MergedCutProfiles.Batch616.valid24654
  · exact MergedCutProfiles.Batch616.valid24655
theorem numericValid4102 : retention4102.NumericValid := by decide +kernel
def certificate4102 : RatCutBinCertificate := ⟨⟨retention4102,(1993058303095839087/1000000000000000000),(36441619022305257/250000000000000000),(14260494253622171183/1000000000000000000),(1118653101311841638807/250000000000000000),(572262946044617729/250000000000000000)⟩,(999618124099214697/1000000000000000000),(560552148670086351/1000000000000000000),(114981763620132127/1000000000000000000),(54335390705955743/1000000000000000000)⟩
theorem valid4102 : certificate4102.Valid := by decide +kernel
theorem sound4102 : certificate4102.Sound := rat_cut_bin_certificate_sound certificate4102 profilesValid4102 numericValid4102 valid4102

def retention4103 : RatCutRetentionCertificate := ⟨(27/500),(109/2000),(1111204577000000000/312854493878473221417),(346758134583649311/500000000000000000),4,(302756689936862122511/128000000000000000000),true,MergedCutProfiles.Batch616.profile24656,![MergedCutProfiles.Batch616.profile24656,MergedCutProfiles.Batch616.profile24657,MergedCutProfiles.Batch616.profile24658,MergedCutProfiles.Batch616.profile24659,MergedCutProfiles.Batch616.profile24647,MergedCutProfiles.Batch616.profile24660,MergedCutProfiles.Batch616.profile24661,MergedCutProfiles.Batch616.profile24652,MergedCutProfiles.Batch616.profile24662,MergedCutProfiles.Batch616.profile24655,MergedCutProfiles.Batch616.profile24663,MergedCutProfiles.Batch616.profile24664,MergedCutProfiles.Batch616.profile24665,MergedCutProfiles.Batch616.profile24666,MergedCutProfiles.Batch616.profile24667,MergedCutProfiles.Batch616.profile24668]⟩
theorem profilesValid4103 : retention4103.ProfilesValid := by
  change ∀ j : Fin 16, (retention4103.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch616.valid24656
  · exact MergedCutProfiles.Batch616.valid24657
  · exact MergedCutProfiles.Batch616.valid24658
  · exact MergedCutProfiles.Batch616.valid24659
  · exact MergedCutProfiles.Batch616.valid24647
  · exact MergedCutProfiles.Batch616.valid24660
  · exact MergedCutProfiles.Batch616.valid24661
  · exact MergedCutProfiles.Batch616.valid24652
  · exact MergedCutProfiles.Batch616.valid24662
  · exact MergedCutProfiles.Batch616.valid24655
  · exact MergedCutProfiles.Batch616.valid24663
  · exact MergedCutProfiles.Batch616.valid24664
  · exact MergedCutProfiles.Batch616.valid24665
  · exact MergedCutProfiles.Batch616.valid24666
  · exact MergedCutProfiles.Batch616.valid24667
  · exact MergedCutProfiles.Batch616.valid24668
theorem numericValid4103 : retention4103.NumericValid := by decide +kernel
def certificate4103 : RatCutBinCertificate := ⟨⟨retention4103,(1993058303095839087/1000000000000000000),(36441619022305257/250000000000000000),(14260494253622171183/1000000000000000000),(1118653101311841638807/250000000000000000),(1141897958515832049/500000000000000000)⟩,(999618124099214697/1000000000000000000),(277546340944570841/500000000000000000),(118168554731808569/1000000000000000000),(27963323945113549/500000000000000000)⟩
theorem valid4103 : certificate4103.Valid := by decide +kernel
theorem sound4103 : certificate4103.Sound := rat_cut_bin_certificate_sound certificate4103 profilesValid4103 numericValid4103 valid4103

def certificates : List RatCutBinCertificate := [certificate4092,certificate4093,certificate4094,certificate4095,certificate4096,certificate4097,certificate4098,certificate4099,certificate4100,certificate4101,certificate4102,certificate4103]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4092,List.forall_mem_cons.mpr ⟨sound4093,List.forall_mem_cons.mpr ⟨sound4094,List.forall_mem_cons.mpr ⟨sound4095,List.forall_mem_cons.mpr ⟨sound4096,List.forall_mem_cons.mpr ⟨sound4097,List.forall_mem_cons.mpr ⟨sound4098,List.forall_mem_cons.mpr ⟨sound4099,List.forall_mem_cons.mpr ⟨sound4100,List.forall_mem_cons.mpr ⟨sound4101,List.forall_mem_cons.mpr ⟨sound4102,List.forall_mem_cons.mpr ⟨sound4103,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch341
