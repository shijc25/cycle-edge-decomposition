import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch390
import Cycle12.MergedCutProfiles.Batch391
import Cycle12.MergedCutProfiles.Batch392
import Cycle12.MergedCutProfiles.Batch512
import Cycle12.MergedCutProfiles.Batch513
import Cycle12.MergedCutProfiles.Batch619
import Cycle12.MergedCutProfiles.Batch620
import Cycle12.MergedCutProfiles.Batch621

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch344

def retention4128 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(548776937500000000/140896379138290870909),(1080481155841704411/1000000000000000000),(11/4),(599868608495620366543/256000000000000000000),true,MergedCutProfiles.Batch619.profile24791,![MergedCutProfiles.Batch619.profile24791,MergedCutProfiles.Batch620.profile24802,MergedCutProfiles.Batch620.profile24803,MergedCutProfiles.Batch619.profile24780,MergedCutProfiles.Batch620.profile24804,MergedCutProfiles.Batch620.profile24805,MergedCutProfiles.Batch620.profile24806,MergedCutProfiles.Batch620.profile24807,MergedCutProfiles.Batch390.profile15633,MergedCutProfiles.Batch620.profile24808,MergedCutProfiles.Batch619.profile24796,MergedCutProfiles.Batch620.profile24809,MergedCutProfiles.Batch391.profile15663,MergedCutProfiles.Batch620.profile24810,MergedCutProfiles.Batch620.profile24811,MergedCutProfiles.Batch620.profile24812]⟩
theorem profilesValid4128 : retention4128.ProfilesValid := by
  change ∀ j : Fin 16, (retention4128.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch619.valid24791
  · exact MergedCutProfiles.Batch620.valid24802
  · exact MergedCutProfiles.Batch620.valid24803
  · exact MergedCutProfiles.Batch619.valid24780
  · exact MergedCutProfiles.Batch620.valid24804
  · exact MergedCutProfiles.Batch620.valid24805
  · exact MergedCutProfiles.Batch620.valid24806
  · exact MergedCutProfiles.Batch620.valid24807
  · exact MergedCutProfiles.Batch390.valid15633
  · exact MergedCutProfiles.Batch620.valid24808
  · exact MergedCutProfiles.Batch619.valid24796
  · exact MergedCutProfiles.Batch620.valid24809
  · exact MergedCutProfiles.Batch391.valid15663
  · exact MergedCutProfiles.Batch620.valid24810
  · exact MergedCutProfiles.Batch620.valid24811
  · exact MergedCutProfiles.Batch620.valid24812
theorem numericValid4128 : retention4128.NumericValid := by decide +kernel
def certificate4128 : RatCutBinCertificate := ⟨⟨retention4128,(100898051761738163/50000000000000000),(161735409484216873/1000000000000000000),(14767649492315503689/1000000000000000000),(837271614066183087231/200000000000000000),(2282458969059315639/1000000000000000000)⟩,(249898188644278969/250000000000000000),(210261758421694683/500000000000000000),(53798805356000797/250000000000000000),(139543976678887919/1000000000000000000)⟩
theorem valid4128 : certificate4128.Valid := by decide +kernel
theorem sound4128 : certificate4128.Sound := rat_cut_bin_certificate_sound certificate4128 profilesValid4128 numericValid4128 valid4128

def retention4129 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(672446015419087965/140896379138290870909),(8780431/8000000),(11/4),(37449573020786209663/16000000000000000000),true,MergedCutProfiles.Batch620.profile24813,![MergedCutProfiles.Batch620.profile24813,MergedCutProfiles.Batch620.profile24814,MergedCutProfiles.Batch620.profile24815,MergedCutProfiles.Batch619.profile24793,MergedCutProfiles.Batch620.profile24816,MergedCutProfiles.Batch620.profile24817,MergedCutProfiles.Batch620.profile24818,MergedCutProfiles.Batch619.profile24795,MergedCutProfiles.Batch620.profile24819,MergedCutProfiles.Batch620.profile24820,MergedCutProfiles.Batch620.profile24821,MergedCutProfiles.Batch620.profile24800,MergedCutProfiles.Batch620.profile24812,MergedCutProfiles.Batch620.profile24822,MergedCutProfiles.Batch620.profile24823,MergedCutProfiles.Batch620.profile24824]⟩
theorem profilesValid4129 : retention4129.ProfilesValid := by
  change ∀ j : Fin 16, (retention4129.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch620.valid24813
  · exact MergedCutProfiles.Batch620.valid24814
  · exact MergedCutProfiles.Batch620.valid24815
  · exact MergedCutProfiles.Batch619.valid24793
  · exact MergedCutProfiles.Batch620.valid24816
  · exact MergedCutProfiles.Batch620.valid24817
  · exact MergedCutProfiles.Batch620.valid24818
  · exact MergedCutProfiles.Batch619.valid24795
  · exact MergedCutProfiles.Batch620.valid24819
  · exact MergedCutProfiles.Batch620.valid24820
  · exact MergedCutProfiles.Batch620.valid24821
  · exact MergedCutProfiles.Batch620.valid24800
  · exact MergedCutProfiles.Batch620.valid24812
  · exact MergedCutProfiles.Batch620.valid24822
  · exact MergedCutProfiles.Batch620.valid24823
  · exact MergedCutProfiles.Batch620.valid24824
theorem numericValid4129 : retention4129.NumericValid := by decide +kernel
def certificate4129 : RatCutBinCertificate := ⟨⟨retention4129,(100898051761738163/50000000000000000),(161735409484216873/1000000000000000000),(14767649492315503689/1000000000000000000),(837271614066183087231/200000000000000000),(113991027160739317/50000000000000000)⟩,(249898188644278969/250000000000000000),(104448864341596709/250000000000000000),(217567220869063717/1000000000000000000),(141434650130613007/1000000000000000000)⟩
theorem valid4129 : certificate4129.Valid := by decide +kernel
theorem sound4129 : certificate4129.Sound := rat_cut_bin_certificate_sound certificate4129 profilesValid4129 numericValid4129 valid4129

def retention4130 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(7546598652299496306/140896379138290870909),(134489203083817593/100000000000000000),(47/20),(266100931962334422849/128000000000000000000),true,MergedCutProfiles.Batch619.profile24799,![MergedCutProfiles.Batch619.profile24799,MergedCutProfiles.Batch620.profile24825,MergedCutProfiles.Batch620.profile24826,MergedCutProfiles.Batch620.profile24827,MergedCutProfiles.Batch620.profile24828,MergedCutProfiles.Batch620.profile24829,MergedCutProfiles.Batch620.profile24830,MergedCutProfiles.Batch392.profile15692,MergedCutProfiles.Batch620.profile24831,MergedCutProfiles.Batch620.profile24832,MergedCutProfiles.Batch620.profile24833,MergedCutProfiles.Batch620.profile24834,MergedCutProfiles.Batch620.profile24835,MergedCutProfiles.Batch620.profile24836,MergedCutProfiles.Batch620.profile24837,MergedCutProfiles.Batch620.profile24838]⟩
theorem profilesValid4130 : retention4130.ProfilesValid := by
  change ∀ j : Fin 16, (retention4130.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch619.valid24799
  · exact MergedCutProfiles.Batch620.valid24825
  · exact MergedCutProfiles.Batch620.valid24826
  · exact MergedCutProfiles.Batch620.valid24827
  · exact MergedCutProfiles.Batch620.valid24828
  · exact MergedCutProfiles.Batch620.valid24829
  · exact MergedCutProfiles.Batch620.valid24830
  · exact MergedCutProfiles.Batch392.valid15692
  · exact MergedCutProfiles.Batch620.valid24831
  · exact MergedCutProfiles.Batch620.valid24832
  · exact MergedCutProfiles.Batch620.valid24833
  · exact MergedCutProfiles.Batch620.valid24834
  · exact MergedCutProfiles.Batch620.valid24835
  · exact MergedCutProfiles.Batch620.valid24836
  · exact MergedCutProfiles.Batch620.valid24837
  · exact MergedCutProfiles.Batch620.valid24838
theorem numericValid4130 : retention4130.NumericValid := by decide +kernel
def certificate4130 : RatCutBinCertificate := ⟨⟨retention4130,(100898051761738163/50000000000000000),(161735409484216873/1000000000000000000),(14767649492315503689/1000000000000000000),(837271614066183087231/200000000000000000),(506744048320298743/250000000000000000)⟩,(249898188644278969/250000000000000000),(427827356713442981/1000000000000000000),(208931445161857947/1000000000000000000),(141507262852375787/1000000000000000000)⟩
theorem valid4130 : certificate4130.Valid := by decide +kernel
theorem sound4130 : certificate4130.Sound := rat_cut_bin_certificate_sound certificate4130 profilesValid4130 numericValid4130 valid4130

def retention4131 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(32000000000000000000/140896379138290870909),(3773299326149748153/250000000000000000),1,(93201878558603544342446811203668294151/60372789218395970448000000000000000000),false,MergedCutProfiles.Batch620.profile24839,(fun _ => MergedCutProfiles.Batch620.profile24839)⟩
theorem profilesValid4131 : retention4131.ProfilesValid := by
  exact MergedCutProfiles.Batch620.valid24839
theorem numericValid4131 : retention4131.NumericValid := by decide +kernel
def certificate4131 : RatCutBinCertificate := ⟨⟨retention4131,(100898051761738163/50000000000000000),(161735409484216873/1000000000000000000),(14767649492315503689/1000000000000000000),(837271614066183087231/200000000000000000),(12173377303914919/8000000000000000)⟩,(249898188644278969/250000000000000000),(42913063991606137/125000000000000000),(289648761643089481/1000000000000000000),(100053650725981661/250000000000000000)⟩
theorem valid4131 : certificate4131.Valid := by decide +kernel
theorem sound4131 : certificate4131.Sound := rat_cut_bin_certificate_sound certificate4131 profilesValid4131 numericValid4131 valid4131

def retention4132 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(1/2),64,1,(255402311029323201614710967138024893231/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch392.profile15710,(fun _ => MergedCutProfiles.Batch392.profile15710)⟩
theorem profilesValid4132 : retention4132.ProfilesValid := by
  exact MergedCutProfiles.Batch392.valid15710
theorem numericValid4132 : retention4132.NumericValid := by decide +kernel
def certificate4132 : RatCutBinCertificate := ⟨⟨retention4132,(100898051761738163/50000000000000000),(161735409484216873/1000000000000000000),(14767649492315503689/1000000000000000000),(837271614066183087231/200000000000000000),(78045163161703/80000000000000)⟩,(249898188644278969/250000000000000000),(509061376486121667/1000000000000000000),(73613561265675679/500000000000000000),(28282968002138959/200000000000000000)⟩
theorem valid4132 : certificate4132.Valid := by decide +kernel
theorem sound4132 : certificate4132.Sound := rat_cut_bin_certificate_sound certificate4132 profilesValid4132 numericValid4132 valid4132

def retention4133 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(32000000000000000000/140896379138290870909),(1565974799311868649/62500000000000000),1,(156379676133874864537846710874492101623/100222387155959593536000000000000000000),false,MergedCutProfiles.Batch620.profile24839,(fun _ => MergedCutProfiles.Batch620.profile24839)⟩
theorem profilesValid4133 : retention4133.ProfilesValid := by
  exact MergedCutProfiles.Batch620.valid24839
theorem numericValid4133 : retention4133.NumericValid := by decide +kernel
def certificate4133 : RatCutBinCertificate := ⟨⟨retention4133,(94670188561738163/50000000000000000),(161735409484216873/1000000000000000000),(14767649492315503689/1000000000000000000),(837271614066183087231/200000000000000000),(384897547621933053/250000000000000000)⟩,(124952236660861271/125000000000000000),(17203154900298809/500000000000000000),(166309534118938459/200000000000000000),(241131237039142611/200000000000000000)⟩
theorem valid4133 : certificate4133.Valid := by decide +kernel
theorem sound4133 : certificate4133.Sound := rat_cut_bin_certificate_sound certificate4133 profilesValid4133 numericValid4133 valid4133

def retention4134 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(1/2),64,1,(255402311029323201614710967138024893231/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch392.profile15710,(fun _ => MergedCutProfiles.Batch392.profile15710)⟩
theorem profilesValid4134 : retention4134.ProfilesValid := by
  exact MergedCutProfiles.Batch392.valid15710
theorem numericValid4134 : retention4134.NumericValid := by decide +kernel
def certificate4134 : RatCutBinCertificate := ⟨⟨retention4134,(94670188561738163/50000000000000000),(161735409484216873/1000000000000000000),(14767649492315503689/1000000000000000000),(837271614066183087231/200000000000000000),(61058043277925891/62500000000000000)⟩,(124952236660861271/125000000000000000),(433780827357701/8000000000000000),(388567991042436191/500000000000000000),(747502833612610399/1000000000000000000)⟩
theorem valid4134 : certificate4134.Valid := by decide +kernel
theorem sound4134 : certificate4134.Sound := rat_cut_bin_certificate_sound certificate4134 profilesValid4134 numericValid4134 valid4134

def retention4135 : RatCutRetentionCertificate := ⟨(57/1000),(23/400),(721146581742391791/276083073164672771072),(142801303315325107/200000000000000000),(79/20),(611167640464735085539/256000000000000000000),true,MergedCutProfiles.Batch621.profile24840,![MergedCutProfiles.Batch621.profile24840,MergedCutProfiles.Batch621.profile24841,MergedCutProfiles.Batch621.profile24842,MergedCutProfiles.Batch621.profile24843,MergedCutProfiles.Batch621.profile24844,MergedCutProfiles.Batch513.profile20529,MergedCutProfiles.Batch621.profile24845,MergedCutProfiles.Batch621.profile24846,MergedCutProfiles.Batch621.profile24847,MergedCutProfiles.Batch621.profile24848,MergedCutProfiles.Batch621.profile24849,MergedCutProfiles.Batch513.profile20530,MergedCutProfiles.Batch621.profile24850,MergedCutProfiles.Batch621.profile24851,MergedCutProfiles.Batch621.profile24852,MergedCutProfiles.Batch621.profile24853]⟩
theorem profilesValid4135 : retention4135.ProfilesValid := by
  change ∀ j : Fin 16, (retention4135.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch621.valid24840
  · exact MergedCutProfiles.Batch621.valid24841
  · exact MergedCutProfiles.Batch621.valid24842
  · exact MergedCutProfiles.Batch621.valid24843
  · exact MergedCutProfiles.Batch621.valid24844
  · exact MergedCutProfiles.Batch513.valid20529
  · exact MergedCutProfiles.Batch621.valid24845
  · exact MergedCutProfiles.Batch621.valid24846
  · exact MergedCutProfiles.Batch621.valid24847
  · exact MergedCutProfiles.Batch621.valid24848
  · exact MergedCutProfiles.Batch621.valid24849
  · exact MergedCutProfiles.Batch513.valid20530
  · exact MergedCutProfiles.Batch621.valid24850
  · exact MergedCutProfiles.Batch621.valid24851
  · exact MergedCutProfiles.Batch621.valid24852
  · exact MergedCutProfiles.Batch621.valid24853
theorem numericValid4135 : retention4135.NumericValid := by decide +kernel
def certificate4135 : RatCutBinCertificate := ⟨⟨retention4135,(2029116924191451017/1000000000000000000),(165065648943161283/1000000000000000000),(15031599453156358853/1000000000000000000),(4162450143084543733863/1000000000000000000),(2299357563809452891/1000000000000000000)⟩,(9995913293345847/10000000000000000),(103175145726222779/200000000000000000),(142671577415039127/1000000000000000000),(68808519838188681/1000000000000000000)⟩
theorem valid4135 : certificate4135.Valid := by decide +kernel
theorem sound4135 : certificate4135.Sound := rat_cut_bin_certificate_sound certificate4135 profilesValid4135 numericValid4135 valid4135

def retention4136 : RatCutRetentionCertificate := ⟨(57/1000),(23/400),(136908767612465441/34510384145584096384),(721146581742391791/1000000000000000000),(39/10),(3032590710333495285611/1280000000000000000000),true,MergedCutProfiles.Batch621.profile24854,![MergedCutProfiles.Batch621.profile24854,MergedCutProfiles.Batch621.profile24842,MergedCutProfiles.Batch621.profile24855,MergedCutProfiles.Batch513.profile20529,MergedCutProfiles.Batch621.profile24856,MergedCutProfiles.Batch621.profile24847,MergedCutProfiles.Batch621.profile24857,MergedCutProfiles.Batch513.profile20545,MergedCutProfiles.Batch621.profile24858,MergedCutProfiles.Batch621.profile24852,MergedCutProfiles.Batch621.profile24859,MergedCutProfiles.Batch513.profile20531,MergedCutProfiles.Batch621.profile24860,MergedCutProfiles.Batch621.profile24861,MergedCutProfiles.Batch621.profile24862,MergedCutProfiles.Batch513.profile20532]⟩
theorem profilesValid4136 : retention4136.ProfilesValid := by
  change ∀ j : Fin 16, (retention4136.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch621.valid24854
  · exact MergedCutProfiles.Batch621.valid24842
  · exact MergedCutProfiles.Batch621.valid24855
  · exact MergedCutProfiles.Batch513.valid20529
  · exact MergedCutProfiles.Batch621.valid24856
  · exact MergedCutProfiles.Batch621.valid24847
  · exact MergedCutProfiles.Batch621.valid24857
  · exact MergedCutProfiles.Batch513.valid20545
  · exact MergedCutProfiles.Batch621.valid24858
  · exact MergedCutProfiles.Batch621.valid24852
  · exact MergedCutProfiles.Batch621.valid24859
  · exact MergedCutProfiles.Batch513.valid20531
  · exact MergedCutProfiles.Batch621.valid24860
  · exact MergedCutProfiles.Batch621.valid24861
  · exact MergedCutProfiles.Batch621.valid24862
  · exact MergedCutProfiles.Batch513.valid20532
theorem numericValid4136 : retention4136.NumericValid := by decide +kernel
def certificate4136 : RatCutBinCertificate := ⟨⟨retention4136,(2029116924191451017/1000000000000000000),(165065648943161283/1000000000000000000),(15031599453156358853/1000000000000000000),(4162450143084543733863/1000000000000000000),(228230958426414691/100000000000000000)⟩,(9995913293345847/10000000000000000),(10333683908518197/20000000000000000),(28427419167847051/200000000000000000),(13763847446593447/200000000000000000)⟩
theorem valid4136 : certificate4136.Valid := by decide +kernel
theorem sound4136 : certificate4136.Sound := rat_cut_bin_certificate_sound certificate4136 profilesValid4136 numericValid4136 valid4136

def retention4137 : RatCutRetentionCertificate := ⟨(57/1000),(23/400),(2170097322265625/539224752274751506),(136908767612465441/125000000000000000),(11/4),(75166273512017996779/32000000000000000000),true,MergedCutProfiles.Batch621.profile24854,![MergedCutProfiles.Batch621.profile24854,MergedCutProfiles.Batch621.profile24842,MergedCutProfiles.Batch621.profile24863,MergedCutProfiles.Batch513.profile20529,MergedCutProfiles.Batch621.profile24856,MergedCutProfiles.Batch621.profile24864,MergedCutProfiles.Batch621.profile24857,MergedCutProfiles.Batch513.profile20545,MergedCutProfiles.Batch621.profile24851,MergedCutProfiles.Batch621.profile24865,MergedCutProfiles.Batch513.profile20557,MergedCutProfiles.Batch513.profile20546,MergedCutProfiles.Batch621.profile24866,MergedCutProfiles.Batch621.profile24867,MergedCutProfiles.Batch512.profile20516,MergedCutProfiles.Batch513.profile20547]⟩
theorem profilesValid4137 : retention4137.ProfilesValid := by
  change ∀ j : Fin 16, (retention4137.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch621.valid24854
  · exact MergedCutProfiles.Batch621.valid24842
  · exact MergedCutProfiles.Batch621.valid24863
  · exact MergedCutProfiles.Batch513.valid20529
  · exact MergedCutProfiles.Batch621.valid24856
  · exact MergedCutProfiles.Batch621.valid24864
  · exact MergedCutProfiles.Batch621.valid24857
  · exact MergedCutProfiles.Batch513.valid20545
  · exact MergedCutProfiles.Batch621.valid24851
  · exact MergedCutProfiles.Batch621.valid24865
  · exact MergedCutProfiles.Batch513.valid20557
  · exact MergedCutProfiles.Batch513.valid20546
  · exact MergedCutProfiles.Batch621.valid24866
  · exact MergedCutProfiles.Batch621.valid24867
  · exact MergedCutProfiles.Batch512.valid20516
  · exact MergedCutProfiles.Batch513.valid20547
theorem numericValid4137 : retention4137.NumericValid := by decide +kernel
def certificate4137 : RatCutBinCertificate := ⟨⟨retention4137,(2029116924191451017/1000000000000000000),(165065648943161283/1000000000000000000),(15031599453156358853/1000000000000000000),(4162450143084543733863/1000000000000000000),(2287669117943558371/1000000000000000000)⟩,(9995913293345847/10000000000000000),(411708418158355887/1000000000000000000),(44584832633297841/200000000000000000),(9077651067717421/62500000000000000)⟩
theorem valid4137 : certificate4137.Valid := by decide +kernel
theorem sound4137 : certificate4137.Sound := rat_cut_bin_certificate_sound certificate4137 profilesValid4137 numericValid4137 valid4137

def retention4138 : RatCutRetentionCertificate := ⟨(57/1000),(23/400),(1893201353135522933/276083073164672771072),(1111089829/1000000000),(27/10),(37103822068666921339/16000000000000000000),true,MergedCutProfiles.Batch621.profile24868,![MergedCutProfiles.Batch621.profile24868,MergedCutProfiles.Batch621.profile24869,MergedCutProfiles.Batch621.profile24870,MergedCutProfiles.Batch621.profile24871,MergedCutProfiles.Batch621.profile24850,MergedCutProfiles.Batch621.profile24872,MergedCutProfiles.Batch513.profile20546,MergedCutProfiles.Batch621.profile24873,MergedCutProfiles.Batch512.profile20501,MergedCutProfiles.Batch621.profile24874,MergedCutProfiles.Batch512.profile20517,MergedCutProfiles.Batch621.profile24875,MergedCutProfiles.Batch513.profile20559,MergedCutProfiles.Batch621.profile24876,MergedCutProfiles.Batch621.profile24877,MergedCutProfiles.Batch513.profile20535]⟩
theorem profilesValid4138 : retention4138.ProfilesValid := by
  change ∀ j : Fin 16, (retention4138.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch621.valid24868
  · exact MergedCutProfiles.Batch621.valid24869
  · exact MergedCutProfiles.Batch621.valid24870
  · exact MergedCutProfiles.Batch621.valid24871
  · exact MergedCutProfiles.Batch621.valid24850
  · exact MergedCutProfiles.Batch621.valid24872
  · exact MergedCutProfiles.Batch513.valid20546
  · exact MergedCutProfiles.Batch621.valid24873
  · exact MergedCutProfiles.Batch512.valid20501
  · exact MergedCutProfiles.Batch621.valid24874
  · exact MergedCutProfiles.Batch512.valid20517
  · exact MergedCutProfiles.Batch621.valid24875
  · exact MergedCutProfiles.Batch513.valid20559
  · exact MergedCutProfiles.Batch621.valid24876
  · exact MergedCutProfiles.Batch621.valid24877
  · exact MergedCutProfiles.Batch513.valid20535
theorem numericValid4138 : retention4138.NumericValid := by decide +kernel
def certificate4138 : RatCutBinCertificate := ⟨⟨retention4138,(2029116924191451017/1000000000000000000),(165065648943161283/1000000000000000000),(15031599453156358853/1000000000000000000),(4162450143084543733863/1000000000000000000),(564706518197588191/250000000000000000)⟩,(9995913293345847/10000000000000000),(207040688728635271/500000000000000000),(3450393690296697/15625000000000000),(72194000277067797/500000000000000000)⟩
theorem valid4138 : certificate4138.Valid := by decide +kernel
theorem sound4138 : certificate4138.Sound := rat_cut_bin_certificate_sound certificate4138 profilesValid4138 numericValid4138 valid4138

def retention4139 : RatCutRetentionCertificate := ⟨(57/1000),(23/400),(21964479993516306387/138041536582336385536),(1893201353135522933/1000000000000000000),(19/10),(1330028275129108723879752406523161278151/757280541254209173200000000000000000000),false,MergedCutProfiles.Batch621.profile24878,(fun _ => MergedCutProfiles.Batch621.profile24878)⟩
theorem profilesValid4139 : retention4139.ProfilesValid := by
  exact MergedCutProfiles.Batch621.valid24878
theorem numericValid4139 : retention4139.NumericValid := by decide +kernel
def certificate4139 : RatCutBinCertificate := ⟨⟨retention4139,(2029116924191451017/1000000000000000000),(165065648943161283/1000000000000000000),(15031599453156358853/1000000000000000000),(4162450143084543733863/1000000000000000000),(1713985039505912131/1000000000000000000)⟩,(9995913293345847/10000000000000000),(1092485293590599/2500000000000000),(100623097117636617/500000000000000000),(72537670218310963/500000000000000000)⟩
theorem valid4139 : certificate4139.Valid := by decide +kernel
theorem sound4139 : certificate4139.Sound := rat_cut_bin_certificate_sound certificate4139 profilesValid4139 numericValid4139 valid4139

def certificates : List RatCutBinCertificate := [certificate4128,certificate4129,certificate4130,certificate4131,certificate4132,certificate4133,certificate4134,certificate4135,certificate4136,certificate4137,certificate4138,certificate4139]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4128,List.forall_mem_cons.mpr ⟨sound4129,List.forall_mem_cons.mpr ⟨sound4130,List.forall_mem_cons.mpr ⟨sound4131,List.forall_mem_cons.mpr ⟨sound4132,List.forall_mem_cons.mpr ⟨sound4133,List.forall_mem_cons.mpr ⟨sound4134,List.forall_mem_cons.mpr ⟨sound4135,List.forall_mem_cons.mpr ⟨sound4136,List.forall_mem_cons.mpr ⟨sound4137,List.forall_mem_cons.mpr ⟨sound4138,List.forall_mem_cons.mpr ⟨sound4139,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch344
