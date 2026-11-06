import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch016
import Cycle12.MergedCutProfiles.Batch017
import Cycle12.MergedCutProfiles.Batch018
import Cycle12.MergedCutProfiles.Batch019

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch008

def retention96 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(634350660655962455/253857478123666143223),(307847250782034791/500000000000000000),4,(72334686335908737991/32000000000000000000),true,MergedCutProfiles.Batch016.profile656,![MergedCutProfiles.Batch016.profile656,MergedCutProfiles.Batch016.profile657,MergedCutProfiles.Batch016.profile658,MergedCutProfiles.Batch016.profile659,MergedCutProfiles.Batch016.profile660,MergedCutProfiles.Batch016.profile661,MergedCutProfiles.Batch016.profile662,MergedCutProfiles.Batch016.profile663,MergedCutProfiles.Batch016.profile664,MergedCutProfiles.Batch016.profile665,MergedCutProfiles.Batch016.profile666,MergedCutProfiles.Batch016.profile667,MergedCutProfiles.Batch016.profile668,MergedCutProfiles.Batch016.profile669,MergedCutProfiles.Batch016.profile670,MergedCutProfiles.Batch016.profile671]⟩
theorem profilesValid96 : retention96.ProfilesValid := by
  change ∀ j : Fin 16, (retention96.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch016.valid656
  · exact MergedCutProfiles.Batch016.valid657
  · exact MergedCutProfiles.Batch016.valid658
  · exact MergedCutProfiles.Batch016.valid659
  · exact MergedCutProfiles.Batch016.valid660
  · exact MergedCutProfiles.Batch016.valid661
  · exact MergedCutProfiles.Batch016.valid662
  · exact MergedCutProfiles.Batch016.valid663
  · exact MergedCutProfiles.Batch016.valid664
  · exact MergedCutProfiles.Batch016.valid665
  · exact MergedCutProfiles.Batch016.valid666
  · exact MergedCutProfiles.Batch016.valid667
  · exact MergedCutProfiles.Batch016.valid668
  · exact MergedCutProfiles.Batch016.valid669
  · exact MergedCutProfiles.Batch016.valid670
  · exact MergedCutProfiles.Batch016.valid671
theorem numericValid96 : retention96.NumericValid := by decide +kernel
def certificate96 : RatCutBinCertificate := ⟨⟨retention96,(944227606103878461/500000000000000000),(9292470143341151/1000000000000000000),(247170379103520391/31250000000000000),(252147263830554027219/125000000000000000),(2251584276927777071/1000000000000000000)⟩,(999071358589919201/1000000000000000000),(517826276155325461/1000000000000000000),(7069210780709091/50000000000000000),(64707838864209281/1000000000000000000)⟩
theorem valid96 : certificate96.Valid := by decide +kernel
theorem sound96 : certificate96.Sound := rat_cut_bin_certificate_sound certificate96 profilesValid96 numericValid96 valid96

def retention97 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(1225046682000000000/253857478123666143223),(126870132131192491/200000000000000000),4,(579732163006825231311/256000000000000000000),true,MergedCutProfiles.Batch016.profile672,![MergedCutProfiles.Batch016.profile672,MergedCutProfiles.Batch016.profile673,MergedCutProfiles.Batch016.profile674,MergedCutProfiles.Batch016.profile675,MergedCutProfiles.Batch016.profile676,MergedCutProfiles.Batch016.profile677,MergedCutProfiles.Batch016.profile678,MergedCutProfiles.Batch016.profile679,MergedCutProfiles.Batch017.profile680,MergedCutProfiles.Batch017.profile681,MergedCutProfiles.Batch017.profile682,MergedCutProfiles.Batch017.profile683,MergedCutProfiles.Batch017.profile684,MergedCutProfiles.Batch017.profile685,MergedCutProfiles.Batch017.profile686,MergedCutProfiles.Batch017.profile687]⟩
theorem profilesValid97 : retention97.ProfilesValid := by
  change ∀ j : Fin 16, (retention97.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch016.valid672
  · exact MergedCutProfiles.Batch016.valid673
  · exact MergedCutProfiles.Batch016.valid674
  · exact MergedCutProfiles.Batch016.valid675
  · exact MergedCutProfiles.Batch016.valid676
  · exact MergedCutProfiles.Batch016.valid677
  · exact MergedCutProfiles.Batch016.valid678
  · exact MergedCutProfiles.Batch016.valid679
  · exact MergedCutProfiles.Batch017.valid680
  · exact MergedCutProfiles.Batch017.valid681
  · exact MergedCutProfiles.Batch017.valid682
  · exact MergedCutProfiles.Batch017.valid683
  · exact MergedCutProfiles.Batch017.valid684
  · exact MergedCutProfiles.Batch017.valid685
  · exact MergedCutProfiles.Batch017.valid686
  · exact MergedCutProfiles.Batch017.valid687
theorem numericValid97 : retention97.NumericValid := by decide +kernel
def certificate97 : RatCutBinCertificate := ⟨⟨retention97,(944227606103878461/500000000000000000),(9292470143341151/1000000000000000000),(247170379103520391/31250000000000000),(252147263830554027219/125000000000000000),(2255704091164249263/1000000000000000000)⟩,(999071358589919201/1000000000000000000),(507300807660556691/1000000000000000000),(148418880702330773/1000000000000000000),(68403648404310191/1000000000000000000)⟩
theorem valid97 : certificate97.Valid := by decide +kernel
theorem sound97 : certificate97.Sound := rat_cut_bin_certificate_sound certificate97 profilesValid97 numericValid97 valid97

def retention98 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(1648850497553751396/253857478123666143223),(612523341/500000000),(49/20),(18049695720870234153/8000000000000000000),true,MergedCutProfiles.Batch017.profile688,![MergedCutProfiles.Batch017.profile688,MergedCutProfiles.Batch017.profile689,MergedCutProfiles.Batch016.profile675,MergedCutProfiles.Batch017.profile690,MergedCutProfiles.Batch016.profile668,MergedCutProfiles.Batch017.profile691,MergedCutProfiles.Batch017.profile692,MergedCutProfiles.Batch017.profile693,MergedCutProfiles.Batch017.profile683,MergedCutProfiles.Batch017.profile694,MergedCutProfiles.Batch017.profile695,MergedCutProfiles.Batch017.profile687,MergedCutProfiles.Batch017.profile696,MergedCutProfiles.Batch017.profile697,MergedCutProfiles.Batch017.profile698,MergedCutProfiles.Batch017.profile699]⟩
theorem profilesValid98 : retention98.ProfilesValid := by
  change ∀ j : Fin 16, (retention98.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch017.valid688
  · exact MergedCutProfiles.Batch017.valid689
  · exact MergedCutProfiles.Batch016.valid675
  · exact MergedCutProfiles.Batch017.valid690
  · exact MergedCutProfiles.Batch016.valid668
  · exact MergedCutProfiles.Batch017.valid691
  · exact MergedCutProfiles.Batch017.valid692
  · exact MergedCutProfiles.Batch017.valid693
  · exact MergedCutProfiles.Batch017.valid683
  · exact MergedCutProfiles.Batch017.valid694
  · exact MergedCutProfiles.Batch017.valid695
  · exact MergedCutProfiles.Batch017.valid687
  · exact MergedCutProfiles.Batch017.valid696
  · exact MergedCutProfiles.Batch017.valid697
  · exact MergedCutProfiles.Batch017.valid698
  · exact MergedCutProfiles.Batch017.valid699
theorem numericValid98 : retention98.NumericValid := by decide +kernel
def certificate98 : RatCutBinCertificate := ⟨⟨retention98,(944227606103878461/500000000000000000),(9292470143341151/1000000000000000000),(247170379103520391/31250000000000000),(252147263830554027219/125000000000000000),(562694057725834957/250000000000000000)⟩,(999071358589919201/1000000000000000000),(71126990185345109/200000000000000000),(69171682086002339/250000000000000000),(97205955631811367/500000000000000000)⟩
theorem valid98 : certificate98.Valid := by decide +kernel
theorem sound98 : certificate98.Sound := rat_cut_bin_certificate_sound certificate98 profilesValid98 numericValid98 valid98

def retention99 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(22133996498656045365/253857478123666143223),(412212624388437849/250000000000000000),(41/20),(106006488953635920843161312073247437093/54961683251791713200000000000000000000),false,MergedCutProfiles.Batch017.profile700,(fun _ => MergedCutProfiles.Batch017.profile700)⟩
theorem profilesValid99 : retention99.ProfilesValid := by
  exact MergedCutProfiles.Batch017.valid700
theorem numericValid99 : retention99.NumericValid := by decide +kernel
def certificate99 : RatCutBinCertificate := ⟨⟨retention99,(944227606103878461/500000000000000000),(9292470143341151/1000000000000000000),(247170379103520391/31250000000000000),(252147263830554027219/125000000000000000),(962093064727955203/500000000000000000)⟩,(999071358589919201/1000000000000000000),(366668800934968437/1000000000000000000),(265450146325395753/1000000000000000000),(24350468724605819/125000000000000000)⟩
theorem valid99 : certificate99.Valid := by decide +kernel
theorem sound99 : certificate99.Sound := rat_cut_bin_certificate_sound certificate99 profilesValid99 numericValid99 valid99

def retention100 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(64000000000000000000/253857478123666143223),(4426799299731209073/200000000000000000),1,(264104373440756554135126112820438457/177071971989248362920000000000000000),false,MergedCutProfiles.Batch017.profile701,(fun _ => MergedCutProfiles.Batch017.profile701)⟩
theorem profilesValid100 : retention100.ProfilesValid := by
  exact MergedCutProfiles.Batch017.valid701
theorem numericValid100 : retention100.NumericValid := by decide +kernel
def certificate100 : RatCutBinCertificate := ⟨⟨retention100,(944227606103878461/500000000000000000),(9292470143341151/1000000000000000000),(247170379103520391/31250000000000000),(252147263830554027219/125000000000000000),(1489289960768655743/1000000000000000000)⟩,(999071358589919201/1000000000000000000),(303241369642742711/1000000000000000000),(83725497934503769/250000000000000000),(29179902216527969/62500000000000000)⟩
theorem valid100 : certificate100.Valid := by decide +kernel
theorem sound100 : certificate100.Sound := rat_cut_bin_certificate_sound certificate100 profilesValid100 numericValid100 valid100

def retention101 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(1/2),64,1,(255369839288059878534814821034680834799/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch017.profile702,(fun _ => MergedCutProfiles.Batch017.profile702)⟩
theorem profilesValid101 : retention101.ProfilesValid := by
  exact MergedCutProfiles.Batch017.valid702
theorem numericValid101 : retention101.NumericValid := by decide +kernel
def certificate101 : RatCutBinCertificate := ⟨⟨retention101,(944227606103878461/500000000000000000),(9292470143341151/1000000000000000000),(247170379103520391/31250000000000000),(252147263830554027219/125000000000000000),(995319770941991571/1000000000000000000)⟩,(999071358589919201/1000000000000000000),(6879767816280821/15625000000000000),(198517766645671359/1000000000000000000),(24297583106451159/125000000000000000)⟩
theorem valid101 : certificate101.Valid := by decide +kernel
theorem sound101 : certificate101.Sound := rat_cut_bin_certificate_sound certificate101 profilesValid101 numericValid101 valid101

def retention102 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(64000000000000000000/253857478123666143223),(3411859671637580543/1000000000000000000),(13/10),(2046625137830959923622578205965607852159/1364743868655032217200000000000000000000),false,MergedCutProfiles.Batch017.profile701,(fun _ => MergedCutProfiles.Batch017.profile701)⟩
theorem profilesValid102 : retention102.ProfilesValid := by
  exact MergedCutProfiles.Batch017.valid701
theorem numericValid102 : retention102.NumericValid := by decide +kernel
def certificate102 : RatCutBinCertificate := ⟨⟨retention102,(1125634264103878461/500000000000000000),(9292470143341151/1000000000000000000),(247170379103520391/31250000000000000),(252147263830554027219/125000000000000000),(1496202075022589961/1000000000000000000)⟩,(499446472386422489/500000000000000000),(26377720147486929/100000000000000000),(19232019304303479/50000000000000000),(87766498285083209/250000000000000000)⟩
theorem valid102 : certificate102.Valid := by decide +kernel
theorem sound102 : certificate102.Sound := rat_cut_bin_certificate_sound certificate102 profilesValid102 numericValid102 valid102

def retention103 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(1/2),64,1,(255369839288059878534814821034680834799/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch017.profile702,(fun _ => MergedCutProfiles.Batch017.profile702)⟩
theorem profilesValid103 : retention103.ProfilesValid := by
  exact MergedCutProfiles.Batch017.valid702
theorem numericValid103 : retention103.NumericValid := by decide +kernel
def certificate103 : RatCutBinCertificate := ⟨⟨retention103,(1125634264103878461/500000000000000000),(9292470143341151/1000000000000000000),(247170379103520391/31250000000000000),(252147263830554027219/125000000000000000),(497446758689694309/500000000000000000)⟩,(499446472386422489/500000000000000000),(396689685173465309/1000000000000000000),(236529168116514709/1000000000000000000),(231460902167839741/1000000000000000000)⟩
theorem valid103 : certificate103.Valid := by decide +kernel
theorem sound103 : certificate103.Sound := rat_cut_bin_certificate_sound certificate103 profilesValid103 numericValid103 valid103

def retention104 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(634827510445145371/222081867547298675643),(622318900544206813/1000000000000000000),4,(145049608936912104253/64000000000000000000),true,MergedCutProfiles.Batch017.profile703,![MergedCutProfiles.Batch017.profile703,MergedCutProfiles.Batch017.profile704,MergedCutProfiles.Batch017.profile705,MergedCutProfiles.Batch017.profile706,MergedCutProfiles.Batch017.profile707,MergedCutProfiles.Batch017.profile708,MergedCutProfiles.Batch017.profile709,MergedCutProfiles.Batch017.profile710,MergedCutProfiles.Batch017.profile711,MergedCutProfiles.Batch017.profile712,MergedCutProfiles.Batch017.profile713,MergedCutProfiles.Batch017.profile714,MergedCutProfiles.Batch017.profile715,MergedCutProfiles.Batch017.profile716,MergedCutProfiles.Batch017.profile717,MergedCutProfiles.Batch017.profile718]⟩
theorem profilesValid104 : retention104.ProfilesValid := by
  change ∀ j : Fin 16, (retention104.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch017.valid703
  · exact MergedCutProfiles.Batch017.valid704
  · exact MergedCutProfiles.Batch017.valid705
  · exact MergedCutProfiles.Batch017.valid706
  · exact MergedCutProfiles.Batch017.valid707
  · exact MergedCutProfiles.Batch017.valid708
  · exact MergedCutProfiles.Batch017.valid709
  · exact MergedCutProfiles.Batch017.valid710
  · exact MergedCutProfiles.Batch017.valid711
  · exact MergedCutProfiles.Batch017.valid712
  · exact MergedCutProfiles.Batch017.valid713
  · exact MergedCutProfiles.Batch017.valid714
  · exact MergedCutProfiles.Batch017.valid715
  · exact MergedCutProfiles.Batch017.valid716
  · exact MergedCutProfiles.Batch017.valid717
  · exact MergedCutProfiles.Batch017.valid718
theorem numericValid104 : retention104.NumericValid := by decide +kernel
def certificate104 : RatCutBinCertificate := ⟨⟨retention104,(947937277989206349/500000000000000000),(1060946273715283/100000000000000000),(2002589223420813337/250000000000000000),(893623095659599263587/500000000000000000),(28204450170888271/12500000000000000)⟩,(998949067136812011/1000000000000000000),(102141378053873527/200000000000000000),(2922375046196937/20000000000000000),(33556816299067327/500000000000000000)⟩
theorem valid104 : certificate104.Valid := by decide +kernel
theorem sound104 : certificate104.Sound := rat_cut_bin_certificate_sound certificate104 profilesValid104 numericValid104 valid104

def retention105 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(403527526000000000/74027289182432891881),(634827510445145371/1000000000000000000),4,(115804587256824823463/51200000000000000000),true,MergedCutProfiles.Batch017.profile719,![MergedCutProfiles.Batch017.profile719,MergedCutProfiles.Batch018.profile720,MergedCutProfiles.Batch018.profile721,MergedCutProfiles.Batch018.profile722,MergedCutProfiles.Batch018.profile723,MergedCutProfiles.Batch018.profile724,MergedCutProfiles.Batch018.profile725,MergedCutProfiles.Batch017.profile717,MergedCutProfiles.Batch018.profile726,MergedCutProfiles.Batch018.profile727,MergedCutProfiles.Batch018.profile728,MergedCutProfiles.Batch018.profile729,MergedCutProfiles.Batch018.profile730,MergedCutProfiles.Batch018.profile731,MergedCutProfiles.Batch018.profile732,MergedCutProfiles.Batch018.profile733]⟩
theorem profilesValid105 : retention105.ProfilesValid := by
  change ∀ j : Fin 16, (retention105.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch017.valid719
  · exact MergedCutProfiles.Batch018.valid720
  · exact MergedCutProfiles.Batch018.valid721
  · exact MergedCutProfiles.Batch018.valid722
  · exact MergedCutProfiles.Batch018.valid723
  · exact MergedCutProfiles.Batch018.valid724
  · exact MergedCutProfiles.Batch018.valid725
  · exact MergedCutProfiles.Batch017.valid717
  · exact MergedCutProfiles.Batch018.valid726
  · exact MergedCutProfiles.Batch018.valid727
  · exact MergedCutProfiles.Batch018.valid728
  · exact MergedCutProfiles.Batch018.valid729
  · exact MergedCutProfiles.Batch018.valid730
  · exact MergedCutProfiles.Batch018.valid731
  · exact MergedCutProfiles.Batch018.valid732
  · exact MergedCutProfiles.Batch018.valid733
theorem numericValid105 : retention105.NumericValid := by decide +kernel
def certificate105 : RatCutBinCertificate := ⟨⟨retention105,(947937277989206349/500000000000000000),(1060946273715283/100000000000000000),(2002589223420813337/250000000000000000),(893623095659599263587/500000000000000000),(450352843872724947/200000000000000000)⟩,(998949067136812011/1000000000000000000),(505461903656978437/1000000000000000000),(74835094633898013/500000000000000000),(68881266560230177/1000000000000000000)⟩
theorem valid105 : certificate105.Valid := by decide +kernel
theorem sound105 : certificate105.Sound := rat_cut_bin_certificate_sound certificate105 profilesValid105 numericValid105 valid105

def retention106 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(483290777850276887/74027289182432891881),(605291289/500000000),(49/20),(18019648588092124479/8000000000000000000),true,MergedCutProfiles.Batch018.profile734,![MergedCutProfiles.Batch018.profile734,MergedCutProfiles.Batch018.profile735,MergedCutProfiles.Batch018.profile736,MergedCutProfiles.Batch017.profile711,MergedCutProfiles.Batch018.profile724,MergedCutProfiles.Batch018.profile737,MergedCutProfiles.Batch017.profile718,MergedCutProfiles.Batch018.profile738,MergedCutProfiles.Batch018.profile739,MergedCutProfiles.Batch018.profile729,MergedCutProfiles.Batch018.profile740,MergedCutProfiles.Batch018.profile741,MergedCutProfiles.Batch018.profile742,MergedCutProfiles.Batch018.profile743,MergedCutProfiles.Batch018.profile744,MergedCutProfiles.Batch018.profile745]⟩
theorem profilesValid106 : retention106.ProfilesValid := by
  change ∀ j : Fin 16, (retention106.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch018.valid734
  · exact MergedCutProfiles.Batch018.valid735
  · exact MergedCutProfiles.Batch018.valid736
  · exact MergedCutProfiles.Batch017.valid711
  · exact MergedCutProfiles.Batch018.valid724
  · exact MergedCutProfiles.Batch018.valid737
  · exact MergedCutProfiles.Batch017.valid718
  · exact MergedCutProfiles.Batch018.valid738
  · exact MergedCutProfiles.Batch018.valid739
  · exact MergedCutProfiles.Batch018.valid729
  · exact MergedCutProfiles.Batch018.valid740
  · exact MergedCutProfiles.Batch018.valid741
  · exact MergedCutProfiles.Batch018.valid742
  · exact MergedCutProfiles.Batch018.valid743
  · exact MergedCutProfiles.Batch018.valid744
  · exact MergedCutProfiles.Batch018.valid745
theorem numericValid106 : retention106.NumericValid := by decide +kernel
def certificate106 : RatCutBinCertificate := ⟨⟨retention106,(947937277989206349/500000000000000000),(1060946273715283/100000000000000000),(2002589223420813337/250000000000000000),(893623095659599263587/500000000000000000),(1123152024356864127/500000000000000000)⟩,(998949067136812011/1000000000000000000),(357581150413265883/1000000000000000000),(68670058113390081/250000000000000000),(192144047825738301/1000000000000000000)⟩
theorem valid106 : certificate106.Valid := by decide +kernel
theorem sound106 : certificate106.Sound := rat_cut_bin_certificate_sound certificate106 profilesValid106 numericValid106 valid106

def retention107 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(11372452609446699752/222081867547298675643),(1449872333550830661/1000000000000000000),(11/5),(2617399409896508314761/1280000000000000000000),true,MergedCutProfiles.Batch018.profile746,![MergedCutProfiles.Batch018.profile746,MergedCutProfiles.Batch018.profile747,MergedCutProfiles.Batch018.profile748,MergedCutProfiles.Batch018.profile749,MergedCutProfiles.Batch018.profile750,MergedCutProfiles.Batch018.profile751,MergedCutProfiles.Batch018.profile752,MergedCutProfiles.Batch018.profile753,MergedCutProfiles.Batch018.profile754,MergedCutProfiles.Batch018.profile755,MergedCutProfiles.Batch018.profile756,MergedCutProfiles.Batch018.profile757,MergedCutProfiles.Batch018.profile758,MergedCutProfiles.Batch018.profile759,MergedCutProfiles.Batch019.profile760,MergedCutProfiles.Batch019.profile761]⟩
theorem profilesValid107 : retention107.ProfilesValid := by
  change ∀ j : Fin 16, (retention107.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch018.valid746
  · exact MergedCutProfiles.Batch018.valid747
  · exact MergedCutProfiles.Batch018.valid748
  · exact MergedCutProfiles.Batch018.valid749
  · exact MergedCutProfiles.Batch018.valid750
  · exact MergedCutProfiles.Batch018.valid751
  · exact MergedCutProfiles.Batch018.valid752
  · exact MergedCutProfiles.Batch018.valid753
  · exact MergedCutProfiles.Batch018.valid754
  · exact MergedCutProfiles.Batch018.valid755
  · exact MergedCutProfiles.Batch018.valid756
  · exact MergedCutProfiles.Batch018.valid757
  · exact MergedCutProfiles.Batch018.valid758
  · exact MergedCutProfiles.Batch018.valid759
  · exact MergedCutProfiles.Batch019.valid760
  · exact MergedCutProfiles.Batch019.valid761
theorem numericValid107 : retention107.NumericValid := by decide +kernel
def certificate107 : RatCutBinCertificate := ⟨⟨retention107,(947937277989206349/500000000000000000),(1060946273715283/100000000000000000),(2002589223420813337/250000000000000000),(893623095659599263587/500000000000000000),(509829755648005829/250000000000000000)⟩,(998949067136812011/1000000000000000000),(363986346132079319/1000000000000000000),(268150988751609049/1000000000000000000),(48091754748796461/250000000000000000)⟩
theorem valid107 : certificate107.Valid := by decide +kernel
theorem sound107 : certificate107.Sound := rat_cut_bin_certificate_sound certificate107 profilesValid107 numericValid107 valid107

def certificates : List RatCutBinCertificate := [certificate96,certificate97,certificate98,certificate99,certificate100,certificate101,certificate102,certificate103,certificate104,certificate105,certificate106,certificate107]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound96,List.forall_mem_cons.mpr ⟨sound97,List.forall_mem_cons.mpr ⟨sound98,List.forall_mem_cons.mpr ⟨sound99,List.forall_mem_cons.mpr ⟨sound100,List.forall_mem_cons.mpr ⟨sound101,List.forall_mem_cons.mpr ⟨sound102,List.forall_mem_cons.mpr ⟨sound103,List.forall_mem_cons.mpr ⟨sound104,List.forall_mem_cons.mpr ⟨sound105,List.forall_mem_cons.mpr ⟨sound106,List.forall_mem_cons.mpr ⟨sound107,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch008
