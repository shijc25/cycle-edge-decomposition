import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch392
import Cycle12.MergedCutProfiles.Batch393
import Cycle12.MergedCutProfiles.Batch394

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch210

def retention2520 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(14087675208130537496/28179275827658174181),(6974096637688384899/500000000000000000),1,(3430342404499830485902502494026455801/3487048318844192449500000000000000000),false,MergedCutProfiles.Batch392.profile15709,(fun _ => MergedCutProfiles.Batch392.profile15709)⟩
theorem profilesValid2520 : retention2520.ProfilesValid := by
  exact MergedCutProfiles.Batch392.valid15709
theorem numericValid2520 : retention2520.NumericValid := by decide +kernel
def certificate2520 : RatCutBinCertificate := ⟨⟨retention2520,(557613105836908149/250000000000000000),(161735409484216873/1000000000000000000),(7383208782333271881/500000000000000000),(418600884141280149851/1000000000000000000),(119913435861247921/125000000000000000)⟩,(7777303772568247/7812500000000000),(212104958202605357/500000000000000000),(53004512162647093/250000000000000000),(47352364004187593/250000000000000000)⟩
theorem valid2520 : certificate2520.Valid := by decide +kernel
theorem sound2520 : certificate2520.Sound := rat_cut_bin_certificate_sound certificate2520 profilesValid2520 numericValid2520 valid2520

def retention2521 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(1/2),(1760959401016317187/125000000000000000),1,(55436785027486829275049102243800737423/56350700832522149984000000000000000000),false,MergedCutProfiles.Batch392.profile15710,(fun _ => MergedCutProfiles.Batch392.profile15710)⟩
theorem profilesValid2521 : retention2521.ProfilesValid := by
  exact MergedCutProfiles.Batch392.valid15710
theorem numericValid2521 : retention2521.NumericValid := by decide +kernel
def certificate2521 : RatCutBinCertificate := ⟨⟨retention2521,(557613105836908149/250000000000000000),(161735409484216873/1000000000000000000),(7383208782333271881/500000000000000000),(418600884141280149851/1000000000000000000),(38374040109376737/40000000000000000)⟩,(7777303772568247/7812500000000000),(53000373448359443/125000000000000000),(106097770998293593/500000000000000000),(189697264479814093/1000000000000000000)⟩
theorem valid2521 : certificate2521.Valid := by decide +kernel
theorem sound2521 : certificate2521.Sound := rat_cut_bin_certificate_sound certificate2521 profilesValid2521 numericValid2521 valid2521

def retention2522 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(467441006873552755/1043676882505858303),(2628934007397505761/500000000000000000),(21/20),(752180615665492037519963721188094227133/701049068639334869600000000000000000000),false,MergedCutProfiles.Batch392.profile15711,(fun _ => MergedCutProfiles.Batch392.profile15711)⟩
theorem profilesValid2522 : retention2522.ProfilesValid := by
  exact MergedCutProfiles.Batch392.valid15711
theorem numericValid2522 : retention2522.NumericValid := by decide +kernel
def certificate2522 : RatCutBinCertificate := ⟨⟨retention2522,(622170130586908149/250000000000000000),(161735409484216873/1000000000000000000),(7383208782333271881/500000000000000000),(418600884141280149851/1000000000000000000),(522156259759730437/500000000000000000)⟩,(994972826364570823/1000000000000000000),(113388439146085331/500000000000000000),(682158542820417/1562500000000000),(36592621335585481/100000000000000000)⟩
theorem valid2522 : certificate2522.Valid := by decide +kernel
theorem sound2522 : certificate2522.Sound := rat_cut_bin_certificate_sound certificate2522 profilesValid2522 numericValid2522 valid2522

def retention2523 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(13941333319959467125/28179275827658174181),(2524181437117184877/200000000000000000),1,(57953444126271569065725388341132681/58430125859194094375000000000000000),false,MergedCutProfiles.Batch392.profile15712,(fun _ => MergedCutProfiles.Batch392.profile15712)⟩
theorem profilesValid2523 : retention2523.ProfilesValid := by
  exact MergedCutProfiles.Batch392.valid15712
theorem numericValid2523 : retention2523.NumericValid := by decide +kernel
def certificate2523 : RatCutBinCertificate := ⟨⟨retention2523,(622170130586908149/250000000000000000),(161735409484216873/1000000000000000000),(7383208782333271881/500000000000000000),(418600884141280149851/1000000000000000000),(192916538718355583/200000000000000000)⟩,(994972826364570823/1000000000000000000),(24552164859623973/100000000000000000),(204789965730775327/500000000000000000),(182551553420980709/500000000000000000)⟩
theorem valid2523 : certificate2523.Valid := by decide +kernel
theorem sound2523 : certificate2523.Sound := rat_cut_bin_certificate_sound certificate2523 profilesValid2523 numericValid2523 valid2523

def retention2524 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(14080746653159061797/28179275827658174181),(111530666559675737/8000000000000000),1,(54884471670387515811703281422940889179/55765333279837868500000000000000000000),false,MergedCutProfiles.Batch392.profile15713,(fun _ => MergedCutProfiles.Batch392.profile15713)⟩
theorem profilesValid2524 : retention2524.ProfilesValid := by
  exact MergedCutProfiles.Batch392.valid15713
theorem numericValid2524 : retention2524.NumericValid := by decide +kernel
def certificate2524 : RatCutBinCertificate := ⟨⟨retention2524,(622170130586908149/250000000000000000),(161735409484216873/1000000000000000000),(7383208782333271881/500000000000000000),(418600884141280149851/1000000000000000000),(478472529426013891/500000000000000000)⟩,(994972826364570823/1000000000000000000),(123740611306440333/500000000000000000),(101710097690271303/250000000000000000),(36241758936811843/100000000000000000)⟩
theorem valid2524 : certificate2524.Valid := by decide +kernel
theorem sound2524 : certificate2524.Sound := rat_cut_bin_certificate_sound certificate2524 profilesValid2524 numericValid2524 valid2524

def retention2525 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(1/2),(14080746653159061797/1000000000000000000),1,(2216361076429098798888897190094791899/2252919464505449887520000000000000000),false,MergedCutProfiles.Batch392.profile15710,(fun _ => MergedCutProfiles.Batch392.profile15710)⟩
theorem profilesValid2525 : retention2525.ProfilesValid := by
  exact MergedCutProfiles.Batch392.valid15710
theorem numericValid2525 : retention2525.NumericValid := by decide +kernel
def certificate2525 : RatCutBinCertificate := ⟨⟨retention2525,(622170130586908149/250000000000000000),(161735409484216873/1000000000000000000),(7383208782333271881/500000000000000000),(418600884141280149851/1000000000000000000),(478256906493431049/500000000000000000)⟩,(994972826364570823/1000000000000000000),(247592799939322703/1000000000000000000),(406684863855972053/1000000000000000000),(181178619738042673/500000000000000000)⟩
theorem valid2525 : certificate2525.Valid := by decide +kernel
theorem sound2525 : certificate2525.Sound := rat_cut_bin_certificate_sound certificate2525 profilesValid2525 numericValid2525 valid2525

def retention2526 : RatCutRetentionCertificate := ⟨(57/1000),(29/500),(902137290667558439/27052727392284285148),(35728209531388453/40000000000000000),(14/5),(33908104460856827953/16000000000000000000),true,MergedCutProfiles.Batch392.profile15714,![MergedCutProfiles.Batch392.profile15714,MergedCutProfiles.Batch392.profile15715,MergedCutProfiles.Batch392.profile15716,MergedCutProfiles.Batch392.profile15717,MergedCutProfiles.Batch392.profile15718,MergedCutProfiles.Batch392.profile15719,MergedCutProfiles.Batch393.profile15720,MergedCutProfiles.Batch393.profile15721,MergedCutProfiles.Batch393.profile15722,MergedCutProfiles.Batch393.profile15723,MergedCutProfiles.Batch393.profile15724,MergedCutProfiles.Batch393.profile15725,MergedCutProfiles.Batch393.profile15726,MergedCutProfiles.Batch393.profile15727,MergedCutProfiles.Batch393.profile15728,MergedCutProfiles.Batch393.profile15729]⟩
theorem profilesValid2526 : retention2526.ProfilesValid := by
  change ∀ j : Fin 16, (retention2526.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch392.valid15714
  · exact MergedCutProfiles.Batch392.valid15715
  · exact MergedCutProfiles.Batch392.valid15716
  · exact MergedCutProfiles.Batch392.valid15717
  · exact MergedCutProfiles.Batch392.valid15718
  · exact MergedCutProfiles.Batch392.valid15719
  · exact MergedCutProfiles.Batch393.valid15720
  · exact MergedCutProfiles.Batch393.valid15721
  · exact MergedCutProfiles.Batch393.valid15722
  · exact MergedCutProfiles.Batch393.valid15723
  · exact MergedCutProfiles.Batch393.valid15724
  · exact MergedCutProfiles.Batch393.valid15725
  · exact MergedCutProfiles.Batch393.valid15726
  · exact MergedCutProfiles.Batch393.valid15727
  · exact MergedCutProfiles.Batch393.valid15728
  · exact MergedCutProfiles.Batch393.valid15729
theorem numericValid2526 : retention2526.NumericValid := by decide +kernel
def certificate2526 : RatCutBinCertificate := ⟨⟨retention2526,(2243427814624929509/1000000000000000000),(168442616661570077/1000000000000000000),(375756560868537411/25000000000000000),(204531460842563318341/500000000000000000),(512211927995874627/250000000000000000)⟩,(39815941456426527/40000000000000000),(322026317439859171/1000000000000000000),(9783309482966681/31250000000000000),(22031924136598833/125000000000000000)⟩
theorem valid2526 : certificate2526.Valid := by decide +kernel
theorem sound2526 : certificate2526.Sound := rat_cut_bin_certificate_sound certificate2526 profilesValid2526 numericValid2526 valid2526

def retention2527 : RatCutRetentionCertificate := ⟨(57/1000),(29/500),(246482864000000000/6763181848071071287),(902137290667558439/1000000000000000000),(11/4),(8410252098510475051/4000000000000000000),true,MergedCutProfiles.Batch393.profile15730,![MergedCutProfiles.Batch393.profile15730,MergedCutProfiles.Batch393.profile15731,MergedCutProfiles.Batch393.profile15732,MergedCutProfiles.Batch393.profile15733,MergedCutProfiles.Batch393.profile15734,MergedCutProfiles.Batch393.profile15735,MergedCutProfiles.Batch393.profile15736,MergedCutProfiles.Batch393.profile15737,MergedCutProfiles.Batch393.profile15738,MergedCutProfiles.Batch393.profile15739,MergedCutProfiles.Batch393.profile15740,MergedCutProfiles.Batch393.profile15741,MergedCutProfiles.Batch393.profile15742,MergedCutProfiles.Batch393.profile15743,MergedCutProfiles.Batch393.profile15744,MergedCutProfiles.Batch393.profile15745]⟩
theorem profilesValid2527 : retention2527.ProfilesValid := by
  change ∀ j : Fin 16, (retention2527.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch393.valid15730
  · exact MergedCutProfiles.Batch393.valid15731
  · exact MergedCutProfiles.Batch393.valid15732
  · exact MergedCutProfiles.Batch393.valid15733
  · exact MergedCutProfiles.Batch393.valid15734
  · exact MergedCutProfiles.Batch393.valid15735
  · exact MergedCutProfiles.Batch393.valid15736
  · exact MergedCutProfiles.Batch393.valid15737
  · exact MergedCutProfiles.Batch393.valid15738
  · exact MergedCutProfiles.Batch393.valid15739
  · exact MergedCutProfiles.Batch393.valid15740
  · exact MergedCutProfiles.Batch393.valid15741
  · exact MergedCutProfiles.Batch393.valid15742
  · exact MergedCutProfiles.Batch393.valid15743
  · exact MergedCutProfiles.Batch393.valid15744
  · exact MergedCutProfiles.Batch393.valid15745
theorem numericValid2527 : retention2527.NumericValid := by decide +kernel
def certificate2527 : RatCutBinCertificate := ⟨⟨retention2527,(2243427814624929509/1000000000000000000),(168442616661570077/1000000000000000000),(375756560868537411/25000000000000000),(204531460842563318341/500000000000000000),(2033411415890872417/1000000000000000000)⟩,(39815941456426527/40000000000000000),(323123460113049271/1000000000000000000),(311824949477618359/1000000000000000000),(88326876027250079/500000000000000000)⟩
theorem valid2527 : certificate2527.Valid := by decide +kernel
theorem sound2527 : certificate2527.Sound := rat_cut_bin_certificate_sound certificate2527 profilesValid2527 numericValid2527 valid2527

def retention2528 : RatCutRetentionCertificate := ⟨(57/1000),(29/500),(1100778936738198701/27052727392284285148),(15405179/15625000),(13/5),(4188188365495085207/2000000000000000000),true,MergedCutProfiles.Batch393.profile15746,![MergedCutProfiles.Batch393.profile15746,MergedCutProfiles.Batch393.profile15747,MergedCutProfiles.Batch393.profile15748,MergedCutProfiles.Batch393.profile15749,MergedCutProfiles.Batch393.profile15750,MergedCutProfiles.Batch393.profile15751,MergedCutProfiles.Batch393.profile15752,MergedCutProfiles.Batch393.profile15753,MergedCutProfiles.Batch393.profile15739,MergedCutProfiles.Batch393.profile15754,MergedCutProfiles.Batch393.profile15755,MergedCutProfiles.Batch393.profile15756,MergedCutProfiles.Batch393.profile15757,MergedCutProfiles.Batch393.profile15758,MergedCutProfiles.Batch393.profile15759,MergedCutProfiles.Batch394.profile15760]⟩
theorem profilesValid2528 : retention2528.ProfilesValid := by
  change ∀ j : Fin 16, (retention2528.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch393.valid15746
  · exact MergedCutProfiles.Batch393.valid15747
  · exact MergedCutProfiles.Batch393.valid15748
  · exact MergedCutProfiles.Batch393.valid15749
  · exact MergedCutProfiles.Batch393.valid15750
  · exact MergedCutProfiles.Batch393.valid15751
  · exact MergedCutProfiles.Batch393.valid15752
  · exact MergedCutProfiles.Batch393.valid15753
  · exact MergedCutProfiles.Batch393.valid15739
  · exact MergedCutProfiles.Batch393.valid15754
  · exact MergedCutProfiles.Batch393.valid15755
  · exact MergedCutProfiles.Batch393.valid15756
  · exact MergedCutProfiles.Batch393.valid15757
  · exact MergedCutProfiles.Batch393.valid15758
  · exact MergedCutProfiles.Batch393.valid15759
  · exact MergedCutProfiles.Batch394.valid15760
theorem numericValid2528 : retention2528.NumericValid := by decide +kernel
def certificate2528 : RatCutBinCertificate := ⟨⟨retention2528,(2243427814624929509/1000000000000000000),(168442616661570077/1000000000000000000),(375756560868537411/25000000000000000),(204531460842563318341/500000000000000000),(2028714829318706089/1000000000000000000)⟩,(39815941456426527/40000000000000000),(312392910033559741/1000000000000000000),(162061736715385779/500000000000000000),(96415315161629233/500000000000000000)⟩
theorem valid2528 : certificate2528.Valid := by decide +kernel
theorem sound2528 : certificate2528.Sound := rat_cut_bin_certificate_sound certificate2528 profilesValid2528 numericValid2528 valid2528

def retention2529 : RatCutRetentionCertificate := ⟨(57/1000),(29/500),(1082738381995606641/13526363696142142574),(1100778936738198701/1000000000000000000),(12/5),(629922300002403926041/320000000000000000000),true,MergedCutProfiles.Batch394.profile15761,![MergedCutProfiles.Batch394.profile15761,MergedCutProfiles.Batch394.profile15762,MergedCutProfiles.Batch394.profile15763,MergedCutProfiles.Batch394.profile15764,MergedCutProfiles.Batch393.profile15725,MergedCutProfiles.Batch394.profile15765,MergedCutProfiles.Batch394.profile15766,MergedCutProfiles.Batch394.profile15767,MergedCutProfiles.Batch394.profile15768,MergedCutProfiles.Batch394.profile15769,MergedCutProfiles.Batch394.profile15770,MergedCutProfiles.Batch394.profile15771,MergedCutProfiles.Batch394.profile15772,MergedCutProfiles.Batch394.profile15773,MergedCutProfiles.Batch394.profile15774,MergedCutProfiles.Batch394.profile15775]⟩
theorem profilesValid2529 : retention2529.ProfilesValid := by
  change ∀ j : Fin 16, (retention2529.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch394.valid15761
  · exact MergedCutProfiles.Batch394.valid15762
  · exact MergedCutProfiles.Batch394.valid15763
  · exact MergedCutProfiles.Batch394.valid15764
  · exact MergedCutProfiles.Batch393.valid15725
  · exact MergedCutProfiles.Batch394.valid15765
  · exact MergedCutProfiles.Batch394.valid15766
  · exact MergedCutProfiles.Batch394.valid15767
  · exact MergedCutProfiles.Batch394.valid15768
  · exact MergedCutProfiles.Batch394.valid15769
  · exact MergedCutProfiles.Batch394.valid15770
  · exact MergedCutProfiles.Batch394.valid15771
  · exact MergedCutProfiles.Batch394.valid15772
  · exact MergedCutProfiles.Batch394.valid15773
  · exact MergedCutProfiles.Batch394.valid15774
  · exact MergedCutProfiles.Batch394.valid15775
theorem numericValid2529 : retention2529.NumericValid := by decide +kernel
def certificate2529 : RatCutBinCertificate := ⟨⟨retention2529,(2243427814624929509/1000000000000000000),(168442616661570077/1000000000000000000),(375756560868537411/25000000000000000),(204531460842563318341/500000000000000000),(954078651465247221/500000000000000000)⟩,(39815941456426527/40000000000000000),(159210930361174237/500000000000000000),(63433825522579319/200000000000000000),(192782966825875723/1000000000000000000)⟩
theorem valid2529 : certificate2529.Valid := by decide +kernel
theorem sound2529 : certificate2529.Sound := rat_cut_bin_certificate_sound certificate2529 profilesValid2529 numericValid2529 valid2529

def retention2530 : RatCutRetentionCertificate := ⟨(57/1000),(29/500),(7973582526826774937/27052727392284285148),(1082738381995606641/500000000000000000),(3/2),(181393934131401925209/128000000000000000000),true,MergedCutProfiles.Batch394.profile15776,![MergedCutProfiles.Batch394.profile15776,MergedCutProfiles.Batch394.profile15777,MergedCutProfiles.Batch394.profile15778,MergedCutProfiles.Batch394.profile15779,MergedCutProfiles.Batch394.profile15780,MergedCutProfiles.Batch394.profile15781,MergedCutProfiles.Batch394.profile15782,MergedCutProfiles.Batch394.profile15783,MergedCutProfiles.Batch394.profile15784,MergedCutProfiles.Batch394.profile15785,MergedCutProfiles.Batch394.profile15786,MergedCutProfiles.Batch394.profile15787,MergedCutProfiles.Batch394.profile15788,MergedCutProfiles.Batch394.profile15789,MergedCutProfiles.Batch394.profile15790,MergedCutProfiles.Batch394.profile15791]⟩
theorem profilesValid2530 : retention2530.ProfilesValid := by
  change ∀ j : Fin 16, (retention2530.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch394.valid15776
  · exact MergedCutProfiles.Batch394.valid15777
  · exact MergedCutProfiles.Batch394.valid15778
  · exact MergedCutProfiles.Batch394.valid15779
  · exact MergedCutProfiles.Batch394.valid15780
  · exact MergedCutProfiles.Batch394.valid15781
  · exact MergedCutProfiles.Batch394.valid15782
  · exact MergedCutProfiles.Batch394.valid15783
  · exact MergedCutProfiles.Batch394.valid15784
  · exact MergedCutProfiles.Batch394.valid15785
  · exact MergedCutProfiles.Batch394.valid15786
  · exact MergedCutProfiles.Batch394.valid15787
  · exact MergedCutProfiles.Batch394.valid15788
  · exact MergedCutProfiles.Batch394.valid15789
  · exact MergedCutProfiles.Batch394.valid15790
  · exact MergedCutProfiles.Batch394.valid15791
theorem numericValid2530 : retention2530.NumericValid := by decide +kernel
def certificate2530 : RatCutBinCertificate := ⟨⟨retention2530,(2243427814624929509/1000000000000000000),(168442616661570077/1000000000000000000),(375756560868537411/25000000000000000),(204531460842563318341/500000000000000000),(689711264907104901/500000000000000000)⟩,(39815941456426527/40000000000000000),(360436436332655129/1000000000000000000),(6793890352216079/25000000000000000),(193739260146822441/1000000000000000000)⟩
theorem valid2530 : certificate2530.Valid := by decide +kernel
theorem sound2530 : certificate2530.Sound := rat_cut_bin_certificate_sound certificate2530 profilesValid2530 numericValid2530 valid2530

def retention2531 : RatCutRetentionCertificate := ⟨(57/1000),(29/500),(3181984574827565493/6763181848071071287),(7973582526826774937/1000000000000000000),1,(32713005183615491398001701704020413851/31894330107307099748000000000000000000),false,MergedCutProfiles.Batch394.profile15792,(fun _ => MergedCutProfiles.Batch394.profile15792)⟩
theorem profilesValid2531 : retention2531.ProfilesValid := by
  exact MergedCutProfiles.Batch394.valid15792
theorem numericValid2531 : retention2531.NumericValid := by decide +kernel
def certificate2531 : RatCutBinCertificate := ⟨⟨retention2531,(2243427814624929509/1000000000000000000),(168442616661570077/1000000000000000000),(375756560868537411/25000000000000000),(204531460842563318341/500000000000000000),(500262596450202269/500000000000000000)⟩,(39815941456426527/40000000000000000),(413830495887411503/1000000000000000000),(221046465858212047/1000000000000000000),(48884600321259139/250000000000000000)⟩
theorem valid2531 : certificate2531.Valid := by decide +kernel
theorem sound2531 : certificate2531.Sound := rat_cut_bin_certificate_sound certificate2531 profilesValid2531 numericValid2531 valid2531

def certificates : List RatCutBinCertificate := [certificate2520,certificate2521,certificate2522,certificate2523,certificate2524,certificate2525,certificate2526,certificate2527,certificate2528,certificate2529,certificate2530,certificate2531]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2520,List.forall_mem_cons.mpr ⟨sound2521,List.forall_mem_cons.mpr ⟨sound2522,List.forall_mem_cons.mpr ⟨sound2523,List.forall_mem_cons.mpr ⟨sound2524,List.forall_mem_cons.mpr ⟨sound2525,List.forall_mem_cons.mpr ⟨sound2526,List.forall_mem_cons.mpr ⟨sound2527,List.forall_mem_cons.mpr ⟨sound2528,List.forall_mem_cons.mpr ⟨sound2529,List.forall_mem_cons.mpr ⟨sound2530,List.forall_mem_cons.mpr ⟨sound2531,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch210
