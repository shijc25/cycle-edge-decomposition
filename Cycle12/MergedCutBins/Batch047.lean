import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch094
import Cycle12.MergedCutProfiles.Batch095
import Cycle12.MergedCutProfiles.Batch096

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch047

def retention564 : RatCutRetentionCertificate := ⟨(21/500),(169/4000),(6806238241234014049/27900829796345877247),(853505247037612859/500000000000000000),(7/4),(41828151720093997249394126100569511031/27312167905203611488000000000000000000),false,MergedCutProfiles.Batch094.profile3793,(fun _ => MergedCutProfiles.Batch094.profile3793)⟩
theorem profilesValid564 : retention564.ProfilesValid := by
  exact MergedCutProfiles.Batch094.valid3793
theorem numericValid564 : retention564.NumericValid := by decide +kernel
def certificate564 : RatCutBinCertificate := ⟨⟨retention564,(104322979946200783/50000000000000000),(20564159142100463/250000000000000000),(2341603643328142737/200000000000000000),(65421735753294979399/200000000000000000),(1505829123289855311/1000000000000000000)⟩,(62133518026871259/62500000000000000),(52509469997838631/125000000000000000),(53895830346592199/250000000000000000),(71525631862053671/500000000000000000)⟩
theorem valid564 : certificate564.Valid := by decide +kernel
theorem sound564 : certificate564.Sound := rat_cut_bin_certificate_sound certificate564 profilesValid564 numericValid564 valid564

def retention565 : RatCutRetentionCertificate := ⟨(21/500),(169/4000),(12739538484798497984/27900829796345877247),(6806238241234014049/1000000000000000000),1,(268107161837925182929/256000000000000000000),true,MergedCutProfiles.Batch094.profile3764,![MergedCutProfiles.Batch094.profile3764,MergedCutProfiles.Batch094.profile3794,MergedCutProfiles.Batch094.profile3795,MergedCutProfiles.Batch094.profile3796,MergedCutProfiles.Batch094.profile3797,MergedCutProfiles.Batch094.profile3798,MergedCutProfiles.Batch094.profile3799,MergedCutProfiles.Batch095.profile3800,MergedCutProfiles.Batch095.profile3801,MergedCutProfiles.Batch095.profile3802,MergedCutProfiles.Batch095.profile3803,MergedCutProfiles.Batch095.profile3804,MergedCutProfiles.Batch095.profile3805,MergedCutProfiles.Batch095.profile3806,MergedCutProfiles.Batch095.profile3807,MergedCutProfiles.Batch095.profile3808]⟩
theorem profilesValid565 : retention565.ProfilesValid := by
  change ∀ j : Fin 16, (retention565.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch094.valid3764
  · exact MergedCutProfiles.Batch094.valid3794
  · exact MergedCutProfiles.Batch094.valid3795
  · exact MergedCutProfiles.Batch094.valid3796
  · exact MergedCutProfiles.Batch094.valid3797
  · exact MergedCutProfiles.Batch094.valid3798
  · exact MergedCutProfiles.Batch094.valid3799
  · exact MergedCutProfiles.Batch095.valid3800
  · exact MergedCutProfiles.Batch095.valid3801
  · exact MergedCutProfiles.Batch095.valid3802
  · exact MergedCutProfiles.Batch095.valid3803
  · exact MergedCutProfiles.Batch095.valid3804
  · exact MergedCutProfiles.Batch095.valid3805
  · exact MergedCutProfiles.Batch095.valid3806
  · exact MergedCutProfiles.Batch095.valid3807
  · exact MergedCutProfiles.Batch095.valid3808
theorem numericValid565 : retention565.NumericValid := by decide +kernel
def certificate565 : RatCutBinCertificate := ⟨⟨retention565,(104322979946200783/50000000000000000),(20564159142100463/250000000000000000),(2341603643328142737/200000000000000000),(65421735753294979399/200000000000000000),(103263428910623333/100000000000000000)⟩,(62133518026871259/62500000000000000),(121546098965056273/250000000000000000),(2549925437035409/15625000000000000),(145401606832715691/1000000000000000000)⟩
theorem valid565 : certificate565.Valid := by decide +kernel
theorem sound565 : certificate565.Sound := rat_cut_bin_certificate_sound certificate565 profilesValid565 numericValid565 valid565

def retention566 : RatCutRetentionCertificate := ⟨(21/500),(169/4000),(13795094674871044725/27900829796345877247),(199055288824976531/15625000000000000),(21/20),(321643902879191013665395854952282636271/318488462119962449600000000000000000000),false,MergedCutProfiles.Batch095.profile3809,(fun _ => MergedCutProfiles.Batch095.profile3809)⟩
theorem profilesValid566 : retention566.ProfilesValid := by
  exact MergedCutProfiles.Batch095.valid3809
theorem numericValid566 : retention566.NumericValid := by decide +kernel
def certificate566 : RatCutBinCertificate := ⟨⟨retention566,(104322979946200783/50000000000000000),(20564159142100463/250000000000000000),(2341603643328142737/200000000000000000),(65421735753294979399/200000000000000000),(994515553148378959/1000000000000000000)⟩,(62133518026871259/62500000000000000),(96871805926819979/200000000000000000),(164515047976190173/1000000000000000000),(144631063332847743/1000000000000000000)⟩
theorem valid566 : certificate566.Valid := by decide +kernel
theorem sound566 : certificate566.Sound := rat_cut_bin_certificate_sound certificate566 profilesValid566 numericValid566 valid566

def retention567 : RatCutRetentionCertificate := ⟨(21/500),(169/4000),(13933045621619755173/27900829796345877247),(551803786994841789/40000000000000000),(21/20),(883761205831225332982151985576133459871/882886059191746862400000000000000000000),false,MergedCutProfiles.Batch095.profile3810,(fun _ => MergedCutProfiles.Batch095.profile3810)⟩
theorem profilesValid567 : retention567.ProfilesValid := by
  exact MergedCutProfiles.Batch095.valid3810
theorem numericValid567 : retention567.NumericValid := by decide +kernel
def certificate567 : RatCutBinCertificate := ⟨⟨retention567,(104322979946200783/50000000000000000),(20564159142100463/250000000000000000),(2341603643328142737/200000000000000000),(65421735753294979399/200000000000000000),(492799628999049169/500000000000000000)⟩,(62133518026871259/62500000000000000),(12173217069908827/25000000000000000),(162659044081512111/1000000000000000000),(142518802828866729/1000000000000000000)⟩
theorem valid567 : certificate567.Valid := by decide +kernel
theorem sound567 : certificate567.Sound := rat_cut_bin_certificate_sound certificate567 profilesValid567 numericValid567 valid567

def retention568 : RatCutRetentionCertificate := ⟨(21/500),(169/4000),(1/2),(13933045621619755173/1000000000000000000),(21/20),(2476619436379997147509172195951165093759/2476985888287956475200000000000000000000),false,MergedCutProfiles.Batch095.profile3811,(fun _ => MergedCutProfiles.Batch095.profile3811)⟩
theorem profilesValid568 : retention568.ProfilesValid := by
  exact MergedCutProfiles.Batch095.valid3811
theorem numericValid568 : retention568.NumericValid := by decide +kernel
def certificate568 : RatCutBinCertificate := ⟨⟨retention568,(104322979946200783/50000000000000000),(20564159142100463/250000000000000000),(2341603643328142737/200000000000000000),(65421735753294979399/200000000000000000),(984460084018783839/1000000000000000000)⟩,(62133518026871259/62500000000000000),(487275342917966541/1000000000000000000),(40602424688475691/250000000000000000),(35557937757226821/250000000000000000)⟩
theorem valid568 : certificate568.Valid := by decide +kernel
theorem sound568 : certificate568.Sound := rat_cut_bin_certificate_sound certificate568 profilesValid568 numericValid568 valid568

def retention569 : RatCutRetentionCertificate := ⟨(21/500),(169/4000),(12265935951498020191/27900829796345877247),(3791216503948534307/1000000000000000000),(6/5),(422565593404782957020851410416958013551/379121650394853430700000000000000000000),false,MergedCutProfiles.Batch095.profile3812,(fun _ => MergedCutProfiles.Batch095.profile3812)⟩
theorem profilesValid569 : retention569.ProfilesValid := by
  exact MergedCutProfiles.Batch095.valid3812
theorem numericValid569 : retention569.NumericValid := by decide +kernel
def certificate569 : RatCutBinCertificate := ⟨⟨retention569,(123843648546200783/50000000000000000),(20564159142100463/250000000000000000),(2341603643328142737/200000000000000000),(65421735753294979399/200000000000000000),(546853930575282603/500000000000000000)⟩,(198607681950536461/200000000000000000),(181993935258661831/500000000000000000),(268149448323070021/1000000000000000000),(8082677396716279/40000000000000000)⟩
theorem valid569 : certificate569.Valid := by decide +kernel
theorem sound569 : certificate569.Sound := rat_cut_bin_certificate_sound certificate569 profilesValid569 numericValid569 valid569

def retention570 : RatCutRetentionCertificate := ⟨(21/500),(169/4000),(13821563648143567294/27900829796345877247),(12265935951498020191/1000000000000000000),(21/20),(19773767206548309749915518392629633978159/19625497522396832305600000000000000000000),false,MergedCutProfiles.Batch095.profile3813,(fun _ => MergedCutProfiles.Batch095.profile3813)⟩
theorem profilesValid570 : retention570.ProfilesValid := by
  exact MergedCutProfiles.Batch095.valid3813
theorem numericValid570 : retention570.NumericValid := by decide +kernel
def certificate570 : RatCutBinCertificate := ⟨⟨retention570,(123843648546200783/50000000000000000),(20564159142100463/250000000000000000),(2341603643328142737/200000000000000000),(65421735753294979399/200000000000000000),(494641413036448519/500000000000000000)⟩,(198607681950536461/200000000000000000),(80481816697162901/200000000000000000),(14455142315914647/62500000000000000),(100795859991542519/500000000000000000)⟩
theorem valid570 : certificate570.Valid := by decide +kernel
theorem sound570 : certificate570.Sound := rat_cut_bin_certificate_sound certificate570 profilesValid570 numericValid570 valid570

def retention571 : RatCutRetentionCertificate := ⟨(21/500),(169/4000),(1/2),(6910781824071783647/500000000000000000),1,(1235618956567757624038583344904118801/1256505786194869754000000000000000000),false,MergedCutProfiles.Batch095.profile3811,(fun _ => MergedCutProfiles.Batch095.profile3811)⟩
theorem profilesValid571 : retention571.ProfilesValid := by
  exact MergedCutProfiles.Batch095.valid3811
theorem numericValid571 : retention571.NumericValid := by decide +kernel
def certificate571 : RatCutBinCertificate := ⟨⟨retention571,(123843648546200783/50000000000000000),(20564159142100463/250000000000000000),(2341603643328142737/200000000000000000),(65421735753294979399/200000000000000000),(96597505141315411/100000000000000000)⟩,(198607681950536461/200000000000000000),(412118713382776999/1000000000000000000),(55640066749823933/250000000000000000),(199500085936065121/1000000000000000000)⟩
theorem valid571 : certificate571.Valid := by decide +kernel
theorem sound571 : certificate571.Sound := rat_cut_bin_certificate_sound certificate571 profilesValid571 numericValid571 valid571

def retention572 : RatCutRetentionCertificate := ⟨(169/4000),(17/400),(809927025391471826/27535959003721291749),(400953972966075161/500000000000000000),(63/20),(5348333896287245703/2500000000000000000),true,MergedCutProfiles.Batch095.profile3814,![MergedCutProfiles.Batch095.profile3814,MergedCutProfiles.Batch095.profile3815,MergedCutProfiles.Batch095.profile3816,MergedCutProfiles.Batch095.profile3817,MergedCutProfiles.Batch095.profile3818,MergedCutProfiles.Batch095.profile3819,MergedCutProfiles.Batch095.profile3820,MergedCutProfiles.Batch095.profile3821,MergedCutProfiles.Batch095.profile3822,MergedCutProfiles.Batch095.profile3823,MergedCutProfiles.Batch095.profile3824,MergedCutProfiles.Batch095.profile3825,MergedCutProfiles.Batch095.profile3826,MergedCutProfiles.Batch095.profile3827,MergedCutProfiles.Batch095.profile3828,MergedCutProfiles.Batch095.profile3829]⟩
theorem profilesValid572 : retention572.ProfilesValid := by
  change ∀ j : Fin 16, (retention572.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch095.valid3814
  · exact MergedCutProfiles.Batch095.valid3815
  · exact MergedCutProfiles.Batch095.valid3816
  · exact MergedCutProfiles.Batch095.valid3817
  · exact MergedCutProfiles.Batch095.valid3818
  · exact MergedCutProfiles.Batch095.valid3819
  · exact MergedCutProfiles.Batch095.valid3820
  · exact MergedCutProfiles.Batch095.valid3821
  · exact MergedCutProfiles.Batch095.valid3822
  · exact MergedCutProfiles.Batch095.valid3823
  · exact MergedCutProfiles.Batch095.valid3824
  · exact MergedCutProfiles.Batch095.valid3825
  · exact MergedCutProfiles.Batch095.valid3826
  · exact MergedCutProfiles.Batch095.valid3827
  · exact MergedCutProfiles.Batch095.valid3828
  · exact MergedCutProfiles.Batch095.valid3829
theorem numericValid572 : retention572.NumericValid := by decide +kernel
def certificate572 : RatCutBinCertificate := ⟨⟨retention572,(1044139307680908281/500000000000000000),(5208213269348153/62500000000000000),(5876883677324390017/500000000000000000),(162046546899711298817/500000000000000000),(1046345903471489727/500000000000000000)⟩,(994083368911693427/1000000000000000000),(395687268105855213/1000000000000000000),(59364306484681243/250000000000000000),(62017102842477051/500000000000000000)⟩
theorem valid572 : certificate572.Valid := by decide +kernel
theorem sound572 : certificate572.Sound := rat_cut_bin_certificate_sound certificate572 profilesValid572 numericValid572 valid572

def retention573 : RatCutRetentionCertificate := ⟨(169/4000),(17/400),(894663312215902217/27535959003721291749),(404963512695735913/500000000000000000),(31/10),(1359037903886436764917/640000000000000000000),true,MergedCutProfiles.Batch095.profile3830,![MergedCutProfiles.Batch095.profile3830,MergedCutProfiles.Batch095.profile3831,MergedCutProfiles.Batch095.profile3832,MergedCutProfiles.Batch095.profile3833,MergedCutProfiles.Batch095.profile3834,MergedCutProfiles.Batch095.profile3835,MergedCutProfiles.Batch095.profile3836,MergedCutProfiles.Batch095.profile3837,MergedCutProfiles.Batch095.profile3838,MergedCutProfiles.Batch095.profile3824,MergedCutProfiles.Batch095.profile3839,MergedCutProfiles.Batch096.profile3840,MergedCutProfiles.Batch096.profile3841,MergedCutProfiles.Batch096.profile3842,MergedCutProfiles.Batch096.profile3843,MergedCutProfiles.Batch096.profile3844]⟩
theorem profilesValid573 : retention573.ProfilesValid := by
  change ∀ j : Fin 16, (retention573.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch095.valid3830
  · exact MergedCutProfiles.Batch095.valid3831
  · exact MergedCutProfiles.Batch095.valid3832
  · exact MergedCutProfiles.Batch095.valid3833
  · exact MergedCutProfiles.Batch095.valid3834
  · exact MergedCutProfiles.Batch095.valid3835
  · exact MergedCutProfiles.Batch095.valid3836
  · exact MergedCutProfiles.Batch095.valid3837
  · exact MergedCutProfiles.Batch095.valid3838
  · exact MergedCutProfiles.Batch095.valid3824
  · exact MergedCutProfiles.Batch095.valid3839
  · exact MergedCutProfiles.Batch096.valid3840
  · exact MergedCutProfiles.Batch096.valid3841
  · exact MergedCutProfiles.Batch096.valid3842
  · exact MergedCutProfiles.Batch096.valid3843
  · exact MergedCutProfiles.Batch096.valid3844
theorem numericValid573 : retention573.NumericValid := by decide +kernel
def certificate573 : RatCutBinCertificate := ⟨⟨retention573,(1044139307680908281/500000000000000000),(5208213269348153/62500000000000000),(5876883677324390017/500000000000000000),(162046546899711298817/500000000000000000),(1038797645081739587/500000000000000000)⟩,(994083368911693427/1000000000000000000),(79359880828082953/200000000000000000),(118213870966974561/500000000000000000),(62098406193420629/500000000000000000)⟩
theorem valid573 : certificate573.Valid := by decide +kernel
theorem sound573 : certificate573.Sound := rat_cut_bin_certificate_sound certificate573 profilesValid573 numericValid573 valid573

def retention574 : RatCutRetentionCertificate := ⟨(169/4000),(17/400),(906886717000000000/27535959003721291749),(894663312215902217/1000000000000000000),(57/20),(84626076439669248267/40000000000000000000),true,MergedCutProfiles.Batch095.profile3830,![MergedCutProfiles.Batch095.profile3830,MergedCutProfiles.Batch096.profile3845,MergedCutProfiles.Batch096.profile3846,MergedCutProfiles.Batch096.profile3847,MergedCutProfiles.Batch096.profile3848,MergedCutProfiles.Batch096.profile3849,MergedCutProfiles.Batch096.profile3850,MergedCutProfiles.Batch096.profile3851,MergedCutProfiles.Batch096.profile3852,MergedCutProfiles.Batch096.profile3853,MergedCutProfiles.Batch096.profile3854,MergedCutProfiles.Batch096.profile3855,MergedCutProfiles.Batch096.profile3856,MergedCutProfiles.Batch096.profile3857,MergedCutProfiles.Batch096.profile3858,MergedCutProfiles.Batch096.profile3859]⟩
theorem profilesValid574 : retention574.ProfilesValid := by
  change ∀ j : Fin 16, (retention574.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch095.valid3830
  · exact MergedCutProfiles.Batch096.valid3845
  · exact MergedCutProfiles.Batch096.valid3846
  · exact MergedCutProfiles.Batch096.valid3847
  · exact MergedCutProfiles.Batch096.valid3848
  · exact MergedCutProfiles.Batch096.valid3849
  · exact MergedCutProfiles.Batch096.valid3850
  · exact MergedCutProfiles.Batch096.valid3851
  · exact MergedCutProfiles.Batch096.valid3852
  · exact MergedCutProfiles.Batch096.valid3853
  · exact MergedCutProfiles.Batch096.valid3854
  · exact MergedCutProfiles.Batch096.valid3855
  · exact MergedCutProfiles.Batch096.valid3856
  · exact MergedCutProfiles.Batch096.valid3857
  · exact MergedCutProfiles.Batch096.valid3858
  · exact MergedCutProfiles.Batch096.valid3859
theorem numericValid574 : retention574.NumericValid := by decide +kernel
def certificate574 : RatCutBinCertificate := ⟨⟨retention574,(1044139307680908281/500000000000000000),(5208213269348153/62500000000000000),(5876883677324390017/500000000000000000),(162046546899711298817/500000000000000000),(2073452271055577351/1000000000000000000)⟩,(994083368911693427/1000000000000000000),(380860389324790881/1000000000000000000),(251484162533021751/1000000000000000000),(14135899126079/100000000000000)⟩
theorem valid574 : certificate574.Valid := by decide +kernel
theorem sound574 : certificate574.Sound := rat_cut_bin_certificate_sound certificate574 profilesValid574 numericValid574 valid574

def retention575 : RatCutRetentionCertificate := ⟨(169/4000),(17/400),(998147538362031541/27535959003721291749),(906886717/1000000000),(57/20),(2109216886242407397/1000000000000000000),true,MergedCutProfiles.Batch096.profile3860,![MergedCutProfiles.Batch096.profile3860,MergedCutProfiles.Batch096.profile3861,MergedCutProfiles.Batch096.profile3862,MergedCutProfiles.Batch096.profile3863,MergedCutProfiles.Batch096.profile3864,MergedCutProfiles.Batch096.profile3865,MergedCutProfiles.Batch096.profile3866,MergedCutProfiles.Batch096.profile3867,MergedCutProfiles.Batch096.profile3868,MergedCutProfiles.Batch096.profile3854,MergedCutProfiles.Batch096.profile3869,MergedCutProfiles.Batch096.profile3870,MergedCutProfiles.Batch095.profile3829,MergedCutProfiles.Batch096.profile3871,MergedCutProfiles.Batch096.profile3872,MergedCutProfiles.Batch096.profile3873]⟩
theorem profilesValid575 : retention575.ProfilesValid := by
  change ∀ j : Fin 16, (retention575.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch096.valid3860
  · exact MergedCutProfiles.Batch096.valid3861
  · exact MergedCutProfiles.Batch096.valid3862
  · exact MergedCutProfiles.Batch096.valid3863
  · exact MergedCutProfiles.Batch096.valid3864
  · exact MergedCutProfiles.Batch096.valid3865
  · exact MergedCutProfiles.Batch096.valid3866
  · exact MergedCutProfiles.Batch096.valid3867
  · exact MergedCutProfiles.Batch096.valid3868
  · exact MergedCutProfiles.Batch096.valid3854
  · exact MergedCutProfiles.Batch096.valid3869
  · exact MergedCutProfiles.Batch096.valid3870
  · exact MergedCutProfiles.Batch095.valid3829
  · exact MergedCutProfiles.Batch096.valid3871
  · exact MergedCutProfiles.Batch096.valid3872
  · exact MergedCutProfiles.Batch096.valid3873
theorem numericValid575 : retention575.NumericValid := by decide +kernel
def certificate575 : RatCutBinCertificate := ⟨⟨retention575,(1044139307680908281/500000000000000000),(5208213269348153/62500000000000000),(5876883677324390017/500000000000000000),(162046546899711298817/500000000000000000),(20670173036569351/10000000000000000)⟩,(994083368911693427/1000000000000000000),(75976760061152683/200000000000000000),(25242806936632747/100000000000000000),(14197191203953897/100000000000000000)⟩
theorem valid575 : certificate575.Valid := by decide +kernel
theorem sound575 : certificate575.Sound := rat_cut_bin_certificate_sound certificate575 profilesValid575 numericValid575 valid575

def certificates : List RatCutBinCertificate := [certificate564,certificate565,certificate566,certificate567,certificate568,certificate569,certificate570,certificate571,certificate572,certificate573,certificate574,certificate575]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound564,List.forall_mem_cons.mpr ⟨sound565,List.forall_mem_cons.mpr ⟨sound566,List.forall_mem_cons.mpr ⟨sound567,List.forall_mem_cons.mpr ⟨sound568,List.forall_mem_cons.mpr ⟨sound569,List.forall_mem_cons.mpr ⟨sound570,List.forall_mem_cons.mpr ⟨sound571,List.forall_mem_cons.mpr ⟨sound572,List.forall_mem_cons.mpr ⟨sound573,List.forall_mem_cons.mpr ⟨sound574,List.forall_mem_cons.mpr ⟨sound575,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch047
