import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch096
import Cycle12.MergedCutProfiles.Batch097
import Cycle12.MergedCutProfiles.Batch098

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch048

def retention576 : RatCutRetentionCertificate := ⟨(169/4000),(17/400),(1924887754602205451/27535959003721291749),(998147538362031541/1000000000000000000),(13/5),(636572591958393528689/320000000000000000000),true,MergedCutProfiles.Batch096.profile3874,![MergedCutProfiles.Batch096.profile3874,MergedCutProfiles.Batch096.profile3875,MergedCutProfiles.Batch096.profile3876,MergedCutProfiles.Batch096.profile3877,MergedCutProfiles.Batch096.profile3878,MergedCutProfiles.Batch096.profile3879,MergedCutProfiles.Batch097.profile3880,MergedCutProfiles.Batch097.profile3881,MergedCutProfiles.Batch097.profile3882,MergedCutProfiles.Batch097.profile3883,MergedCutProfiles.Batch097.profile3884,MergedCutProfiles.Batch097.profile3885,MergedCutProfiles.Batch097.profile3886,MergedCutProfiles.Batch097.profile3887,MergedCutProfiles.Batch097.profile3888,MergedCutProfiles.Batch097.profile3889]⟩
theorem profilesValid576 : retention576.ProfilesValid := by
  change ∀ j : Fin 16, (retention576.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch096.valid3874
  · exact MergedCutProfiles.Batch096.valid3875
  · exact MergedCutProfiles.Batch096.valid3876
  · exact MergedCutProfiles.Batch096.valid3877
  · exact MergedCutProfiles.Batch096.valid3878
  · exact MergedCutProfiles.Batch096.valid3879
  · exact MergedCutProfiles.Batch097.valid3880
  · exact MergedCutProfiles.Batch097.valid3881
  · exact MergedCutProfiles.Batch097.valid3882
  · exact MergedCutProfiles.Batch097.valid3883
  · exact MergedCutProfiles.Batch097.valid3884
  · exact MergedCutProfiles.Batch097.valid3885
  · exact MergedCutProfiles.Batch097.valid3886
  · exact MergedCutProfiles.Batch097.valid3887
  · exact MergedCutProfiles.Batch097.valid3888
  · exact MergedCutProfiles.Batch097.valid3889
theorem numericValid576 : retention576.NumericValid := by decide +kernel
def certificate576 : RatCutBinCertificate := ⟨⟨retention576,(1044139307680908281/500000000000000000),(5208213269348153/62500000000000000),(5876883677324390017/500000000000000000),(162046546899711298817/500000000000000000),(975395750316094957/500000000000000000)⟩,(994083368911693427/1000000000000000000),(19359238207315981/50000000000000000),(122715865101748207/500000000000000000),(141861171105740723/1000000000000000000)⟩
theorem valid576 : certificate576.Valid := by decide +kernel
theorem sound576 : certificate576.Sound := rat_cut_bin_certificate_sound certificate576 profilesValid576 numericValid576 valid576

def retention577 : RatCutRetentionCertificate := ⟨(169/4000),(17/400),(2532991526601514178/9178653001240430583),(1924887754602205451/1000000000000000000),(33/20),(4506031231682562412500568105490801466351/3079820407363528721600000000000000000000),false,MergedCutProfiles.Batch097.profile3890,(fun _ => MergedCutProfiles.Batch097.profile3890)⟩
theorem profilesValid577 : retention577.ProfilesValid := by
  exact MergedCutProfiles.Batch097.valid3890
theorem numericValid577 : retention577.NumericValid := by decide +kernel
def certificate577 : RatCutBinCertificate := ⟨⟨retention577,(1044139307680908281/500000000000000000),(5208213269348153/62500000000000000),(5876883677324390017/500000000000000000),(162046546899711298817/500000000000000000),(143865157971620131/100000000000000000)⟩,(994083368911693427/1000000000000000000),(425550643511173521/1000000000000000000),(105435240952982433/500000000000000000),(143285217337860033/1000000000000000000)⟩
theorem valid577 : certificate577.Valid := by decide +kernel
theorem sound577 : certificate577.Sound := rat_cut_bin_certificate_sound certificate577 profilesValid577 numericValid577 valid577

def retention578 : RatCutRetentionCertificate := ⟨(169/4000),(17/400),(4334988215967881462/9178653001240430583),(3799487289902271267/500000000000000000),(21/20),(3167612185732886821618126559507525415191/3039589831921817013600000000000000000000),false,MergedCutProfiles.Batch097.profile3891,(fun _ => MergedCutProfiles.Batch097.profile3891)⟩
theorem profilesValid578 : retention578.ProfilesValid := by
  exact MergedCutProfiles.Batch097.valid3891
theorem numericValid578 : retention578.NumericValid := by decide +kernel
def certificate578 : RatCutBinCertificate := ⟨⟨retention578,(1044139307680908281/500000000000000000),(5208213269348153/62500000000000000),(5876883677324390017/500000000000000000),(162046546899711298817/500000000000000000),(128321516255795943/125000000000000000)⟩,(994083368911693427/1000000000000000000),(484268325102465607/1000000000000000000),(164580810525246021/1000000000000000000),(71221286555050549/500000000000000000)⟩
theorem valid578 : certificate578.Valid := by decide +kernel
theorem sound578 : certificate578.Sound := rat_cut_bin_certificate_sound certificate578 profilesValid578 numericValid578 valid578

def retention579 : RatCutRetentionCertificate := ⟨(169/4000),(17/400),(13668348546141938149/27535959003721291749),(6502482323951822193/500000000000000000),(21/20),(5234759190808734857202308105662943584511/5201985859161457754400000000000000000000),false,MergedCutProfiles.Batch097.profile3892,(fun _ => MergedCutProfiles.Batch097.profile3892)⟩
theorem profilesValid579 : retention579.ProfilesValid := by
  exact MergedCutProfiles.Batch097.valid3892
theorem numericValid579 : retention579.NumericValid := by decide +kernel
def certificate579 : RatCutBinCertificate := ⟨⟨retention579,(1044139307680908281/500000000000000000),(5208213269348153/62500000000000000),(5876883677324390017/500000000000000000),(162046546899711298817/500000000000000000),(19815083938403089/20000000000000000)⟩,(994083368911693427/1000000000000000000),(485395463658009643/1000000000000000000),(8188240912176219/50000000000000000),(28729741780543717/200000000000000000)⟩
theorem valid579 : certificate579.Valid := by decide +kernel
theorem sound579 : certificate579.Sound := rat_cut_bin_certificate_sound certificate579 profilesValid579 numericValid579 valid579

def retention580 : RatCutRetentionCertificate := ⟨(169/4000),(17/400),(1/2),(13668348546141938149/1000000000000000000),(21/20),(21862138367541801446664788471911523070639/21869357673827101038400000000000000000000),false,MergedCutProfiles.Batch097.profile3893,(fun _ => MergedCutProfiles.Batch097.profile3893)⟩
theorem profilesValid580 : retention580.ProfilesValid := by
  exact MergedCutProfiles.Batch097.valid3893
theorem numericValid580 : retention580.NumericValid := by decide +kernel
def certificate580 : RatCutBinCertificate := ⟨⟨retention580,(1044139307680908281/500000000000000000),(5208213269348153/62500000000000000),(5876883677324390017/500000000000000000),(162046546899711298817/500000000000000000),(98412394277649253/100000000000000000)⟩,(994083368911693427/1000000000000000000),(243770322974809911/500000000000000000),(162219038465661491/1000000000000000000),(141845371262771579/1000000000000000000)⟩
theorem valid580 : certificate580.Valid := by decide +kernel
theorem sound580 : certificate580.Sound := rat_cut_bin_certificate_sound certificate580 profilesValid580 numericValid580 valid580

def retention581 : RatCutRetentionCertificate := ⟨(169/4000),(17/400),(4058367446189522746/9178653001240430583),(152030904439158931/40000000000000000),(6/5),(168725436485886467416749663196339181/152030904439158931000000000000000000),false,MergedCutProfiles.Batch097.profile3894,(fun _ => MergedCutProfiles.Batch097.profile3894)⟩
theorem profilesValid581 : retention581.ProfilesValid := by
  exact MergedCutProfiles.Batch097.valid3894
theorem numericValid581 : retention581.NumericValid := by decide +kernel
def certificate581 : RatCutBinCertificate := ⟨⟨retention581,(1239578176680908281/500000000000000000),(5208213269348153/62500000000000000),(5876883677324390017/500000000000000000),(162046546899711298817/500000000000000000),(544358489087491083/500000000000000000)⟩,(198595042884500159/200000000000000000),(364756729903297513/1000000000000000000),(53474661858558857/200000000000000000),(40157115423819067/200000000000000000)⟩
theorem valid581 : certificate581.Valid := by decide +kernel
theorem sound581 : certificate581.Sound := rat_cut_bin_certificate_sound certificate581 profilesValid581 numericValid581 valid581

def retention582 : RatCutRetentionCertificate := ⟨(169/4000),(17/400),(13583376296551823686/27535959003721291749),(6087551169284284119/500000000000000000),(21/20),(234590210228265720384523415206469137539/231906711210829871200000000000000000000),false,MergedCutProfiles.Batch097.profile3895,(fun _ => MergedCutProfiles.Batch097.profile3895)⟩
theorem profilesValid582 : retention582.ProfilesValid := by
  exact MergedCutProfiles.Batch097.valid3895
theorem numericValid582 : retention582.NumericValid := by decide +kernel
def certificate582 : RatCutBinCertificate := ⟨⟨retention582,(1239578176680908281/500000000000000000),(5208213269348153/62500000000000000),(5876883677324390017/500000000000000000),(162046546899711298817/500000000000000000),(993115628131987229/1000000000000000000)⟩,(198595042884500159/200000000000000000),(399869696438337117/1000000000000000000),(116800887468910603/500000000000000000),(204230263361146483/1000000000000000000)⟩
theorem valid582 : certificate582.Valid := by decide +kernel
theorem sound582 : certificate582.Sound := rat_cut_bin_certificate_sound certificate582 profilesValid582 numericValid582 valid582

def retention583 : RatCutRetentionCertificate := ⟨(169/4000),(17/400),(13719210059517341923/27535959003721291749),(6791688148275911843/500000000000000000),1,(418740309143038232631635459184021441/424480509267244490187500000000000000),false,MergedCutProfiles.Batch097.profile3896,(fun _ => MergedCutProfiles.Batch097.profile3896)⟩
theorem profilesValid583 : retention583.ProfilesValid := by
  exact MergedCutProfiles.Batch097.valid3896
theorem numericValid583 : retention583.NumericValid := by decide +kernel
def certificate583 : RatCutBinCertificate := ⟨⟨retention583,(1239578176680908281/500000000000000000),(5208213269348153/62500000000000000),(5876883677324390017/500000000000000000),(162046546899711298817/500000000000000000),(193780031257198661/200000000000000000)⟩,(198595042884500159/200000000000000000),(204931768342128327/500000000000000000),(56141367345616737/250000000000000000),(201621485245578301/1000000000000000000)⟩
theorem valid583 : certificate583.Valid := by decide +kernel
theorem sound583 : certificate583.Sound := rat_cut_bin_certificate_sound certificate583 profilesValid583 numericValid583 valid583

def retention584 : RatCutRetentionCertificate := ⟨(169/4000),(17/400),(1/2),(13719210059517341923/1000000000000000000),1,(53957247341040273828469755459317457147/54876840238069367692000000000000000000),false,MergedCutProfiles.Batch097.profile3893,(fun _ => MergedCutProfiles.Batch097.profile3893)⟩
theorem profilesValid584 : retention584.ProfilesValid := by
  exact MergedCutProfiles.Batch097.valid3893
theorem numericValid584 : retention584.NumericValid := by decide +kernel
def certificate584 : RatCutBinCertificate := ⟨⟨retention584,(1239578176680908281/500000000000000000),(5208213269348153/62500000000000000),(5876883677324390017/500000000000000000),(162046546899711298817/500000000000000000),(965665647093622329/1000000000000000000)⟩,(198595042884500159/200000000000000000),(5140454746740169/12500000000000000),(223343325837414077/1000000000000000000),(20003109355905479/100000000000000000)⟩
theorem valid584 : certificate584.Valid := by decide +kernel
theorem sound584 : certificate584.Sound := rat_cut_bin_certificate_sound certificate584 profilesValid584 numericValid584 valid584

def retention585 : RatCutRetentionCertificate := ⟨(17/400),(43/1000),(814830785514356863/26825845523449284044),(161352630794922151/200000000000000000),(63/20),(109484702977747333899/51200000000000000000),true,MergedCutProfiles.Batch097.profile3897,![MergedCutProfiles.Batch097.profile3897,MergedCutProfiles.Batch097.profile3898,MergedCutProfiles.Batch097.profile3899,MergedCutProfiles.Batch097.profile3900,MergedCutProfiles.Batch097.profile3901,MergedCutProfiles.Batch097.profile3902,MergedCutProfiles.Batch097.profile3903,MergedCutProfiles.Batch097.profile3904,MergedCutProfiles.Batch097.profile3905,MergedCutProfiles.Batch097.profile3906,MergedCutProfiles.Batch097.profile3907,MergedCutProfiles.Batch097.profile3908,MergedCutProfiles.Batch097.profile3909,MergedCutProfiles.Batch097.profile3910,MergedCutProfiles.Batch097.profile3911,MergedCutProfiles.Batch097.profile3912]⟩
theorem profilesValid585 : retention585.ProfilesValid := by
  change ∀ j : Fin 16, (retention585.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch097.valid3897
  · exact MergedCutProfiles.Batch097.valid3898
  · exact MergedCutProfiles.Batch097.valid3899
  · exact MergedCutProfiles.Batch097.valid3900
  · exact MergedCutProfiles.Batch097.valid3901
  · exact MergedCutProfiles.Batch097.valid3902
  · exact MergedCutProfiles.Batch097.valid3903
  · exact MergedCutProfiles.Batch097.valid3904
  · exact MergedCutProfiles.Batch097.valid3905
  · exact MergedCutProfiles.Batch097.valid3906
  · exact MergedCutProfiles.Batch097.valid3907
  · exact MergedCutProfiles.Batch097.valid3908
  · exact MergedCutProfiles.Batch097.valid3909
  · exact MergedCutProfiles.Batch097.valid3910
  · exact MergedCutProfiles.Batch097.valid3911
  · exact MergedCutProfiles.Batch097.valid3912
theorem numericValid585 : retention585.NumericValid := by decide +kernel
def certificate585 : RatCutBinCertificate := ⟨⟨retention585,(522035734245703707/250000000000000000),(21376650541548341/250000000000000000),(2949939795123234019/250000000000000000),(39675673919527877589/125000000000000000),(1045351653192987211/500000000000000000)⟩,(993966059501501379/1000000000000000000),(196474675343902219/500000000000000000),(30000624666432787/125000000000000000),(125410499346611927/1000000000000000000)⟩
theorem valid585 : certificate585.Valid := by decide +kernel
theorem sound585 : certificate585.Sound := rat_cut_bin_certificate_sound certificate585 profilesValid585 numericValid585 valid585

def retention586 : RatCutRetentionCertificate := ⟨(17/400),(43/1000),(222520471750000000/6706461380862321011),(814830785514356863/1000000000000000000),(31/10),(2718413125481339720267/1280000000000000000000),true,MergedCutProfiles.Batch097.profile3913,![MergedCutProfiles.Batch097.profile3913,MergedCutProfiles.Batch097.profile3914,MergedCutProfiles.Batch097.profile3915,MergedCutProfiles.Batch097.profile3916,MergedCutProfiles.Batch097.profile3917,MergedCutProfiles.Batch097.profile3918,MergedCutProfiles.Batch097.profile3919,MergedCutProfiles.Batch098.profile3920,MergedCutProfiles.Batch098.profile3921,MergedCutProfiles.Batch098.profile3922,MergedCutProfiles.Batch097.profile3908,MergedCutProfiles.Batch098.profile3923,MergedCutProfiles.Batch098.profile3924,MergedCutProfiles.Batch098.profile3925,MergedCutProfiles.Batch098.profile3926,MergedCutProfiles.Batch098.profile3927]⟩
theorem profilesValid586 : retention586.ProfilesValid := by
  change ∀ j : Fin 16, (retention586.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch097.valid3913
  · exact MergedCutProfiles.Batch097.valid3914
  · exact MergedCutProfiles.Batch097.valid3915
  · exact MergedCutProfiles.Batch097.valid3916
  · exact MergedCutProfiles.Batch097.valid3917
  · exact MergedCutProfiles.Batch097.valid3918
  · exact MergedCutProfiles.Batch097.valid3919
  · exact MergedCutProfiles.Batch098.valid3920
  · exact MergedCutProfiles.Batch098.valid3921
  · exact MergedCutProfiles.Batch098.valid3922
  · exact MergedCutProfiles.Batch097.valid3908
  · exact MergedCutProfiles.Batch098.valid3923
  · exact MergedCutProfiles.Batch098.valid3924
  · exact MergedCutProfiles.Batch098.valid3925
  · exact MergedCutProfiles.Batch098.valid3926
  · exact MergedCutProfiles.Batch098.valid3927
theorem numericValid586 : retention586.NumericValid := by decide +kernel
def certificate586 : RatCutBinCertificate := ⟨⟨retention586,(522035734245703707/250000000000000000),(21376650541548341/250000000000000000),(2949939795123234019/250000000000000000),(39675673919527877589/125000000000000000),(519211772232430013/250000000000000000)⟩,(993966059501501379/1000000000000000000),(393840136430731673/1000000000000000000),(14948374362534121/62500000000000000),(25149168877893849/200000000000000000)⟩
theorem valid586 : certificate586.Valid := by decide +kernel
theorem sound586 : certificate586.Sound := rat_cut_bin_certificate_sound certificate586 profilesValid586 numericValid586 valid586

def retention587 : RatCutRetentionCertificate := ⟨(17/400),(43/1000),(900080114145350195/26825845523449284044),(890081887/1000000000),(57/20),(8446225431735283467/4000000000000000000),true,MergedCutProfiles.Batch097.profile3913,![MergedCutProfiles.Batch097.profile3913,MergedCutProfiles.Batch098.profile3928,MergedCutProfiles.Batch098.profile3929,MergedCutProfiles.Batch098.profile3930,MergedCutProfiles.Batch098.profile3931,MergedCutProfiles.Batch098.profile3932,MergedCutProfiles.Batch098.profile3933,MergedCutProfiles.Batch098.profile3934,MergedCutProfiles.Batch098.profile3935,MergedCutProfiles.Batch098.profile3936,MergedCutProfiles.Batch098.profile3937,MergedCutProfiles.Batch098.profile3938,MergedCutProfiles.Batch098.profile3939,MergedCutProfiles.Batch098.profile3940,MergedCutProfiles.Batch098.profile3941,MergedCutProfiles.Batch098.profile3942]⟩
theorem profilesValid587 : retention587.ProfilesValid := by
  change ∀ j : Fin 16, (retention587.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch097.valid3913
  · exact MergedCutProfiles.Batch098.valid3928
  · exact MergedCutProfiles.Batch098.valid3929
  · exact MergedCutProfiles.Batch098.valid3930
  · exact MergedCutProfiles.Batch098.valid3931
  · exact MergedCutProfiles.Batch098.valid3932
  · exact MergedCutProfiles.Batch098.valid3933
  · exact MergedCutProfiles.Batch098.valid3934
  · exact MergedCutProfiles.Batch098.valid3935
  · exact MergedCutProfiles.Batch098.valid3936
  · exact MergedCutProfiles.Batch098.valid3937
  · exact MergedCutProfiles.Batch098.valid3938
  · exact MergedCutProfiles.Batch098.valid3939
  · exact MergedCutProfiles.Batch098.valid3940
  · exact MergedCutProfiles.Batch098.valid3941
  · exact MergedCutProfiles.Batch098.valid3942
theorem numericValid587 : retention587.NumericValid := by decide +kernel
def certificate587 : RatCutBinCertificate := ⟨⟨retention587,(522035734245703707/250000000000000000),(21376650541548341/250000000000000000),(2949939795123234019/250000000000000000),(39675673919527877589/125000000000000000),(2068426531872574877/1000000000000000000)⟩,(993966059501501379/1000000000000000000),(190375179551679727/500000000000000000),(251590385323601491/1000000000000000000),(70485206216623753/500000000000000000)⟩
theorem valid587 : certificate587.Valid := by decide +kernel
theorem sound587 : certificate587.Sound := rat_cut_bin_certificate_sound certificate587 profilesValid587 numericValid587 valid587

def certificates : List RatCutBinCertificate := [certificate576,certificate577,certificate578,certificate579,certificate580,certificate581,certificate582,certificate583,certificate584,certificate585,certificate586,certificate587]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound576,List.forall_mem_cons.mpr ⟨sound577,List.forall_mem_cons.mpr ⟨sound578,List.forall_mem_cons.mpr ⟨sound579,List.forall_mem_cons.mpr ⟨sound580,List.forall_mem_cons.mpr ⟨sound581,List.forall_mem_cons.mpr ⟨sound582,List.forall_mem_cons.mpr ⟨sound583,List.forall_mem_cons.mpr ⟨sound584,List.forall_mem_cons.mpr ⟨sound585,List.forall_mem_cons.mpr ⟨sound586,List.forall_mem_cons.mpr ⟨sound587,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch048
