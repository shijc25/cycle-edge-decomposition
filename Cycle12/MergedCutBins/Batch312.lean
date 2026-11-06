import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch569
import Cycle12.MergedCutProfiles.Batch570
import Cycle12.MergedCutProfiles.Batch571
import Cycle12.MergedCutProfiles.Batch572

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch312

def retention3744 : RatCutRetentionCertificate := ⟨(3/250),(1/80),(412930536986423739/1056532097047686002239),(1274340723/1000000000),(5/2),(37724583854619870007/16000000000000000000),true,MergedCutProfiles.Batch569.profile22791,![MergedCutProfiles.Batch569.profile22791,MergedCutProfiles.Batch569.profile22795,MergedCutProfiles.Batch569.profile22798,MergedCutProfiles.Batch570.profile22801,MergedCutProfiles.Batch570.profile22803,MergedCutProfiles.Batch570.profile22805,MergedCutProfiles.Batch570.profile22807,MergedCutProfiles.Batch570.profile22808,MergedCutProfiles.Batch570.profile22809,MergedCutProfiles.Batch570.profile22810,MergedCutProfiles.Batch570.profile22811,MergedCutProfiles.Batch570.profile22812,MergedCutProfiles.Batch570.profile22813,MergedCutProfiles.Batch570.profile22814,MergedCutProfiles.Batch570.profile22815,MergedCutProfiles.Batch570.profile22816]⟩
theorem profilesValid3744 : retention3744.ProfilesValid := by
  change ∀ j : Fin 16, (retention3744.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch569.valid22791
  · exact MergedCutProfiles.Batch569.valid22795
  · exact MergedCutProfiles.Batch569.valid22798
  · exact MergedCutProfiles.Batch570.valid22801
  · exact MergedCutProfiles.Batch570.valid22803
  · exact MergedCutProfiles.Batch570.valid22805
  · exact MergedCutProfiles.Batch570.valid22807
  · exact MergedCutProfiles.Batch570.valid22808
  · exact MergedCutProfiles.Batch570.valid22809
  · exact MergedCutProfiles.Batch570.valid22810
  · exact MergedCutProfiles.Batch570.valid22811
  · exact MergedCutProfiles.Batch570.valid22812
  · exact MergedCutProfiles.Batch570.valid22813
  · exact MergedCutProfiles.Batch570.valid22814
  · exact MergedCutProfiles.Batch570.valid22815
  · exact MergedCutProfiles.Batch570.valid22816
theorem numericValid3744 : retention3744.NumericValid := by decide +kernel
def certificate3744 : RatCutBinCertificate := ⟨⟨retention3744,(903871676627028339/500000000000000000),(6398394180380671/1000000000000000000),(1928357816880769413/250000000000000000),(28588376033724291777339/500000000000000000),(58850940567189743/25000000000000000)⟩,(249992142340777621/250000000000000000),(91959338194481043/250000000000000000),(26427972269465887/100000000000000000),(7682873773502021/40000000000000000)⟩
theorem valid3744 : certificate3744.Valid := by decide +kernel
theorem sound3744 : certificate3744.Sound := rat_cut_bin_certificate_sound certificate3744 profilesValid3744 numericValid3744 valid3744

def retention3745 : RatCutRetentionCertificate := ⟨(3/250),(1/80),(64000000000000000000/7395724679333802015673),(2890513758904966173/1000000000000000000),(3/2),(142592894337177487049/64000000000000000000),true,MergedCutProfiles.Batch570.profile22817,![MergedCutProfiles.Batch570.profile22817,MergedCutProfiles.Batch570.profile22818,MergedCutProfiles.Batch570.profile22819,MergedCutProfiles.Batch570.profile22820,MergedCutProfiles.Batch570.profile22821,MergedCutProfiles.Batch570.profile22822,MergedCutProfiles.Batch570.profile22823,MergedCutProfiles.Batch570.profile22824,MergedCutProfiles.Batch570.profile22825,MergedCutProfiles.Batch570.profile22826,MergedCutProfiles.Batch570.profile22827,MergedCutProfiles.Batch570.profile22828,MergedCutProfiles.Batch570.profile22829,MergedCutProfiles.Batch570.profile22830,MergedCutProfiles.Batch570.profile22831,MergedCutProfiles.Batch570.profile22832]⟩
theorem profilesValid3745 : retention3745.ProfilesValid := by
  change ∀ j : Fin 16, (retention3745.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch570.valid22817
  · exact MergedCutProfiles.Batch570.valid22818
  · exact MergedCutProfiles.Batch570.valid22819
  · exact MergedCutProfiles.Batch570.valid22820
  · exact MergedCutProfiles.Batch570.valid22821
  · exact MergedCutProfiles.Batch570.valid22822
  · exact MergedCutProfiles.Batch570.valid22823
  · exact MergedCutProfiles.Batch570.valid22824
  · exact MergedCutProfiles.Batch570.valid22825
  · exact MergedCutProfiles.Batch570.valid22826
  · exact MergedCutProfiles.Batch570.valid22827
  · exact MergedCutProfiles.Batch570.valid22828
  · exact MergedCutProfiles.Batch570.valid22829
  · exact MergedCutProfiles.Batch570.valid22830
  · exact MergedCutProfiles.Batch570.valid22831
  · exact MergedCutProfiles.Batch570.valid22832
theorem numericValid3745 : retention3745.NumericValid := by decide +kernel
def certificate3745 : RatCutBinCertificate := ⟨⟨retention3745,(903871676627028339/500000000000000000),(6398394180380671/1000000000000000000),(1928357816880769413/250000000000000000),(28588376033724291777339/500000000000000000),(2225764653103661487/1000000000000000000)⟩,(249992142340777621/250000000000000000),(280361805144081341/1000000000000000000),(363070569546265493/1000000000000000000),(40136195561909439/100000000000000000)⟩
theorem valid3745 : certificate3745.Valid := by decide +kernel
theorem sound3745 : certificate3745.Sound := rat_cut_bin_certificate_sound certificate3745 profilesValid3745 numericValid3745 valid3745

def retention3746 : RatCutRetentionCertificate := ⟨(3/250),(1/80),(1/2),64,1,(15960593938739604568934367293438872551/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch570.profile22833,(fun _ => MergedCutProfiles.Batch570.profile22833)⟩
theorem profilesValid3746 : retention3746.ProfilesValid := by
  exact MergedCutProfiles.Batch570.valid22833
theorem numericValid3746 : retention3746.NumericValid := by decide +kernel
def certificate3746 : RatCutBinCertificate := ⟨⟨retention3746,(903871676627028339/500000000000000000),(6398394180380671/1000000000000000000),(1928357816880769413/250000000000000000),(28588376033724291777339/500000000000000000),(996037573930815191/1000000000000000000)⟩,(249992142340777621/250000000000000000),(17746713631573631/40000000000000000),(97886116828406347/500000000000000000),(192002172451654121/1000000000000000000)⟩
theorem valid3746 : certificate3746.Valid := by decide +kernel
theorem sound3746 : certificate3746.Sound := rat_cut_bin_certificate_sound certificate3746 profilesValid3746 numericValid3746 valid3746

def retention3747 : RatCutRetentionCertificate := ⟨(3/250),(1/80),(64000000000000000000/7395724679333802015673),(4200580660322092803/250000000000000000),1,(49425135897258551149190276857305764517/22403096855051161616000000000000000000),false,MergedCutProfiles.Batch570.profile22834,(fun _ => MergedCutProfiles.Batch570.profile22834)⟩
theorem profilesValid3747 : retention3747.ProfilesValid := by
  exact MergedCutProfiles.Batch570.valid22834
theorem numericValid3747 : retention3747.NumericValid := by decide +kernel
def certificate3747 : RatCutBinCertificate := ⟨⟨retention3747,(885223106627028339/500000000000000000),(6398394180380671/1000000000000000000),(1928357816880769413/250000000000000000),(28588376033724291777339/500000000000000000),(2204705663340340589/1000000000000000000)⟩,(999969217836288899/1000000000000000000),(16312722227792763/500000000000000000),(418328639329459357/500000000000000000),(1630570342053135313/1000000000000000000)⟩
theorem valid3747 : certificate3747.Valid := by decide +kernel
theorem sound3747 : certificate3747.Sound := rat_cut_bin_certificate_sound certificate3747 profilesValid3747 numericValid3747 valid3747

def retention3748 : RatCutRetentionCertificate := ⟨(3/250),(1/80),(1/2),64,1,(15960593938739604568934367293438872551/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch570.profile22833,(fun _ => MergedCutProfiles.Batch570.profile22833)⟩
theorem profilesValid3748 : retention3748.ProfilesValid := by
  exact MergedCutProfiles.Batch570.valid22833
theorem numericValid3748 : retention3748.NumericValid := by decide +kernel
def certificate3748 : RatCutBinCertificate := ⟨⟨retention3748,(885223106627028339/500000000000000000),(6398394180380671/1000000000000000000),(1928357816880769413/250000000000000000),(28588376033724291777339/500000000000000000),(124508564050783677/125000000000000000)⟩,(999969217836288899/1000000000000000000),(36106704139487457/500000000000000000),(365655117041947897/500000000000000000),(179312378380466427/250000000000000000)⟩
theorem valid3748 : certificate3748.Valid := by decide +kernel
theorem sound3748 : certificate3748.Sound := rat_cut_bin_certificate_sound certificate3748 profilesValid3748 numericValid3748 valid3748

def retention3749 : RatCutRetentionCertificate := ⟨(1/80),(13/1000),(618977901062613410/6822131672314993651691),(282978072632990137/500000000000000000),4,(70142622616782641353/32000000000000000000),true,MergedCutProfiles.Batch570.profile22835,![MergedCutProfiles.Batch570.profile22835,MergedCutProfiles.Batch570.profile22836,MergedCutProfiles.Batch570.profile22837,MergedCutProfiles.Batch570.profile22838,MergedCutProfiles.Batch570.profile22839,MergedCutProfiles.Batch571.profile22840,MergedCutProfiles.Batch571.profile22841,MergedCutProfiles.Batch571.profile22842,MergedCutProfiles.Batch571.profile22843,MergedCutProfiles.Batch571.profile22844,MergedCutProfiles.Batch571.profile22845,MergedCutProfiles.Batch571.profile22845,MergedCutProfiles.Batch571.profile22846,MergedCutProfiles.Batch571.profile22847,MergedCutProfiles.Batch571.profile22847,MergedCutProfiles.Batch571.profile22848]⟩
theorem profilesValid3749 : retention3749.ProfilesValid := by
  change ∀ j : Fin 16, (retention3749.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch570.valid22835
  · exact MergedCutProfiles.Batch570.valid22836
  · exact MergedCutProfiles.Batch570.valid22837
  · exact MergedCutProfiles.Batch570.valid22838
  · exact MergedCutProfiles.Batch570.valid22839
  · exact MergedCutProfiles.Batch571.valid22840
  · exact MergedCutProfiles.Batch571.valid22841
  · exact MergedCutProfiles.Batch571.valid22842
  · exact MergedCutProfiles.Batch571.valid22843
  · exact MergedCutProfiles.Batch571.valid22844
  · exact MergedCutProfiles.Batch571.valid22845
  · exact MergedCutProfiles.Batch571.valid22845
  · exact MergedCutProfiles.Batch571.valid22846
  · exact MergedCutProfiles.Batch571.valid22847
  · exact MergedCutProfiles.Batch571.valid22847
  · exact MergedCutProfiles.Batch571.valid22848
theorem numericValid3749 : retention3749.NumericValid := by decide +kernel
def certificate3749 : RatCutBinCertificate := ⟨⟨retention3749,(225002495593763589/125000000000000000),(21663071517499/3125000000000000),(3880866428226591227/500000000000000000),(53072891309973047297007/1000000000000000000),(34148849980972927/15625000000000000)⟩,(31248946906396391/31250000000000000),(20213799667084887/31250000000000000),(8919922468185527/125000000000000000),(3925944572223677/125000000000000000)⟩
theorem valid3749 : certificate3749.Valid := by decide +kernel
theorem sound3749 : certificate3749.Sound := rat_cut_bin_certificate_sound certificate3749 profilesValid3749 numericValid3749 valid3749

def retention3750 : RatCutRetentionCertificate := ⟨(1/80),(13/1000),(1275587992000000000/6822131672314993651691),(61897790106261341/100000000000000000),4,(293246745460484084641/128000000000000000000),true,MergedCutProfiles.Batch571.profile22849,![MergedCutProfiles.Batch571.profile22849,MergedCutProfiles.Batch570.profile22838,MergedCutProfiles.Batch571.profile22841,MergedCutProfiles.Batch571.profile22843,MergedCutProfiles.Batch571.profile22844,MergedCutProfiles.Batch571.profile22846,MergedCutProfiles.Batch571.profile22847,MergedCutProfiles.Batch571.profile22848,MergedCutProfiles.Batch571.profile22850,MergedCutProfiles.Batch571.profile22851,MergedCutProfiles.Batch571.profile22852,MergedCutProfiles.Batch571.profile22853,MergedCutProfiles.Batch571.profile22854,MergedCutProfiles.Batch571.profile22855,MergedCutProfiles.Batch571.profile22856,MergedCutProfiles.Batch571.profile22857]⟩
theorem profilesValid3750 : retention3750.ProfilesValid := by
  change ∀ j : Fin 16, (retention3750.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch571.valid22849
  · exact MergedCutProfiles.Batch570.valid22838
  · exact MergedCutProfiles.Batch571.valid22841
  · exact MergedCutProfiles.Batch571.valid22843
  · exact MergedCutProfiles.Batch571.valid22844
  · exact MergedCutProfiles.Batch571.valid22846
  · exact MergedCutProfiles.Batch571.valid22847
  · exact MergedCutProfiles.Batch571.valid22848
  · exact MergedCutProfiles.Batch571.valid22850
  · exact MergedCutProfiles.Batch571.valid22851
  · exact MergedCutProfiles.Batch571.valid22852
  · exact MergedCutProfiles.Batch571.valid22853
  · exact MergedCutProfiles.Batch571.valid22854
  · exact MergedCutProfiles.Batch571.valid22855
  · exact MergedCutProfiles.Batch571.valid22856
  · exact MergedCutProfiles.Batch571.valid22857
theorem numericValid3750 : retention3750.NumericValid := by decide +kernel
def certificate3750 : RatCutBinCertificate := ⟨⟨retention3750,(225002495593763589/125000000000000000),(21663071517499/3125000000000000),(3880866428226591227/500000000000000000),(53072891309973047297007/1000000000000000000),(28556995511870297/12500000000000000)⟩,(31248946906396391/31250000000000000),(291070971025129851/500000000000000000),(51447706162414823/500000000000000000),(23875172827164671/500000000000000000)⟩
theorem valid3750 : certificate3750.Valid := by decide +kernel
theorem sound3750 : certificate3750.Sound := rat_cut_bin_certificate_sound certificate3750 profilesValid3750 numericValid3750 valid3750

def retention3751 : RatCutRetentionCertificate := ⟨(1/80),(13/1000),(4266007924106231936/6822131672314993651691),(159448499/125000000),(5/2),(37633129689548484621/16000000000000000000),true,MergedCutProfiles.Batch571.profile22841,![MergedCutProfiles.Batch571.profile22841,MergedCutProfiles.Batch571.profile22847,MergedCutProfiles.Batch571.profile22851,MergedCutProfiles.Batch571.profile22854,MergedCutProfiles.Batch571.profile22857,MergedCutProfiles.Batch571.profile22858,MergedCutProfiles.Batch571.profile22859,MergedCutProfiles.Batch571.profile22860,MergedCutProfiles.Batch571.profile22861,MergedCutProfiles.Batch571.profile22862,MergedCutProfiles.Batch571.profile22863,MergedCutProfiles.Batch571.profile22864,MergedCutProfiles.Batch571.profile22865,MergedCutProfiles.Batch571.profile22866,MergedCutProfiles.Batch571.profile22867,MergedCutProfiles.Batch571.profile22868]⟩
theorem profilesValid3751 : retention3751.ProfilesValid := by
  change ∀ j : Fin 16, (retention3751.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch571.valid22841
  · exact MergedCutProfiles.Batch571.valid22847
  · exact MergedCutProfiles.Batch571.valid22851
  · exact MergedCutProfiles.Batch571.valid22854
  · exact MergedCutProfiles.Batch571.valid22857
  · exact MergedCutProfiles.Batch571.valid22858
  · exact MergedCutProfiles.Batch571.valid22859
  · exact MergedCutProfiles.Batch571.valid22860
  · exact MergedCutProfiles.Batch571.valid22861
  · exact MergedCutProfiles.Batch571.valid22862
  · exact MergedCutProfiles.Batch571.valid22863
  · exact MergedCutProfiles.Batch571.valid22864
  · exact MergedCutProfiles.Batch571.valid22865
  · exact MergedCutProfiles.Batch571.valid22866
  · exact MergedCutProfiles.Batch571.valid22867
  · exact MergedCutProfiles.Batch571.valid22868
theorem numericValid3751 : retention3751.NumericValid := by decide +kernel
def certificate3751 : RatCutBinCertificate := ⟨⟨retention3751,(225002495593763589/125000000000000000),(21663071517499/3125000000000000),(3880866428226591227/500000000000000000),(53072891309973047297007/1000000000000000000),(23480515069189347/10000000000000000)⟩,(31248946906396391/31250000000000000),(7408427984894403/20000000000000000),(261704687820418207/1000000000000000000),(94934305516210389/500000000000000000)⟩
theorem valid3751 : certificate3751.Valid := by decide +kernel
theorem sound3751 : certificate3751.Sound := rat_cut_bin_certificate_sound certificate3751 profilesValid3751 numericValid3751 valid3751

def retention3752 : RatCutRetentionCertificate := ⟨(1/80),(13/1000),(64000000000000000000/6822131672314993651691),(33328186907079937/7812500000000000),(13/10),(948453501745536321351554707631661170679/426600792410623193600000000000000000000),true,MergedCutProfiles.Batch571.profile22867,![MergedCutProfiles.Batch571.profile22867,MergedCutProfiles.Batch571.profile22869,MergedCutProfiles.Batch571.profile22870,MergedCutProfiles.Batch571.profile22871,MergedCutProfiles.Batch571.profile22872,MergedCutProfiles.Batch571.profile22873,MergedCutProfiles.Batch571.profile22874,MergedCutProfiles.Batch571.profile22875,MergedCutProfiles.Batch571.profile22876,MergedCutProfiles.Batch571.profile22877,MergedCutProfiles.Batch571.profile22878,MergedCutProfiles.Batch571.profile22879,MergedCutProfiles.Batch572.profile22880,MergedCutProfiles.Batch572.profile22881,MergedCutProfiles.Batch572.profile22882,MergedCutProfiles.Batch572.profile22883]⟩
theorem profilesValid3752 : retention3752.ProfilesValid := by
  change ∀ j : Fin 16, (retention3752.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch571.valid22867
  · exact MergedCutProfiles.Batch571.valid22869
  · exact MergedCutProfiles.Batch571.valid22870
  · exact MergedCutProfiles.Batch571.valid22871
  · exact MergedCutProfiles.Batch571.valid22872
  · exact MergedCutProfiles.Batch571.valid22873
  · exact MergedCutProfiles.Batch571.valid22874
  · exact MergedCutProfiles.Batch571.valid22875
  · exact MergedCutProfiles.Batch571.valid22876
  · exact MergedCutProfiles.Batch571.valid22877
  · exact MergedCutProfiles.Batch571.valid22878
  · exact MergedCutProfiles.Batch571.valid22879
  · exact MergedCutProfiles.Batch572.valid22880
  · exact MergedCutProfiles.Batch572.valid22881
  · exact MergedCutProfiles.Batch572.valid22882
  · exact MergedCutProfiles.Batch572.valid22883
theorem numericValid3752 : retention3752.NumericValid := by decide +kernel
def certificate3752 : RatCutBinCertificate := ⟨⟨retention3752,(225002495593763589/125000000000000000),(21663071517499/3125000000000000),(3880866428226591227/500000000000000000),(53072891309973047297007/1000000000000000000),(1110595611007439409/500000000000000000)⟩,(31248946906396391/31250000000000000),(254675456607703657/1000000000000000000),(396912976645232409/1000000000000000000),(518423286523416079/1000000000000000000)⟩
theorem valid3752 : certificate3752.Valid := by decide +kernel
theorem sound3752 : certificate3752.Sound := rat_cut_bin_certificate_sound certificate3752 profilesValid3752 numericValid3752 valid3752

def retention3753 : RatCutRetentionCertificate := ⟨(1/80),(13/1000),(1/2),64,1,(255369591088824322579348446945530987991/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch572.profile22884,(fun _ => MergedCutProfiles.Batch572.profile22884)⟩
theorem profilesValid3753 : retention3753.ProfilesValid := by
  exact MergedCutProfiles.Batch572.valid22884
theorem numericValid3753 : retention3753.NumericValid := by decide +kernel
def certificate3753 : RatCutBinCertificate := ⟨⟨retention3753,(225002495593763589/125000000000000000),(21663071517499/3125000000000000),(3880866428226591227/500000000000000000),(53072891309973047297007/1000000000000000000),(497964912891073849/500000000000000000)⟩,(31248946906396391/31250000000000000),(89287153174500311/200000000000000000),(96765722239821479/500000000000000000),(18978388266955653/100000000000000000)⟩
theorem valid3753 : certificate3753.Valid := by decide +kernel
theorem sound3753 : certificate3753.Sound := rat_cut_bin_certificate_sound certificate3753 profilesValid3753 numericValid3753 valid3753

def retention3754 : RatCutRetentionCertificate := ⟨(1/80),(13/1000),(64000000000000000000/6822131672314993651691),(16837411258889767929/1000000000000000000),1,(4631962226422649534656658816625562279/2104676407361220991125000000000000000),false,MergedCutProfiles.Batch572.profile22885,(fun _ => MergedCutProfiles.Batch572.profile22885)⟩
theorem profilesValid3754 : retention3754.ProfilesValid := by
  exact MergedCutProfiles.Batch572.valid22885
theorem numericValid3754 : retention3754.NumericValid := by decide +kernel
def certificate3754 : RatCutBinCertificate := ⟨⟨retention3754,(221589144843763589/125000000000000000),(21663071517499/3125000000000000),(3880866428226591227/500000000000000000),(53072891309973047297007/1000000000000000000),(1099606091236176187/500000000000000000)⟩,(24999170305699303/25000000000000000),(32728730382590879/1000000000000000000),(52272493565300671/62500000000000000),(1626787726717236611/1000000000000000000)⟩
theorem valid3754 : certificate3754.Valid := by decide +kernel
theorem sound3754 : certificate3754.Sound := rat_cut_bin_certificate_sound certificate3754 profilesValid3754 numericValid3754 valid3754

def retention3755 : RatCutRetentionCertificate := ⟨(1/80),(13/1000),(1/2),64,1,(255369591088824322579348446945530987991/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch572.profile22884,(fun _ => MergedCutProfiles.Batch572.profile22884)⟩
theorem profilesValid3755 : retention3755.ProfilesValid := by
  exact MergedCutProfiles.Batch572.valid22884
theorem numericValid3755 : retention3755.NumericValid := by decide +kernel
def certificate3755 : RatCutBinCertificate := ⟨⟨retention3755,(221589144843763589/125000000000000000),(21663071517499/3125000000000000),(3880866428226591227/500000000000000000),(53072891309973047297007/1000000000000000000),(995954214121336999/1000000000000000000)⟩,(24999170305699303/25000000000000000),(14453962150809851/200000000000000000),(731171504537839053/1000000000000000000),(71703068379307087/100000000000000000)⟩
theorem valid3755 : certificate3755.Valid := by decide +kernel
theorem sound3755 : certificate3755.Sound := rat_cut_bin_certificate_sound certificate3755 profilesValid3755 numericValid3755 valid3755

def certificates : List RatCutBinCertificate := [certificate3744,certificate3745,certificate3746,certificate3747,certificate3748,certificate3749,certificate3750,certificate3751,certificate3752,certificate3753,certificate3754,certificate3755]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3744,List.forall_mem_cons.mpr ⟨sound3745,List.forall_mem_cons.mpr ⟨sound3746,List.forall_mem_cons.mpr ⟨sound3747,List.forall_mem_cons.mpr ⟨sound3748,List.forall_mem_cons.mpr ⟨sound3749,List.forall_mem_cons.mpr ⟨sound3750,List.forall_mem_cons.mpr ⟨sound3751,List.forall_mem_cons.mpr ⟨sound3752,List.forall_mem_cons.mpr ⟨sound3753,List.forall_mem_cons.mpr ⟨sound3754,List.forall_mem_cons.mpr ⟨sound3755,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch312
