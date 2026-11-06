import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch070
import Cycle12.MergedCutProfiles.Batch071
import Cycle12.MergedCutProfiles.Batch072

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch035

def retention420 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(14465976936901554450/37419646445651247031),(925251012076852789/250000000000000000),(5/4),(18146199984128053366169729601687485551/14804016193229644624000000000000000000),false,MergedCutProfiles.Batch070.profile2818,(fun _ => MergedCutProfiles.Batch070.profile2818)⟩
theorem profilesValid420 : retention420.ProfilesValid := by
  exact MergedCutProfiles.Batch070.valid2818
theorem numericValid420 : retention420.NumericValid := by decide +kernel
def certificate420 : RatCutBinCertificate := ⟨⟨retention420,(2044963405672943657/1000000000000000000),(61591158108543061/1000000000000000000),(10686964870379908197/1000000000000000000),(201006317128626647647/500000000000000000),(242205910203449211/200000000000000000)⟩,(248801762650866271/250000000000000000),(14211386577624741/31250000000000000),(186892044445255203/1000000000000000000),(148924622020979981/1000000000000000000)⟩
theorem valid420 : certificate420.Valid := by decide +kernel
theorem sound420 : certificate420.Sound := rat_cut_bin_certificate_sound certificate420 profilesValid420 numericValid420 valid420

def retention421 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(18367952141647475901/37419646445651247031),(289319538738031089/20000000000000000),(21/20),(235690618118579278656696782597173115231/231455630990424871200000000000000000000),false,MergedCutProfiles.Batch070.profile2819,(fun _ => MergedCutProfiles.Batch070.profile2819)⟩
theorem profilesValid421 : retention421.ProfilesValid := by
  exact MergedCutProfiles.Batch070.valid2819
theorem numericValid421 : retention421.NumericValid := by decide +kernel
def certificate421 : RatCutBinCertificate := ⟨⟨retention421,(2044963405672943657/1000000000000000000),(61591158108543061/1000000000000000000),(10686964870379908197/1000000000000000000),(201006317128626647647/500000000000000000),(1005922244670257999/1000000000000000000)⟩,(248801762650866271/250000000000000000),(481589705006877667/1000000000000000000),(166530534419947177/1000000000000000000),(74665217116946679/500000000000000000)⟩
theorem valid421 : certificate421.Valid := by decide +kernel
theorem sound421 : certificate421.Sound := rat_cut_bin_certificate_sound certificate421 profilesValid421 numericValid421 valid421

def retention422 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(18551631663063950661/37419646445651247031),(18367952141647475901/1000000000000000000),1,(406579542088014340224178088330561869/408176714258832797800000000000000000),false,MergedCutProfiles.Batch070.profile2820,(fun _ => MergedCutProfiles.Batch070.profile2820)⟩
theorem profilesValid422 : retention422.ProfilesValid := by
  exact MergedCutProfiles.Batch070.valid2820
theorem numericValid422 : retention422.NumericValid := by decide +kernel
def certificate422 : RatCutBinCertificate := ⟨⟨retention422,(2044963405672943657/1000000000000000000),(61591158108543061/1000000000000000000),(10686964870379908197/1000000000000000000),(201006317128626647647/500000000000000000),(984301417641161051/1000000000000000000)⟩,(248801762650866271/250000000000000000),(60906167944798703/125000000000000000),(162428390989424697/1000000000000000000),(4718708898982567/31250000000000000)⟩
theorem valid422 : certificate422.Valid := by decide +kernel
theorem sound422 : certificate422.Sound := rat_cut_bin_certificate_sound certificate422 profilesValid422 numericValid422 valid422

def retention423 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(1/2),(18551631663063950661/1000000000000000000),1,(65459608346180289192880511061086447/66255827368085538075000000000000000),false,MergedCutProfiles.Batch070.profile2821,(fun _ => MergedCutProfiles.Batch070.profile2821)⟩
theorem profilesValid423 : retention423.ProfilesValid := by
  exact MergedCutProfiles.Batch070.valid2821
theorem numericValid423 : retention423.NumericValid := by decide +kernel
def certificate423 : RatCutBinCertificate := ⟨⟨retention423,(2044963405672943657/1000000000000000000),(61591158108543061/1000000000000000000),(10686964870379908197/1000000000000000000),(201006317128626647647/500000000000000000),(48809850910995241/50000000000000000)⟩,(248801762650866271/250000000000000000),(61389055403632553/125000000000000000),(79833093061424351/500000000000000000),(147344197696662797/1000000000000000000)⟩
theorem valid423 : certificate423.Valid := by decide +kernel
theorem sound423 : certificate423.Sound := rat_cut_bin_certificate_sound certificate423 profilesValid423 numericValid423 valid423

def retention424 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(16028087832452208432/37419646445651247031),(3675516644893656647/1000000000000000000),(5/4),(268821393618292057795669735380343297231/235233065273194025408000000000000000000),false,MergedCutProfiles.Batch070.profile2822,(fun _ => MergedCutProfiles.Batch070.profile2822)⟩
theorem profilesValid424 : retention424.ProfilesValid := by
  exact MergedCutProfiles.Batch070.valid2822
theorem numericValid424 : retention424.NumericValid := by decide +kernel
def certificate424 : RatCutBinCertificate := ⟨⟨retention424,(2430885917672943657/1000000000000000000),(61591158108543061/1000000000000000000),(10686964870379908197/1000000000000000000),(201006317128626647647/500000000000000000),(281318686696646967/250000000000000000)⟩,(99430221458091091/100000000000000000),(182500187508067443/500000000000000000),(133563847633652317/500000000000000000),(199832986498918487/1000000000000000000)⟩
theorem valid424 : certificate424.Valid := by decide +kernel
theorem sound424 : certificate424.Sound := rat_cut_bin_certificate_sound certificate424 profilesValid424 numericValid424 valid424

def retention425 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(18608112387420624539/37419646445651247031),(1001755489528263027/62500000000000000),1,(63543669629632548527833393568923330271/64112351329808833728000000000000000000),false,MergedCutProfiles.Batch070.profile2823,(fun _ => MergedCutProfiles.Batch070.profile2823)⟩
theorem profilesValid425 : retention425.ProfilesValid := by
  exact MergedCutProfiles.Batch070.valid2823
theorem numericValid425 : retention425.NumericValid := by decide +kernel
def certificate425 : RatCutBinCertificate := ⟨⟨retention425,(2430885917672943657/1000000000000000000),(61591158108543061/1000000000000000000),(10686964870379908197/1000000000000000000),(201006317128626647647/500000000000000000),(977120094541568527/1000000000000000000)⟩,(99430221458091091/100000000000000000),(210171557655862819/500000000000000000),(107675764896570151/500000000000000000),(197172471667822921/1000000000000000000)⟩
theorem valid425 : certificate425.Valid := by decide +kernel
theorem sound425 : certificate425.Sound := rat_cut_bin_certificate_sound certificate425 profilesValid425 numericValid425 valid425

def retention426 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(1/2),(18608112387420624539/1000000000000000000),1,(1149078482836972475545489931583779857/1163007024213789033687500000000000000),false,MergedCutProfiles.Batch070.profile2821,(fun _ => MergedCutProfiles.Batch070.profile2821)⟩
theorem profilesValid426 : retention426.ProfilesValid := by
  exact MergedCutProfiles.Batch070.valid2821
theorem numericValid426 : retention426.NumericValid := by decide +kernel
def certificate426 : RatCutBinCertificate := ⟨⟨retention426,(2430885917672943657/1000000000000000000),(61591158108543061/1000000000000000000),(10686964870379908197/1000000000000000000),(201006317128626647647/500000000000000000),(243503468960249823/250000000000000000)⟩,(99430221458091091/100000000000000000),(16867345107117911/40000000000000000),(42838378792358247/200000000000000000),(197092536105364367/1000000000000000000)⟩
theorem valid426 : certificate426.Valid := by decide +kernel
theorem sound426 : certificate426.Sound := rat_cut_bin_certificate_sound certificate426 profilesValid426 numericValid426 valid426

def retention427 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(777910158341618453/36332269783165894480),(48138004847872429/62500000000000000),(67/20),(174568010865028500741/80000000000000000000),true,MergedCutProfiles.Batch070.profile2824,![MergedCutProfiles.Batch070.profile2824,MergedCutProfiles.Batch070.profile2825,MergedCutProfiles.Batch070.profile2826,MergedCutProfiles.Batch070.profile2827,MergedCutProfiles.Batch070.profile2828,MergedCutProfiles.Batch070.profile2829,MergedCutProfiles.Batch070.profile2830,MergedCutProfiles.Batch070.profile2831,MergedCutProfiles.Batch070.profile2832,MergedCutProfiles.Batch070.profile2833,MergedCutProfiles.Batch070.profile2834,MergedCutProfiles.Batch070.profile2835,MergedCutProfiles.Batch070.profile2836,MergedCutProfiles.Batch070.profile2837,MergedCutProfiles.Batch070.profile2838,MergedCutProfiles.Batch070.profile2839]⟩
theorem profilesValid427 : retention427.ProfilesValid := by
  change ∀ j : Fin 16, (retention427.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch070.valid2824
  · exact MergedCutProfiles.Batch070.valid2825
  · exact MergedCutProfiles.Batch070.valid2826
  · exact MergedCutProfiles.Batch070.valid2827
  · exact MergedCutProfiles.Batch070.valid2828
  · exact MergedCutProfiles.Batch070.valid2829
  · exact MergedCutProfiles.Batch070.valid2830
  · exact MergedCutProfiles.Batch070.valid2831
  · exact MergedCutProfiles.Batch070.valid2832
  · exact MergedCutProfiles.Batch070.valid2833
  · exact MergedCutProfiles.Batch070.valid2834
  · exact MergedCutProfiles.Batch070.valid2835
  · exact MergedCutProfiles.Batch070.valid2836
  · exact MergedCutProfiles.Batch070.valid2837
  · exact MergedCutProfiles.Batch070.valid2838
  · exact MergedCutProfiles.Batch070.valid2839
theorem numericValid427 : retention427.NumericValid := by decide +kernel
def certificate427 : RatCutBinCertificate := ⟨⟨retention427,(102635127272770413/50000000000000000),(247684185361181/3906250000000000),(10847452451916845639/1000000000000000000),(395155788030754533383/1000000000000000000),(2141901776895236091/1000000000000000000)⟩,(24878092418289623/25000000000000000),(25708851475633127/62500000000000000),(223249824043344261/1000000000000000000),(113740023835930781/1000000000000000000)⟩
theorem valid427 : certificate427.Valid := by decide +kernel
theorem sound427 : certificate427.Sound := rat_cut_bin_certificate_sound certificate427 profilesValid427 numericValid427 valid427

def retention428 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(885334323989392153/36332269783165894480),(777910158341618453/1000000000000000000),(33/10),(2771767534470760487641/1280000000000000000000),true,MergedCutProfiles.Batch071.profile2840,![MergedCutProfiles.Batch071.profile2840,MergedCutProfiles.Batch071.profile2841,MergedCutProfiles.Batch071.profile2842,MergedCutProfiles.Batch071.profile2843,MergedCutProfiles.Batch071.profile2844,MergedCutProfiles.Batch071.profile2845,MergedCutProfiles.Batch070.profile2831,MergedCutProfiles.Batch071.profile2846,MergedCutProfiles.Batch071.profile2847,MergedCutProfiles.Batch071.profile2848,MergedCutProfiles.Batch071.profile2849,MergedCutProfiles.Batch071.profile2850,MergedCutProfiles.Batch071.profile2851,MergedCutProfiles.Batch070.profile2839,MergedCutProfiles.Batch071.profile2852,MergedCutProfiles.Batch071.profile2853]⟩
theorem profilesValid428 : retention428.ProfilesValid := by
  change ∀ j : Fin 16, (retention428.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch071.valid2840
  · exact MergedCutProfiles.Batch071.valid2841
  · exact MergedCutProfiles.Batch071.valid2842
  · exact MergedCutProfiles.Batch071.valid2843
  · exact MergedCutProfiles.Batch071.valid2844
  · exact MergedCutProfiles.Batch071.valid2845
  · exact MergedCutProfiles.Batch070.valid2831
  · exact MergedCutProfiles.Batch071.valid2846
  · exact MergedCutProfiles.Batch071.valid2847
  · exact MergedCutProfiles.Batch071.valid2848
  · exact MergedCutProfiles.Batch071.valid2849
  · exact MergedCutProfiles.Batch071.valid2850
  · exact MergedCutProfiles.Batch071.valid2851
  · exact MergedCutProfiles.Batch070.valid2839
  · exact MergedCutProfiles.Batch071.valid2852
  · exact MergedCutProfiles.Batch071.valid2853
theorem numericValid428 : retention428.NumericValid := by decide +kernel
def certificate428 : RatCutBinCertificate := ⟨⟨retention428,(102635127272770413/50000000000000000),(247684185361181/3906250000000000),(10847452451916845639/1000000000000000000),(395155788030754533383/1000000000000000000),(106292249516707113/50000000000000000)⟩,(24878092418289623/25000000000000000),(41249052606041913/100000000000000000),(13889428387496039/62500000000000000),(5689397228127093/50000000000000000)⟩
theorem valid428 : certificate428.Valid := by decide +kernel
theorem sound428 : certificate428.Sound := rat_cut_bin_certificate_sound certificate428 profilesValid428 numericValid428 valid428

def retention429 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(12008718850000000/454153372289573681),(885334323989392153/1000000000000000000),(59/20),(2750960277383885226969/1280000000000000000000),true,MergedCutProfiles.Batch071.profile2854,![MergedCutProfiles.Batch071.profile2854,MergedCutProfiles.Batch071.profile2855,MergedCutProfiles.Batch071.profile2856,MergedCutProfiles.Batch071.profile2857,MergedCutProfiles.Batch071.profile2858,MergedCutProfiles.Batch071.profile2859,MergedCutProfiles.Batch071.profile2860,MergedCutProfiles.Batch071.profile2861,MergedCutProfiles.Batch071.profile2862,MergedCutProfiles.Batch071.profile2863,MergedCutProfiles.Batch071.profile2850,MergedCutProfiles.Batch071.profile2851,MergedCutProfiles.Batch071.profile2864,MergedCutProfiles.Batch071.profile2865,MergedCutProfiles.Batch071.profile2866,MergedCutProfiles.Batch071.profile2867]⟩
theorem profilesValid429 : retention429.ProfilesValid := by
  change ∀ j : Fin 16, (retention429.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch071.valid2854
  · exact MergedCutProfiles.Batch071.valid2855
  · exact MergedCutProfiles.Batch071.valid2856
  · exact MergedCutProfiles.Batch071.valid2857
  · exact MergedCutProfiles.Batch071.valid2858
  · exact MergedCutProfiles.Batch071.valid2859
  · exact MergedCutProfiles.Batch071.valid2860
  · exact MergedCutProfiles.Batch071.valid2861
  · exact MergedCutProfiles.Batch071.valid2862
  · exact MergedCutProfiles.Batch071.valid2863
  · exact MergedCutProfiles.Batch071.valid2850
  · exact MergedCutProfiles.Batch071.valid2851
  · exact MergedCutProfiles.Batch071.valid2864
  · exact MergedCutProfiles.Batch071.valid2865
  · exact MergedCutProfiles.Batch071.valid2866
  · exact MergedCutProfiles.Batch071.valid2867
theorem numericValid429 : retention429.NumericValid := by decide +kernel
def certificate429 : RatCutBinCertificate := ⟨⟨retention429,(102635127272770413/50000000000000000),(247684185361181/3906250000000000),(10847452451916845639/1000000000000000000),(395155788030754533383/1000000000000000000),(2113789188420967737/1000000000000000000)⟩,(24878092418289623/25000000000000000),(625519331651773/1600000000000000),(9675116987454451/40000000000000000),(5409167641636057/40000000000000000)⟩
theorem valid429 : certificate429.Valid := by decide +kernel
theorem sound429 : certificate429.Sound := rat_cut_bin_certificate_sound certificate429 profilesValid429 numericValid429 valid429

def retention430 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(140517458337988869/4541533722895736810),(240174377/250000000),(11/4),(34017298366268389789/16000000000000000000),true,MergedCutProfiles.Batch071.profile2868,![MergedCutProfiles.Batch071.profile2868,MergedCutProfiles.Batch071.profile2869,MergedCutProfiles.Batch071.profile2870,MergedCutProfiles.Batch071.profile2871,MergedCutProfiles.Batch071.profile2872,MergedCutProfiles.Batch071.profile2860,MergedCutProfiles.Batch071.profile2873,MergedCutProfiles.Batch071.profile2874,MergedCutProfiles.Batch070.profile2836,MergedCutProfiles.Batch071.profile2875,MergedCutProfiles.Batch071.profile2876,MergedCutProfiles.Batch071.profile2865,MergedCutProfiles.Batch071.profile2877,MergedCutProfiles.Batch071.profile2878,MergedCutProfiles.Batch071.profile2879,MergedCutProfiles.Batch072.profile2880]⟩
theorem profilesValid430 : retention430.ProfilesValid := by
  change ∀ j : Fin 16, (retention430.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch071.valid2868
  · exact MergedCutProfiles.Batch071.valid2869
  · exact MergedCutProfiles.Batch071.valid2870
  · exact MergedCutProfiles.Batch071.valid2871
  · exact MergedCutProfiles.Batch071.valid2872
  · exact MergedCutProfiles.Batch071.valid2860
  · exact MergedCutProfiles.Batch071.valid2873
  · exact MergedCutProfiles.Batch071.valid2874
  · exact MergedCutProfiles.Batch070.valid2836
  · exact MergedCutProfiles.Batch071.valid2875
  · exact MergedCutProfiles.Batch071.valid2876
  · exact MergedCutProfiles.Batch071.valid2865
  · exact MergedCutProfiles.Batch071.valid2877
  · exact MergedCutProfiles.Batch071.valid2878
  · exact MergedCutProfiles.Batch071.valid2879
  · exact MergedCutProfiles.Batch072.valid2880
theorem numericValid430 : retention430.NumericValid := by decide +kernel
def certificate430 : RatCutBinCertificate := ⟨⟨retention430,(102635127272770413/50000000000000000),(247684185361181/3906250000000000),(10847452451916845639/1000000000000000000),(395155788030754533383/1000000000000000000),(523270635747304231/250000000000000000)⟩,(24878092418289623/25000000000000000),(381109778338222413/1000000000000000000),(1962840006439709/7812500000000000),(147615900240813093/1000000000000000000)⟩
theorem valid430 : certificate430.Valid := by decide +kernel
theorem sound430 : certificate430.Sound := rat_cut_bin_certificate_sound certificate430 profilesValid430 numericValid430 valid430

def retention431 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(3040588516702043483/36332269783165894480),(140517458337988869/125000000000000000),(12/5),(310502711339792573523/160000000000000000000),true,MergedCutProfiles.Batch072.profile2881,![MergedCutProfiles.Batch072.profile2881,MergedCutProfiles.Batch072.profile2882,MergedCutProfiles.Batch072.profile2883,MergedCutProfiles.Batch072.profile2884,MergedCutProfiles.Batch072.profile2885,MergedCutProfiles.Batch072.profile2886,MergedCutProfiles.Batch072.profile2887,MergedCutProfiles.Batch072.profile2888,MergedCutProfiles.Batch072.profile2889,MergedCutProfiles.Batch072.profile2890,MergedCutProfiles.Batch072.profile2891,MergedCutProfiles.Batch072.profile2892,MergedCutProfiles.Batch072.profile2893,MergedCutProfiles.Batch072.profile2894,MergedCutProfiles.Batch072.profile2895,MergedCutProfiles.Batch072.profile2896]⟩
theorem profilesValid431 : retention431.ProfilesValid := by
  change ∀ j : Fin 16, (retention431.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch072.valid2881
  · exact MergedCutProfiles.Batch072.valid2882
  · exact MergedCutProfiles.Batch072.valid2883
  · exact MergedCutProfiles.Batch072.valid2884
  · exact MergedCutProfiles.Batch072.valid2885
  · exact MergedCutProfiles.Batch072.valid2886
  · exact MergedCutProfiles.Batch072.valid2887
  · exact MergedCutProfiles.Batch072.valid2888
  · exact MergedCutProfiles.Batch072.valid2889
  · exact MergedCutProfiles.Batch072.valid2890
  · exact MergedCutProfiles.Batch072.valid2891
  · exact MergedCutProfiles.Batch072.valid2892
  · exact MergedCutProfiles.Batch072.valid2893
  · exact MergedCutProfiles.Batch072.valid2894
  · exact MergedCutProfiles.Batch072.valid2895
  · exact MergedCutProfiles.Batch072.valid2896
theorem numericValid431 : retention431.NumericValid := by decide +kernel
def certificate431 : RatCutBinCertificate := ⟨⟨retention431,(102635127272770413/50000000000000000),(247684185361181/3906250000000000),(10847452451916845639/1000000000000000000),(395155788030754533383/1000000000000000000),(1911843199728372019/1000000000000000000)⟩,(24878092418289623/25000000000000000),(78321268748998449/200000000000000000),(1507885595830993/6250000000000000),(147540939449255273/1000000000000000000)⟩
theorem valid431 : certificate431.Valid := by decide +kernel
theorem sound431 : certificate431.Sound := rat_cut_bin_certificate_sound certificate431 profilesValid431 numericValid431 valid431

def certificates : List RatCutBinCertificate := [certificate420,certificate421,certificate422,certificate423,certificate424,certificate425,certificate426,certificate427,certificate428,certificate429,certificate430,certificate431]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound420,List.forall_mem_cons.mpr ⟨sound421,List.forall_mem_cons.mpr ⟨sound422,List.forall_mem_cons.mpr ⟨sound423,List.forall_mem_cons.mpr ⟨sound424,List.forall_mem_cons.mpr ⟨sound425,List.forall_mem_cons.mpr ⟨sound426,List.forall_mem_cons.mpr ⟨sound427,List.forall_mem_cons.mpr ⟨sound428,List.forall_mem_cons.mpr ⟨sound429,List.forall_mem_cons.mpr ⟨sound430,List.forall_mem_cons.mpr ⟨sound431,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch035
