import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch340
import Cycle12.MergedCutProfiles.Batch341
import Cycle12.MergedCutProfiles.Batch342
import Cycle12.MergedCutProfiles.Batch467
import Cycle12.MergedCutProfiles.Batch468

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch252

def retention3024 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(1/2),64,1,(255378512847706981515811673095846818951/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch340.profile13635,(fun _ => MergedCutProfiles.Batch340.profile13635)⟩
theorem profilesValid3024 : retention3024.ProfilesValid := by
  exact MergedCutProfiles.Batch340.valid13635
theorem numericValid3024 : retention3024.NumericValid := by decide +kernel
def certificate3024 : RatCutBinCertificate := ⟨⟨retention3024,(388139244536164797/200000000000000000),(51337219122942991/1000000000000000000),(10227335373511528917/1000000000000000000),(1156931639542237074153/500000000000000000),(197566155452885521/200000000000000000)⟩,(499600816720827933/500000000000000000),(478364234930048671/1000000000000000000),(168898079529432551/1000000000000000000),(82087172865251173/500000000000000000)⟩
theorem valid3024 : certificate3024.Valid := by decide +kernel
theorem sound3024 : certificate3024.Sound := rat_cut_bin_certificate_sound certificate3024 profilesValid3024 numericValid3024 valid3024

def retention3025 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(64000000000000000000/225076812372183446073),(2425348173596243839/250000000000000000),1,(135337196539032038934829657316721363/97013926943849753560000000000000000),false,MergedCutProfiles.Batch467.profile18692,(fun _ => MergedCutProfiles.Batch467.profile18692)⟩
theorem profilesValid3025 : retention3025.ProfilesValid := by
  exact MergedCutProfiles.Batch467.valid18692
theorem numericValid3025 : retention3025.NumericValid := by decide +kernel
def certificate3025 : RatCutBinCertificate := ⟨⟨retention3025,(417528117136164797/200000000000000000),(51337219122942991/1000000000000000000),(10227335373511528917/1000000000000000000),(1156931639542237074153/500000000000000000),(6922746871732013/5000000000000000)⟩,(999141180619874663/1000000000000000000),(93626876606916419/1000000000000000000),(680689838530614579/1000000000000000000),(25750060965132337/31250000000000000)⟩
theorem valid3025 : certificate3025.Valid := by decide +kernel
theorem sound3025 : certificate3025.Sound := rat_cut_bin_certificate_sound certificate3025 profilesValid3025 numericValid3025 valid3025

def retention3026 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(1/2),64,1,(255378512847706981515811673095846818951/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch340.profile13635,(fun _ => MergedCutProfiles.Batch340.profile13635)⟩
theorem profilesValid3026 : retention3026.ProfilesValid := by
  exact MergedCutProfiles.Batch340.valid13635
theorem numericValid3026 : retention3026.NumericValid := by decide +kernel
def certificate3026 : RatCutBinCertificate := ⟨⟨retention3026,(417528117136164797/200000000000000000),(51337219122942991/1000000000000000000),(10227335373511528917/1000000000000000000),(1156931639542237074153/500000000000000000),(987093173841651389/1000000000000000000)⟩,(999141180619874663/1000000000000000000),(131326035741494511/1000000000000000000),(300248756656936577/500000000000000000),(583238312191434401/1000000000000000000)⟩
theorem valid3026 : certificate3026.Valid := by decide +kernel
theorem sound3026 : certificate3026.Sound := rat_cut_bin_certificate_sound certificate3026 profilesValid3026 numericValid3026 valid3026

def retention3027 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(95347451055097718/30185364110859643709),(13216478364072951/20000000000000000),4,(18556066995309123291/8000000000000000000),true,MergedCutProfiles.Batch467.profile18693,![MergedCutProfiles.Batch467.profile18693,MergedCutProfiles.Batch467.profile18694,MergedCutProfiles.Batch467.profile18695,MergedCutProfiles.Batch467.profile18696,MergedCutProfiles.Batch467.profile18697,MergedCutProfiles.Batch467.profile18698,MergedCutProfiles.Batch467.profile18699,MergedCutProfiles.Batch467.profile18700,MergedCutProfiles.Batch467.profile18701,MergedCutProfiles.Batch467.profile18702,MergedCutProfiles.Batch341.profile13641,MergedCutProfiles.Batch467.profile18703,MergedCutProfiles.Batch467.profile18704,MergedCutProfiles.Batch467.profile18705,MergedCutProfiles.Batch467.profile18706,MergedCutProfiles.Batch467.profile18707]⟩
theorem profilesValid3027 : retention3027.ProfilesValid := by
  change ∀ j : Fin 16, (retention3027.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch467.valid18693
  · exact MergedCutProfiles.Batch467.valid18694
  · exact MergedCutProfiles.Batch467.valid18695
  · exact MergedCutProfiles.Batch467.valid18696
  · exact MergedCutProfiles.Batch467.valid18697
  · exact MergedCutProfiles.Batch467.valid18698
  · exact MergedCutProfiles.Batch467.valid18699
  · exact MergedCutProfiles.Batch467.valid18700
  · exact MergedCutProfiles.Batch467.valid18701
  · exact MergedCutProfiles.Batch467.valid18702
  · exact MergedCutProfiles.Batch341.valid13641
  · exact MergedCutProfiles.Batch467.valid18703
  · exact MergedCutProfiles.Batch467.valid18704
  · exact MergedCutProfiles.Batch467.valid18705
  · exact MergedCutProfiles.Batch467.valid18706
  · exact MergedCutProfiles.Batch467.valid18707
theorem numericValid3027 : retention3027.NumericValid := by decide +kernel
def certificate3027 : RatCutBinCertificate := ⟨⟨retention3027,(1948413449568935117/1000000000000000000),(853665110250683/15625000000000000),(5188665442598132791/500000000000000000),(440826974595350230217/200000000000000000),(1139237982283854499/500000000000000000)⟩,(999161361927879951/1000000000000000000),(103990657485568011/200000000000000000),(139988761065804507/1000000000000000000),(16384571993189971/250000000000000000)⟩
theorem valid3027 : certificate3027.Valid := by decide +kernel
theorem sound3027 : certificate3027.Sound := rat_cut_bin_certificate_sound certificate3027 profilesValid3027 numericValid3027 valid3027

def retention3028 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(1054849063053687506/211297548776017505963),(333716078692842013/500000000000000000),4,(18467349831666974161/8000000000000000000),true,MergedCutProfiles.Batch467.profile18708,![MergedCutProfiles.Batch467.profile18708,MergedCutProfiles.Batch467.profile18709,MergedCutProfiles.Batch467.profile18710,MergedCutProfiles.Batch467.profile18711,MergedCutProfiles.Batch467.profile18712,MergedCutProfiles.Batch467.profile18713,MergedCutProfiles.Batch341.profile13641,MergedCutProfiles.Batch467.profile18714,MergedCutProfiles.Batch467.profile18715,MergedCutProfiles.Batch467.profile18716,MergedCutProfiles.Batch341.profile13657,MergedCutProfiles.Batch467.profile18717,MergedCutProfiles.Batch341.profile13658,MergedCutProfiles.Batch467.profile18718,MergedCutProfiles.Batch467.profile18719,MergedCutProfiles.Batch468.profile18720]⟩
theorem profilesValid3028 : retention3028.ProfilesValid := by
  change ∀ j : Fin 16, (retention3028.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch467.valid18708
  · exact MergedCutProfiles.Batch467.valid18709
  · exact MergedCutProfiles.Batch467.valid18710
  · exact MergedCutProfiles.Batch467.valid18711
  · exact MergedCutProfiles.Batch467.valid18712
  · exact MergedCutProfiles.Batch467.valid18713
  · exact MergedCutProfiles.Batch341.valid13641
  · exact MergedCutProfiles.Batch467.valid18714
  · exact MergedCutProfiles.Batch467.valid18715
  · exact MergedCutProfiles.Batch467.valid18716
  · exact MergedCutProfiles.Batch341.valid13657
  · exact MergedCutProfiles.Batch467.valid18717
  · exact MergedCutProfiles.Batch341.valid13658
  · exact MergedCutProfiles.Batch467.valid18718
  · exact MergedCutProfiles.Batch467.valid18719
  · exact MergedCutProfiles.Batch468.valid18720
theorem numericValid3028 : retention3028.NumericValid := by decide +kernel
def certificate3028 : RatCutBinCertificate := ⟨⟨retention3028,(1948413449568935117/1000000000000000000),(853665110250683/15625000000000000),(5188665442598132791/500000000000000000),(440826974595350230217/200000000000000000),(566846580730522797/250000000000000000)⟩,(999161361927879951/1000000000000000000),(129838250941957703/250000000000000000),(28076340492112237/200000000000000000),(65573570608796397/1000000000000000000)⟩
theorem valid3028 : certificate3028.Valid := by decide +kernel
theorem sound3028 : certificate3028.Sound := rat_cut_bin_certificate_sound certificate3028 profilesValid3028 numericValid3028 valid3028

def retention3029 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(1163263362000000000/211297548776017505963),(527424531526843753/500000000000000000),(11/4),(292936390947455500733/128000000000000000000),true,MergedCutProfiles.Batch468.profile18721,![MergedCutProfiles.Batch468.profile18721,MergedCutProfiles.Batch341.profile13654,MergedCutProfiles.Batch342.profile13680,MergedCutProfiles.Batch341.profile13655,MergedCutProfiles.Batch468.profile18722,MergedCutProfiles.Batch468.profile18723,MergedCutProfiles.Batch468.profile18724,MergedCutProfiles.Batch467.profile18705,MergedCutProfiles.Batch342.profile13681,MergedCutProfiles.Batch468.profile18725,MergedCutProfiles.Batch467.profile18717,MergedCutProfiles.Batch342.profile13682,MergedCutProfiles.Batch468.profile18726,MergedCutProfiles.Batch341.profile13646,MergedCutProfiles.Batch468.profile18727,MergedCutProfiles.Batch341.profile13660]⟩
theorem profilesValid3029 : retention3029.ProfilesValid := by
  change ∀ j : Fin 16, (retention3029.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch468.valid18721
  · exact MergedCutProfiles.Batch341.valid13654
  · exact MergedCutProfiles.Batch342.valid13680
  · exact MergedCutProfiles.Batch341.valid13655
  · exact MergedCutProfiles.Batch468.valid18722
  · exact MergedCutProfiles.Batch468.valid18723
  · exact MergedCutProfiles.Batch468.valid18724
  · exact MergedCutProfiles.Batch467.valid18705
  · exact MergedCutProfiles.Batch342.valid13681
  · exact MergedCutProfiles.Batch468.valid18725
  · exact MergedCutProfiles.Batch467.valid18717
  · exact MergedCutProfiles.Batch342.valid13682
  · exact MergedCutProfiles.Batch468.valid18726
  · exact MergedCutProfiles.Batch341.valid13646
  · exact MergedCutProfiles.Batch468.valid18727
  · exact MergedCutProfiles.Batch341.valid13660
theorem numericValid3029 : retention3029.NumericValid := by decide +kernel
def certificate3029 : RatCutBinCertificate := ⟨⟨retention3029,(1948413449568935117/1000000000000000000),(853665110250683/15625000000000000),(5188665442598132791/500000000000000000),(440826974595350230217/200000000000000000),(2260355795993410177/1000000000000000000)⟩,(999161361927879951/1000000000000000000),(405163037728874251/1000000000000000000),(114392446749576931/500000000000000000),(146388372198150651/1000000000000000000)⟩
theorem valid3029 : certificate3029.Valid := by decide +kernel
theorem sound3029 : certificate3029.Sound := rat_cut_bin_certificate_sound certificate3029 profilesValid3029 numericValid3029 valid3029

def retention3030 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(1700655167474069176/211297548776017505963),(581631681/500000000),(51/20),(906020776951818313/400000000000000000),true,MergedCutProfiles.Batch468.profile18728,![MergedCutProfiles.Batch468.profile18728,MergedCutProfiles.Batch467.profile18697,MergedCutProfiles.Batch468.profile18729,MergedCutProfiles.Batch468.profile18730,MergedCutProfiles.Batch467.profile18714,MergedCutProfiles.Batch468.profile18731,MergedCutProfiles.Batch468.profile18732,MergedCutProfiles.Batch468.profile18733,MergedCutProfiles.Batch468.profile18734,MergedCutProfiles.Batch468.profile18735,MergedCutProfiles.Batch468.profile18736,MergedCutProfiles.Batch468.profile18737,MergedCutProfiles.Batch341.profile13649,MergedCutProfiles.Batch341.profile13650,MergedCutProfiles.Batch341.profile13663,MergedCutProfiles.Batch468.profile18738]⟩
theorem profilesValid3030 : retention3030.ProfilesValid := by
  change ∀ j : Fin 16, (retention3030.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch468.valid18728
  · exact MergedCutProfiles.Batch467.valid18697
  · exact MergedCutProfiles.Batch468.valid18729
  · exact MergedCutProfiles.Batch468.valid18730
  · exact MergedCutProfiles.Batch467.valid18714
  · exact MergedCutProfiles.Batch468.valid18731
  · exact MergedCutProfiles.Batch468.valid18732
  · exact MergedCutProfiles.Batch468.valid18733
  · exact MergedCutProfiles.Batch468.valid18734
  · exact MergedCutProfiles.Batch468.valid18735
  · exact MergedCutProfiles.Batch468.valid18736
  · exact MergedCutProfiles.Batch468.valid18737
  · exact MergedCutProfiles.Batch341.valid13649
  · exact MergedCutProfiles.Batch341.valid13650
  · exact MergedCutProfiles.Batch341.valid13663
  · exact MergedCutProfiles.Batch468.valid18738
theorem numericValid3030 : retention3030.NumericValid := by decide +kernel
def certificate3030 : RatCutBinCertificate := ⟨⟨retention3030,(1948413449568935117/1000000000000000000),(853665110250683/15625000000000000),(5188665442598132791/500000000000000000),(440826974595350230217/200000000000000000),(55972345195368259/25000000000000000)⟩,(999161361927879951/1000000000000000000),(195137494793646397/500000000000000000),(242512032798917671/1000000000000000000),(82068584803303371/500000000000000000)⟩
theorem valid3030 : certificate3030.Valid := by decide +kernel
theorem sound3030 : certificate3030.Sound := rat_cut_bin_certificate_sound certificate3030 profilesValid3030 numericValid3030 valid3030

def retention3031 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(24720987246582885333/211297548776017505963),(212581895934258647/125000000000000000),2,(788150449818548941516261085436176887/425163791868517294000000000000000000),false,MergedCutProfiles.Batch468.profile18739,(fun _ => MergedCutProfiles.Batch468.profile18739)⟩
theorem profilesValid3031 : retention3031.ProfilesValid := by
  exact MergedCutProfiles.Batch468.valid18739
theorem numericValid3031 : retention3031.NumericValid := by decide +kernel
def certificate3031 : RatCutBinCertificate := ⟨⟨retention3031,(1948413449568935117/1000000000000000000),(853665110250683/15625000000000000),(5188665442598132791/500000000000000000),(440826974595350230217/200000000000000000),(366648212041934377/200000000000000000)⟩,(999161361927879951/1000000000000000000),(406147816970953623/1000000000000000000),(56974102265569469/250000000000000000),(82196838025703979/500000000000000000)⟩
theorem valid3031 : certificate3031.Valid := by decide +kernel
theorem sound3031 : certificate3031.Sound := rat_cut_bin_certificate_sound certificate3031 profilesValid3031 numericValid3031 valid3031

def retention3032 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(64000000000000000000/211297548776017505963),(24720987246582885333/1000000000000000000),1,(1430544026985201378663036153095218887/1030041135274286888875000000000000000),false,MergedCutProfiles.Batch468.profile18740,(fun _ => MergedCutProfiles.Batch468.profile18740)⟩
theorem profilesValid3032 : retention3032.ProfilesValid := by
  exact MergedCutProfiles.Batch468.valid18740
theorem numericValid3032 : retention3032.NumericValid := by decide +kernel
def certificate3032 : RatCutBinCertificate := ⟨⟨retention3032,(1948413449568935117/1000000000000000000),(853665110250683/15625000000000000),(5188665442598132791/500000000000000000),(440826974595350230217/200000000000000000),(344641053483468403/250000000000000000)⟩,(999161361927879951/1000000000000000000),(70232376490169323/200000000000000000),(281338789327417829/1000000000000000000),(183521541752153299/500000000000000000)⟩
theorem valid3032 : certificate3032.Valid := by decide +kernel
theorem sound3032 : certificate3032.Sound := rat_cut_bin_certificate_sound certificate3032 profilesValid3032 numericValid3032 valid3032

def retention3033 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(1/2),64,1,(15961201781755751449307002574243876199/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch342.profile13711,(fun _ => MergedCutProfiles.Batch342.profile13711)⟩
theorem profilesValid3033 : retention3033.ProfilesValid := by
  exact MergedCutProfiles.Batch342.valid13711
theorem numericValid3033 : retention3033.NumericValid := by decide +kernel
def certificate3033 : RatCutBinCertificate := ⟨⟨retention3033,(1948413449568935117/1000000000000000000),(853665110250683/15625000000000000),(5188665442598132791/500000000000000000),(440826974595350230217/200000000000000000),(493658550559496077/500000000000000000)⟩,(999161361927879951/1000000000000000000),(478356445571253659/1000000000000000000),(168903823303522519/1000000000000000000),(82044588499603303/500000000000000000)⟩
theorem valid3033 : certificate3033.Valid := by decide +kernel
theorem sound3033 : certificate3033.Sound := rat_cut_bin_certificate_sound certificate3033 profilesValid3033 numericValid3033 valid3033

def retention3034 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(64000000000000000000/211297548776017505963),(9695420361871502517/1000000000000000000),1,(182827685047255205584172741659684237/134658616137104201625000000000000000),false,MergedCutProfiles.Batch468.profile18740,(fun _ => MergedCutProfiles.Batch468.profile18740)⟩
theorem profilesValid3034 : retention3034.ProfilesValid := by
  exact MergedCutProfiles.Batch468.valid18740
theorem numericValid3034 : retention3034.NumericValid := by decide +kernel
def certificate3034 : RatCutBinCertificate := ⟨⟨retention3034,(2095338807568935117/1000000000000000000),(853665110250683/15625000000000000),(5188665442598132791/500000000000000000),(440826974595350230217/200000000000000000),(1346680923205241633/1000000000000000000)⟩,(1598556990530253/1600000000000000),(4823300858711431/50000000000000000),(84284050426452991/125000000000000000),(796533997391669821/1000000000000000000)⟩
theorem valid3034 : certificate3034.Valid := by decide +kernel
theorem sound3034 : certificate3034.Sound := rat_cut_bin_certificate_sound certificate3034 profilesValid3034 numericValid3034 valid3034

def retention3035 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(1/2),64,1,(15961201781755751449307002574243876199/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch342.profile13711,(fun _ => MergedCutProfiles.Batch342.profile13711)⟩
theorem profilesValid3035 : retention3035.ProfilesValid := by
  exact MergedCutProfiles.Batch342.valid13711
theorem numericValid3035 : retention3035.NumericValid := by decide +kernel
def certificate3035 : RatCutBinCertificate := ⟨⟨retention3035,(2095338807568935117/1000000000000000000),(853665110250683/15625000000000000),(5188665442598132791/500000000000000000),(440826974595350230217/200000000000000000),(493271784129783181/500000000000000000)⟩,(1598556990530253/1600000000000000),(26336180021994317/200000000000000000),(299895516071698691/500000000000000000),(36387961887654341/62500000000000000)⟩
theorem valid3035 : certificate3035.Valid := by decide +kernel
theorem sound3035 : certificate3035.Sound := rat_cut_bin_certificate_sound certificate3035 profilesValid3035 numericValid3035 valid3035

def certificates : List RatCutBinCertificate := [certificate3024,certificate3025,certificate3026,certificate3027,certificate3028,certificate3029,certificate3030,certificate3031,certificate3032,certificate3033,certificate3034,certificate3035]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3024,List.forall_mem_cons.mpr ⟨sound3025,List.forall_mem_cons.mpr ⟨sound3026,List.forall_mem_cons.mpr ⟨sound3027,List.forall_mem_cons.mpr ⟨sound3028,List.forall_mem_cons.mpr ⟨sound3029,List.forall_mem_cons.mpr ⟨sound3030,List.forall_mem_cons.mpr ⟨sound3031,List.forall_mem_cons.mpr ⟨sound3032,List.forall_mem_cons.mpr ⟨sound3033,List.forall_mem_cons.mpr ⟨sound3034,List.forall_mem_cons.mpr ⟨sound3035,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch252
