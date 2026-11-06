import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch715
import Cycle12.MergedCutProfiles.Batch716

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch430

def retention5160 : RatCutRetentionCertificate := ⟨(8/125),(13/200),(780624129104751082/1031383427495183753137),(386447588665718357/500000000000000000),4,(7619427595730670173048676455837831367/3091580709325746856000000000000000000),false,MergedCutProfiles.Batch715.profile28614,(fun _ => MergedCutProfiles.Batch715.profile28614)⟩
theorem profilesValid5160 : retention5160.ProfilesValid := by
  exact MergedCutProfiles.Batch715.valid28614
theorem numericValid5160 : retention5160.NumericValid := by decide +kernel
def certificate5160 : RatCutBinCertificate := ⟨⟨retention5160,(2022184754522424593/1000000000000000000),(55239130418189853/250000000000000000),(2137201757870872743/125000000000000000),(4436447651108718332133/250000000000000000),(590010072813512397/250000000000000000)⟩,(499955148372232589/500000000000000000),(379097794670960321/500000000000000000),(31925337771144539/1000000000000000000),(15815864136616641/1000000000000000000)⟩
theorem valid5160 : certificate5160.Valid := by decide +kernel
theorem sound5160 : certificate5160.Sound := rat_cut_bin_certificate_sound certificate5160 profilesValid5160 numericValid5160 valid5160

def retention5161 : RatCutRetentionCertificate := ⟨(8/125),(13/200),(879626807800203765/1031383427495183753137),(390312064552375541/500000000000000000),(79/20),(768269986821407564652872094141562427719/312249651641900432800000000000000000000),false,MergedCutProfiles.Batch715.profile28615,(fun _ => MergedCutProfiles.Batch715.profile28615)⟩
theorem profilesValid5161 : retention5161.ProfilesValid := by
  exact MergedCutProfiles.Batch715.valid28615
theorem numericValid5161 : retention5161.NumericValid := by decide +kernel
def certificate5161 : RatCutBinCertificate := ⟨⟨retention5161,(2022184754522424593/1000000000000000000),(55239130418189853/250000000000000000),(2137201757870872743/125000000000000000),(4436447651108718332133/250000000000000000),(2357208597672162747/1000000000000000000)⟩,(499955148372232589/500000000000000000),(757621943936859793/1000000000000000000),(200527174073729/6250000000000000),(641610571844429/40000000000000000)⟩
theorem valid5161 : certificate5161.Valid := by decide +kernel
theorem sound5161 : certificate5161.Sound := rat_cut_bin_certificate_sound certificate5161 profilesValid5161 numericValid5161 valid5161

def retention5162 : RatCutRetentionCertificate := ⟨(8/125),(13/200),(2332346588048134443/1031383427495183753137),(175925361560040753/200000000000000000),(18/5),(570322467789179260902485463929942841/234567148746721004000000000000000000),false,MergedCutProfiles.Batch715.profile28616,(fun _ => MergedCutProfiles.Batch715.profile28616)⟩
theorem profilesValid5162 : retention5162.ProfilesValid := by
  exact MergedCutProfiles.Batch715.valid28616
theorem numericValid5162 : retention5162.NumericValid := by decide +kernel
def certificate5162 : RatCutBinCertificate := ⟨⟨retention5162,(2022184754522424593/1000000000000000000),(55239130418189853/250000000000000000),(2137201757870872743/125000000000000000),(4436447651108718332133/250000000000000000),(2337302737492524753/1000000000000000000)⟩,(499955148372232589/500000000000000000),(747224309476805121/1000000000000000000),(35042104716386367/1000000000000000000),(4719532851206157/250000000000000000)⟩
theorem valid5162 : certificate5162.Valid := by decide +kernel
theorem sound5162 : certificate5162.Sound := rat_cut_bin_certificate_sound certificate5162 profilesValid5162 numericValid5162 valid5162

def retention5163 : RatCutRetentionCertificate := ⟨(8/125),(13/200),(22545834242577984823/1031383427495183753137),(2332346588048134443/1000000000000000000),(19/10),(2105791311433354060410544955333045975351/932938635219253777200000000000000000000),false,MergedCutProfiles.Batch715.profile28617,(fun _ => MergedCutProfiles.Batch715.profile28617)⟩
theorem profilesValid5163 : retention5163.ProfilesValid := by
  exact MergedCutProfiles.Batch715.valid28617
theorem numericValid5163 : retention5163.NumericValid := by decide +kernel
def certificate5163 : RatCutBinCertificate := ⟨⟨retention5163,(2022184754522424593/1000000000000000000),(55239130418189853/250000000000000000),(2137201757870872743/125000000000000000),(4436447651108718332133/250000000000000000),(2207506340025178373/1000000000000000000)⟩,(499955148372232589/500000000000000000),(7035407693442679/10000000000000000),(24536787751686897/500000000000000000),(45167913150193629/1000000000000000000)⟩
theorem valid5163 : certificate5163.Valid := by decide +kernel
theorem sound5163 : certificate5163.Sound := rat_cut_bin_certificate_sound certificate5163 profilesValid5163 numericValid5163 valid5163

def retention5164 : RatCutRetentionCertificate := ⟨(8/125),(13/200),(1/40),(22545834242577984823/1000000000000000000),(21/20),(80348578038892942950904104849924032959191/36073334788124775716800000000000000000000),false,MergedCutProfiles.Batch715.profile28618,(fun _ => MergedCutProfiles.Batch715.profile28618)⟩
theorem profilesValid5164 : retention5164.ProfilesValid := by
  exact MergedCutProfiles.Batch715.valid28618
theorem numericValid5164 : retention5164.NumericValid := by decide +kernel
def certificate5164 : RatCutBinCertificate := ⟨⟨retention5164,(2022184754522424593/1000000000000000000),(55239130418189853/250000000000000000),(2137201757870872743/125000000000000000),(4436447651108718332133/250000000000000000),(439985555775927273/200000000000000000)⟩,(499955148372232589/500000000000000000),(3291177425017827/5000000000000000),(8311918872719537/125000000000000000),(127979440977118143/1000000000000000000)⟩
theorem valid5164 : certificate5164.Valid := by decide +kernel
theorem sound5164 : certificate5164.Sound := rat_cut_bin_certificate_sound certificate5164 profilesValid5164 numericValid5164 valid5164

def retention5165 : RatCutRetentionCertificate := ⟨(13/200),(33/500),(122019215042985223/198806338180814466443),(604055520014778331/1000000000000000000),4,(1389662618440882464604116384884848443/604055520014778331000000000000000000),true,MergedCutProfiles.Batch715.profile28619,![MergedCutProfiles.Batch715.profile28619,MergedCutProfiles.Batch715.profile28620,MergedCutProfiles.Batch715.profile28621,MergedCutProfiles.Batch715.profile28622,MergedCutProfiles.Batch715.profile28623,MergedCutProfiles.Batch715.profile28624,MergedCutProfiles.Batch715.profile28625,MergedCutProfiles.Batch715.profile28626,MergedCutProfiles.Batch715.profile28627,MergedCutProfiles.Batch715.profile28628,MergedCutProfiles.Batch715.profile28629,MergedCutProfiles.Batch715.profile28630,MergedCutProfiles.Batch715.profile28631,MergedCutProfiles.Batch715.profile28632,MergedCutProfiles.Batch715.profile28633,MergedCutProfiles.Batch715.profile28634]⟩
theorem profilesValid5165 : retention5165.ProfilesValid := by
  change ∀ j : Fin 16, (retention5165.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch715.valid28619
  · exact MergedCutProfiles.Batch715.valid28620
  · exact MergedCutProfiles.Batch715.valid28621
  · exact MergedCutProfiles.Batch715.valid28622
  · exact MergedCutProfiles.Batch715.valid28623
  · exact MergedCutProfiles.Batch715.valid28624
  · exact MergedCutProfiles.Batch715.valid28625
  · exact MergedCutProfiles.Batch715.valid28626
  · exact MergedCutProfiles.Batch715.valid28627
  · exact MergedCutProfiles.Batch715.valid28628
  · exact MergedCutProfiles.Batch715.valid28629
  · exact MergedCutProfiles.Batch715.valid28630
  · exact MergedCutProfiles.Batch715.valid28631
  · exact MergedCutProfiles.Batch715.valid28632
  · exact MergedCutProfiles.Batch715.valid28633
  · exact MergedCutProfiles.Batch715.valid28634
theorem numericValid5165 : retention5165.NumericValid := by decide +kernel
def certificate5165 : RatCutBinCertificate := ⟨⟨retention5165,(977865315571840637/500000000000000000),(229314578619222081/1000000000000000000),(8713760607559645161/500000000000000000),(272404725454788921341/15625000000000000),(439523684103373237/200000000000000000)⟩,(499956302468977257/500000000000000000),(378294275482296309/500000000000000000),(32371892629721211/1000000000000000000),(3622200444745411/250000000000000000)⟩
theorem valid5165 : certificate5165.Valid := by decide +kernel
theorem sound5165 : certificate5165.Sound := rat_cut_bin_certificate_sound certificate5165 profilesValid5165 numericValid5165 valid5165

def retention5166 : RatCutRetentionCertificate := ⟨(13/200),(33/500),(207889781200000000/198806338180814466443),(122019215042985223/200000000000000000),4,(9230663705107350809/4000000000000000000),true,MergedCutProfiles.Batch715.profile28635,![MergedCutProfiles.Batch715.profile28635,MergedCutProfiles.Batch715.profile28636,MergedCutProfiles.Batch715.profile28623,MergedCutProfiles.Batch715.profile28625,MergedCutProfiles.Batch715.profile28637,MergedCutProfiles.Batch715.profile28628,MergedCutProfiles.Batch715.profile28630,MergedCutProfiles.Batch715.profile28638,MergedCutProfiles.Batch715.profile28633,MergedCutProfiles.Batch715.profile28639,MergedCutProfiles.Batch716.profile28640,MergedCutProfiles.Batch716.profile28641,MergedCutProfiles.Batch716.profile28642,MergedCutProfiles.Batch716.profile28643,MergedCutProfiles.Batch716.profile28644,MergedCutProfiles.Batch716.profile28645]⟩
theorem profilesValid5166 : retention5166.ProfilesValid := by
  change ∀ j : Fin 16, (retention5166.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch715.valid28635
  · exact MergedCutProfiles.Batch715.valid28636
  · exact MergedCutProfiles.Batch715.valid28623
  · exact MergedCutProfiles.Batch715.valid28625
  · exact MergedCutProfiles.Batch715.valid28637
  · exact MergedCutProfiles.Batch715.valid28628
  · exact MergedCutProfiles.Batch715.valid28630
  · exact MergedCutProfiles.Batch715.valid28638
  · exact MergedCutProfiles.Batch715.valid28633
  · exact MergedCutProfiles.Batch715.valid28639
  · exact MergedCutProfiles.Batch716.valid28640
  · exact MergedCutProfiles.Batch716.valid28641
  · exact MergedCutProfiles.Batch716.valid28642
  · exact MergedCutProfiles.Batch716.valid28643
  · exact MergedCutProfiles.Batch716.valid28644
  · exact MergedCutProfiles.Batch716.valid28645
theorem numericValid5166 : retention5166.NumericValid := by decide +kernel
def certificate5166 : RatCutBinCertificate := ⟨⟨retention5166,(977865315571840637/500000000000000000),(229314578619222081/1000000000000000000),(8713760607559645161/500000000000000000),(272404725454788921341/15625000000000000),(2204729896011553003/1000000000000000000)⟩,(499956302468977257/500000000000000000),(374640089364322657/500000000000000000),(17222935437508851/500000000000000000),(241971335994999/15625000000000000)⟩
theorem valid5166 : certificate5166.Valid := by decide +kernel
theorem sound5166 : certificate5166.Sound := rat_cut_bin_certificate_sound certificate5166 profilesValid5166 numericValid5166 valid5166

def retention5167 : RatCutRetentionCertificate := ⟨(13/200),(33/500),(3058164087025109813/994031690904072332215),(519724453/500000000),(61/20),(19268463617680277219/8000000000000000000),true,MergedCutProfiles.Batch715.profile28623,![MergedCutProfiles.Batch715.profile28623,MergedCutProfiles.Batch715.profile28628,MergedCutProfiles.Batch715.profile28633,MergedCutProfiles.Batch716.profile28646,MergedCutProfiles.Batch716.profile28647,MergedCutProfiles.Batch716.profile28648,MergedCutProfiles.Batch716.profile28649,MergedCutProfiles.Batch716.profile28650,MergedCutProfiles.Batch716.profile28651,MergedCutProfiles.Batch716.profile28652,MergedCutProfiles.Batch716.profile28653,MergedCutProfiles.Batch716.profile28654,MergedCutProfiles.Batch716.profile28655,MergedCutProfiles.Batch716.profile28656,MergedCutProfiles.Batch716.profile28657,MergedCutProfiles.Batch716.profile28658]⟩
theorem profilesValid5167 : retention5167.ProfilesValid := by
  change ∀ j : Fin 16, (retention5167.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch715.valid28623
  · exact MergedCutProfiles.Batch715.valid28628
  · exact MergedCutProfiles.Batch715.valid28633
  · exact MergedCutProfiles.Batch716.valid28646
  · exact MergedCutProfiles.Batch716.valid28647
  · exact MergedCutProfiles.Batch716.valid28648
  · exact MergedCutProfiles.Batch716.valid28649
  · exact MergedCutProfiles.Batch716.valid28650
  · exact MergedCutProfiles.Batch716.valid28651
  · exact MergedCutProfiles.Batch716.valid28652
  · exact MergedCutProfiles.Batch716.valid28653
  · exact MergedCutProfiles.Batch716.valid28654
  · exact MergedCutProfiles.Batch716.valid28655
  · exact MergedCutProfiles.Batch716.valid28656
  · exact MergedCutProfiles.Batch716.valid28657
  · exact MergedCutProfiles.Batch716.valid28658
theorem numericValid5167 : retention5167.NumericValid := by decide +kernel
def certificate5167 : RatCutBinCertificate := ⟨⟨retention5167,(977865315571840637/500000000000000000),(229314578619222081/1000000000000000000),(8713760607559645161/500000000000000000),(272404725454788921341/15625000000000000),(2330069326534082513/1000000000000000000)⟩,(499956302468977257/500000000000000000),(518716195470779223/1000000000000000000),(28159862212271447/200000000000000000),(43334313758981031/500000000000000000)⟩
theorem valid5167 : certificate5167.Valid := by decide +kernel
theorem sound5167 : certificate5167.Sound := rat_cut_bin_certificate_sound certificate5167 profilesValid5167 numericValid5167 valid5167

def retention5168 : RatCutRetentionCertificate := ⟨(13/200),(33/500),(12800000000000000000/198806338180814466443),(3058164087025109813/1000000000000000000),(3/2),(522218667977277913197/256000000000000000000),true,MergedCutProfiles.Batch716.profile28659,![MergedCutProfiles.Batch716.profile28659,MergedCutProfiles.Batch716.profile28660,MergedCutProfiles.Batch716.profile28661,MergedCutProfiles.Batch716.profile28662,MergedCutProfiles.Batch716.profile28663,MergedCutProfiles.Batch716.profile28664,MergedCutProfiles.Batch716.profile28665,MergedCutProfiles.Batch716.profile28666,MergedCutProfiles.Batch716.profile28667,MergedCutProfiles.Batch716.profile28668,MergedCutProfiles.Batch716.profile28669,MergedCutProfiles.Batch716.profile28670,MergedCutProfiles.Batch716.profile28671,MergedCutProfiles.Batch716.profile28672,MergedCutProfiles.Batch716.profile28673,MergedCutProfiles.Batch716.profile28674]⟩
theorem profilesValid5168 : retention5168.ProfilesValid := by
  change ∀ j : Fin 16, (retention5168.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch716.valid28659
  · exact MergedCutProfiles.Batch716.valid28660
  · exact MergedCutProfiles.Batch716.valid28661
  · exact MergedCutProfiles.Batch716.valid28662
  · exact MergedCutProfiles.Batch716.valid28663
  · exact MergedCutProfiles.Batch716.valid28664
  · exact MergedCutProfiles.Batch716.valid28665
  · exact MergedCutProfiles.Batch716.valid28666
  · exact MergedCutProfiles.Batch716.valid28667
  · exact MergedCutProfiles.Batch716.valid28668
  · exact MergedCutProfiles.Batch716.valid28669
  · exact MergedCutProfiles.Batch716.valid28670
  · exact MergedCutProfiles.Batch716.valid28671
  · exact MergedCutProfiles.Batch716.valid28672
  · exact MergedCutProfiles.Batch716.valid28673
  · exact MergedCutProfiles.Batch716.valid28674
theorem numericValid5168 : retention5168.NumericValid := by decide +kernel
def certificate5168 : RatCutBinCertificate := ⟨⟨retention5168,(977865315571840637/500000000000000000),(229314578619222081/1000000000000000000),(8713760607559645161/500000000000000000),(272404725454788921341/15625000000000000),(2001315757807221109/1000000000000000000)⟩,(499956302468977257/500000000000000000),(396148897165620081/1000000000000000000),(59257381398574871/250000000000000000),(24496676341147347/100000000000000000)⟩
theorem valid5168 : certificate5168.Valid := by decide +kernel
theorem sound5168 : certificate5168.Sound := rat_cut_bin_certificate_sound certificate5168 profilesValid5168 numericValid5168 valid5168

def retention5169 : RatCutRetentionCertificate := ⟨(13/200),(33/500),(1/2),64,1,(2554163107897985985986722398337318719/2560000000000000000000000000000000000),false,MergedCutProfiles.Batch716.profile28675,(fun _ => MergedCutProfiles.Batch716.profile28675)⟩
theorem profilesValid5169 : retention5169.ProfilesValid := by
  exact MergedCutProfiles.Batch716.valid28675
theorem numericValid5169 : retention5169.NumericValid := by decide +kernel
def certificate5169 : RatCutBinCertificate := ⟨⟨retention5169,(977865315571840637/500000000000000000),(229314578619222081/1000000000000000000),(8713760607559645161/500000000000000000),(272404725454788921341/15625000000000000),(121498261233731159/125000000000000000)⟩,(499956302468977257/500000000000000000),(30295643347135899/50000000000000000),(90513220798777671/1000000000000000000),(21663442988049771/250000000000000000)⟩
theorem valid5169 : certificate5169.Valid := by decide +kernel
theorem sound5169 : certificate5169.Sound := rat_cut_bin_certificate_sound certificate5169 profilesValid5169 numericValid5169 valid5169

def retention5170 : RatCutRetentionCertificate := ⟨(13/200),(33/500),(12800000000000000000/198806338180814466443),(53933615192920888281/1000000000000000000),1,(5873310992686074133509155625752172753/2876459476955780708320000000000000000),false,MergedCutProfiles.Batch716.profile28676,(fun _ => MergedCutProfiles.Batch716.profile28676)⟩
theorem profilesValid5170 : retention5170.ProfilesValid := by
  exact MergedCutProfiles.Batch716.valid28676
theorem numericValid5170 : retention5170.NumericValid := by decide +kernel
def certificate5170 : RatCutBinCertificate := ⟨⟨retention5170,(853561187071840637/500000000000000000),(229314578619222081/1000000000000000000),(8713760607559645161/500000000000000000),(272404725454788921341/15625000000000000),(2019391604214189701/1000000000000000000)⟩,(999923714649996571/1000000000000000000),(3605561356038699/250000000000000000),(891152797286816947/1000000000000000000),(346900671388638699/200000000000000000)⟩
theorem valid5170 : certificate5170.Valid := by decide +kernel
theorem sound5170 : certificate5170.Sound := rat_cut_bin_certificate_sound certificate5170 profilesValid5170 numericValid5170 valid5170

def retention5171 : RatCutRetentionCertificate := ⟨(13/200),(33/500),(1/2),64,1,(2554163107897985985986722398337318719/2560000000000000000000000000000000000),false,MergedCutProfiles.Batch716.profile28675,(fun _ => MergedCutProfiles.Batch716.profile28675)⟩
theorem profilesValid5171 : retention5171.ProfilesValid := by
  exact MergedCutProfiles.Batch716.valid28675
theorem numericValid5171 : retention5171.NumericValid := by decide +kernel
def certificate5171 : RatCutBinCertificate := ⟨⟨retention5171,(853561187071840637/500000000000000000),(229314578619222081/1000000000000000000),(8713760607559645161/500000000000000000),(272404725454788921341/15625000000000000),(243814331103414919/250000000000000000)⟩,(999923714649996571/1000000000000000000),(29863053159805411/1000000000000000000),(422329305056781063/500000000000000000),(811332357899847147/1000000000000000000)⟩
theorem valid5171 : certificate5171.Valid := by decide +kernel
theorem sound5171 : certificate5171.Sound := rat_cut_bin_certificate_sound certificate5171 profilesValid5171 numericValid5171 valid5171

def certificates : List RatCutBinCertificate := [certificate5160,certificate5161,certificate5162,certificate5163,certificate5164,certificate5165,certificate5166,certificate5167,certificate5168,certificate5169,certificate5170,certificate5171]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound5160,List.forall_mem_cons.mpr ⟨sound5161,List.forall_mem_cons.mpr ⟨sound5162,List.forall_mem_cons.mpr ⟨sound5163,List.forall_mem_cons.mpr ⟨sound5164,List.forall_mem_cons.mpr ⟨sound5165,List.forall_mem_cons.mpr ⟨sound5166,List.forall_mem_cons.mpr ⟨sound5167,List.forall_mem_cons.mpr ⟨sound5168,List.forall_mem_cons.mpr ⟨sound5169,List.forall_mem_cons.mpr ⟨sound5170,List.forall_mem_cons.mpr ⟨sound5171,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch430
