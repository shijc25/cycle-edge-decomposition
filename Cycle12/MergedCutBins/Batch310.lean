import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch566
import Cycle12.MergedCutProfiles.Batch567
import Cycle12.MergedCutProfiles.Batch568

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch310

def retention3720 : RatCutRetentionCertificate := ⟨(19/2000),(1/100),(1/2),64,1,(15960572082716405919661104632746380231/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch566.profile22662,(fun _ => MergedCutProfiles.Batch566.profile22662)⟩
theorem profilesValid3720 : retention3720.ProfilesValid := by
  exact MergedCutProfiles.Batch566.valid22662
theorem numericValid3720 : retention3720.NumericValid := by decide +kernel
def certificate3720 : RatCutBinCertificate := ⟨⟨retention3720,(441283115542279867/250000000000000000),(4061079806220747/1000000000000000000),(7478733651448619323/1000000000000000000),(87605946957905369254317/1000000000000000000),(62286078635327663/62500000000000000)⟩,(99997992517842491/100000000000000000),(917381495635967/12500000000000000),(728421120062124091/1000000000000000000),(714782964754431049/1000000000000000000)⟩
theorem valid3720 : certificate3720.Valid := by decide +kernel
theorem sound3720 : certificate3720.Sound := rat_cut_bin_certificate_sound certificate3720 profilesValid3720 numericValid3720 valid3720

def retention3721 : RatCutRetentionCertificate := ⟨(1/100),(21/2000),(574592304218321427/10577178583233964451179),(568903271503288541/1000000000000000000),4,(5003425231376293563625020072394812127/2275613086013154164000000000000000000),true,MergedCutProfiles.Batch566.profile22664,![MergedCutProfiles.Batch566.profile22664,MergedCutProfiles.Batch566.profile22665,MergedCutProfiles.Batch566.profile22666,MergedCutProfiles.Batch566.profile22667,MergedCutProfiles.Batch566.profile22668,MergedCutProfiles.Batch566.profile22669,MergedCutProfiles.Batch566.profile22669,MergedCutProfiles.Batch566.profile22670,MergedCutProfiles.Batch566.profile22671,MergedCutProfiles.Batch566.profile22671,MergedCutProfiles.Batch566.profile22672,MergedCutProfiles.Batch566.profile22673,MergedCutProfiles.Batch566.profile22673,MergedCutProfiles.Batch566.profile22674,MergedCutProfiles.Batch566.profile22674,MergedCutProfiles.Batch566.profile22675]⟩
theorem profilesValid3721 : retention3721.ProfilesValid := by
  change ∀ j : Fin 16, (retention3721.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch566.valid22664
  · exact MergedCutProfiles.Batch566.valid22665
  · exact MergedCutProfiles.Batch566.valid22666
  · exact MergedCutProfiles.Batch566.valid22667
  · exact MergedCutProfiles.Batch566.valid22668
  · exact MergedCutProfiles.Batch566.valid22669
  · exact MergedCutProfiles.Batch566.valid22669
  · exact MergedCutProfiles.Batch566.valid22670
  · exact MergedCutProfiles.Batch566.valid22671
  · exact MergedCutProfiles.Batch566.valid22671
  · exact MergedCutProfiles.Batch566.valid22672
  · exact MergedCutProfiles.Batch566.valid22673
  · exact MergedCutProfiles.Batch566.valid22673
  · exact MergedCutProfiles.Batch566.valid22674
  · exact MergedCutProfiles.Batch566.valid22674
  · exact MergedCutProfiles.Batch566.valid22675
theorem numericValid3721 : retention3721.NumericValid := by decide +kernel
def certificate3721 : RatCutBinCertificate := ⟨⟨retention3721,(893075780585334917/500000000000000000),(4484718117741407/1000000000000000000),(3762392030094046513/500000000000000000),(797707745538915745241/10000000000000000),(68576785341070787/31250000000000000)⟩,(999977699877820541/1000000000000000000),(157695323998600847/250000000000000000),(78557158021847239/1000000000000000000),(868120528203669/25000000000000000)⟩
theorem valid3721 : certificate3721.Valid := by decide +kernel
theorem sound3721 : certificate3721.Sound := rat_cut_bin_certificate_sound certificate3721 profilesValid3721 numericValid3721 valid3721

def retention3722 : RatCutRetentionCertificate := ⟨(1/100),(21/2000),(1281086290000000000/10577178583233964451179),(574592304218321427/1000000000000000000),4,(5079347289302299720551313419715314263/2298369216873285708000000000000000000),true,MergedCutProfiles.Batch566.profile22665,![MergedCutProfiles.Batch566.profile22665,MergedCutProfiles.Batch566.profile22667,MergedCutProfiles.Batch566.profile22669,MergedCutProfiles.Batch566.profile22671,MergedCutProfiles.Batch566.profile22672,MergedCutProfiles.Batch566.profile22673,MergedCutProfiles.Batch566.profile22674,MergedCutProfiles.Batch566.profile22675,MergedCutProfiles.Batch566.profile22676,MergedCutProfiles.Batch566.profile22677,MergedCutProfiles.Batch566.profile22678,MergedCutProfiles.Batch566.profile22679,MergedCutProfiles.Batch567.profile22680,MergedCutProfiles.Batch567.profile22681,MergedCutProfiles.Batch567.profile22681,MergedCutProfiles.Batch567.profile22682]⟩
theorem profilesValid3722 : retention3722.ProfilesValid := by
  change ∀ j : Fin 16, (retention3722.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch566.valid22665
  · exact MergedCutProfiles.Batch566.valid22667
  · exact MergedCutProfiles.Batch566.valid22669
  · exact MergedCutProfiles.Batch566.valid22671
  · exact MergedCutProfiles.Batch566.valid22672
  · exact MergedCutProfiles.Batch566.valid22673
  · exact MergedCutProfiles.Batch566.valid22674
  · exact MergedCutProfiles.Batch566.valid22675
  · exact MergedCutProfiles.Batch566.valid22676
  · exact MergedCutProfiles.Batch566.valid22677
  · exact MergedCutProfiles.Batch566.valid22678
  · exact MergedCutProfiles.Batch566.valid22679
  · exact MergedCutProfiles.Batch567.valid22680
  · exact MergedCutProfiles.Batch567.valid22681
  · exact MergedCutProfiles.Batch567.valid22681
  · exact MergedCutProfiles.Batch567.valid22682
theorem numericValid3722 : retention3722.NumericValid := by decide +kernel
def certificate3722 : RatCutBinCertificate := ⟨⟨retention3722,(893075780585334917/500000000000000000),(4484718117741407/1000000000000000000),(3762392030094046513/500000000000000000),(797707745538915745241/10000000000000000),(2205720684839624077/1000000000000000000)⟩,(999977699877820541/1000000000000000000),(623262497633446401/1000000000000000000),(82066781168770219/1000000000000000000),(9124137818454999/250000000000000000)⟩
theorem valid3722 : certificate3722.Valid := by decide +kernel
theorem sound3722 : certificate3722.Sound := rat_cut_bin_certificate_sound certificate3722 profilesValid3722 numericValid3722 valid3722

def retention3723 : RatCutRetentionCertificate := ⟨(1/100),(21/2000),(2938090069754634178/10577178583233964451179),(128108629/100000000),(5/2),(18899668727691746103/8000000000000000000),true,MergedCutProfiles.Batch566.profile22668,![MergedCutProfiles.Batch566.profile22668,MergedCutProfiles.Batch566.profile22672,MergedCutProfiles.Batch566.profile22674,MergedCutProfiles.Batch566.profile22677,MergedCutProfiles.Batch566.profile22679,MergedCutProfiles.Batch567.profile22680,MergedCutProfiles.Batch567.profile22682,MergedCutProfiles.Batch567.profile22683,MergedCutProfiles.Batch567.profile22684,MergedCutProfiles.Batch567.profile22685,MergedCutProfiles.Batch567.profile22686,MergedCutProfiles.Batch567.profile22687,MergedCutProfiles.Batch567.profile22688,MergedCutProfiles.Batch567.profile22689,MergedCutProfiles.Batch567.profile22690,MergedCutProfiles.Batch567.profile22691]⟩
theorem profilesValid3723 : retention3723.ProfilesValid := by
  change ∀ j : Fin 16, (retention3723.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch566.valid22668
  · exact MergedCutProfiles.Batch566.valid22672
  · exact MergedCutProfiles.Batch566.valid22674
  · exact MergedCutProfiles.Batch566.valid22677
  · exact MergedCutProfiles.Batch566.valid22679
  · exact MergedCutProfiles.Batch567.valid22680
  · exact MergedCutProfiles.Batch567.valid22682
  · exact MergedCutProfiles.Batch567.valid22683
  · exact MergedCutProfiles.Batch567.valid22684
  · exact MergedCutProfiles.Batch567.valid22685
  · exact MergedCutProfiles.Batch567.valid22686
  · exact MergedCutProfiles.Batch567.valid22687
  · exact MergedCutProfiles.Batch567.valid22688
  · exact MergedCutProfiles.Batch567.valid22689
  · exact MergedCutProfiles.Batch567.valid22690
  · exact MergedCutProfiles.Batch567.valid22691
theorem numericValid3723 : retention3723.NumericValid := by decide +kernel
def certificate3723 : RatCutBinCertificate := ⟨⟨retention3723,(893075780585334917/500000000000000000),(4484718117741407/1000000000000000000),(3762392030094046513/500000000000000000),(797707745538915745241/10000000000000000),(2359797256648099517/1000000000000000000)⟩,(999977699877820541/1000000000000000000),(11282291844108639/31250000000000000),(54229415653325977/200000000000000000),(7906990589495887/40000000000000000)⟩
theorem valid3723 : certificate3723.Valid := by decide +kernel
theorem sound3723 : certificate3723.Sound := rat_cut_bin_certificate_sound certificate3723 profilesValid3723 numericValid3723 valid3723

def retention3724 : RatCutRetentionCertificate := ⟨(1/100),(21/2000),(64000000000000000000/10577178583233964451179),(1469045034877317089/500000000000000000),(3/2),(576379783439676033/256000000000000000),true,MergedCutProfiles.Batch567.profile22692,![MergedCutProfiles.Batch567.profile22692,MergedCutProfiles.Batch567.profile22693,MergedCutProfiles.Batch567.profile22694,MergedCutProfiles.Batch567.profile22695,MergedCutProfiles.Batch567.profile22696,MergedCutProfiles.Batch567.profile22697,MergedCutProfiles.Batch567.profile22698,MergedCutProfiles.Batch567.profile22699,MergedCutProfiles.Batch567.profile22700,MergedCutProfiles.Batch567.profile22701,MergedCutProfiles.Batch567.profile22702,MergedCutProfiles.Batch567.profile22703,MergedCutProfiles.Batch567.profile22704,MergedCutProfiles.Batch567.profile22705,MergedCutProfiles.Batch567.profile22706,MergedCutProfiles.Batch567.profile22707]⟩
theorem profilesValid3724 : retention3724.ProfilesValid := by
  change ∀ j : Fin 16, (retention3724.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch567.valid22692
  · exact MergedCutProfiles.Batch567.valid22693
  · exact MergedCutProfiles.Batch567.valid22694
  · exact MergedCutProfiles.Batch567.valid22695
  · exact MergedCutProfiles.Batch567.valid22696
  · exact MergedCutProfiles.Batch567.valid22697
  · exact MergedCutProfiles.Batch567.valid22698
  · exact MergedCutProfiles.Batch567.valid22699
  · exact MergedCutProfiles.Batch567.valid22700
  · exact MergedCutProfiles.Batch567.valid22701
  · exact MergedCutProfiles.Batch567.valid22702
  · exact MergedCutProfiles.Batch567.valid22703
  · exact MergedCutProfiles.Batch567.valid22704
  · exact MergedCutProfiles.Batch567.valid22705
  · exact MergedCutProfiles.Batch567.valid22706
  · exact MergedCutProfiles.Batch567.valid22707
theorem numericValid3724 : retention3724.NumericValid := by decide +kernel
def certificate3724 : RatCutBinCertificate := ⟨⟨retention3724,(893075780585334917/500000000000000000),(4484718117741407/1000000000000000000),(3762392030094046513/500000000000000000),(797707745538915745241/10000000000000000),(1124943364240436771/500000000000000000)⟩,(999977699877820541/1000000000000000000),(272092782467097869/1000000000000000000),(373699899464715451/1000000000000000000),(209091694326056657/500000000000000000)⟩
theorem valid3724 : certificate3724.Valid := by decide +kernel
theorem sound3724 : certificate3724.Sound := rat_cut_bin_certificate_sound certificate3724 profilesValid3724 numericValid3724 valid3724

def retention3725 : RatCutRetentionCertificate := ⟨(1/100),(21/2000),(1/2),64,1,(255369211198680140065824546889814306199/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch567.profile22708,(fun _ => MergedCutProfiles.Batch567.profile22708)⟩
theorem profilesValid3725 : retention3725.ProfilesValid := by
  exact MergedCutProfiles.Batch567.valid22708
theorem numericValid3725 : retention3725.NumericValid := by decide +kernel
def certificate3725 : RatCutBinCertificate := ⟨⟨retention3725,(893075780585334917/500000000000000000),(4484718117741407/1000000000000000000),(3762392030094046513/500000000000000000),(797707745538915745241/10000000000000000),(24911786188431209/25000000000000000)⟩,(999977699877820541/1000000000000000000),(436842137252896437/1000000000000000000),(100686016596184563/500000000000000000),(197580663234461831/1000000000000000000)⟩
theorem valid3725 : certificate3725.Valid := by decide +kernel
theorem sound3725 : certificate3725.Sound := rat_cut_bin_certificate_sound certificate3725 profilesValid3725 numericValid3725 valid3725

def retention3726 : RatCutRetentionCertificate := ⟨(1/100),(21/2000),(64000000000000000000/10577178583233964451179),(3247576877984794851/200000000000000000),1,(752821225149773762835816391495364367/338289258123416130312500000000000000),false,MergedCutProfiles.Batch567.profile22709,(fun _ => MergedCutProfiles.Batch567.profile22709)⟩
theorem profilesValid3726 : retention3726.ProfilesValid := by
  exact MergedCutProfiles.Batch567.valid22709
theorem numericValid3726 : retention3726.NumericValid := by decide +kernel
def certificate3726 : RatCutBinCertificate := ⟨⟨retention3726,(883730687585334917/500000000000000000),(4484718117741407/1000000000000000000),(3762392030094046513/500000000000000000),(797707745538915745241/10000000000000000),(222432387384348963/100000000000000000)⟩,(49998896661251119/50000000000000000),(32909019722338167/1000000000000000000),(835841113490480253/1000000000000000000),(817575138245347623/500000000000000000)⟩
theorem valid3726 : certificate3726.Valid := by decide +kernel
theorem sound3726 : certificate3726.Sound := rat_cut_bin_certificate_sound certificate3726 profilesValid3726 numericValid3726 valid3726

def retention3727 : RatCutRetentionCertificate := ⟨(1/100),(21/2000),(1/2),64,1,(255369211198680140065824546889814306199/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch567.profile22708,(fun _ => MergedCutProfiles.Batch567.profile22708)⟩
theorem profilesValid3727 : retention3727.ProfilesValid := by
  exact MergedCutProfiles.Batch567.valid22708
theorem numericValid3727 : retention3727.NumericValid := by decide +kernel
def certificate3727 : RatCutBinCertificate := ⟨⟨retention3727,(883730687585334917/500000000000000000),(4484718117741407/1000000000000000000),(3762392030094046513/500000000000000000),(797707745538915745241/10000000000000000),(996482586756019469/1000000000000000000)⟩,(49998896661251119/50000000000000000),(14691740569492867/200000000000000000),(36412708275080219/50000000000000000),(714550854679055363/1000000000000000000)⟩
theorem valid3727 : certificate3727.Valid := by decide +kernel
theorem sound3727 : certificate3727.Sound := rat_cut_bin_certificate_sound certificate3727 profilesValid3727 numericValid3727 valid3727

def retention3728 : RatCutRetentionCertificate := ⟨(21/2000),(11/1000),(609260015812111742/9615687695137442862049),(568267816759111399/1000000000000000000),4,(140618290953866148319/64000000000000000000),true,MergedCutProfiles.Batch567.profile22710,![MergedCutProfiles.Batch567.profile22710,MergedCutProfiles.Batch567.profile22711,MergedCutProfiles.Batch567.profile22712,MergedCutProfiles.Batch567.profile22713,MergedCutProfiles.Batch567.profile22714,MergedCutProfiles.Batch567.profile22714,MergedCutProfiles.Batch567.profile22715,MergedCutProfiles.Batch567.profile22716,MergedCutProfiles.Batch567.profile22717,MergedCutProfiles.Batch567.profile22717,MergedCutProfiles.Batch567.profile22718,MergedCutProfiles.Batch567.profile22719,MergedCutProfiles.Batch567.profile22719,MergedCutProfiles.Batch568.profile22720,MergedCutProfiles.Batch568.profile22720,MergedCutProfiles.Batch568.profile22721]⟩
theorem profilesValid3728 : retention3728.ProfilesValid := by
  change ∀ j : Fin 16, (retention3728.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch567.valid22710
  · exact MergedCutProfiles.Batch567.valid22711
  · exact MergedCutProfiles.Batch567.valid22712
  · exact MergedCutProfiles.Batch567.valid22713
  · exact MergedCutProfiles.Batch567.valid22714
  · exact MergedCutProfiles.Batch567.valid22714
  · exact MergedCutProfiles.Batch567.valid22715
  · exact MergedCutProfiles.Batch567.valid22716
  · exact MergedCutProfiles.Batch567.valid22717
  · exact MergedCutProfiles.Batch567.valid22717
  · exact MergedCutProfiles.Batch567.valid22718
  · exact MergedCutProfiles.Batch567.valid22719
  · exact MergedCutProfiles.Batch567.valid22719
  · exact MergedCutProfiles.Batch568.valid22720
  · exact MergedCutProfiles.Batch568.valid22720
  · exact MergedCutProfiles.Batch568.valid22721
theorem numericValid3728 : retention3728.NumericValid := by decide +kernel
def certificate3728 : RatCutBinCertificate := ⟨⟨retention3728,(897833486860996359/500000000000000000),(246507623072377/50000000000000000),(7571273441896334563/1000000000000000000),(72967924963157851309997/1000000000000000000),(2192483690099794729/1000000000000000000)⟩,(999975501371161171/1000000000000000000),(316308562792180089/500000000000000000),(2428558871505413/31250000000000000),(17159815655992413/500000000000000000)⟩
theorem valid3728 : certificate3728.Valid := by decide +kernel
theorem sound3728 : certificate3728.Sound := rat_cut_bin_certificate_sound certificate3728 profilesValid3728 numericValid3728 valid3728

def retention3729 : RatCutRetentionCertificate := ⟨(21/2000),(11/1000),(1279901172000000000/9615687695137442862049),(304630007906055871/500000000000000000),4,(1109447924898112347126806110786827683/487408012649689393600000000000000000),true,MergedCutProfiles.Batch567.profile22711,![MergedCutProfiles.Batch567.profile22711,MergedCutProfiles.Batch567.profile22713,MergedCutProfiles.Batch567.profile22715,MergedCutProfiles.Batch567.profile22716,MergedCutProfiles.Batch567.profile22718,MergedCutProfiles.Batch567.profile22719,MergedCutProfiles.Batch568.profile22720,MergedCutProfiles.Batch568.profile22721,MergedCutProfiles.Batch568.profile22722,MergedCutProfiles.Batch568.profile22723,MergedCutProfiles.Batch568.profile22724,MergedCutProfiles.Batch568.profile22725,MergedCutProfiles.Batch568.profile22726,MergedCutProfiles.Batch568.profile22727,MergedCutProfiles.Batch568.profile22727,MergedCutProfiles.Batch568.profile22728]⟩
theorem profilesValid3729 : retention3729.ProfilesValid := by
  change ∀ j : Fin 16, (retention3729.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch567.valid22711
  · exact MergedCutProfiles.Batch567.valid22713
  · exact MergedCutProfiles.Batch567.valid22715
  · exact MergedCutProfiles.Batch567.valid22716
  · exact MergedCutProfiles.Batch567.valid22718
  · exact MergedCutProfiles.Batch567.valid22719
  · exact MergedCutProfiles.Batch568.valid22720
  · exact MergedCutProfiles.Batch568.valid22721
  · exact MergedCutProfiles.Batch568.valid22722
  · exact MergedCutProfiles.Batch568.valid22723
  · exact MergedCutProfiles.Batch568.valid22724
  · exact MergedCutProfiles.Batch568.valid22725
  · exact MergedCutProfiles.Batch568.valid22726
  · exact MergedCutProfiles.Batch568.valid22727
  · exact MergedCutProfiles.Batch568.valid22727
  · exact MergedCutProfiles.Batch568.valid22728
theorem numericValid3729 : retention3729.NumericValid := by decide +kernel
def certificate3729 : RatCutBinCertificate := ⟨⟨retention3729,(897833486860996359/500000000000000000),(246507623072377/50000000000000000),(7571273441896334563/1000000000000000000),(72967924963157851309997/1000000000000000000),(1135771506829441269/500000000000000000)⟩,(999975501371161171/1000000000000000000),(291090229312829189/500000000000000000),(102874574556947441/1000000000000000000),(23689468323488721/500000000000000000)⟩
theorem valid3729 : certificate3729.Valid := by decide +kernel
theorem sound3729 : certificate3729.Sound := rat_cut_bin_certificate_sound certificate3729 profilesValid3729 numericValid3729 valid3729

def retention3730 : RatCutRetentionCertificate := ⟨(21/2000),(11/1000),(2848495998622289345/9615687695137442862049),(319975293/250000000),(5/2),(9447060842566096151/4000000000000000000),true,MergedCutProfiles.Batch567.profile22713,![MergedCutProfiles.Batch567.profile22713,MergedCutProfiles.Batch567.profile22717,MergedCutProfiles.Batch568.profile22720,MergedCutProfiles.Batch568.profile22722,MergedCutProfiles.Batch568.profile22724,MergedCutProfiles.Batch568.profile22726,MergedCutProfiles.Batch568.profile22728,MergedCutProfiles.Batch568.profile22729,MergedCutProfiles.Batch568.profile22730,MergedCutProfiles.Batch568.profile22731,MergedCutProfiles.Batch568.profile22732,MergedCutProfiles.Batch568.profile22733,MergedCutProfiles.Batch568.profile22734,MergedCutProfiles.Batch568.profile22735,MergedCutProfiles.Batch568.profile22736,MergedCutProfiles.Batch568.profile22737]⟩
theorem profilesValid3730 : retention3730.ProfilesValid := by
  change ∀ j : Fin 16, (retention3730.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch567.valid22713
  · exact MergedCutProfiles.Batch567.valid22717
  · exact MergedCutProfiles.Batch568.valid22720
  · exact MergedCutProfiles.Batch568.valid22722
  · exact MergedCutProfiles.Batch568.valid22724
  · exact MergedCutProfiles.Batch568.valid22726
  · exact MergedCutProfiles.Batch568.valid22728
  · exact MergedCutProfiles.Batch568.valid22729
  · exact MergedCutProfiles.Batch568.valid22730
  · exact MergedCutProfiles.Batch568.valid22731
  · exact MergedCutProfiles.Batch568.valid22732
  · exact MergedCutProfiles.Batch568.valid22733
  · exact MergedCutProfiles.Batch568.valid22734
  · exact MergedCutProfiles.Batch568.valid22735
  · exact MergedCutProfiles.Batch568.valid22736
  · exact MergedCutProfiles.Batch568.valid22737
theorem numericValid3730 : retention3730.NumericValid := by decide +kernel
def certificate3730 : RatCutBinCertificate := ⟨⟨retention3730,(897833486860996359/500000000000000000),(246507623072377/50000000000000000),(7571273441896334563/1000000000000000000),(72967924963157851309997/1000000000000000000),(2358842019382711043/1000000000000000000)⟩,(999975501371161171/1000000000000000000),(72368822679233189/200000000000000000),(13516104047556673/50000000000000000),(49242425354367887/250000000000000000)⟩
theorem valid3730 : certificate3730.Valid := by decide +kernel
theorem sound3730 : certificate3730.Sound := rat_cut_bin_certificate_sound certificate3730 profilesValid3730 numericValid3730 valid3730

def retention3731 : RatCutRetentionCertificate := ⟨(21/2000),(11/1000),(64000000000000000000/9615687695137442862049),(569699199724457869/200000000000000000),(31/20),(144493166655167131799/64000000000000000000),true,MergedCutProfiles.Batch568.profile22738,![MergedCutProfiles.Batch568.profile22738,MergedCutProfiles.Batch568.profile22739,MergedCutProfiles.Batch568.profile22740,MergedCutProfiles.Batch568.profile22741,MergedCutProfiles.Batch568.profile22742,MergedCutProfiles.Batch568.profile22743,MergedCutProfiles.Batch568.profile22744,MergedCutProfiles.Batch568.profile22745,MergedCutProfiles.Batch568.profile22746,MergedCutProfiles.Batch568.profile22747,MergedCutProfiles.Batch568.profile22748,MergedCutProfiles.Batch568.profile22749,MergedCutProfiles.Batch568.profile22750,MergedCutProfiles.Batch568.profile22751,MergedCutProfiles.Batch568.profile22752,MergedCutProfiles.Batch568.profile22753]⟩
theorem profilesValid3731 : retention3731.ProfilesValid := by
  change ∀ j : Fin 16, (retention3731.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch568.valid22738
  · exact MergedCutProfiles.Batch568.valid22739
  · exact MergedCutProfiles.Batch568.valid22740
  · exact MergedCutProfiles.Batch568.valid22741
  · exact MergedCutProfiles.Batch568.valid22742
  · exact MergedCutProfiles.Batch568.valid22743
  · exact MergedCutProfiles.Batch568.valid22744
  · exact MergedCutProfiles.Batch568.valid22745
  · exact MergedCutProfiles.Batch568.valid22746
  · exact MergedCutProfiles.Batch568.valid22747
  · exact MergedCutProfiles.Batch568.valid22748
  · exact MergedCutProfiles.Batch568.valid22749
  · exact MergedCutProfiles.Batch568.valid22750
  · exact MergedCutProfiles.Batch568.valid22751
  · exact MergedCutProfiles.Batch568.valid22752
  · exact MergedCutProfiles.Batch568.valid22753
theorem numericValid3731 : retention3731.NumericValid := by decide +kernel
def certificate3731 : RatCutBinCertificate := ⟨⟨retention3731,(897833486860996359/500000000000000000),(246507623072377/50000000000000000),(7571273441896334563/1000000000000000000),(72967924963157851309997/1000000000000000000),(2255893350417057471/1000000000000000000)⟩,(999975501371161171/1000000000000000000),(54873812817784007/200000000000000000),(370749324893740677/1000000000000000000),(81161784508992701/200000000000000000)⟩
theorem valid3731 : certificate3731.Valid := by decide +kernel
theorem sound3731 : certificate3731.Sound := rat_cut_bin_certificate_sound certificate3731 profilesValid3731 numericValid3731 valid3731

def certificates : List RatCutBinCertificate := [certificate3720,certificate3721,certificate3722,certificate3723,certificate3724,certificate3725,certificate3726,certificate3727,certificate3728,certificate3729,certificate3730,certificate3731]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3720,List.forall_mem_cons.mpr ⟨sound3721,List.forall_mem_cons.mpr ⟨sound3722,List.forall_mem_cons.mpr ⟨sound3723,List.forall_mem_cons.mpr ⟨sound3724,List.forall_mem_cons.mpr ⟨sound3725,List.forall_mem_cons.mpr ⟨sound3726,List.forall_mem_cons.mpr ⟨sound3727,List.forall_mem_cons.mpr ⟨sound3728,List.forall_mem_cons.mpr ⟨sound3729,List.forall_mem_cons.mpr ⟨sound3730,List.forall_mem_cons.mpr ⟨sound3731,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch310
