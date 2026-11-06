import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch140
import Cycle12.MergedCutProfiles.Batch141
import Cycle12.MergedCutProfiles.Batch142

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch069

def retention828 : RatCutRetentionCertificate := ⟨(193/4000),(97/2000),(9495455449227415568/20449941781027281327),(195374609639466943/31250000000000000),1,(16481453230252484321/16000000000000000000),true,MergedCutProfiles.Batch140.profile5610,![MergedCutProfiles.Batch140.profile5610,MergedCutProfiles.Batch140.profile5611,MergedCutProfiles.Batch140.profile5612,MergedCutProfiles.Batch140.profile5613,MergedCutProfiles.Batch140.profile5614,MergedCutProfiles.Batch140.profile5615,MergedCutProfiles.Batch140.profile5616,MergedCutProfiles.Batch140.profile5617,MergedCutProfiles.Batch140.profile5618,MergedCutProfiles.Batch140.profile5619,MergedCutProfiles.Batch140.profile5620,MergedCutProfiles.Batch140.profile5621,MergedCutProfiles.Batch140.profile5622,MergedCutProfiles.Batch140.profile5623,MergedCutProfiles.Batch140.profile5624,MergedCutProfiles.Batch140.profile5625]⟩
theorem profilesValid828 : retention828.ProfilesValid := by
  change ∀ j : Fin 16, (retention828.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch140.valid5610
  · exact MergedCutProfiles.Batch140.valid5611
  · exact MergedCutProfiles.Batch140.valid5612
  · exact MergedCutProfiles.Batch140.valid5613
  · exact MergedCutProfiles.Batch140.valid5614
  · exact MergedCutProfiles.Batch140.valid5615
  · exact MergedCutProfiles.Batch140.valid5616
  · exact MergedCutProfiles.Batch140.valid5617
  · exact MergedCutProfiles.Batch140.valid5618
  · exact MergedCutProfiles.Batch140.valid5619
  · exact MergedCutProfiles.Batch140.valid5620
  · exact MergedCutProfiles.Batch140.valid5621
  · exact MergedCutProfiles.Batch140.valid5622
  · exact MergedCutProfiles.Batch140.valid5623
  · exact MergedCutProfiles.Batch140.valid5624
  · exact MergedCutProfiles.Batch140.valid5625
theorem numericValid828 : retention828.NumericValid := by decide +kernel
def certificate828 : RatCutBinCertificate := ⟨⟨retention828,(1059984774357008223/500000000000000000),(55890737994639571/500000000000000000),(3234869281085007603/250000000000000000),(132493373275799381101/500000000000000000),(252943902800755553/250000000000000000)⟩,(99287721034258331/100000000000000000),(485996920554266343/1000000000000000000),(163330464644405133/1000000000000000000),(70570140501422997/500000000000000000)⟩
theorem valid828 : certificate828.Valid := by decide +kernel
theorem sound828 : certificate828.Sound := rat_cut_bin_certificate_sound certificate828 profilesValid828 numericValid828 valid828

def retention829 : RatCutRetentionCertificate := ⟨(193/4000),(97/2000),(10079617298488972286/20449941781027281327),(593465965576713473/62500000000000000),(21/20),(239306610606196445463771720302039672159/237386386230685389200000000000000000000),false,MergedCutProfiles.Batch140.profile5626,(fun _ => MergedCutProfiles.Batch140.profile5626)⟩
theorem profilesValid829 : retention829.ProfilesValid := by
  exact MergedCutProfiles.Batch140.valid5626
theorem numericValid829 : retention829.NumericValid := by decide +kernel
def certificate829 : RatCutBinCertificate := ⟨⟨retention829,(1059984774357008223/500000000000000000),(55890737994639571/500000000000000000),(3234869281085007603/250000000000000000),(132493373275799381101/500000000000000000),(24721463306103557/25000000000000000)⟩,(99287721034258331/100000000000000000),(482331741061423957/1000000000000000000),(165988930122120669/1000000000000000000),(141759547031007713/1000000000000000000)⟩
theorem valid829 : certificate829.Valid := by decide +kernel
theorem sound829 : certificate829.Sound := rat_cut_bin_certificate_sound certificate829 profilesValid829 numericValid829 valid829

def retention830 : RatCutRetentionCertificate := ⟨(193/4000),(97/2000),(3393471157157954003/6816647260342427109),(5039808649244486143/500000000000000000),(21/20),(4030486193265913373793741167614773708111/4031846919395588914400000000000000000000),false,MergedCutProfiles.Batch140.profile5627,(fun _ => MergedCutProfiles.Batch140.profile5627)⟩
theorem profilesValid830 : retention830.ProfilesValid := by
  exact MergedCutProfiles.Batch140.valid5627
theorem numericValid830 : retention830.NumericValid := by decide +kernel
def certificate830 : RatCutBinCertificate := ⟨⟨retention830,(1059984774357008223/500000000000000000),(55890737994639571/500000000000000000),(3234869281085007603/250000000000000000),(132493373275799381101/500000000000000000),(490216030030646883/500000000000000000)⟩,(99287721034258331/100000000000000000),(242397609978118423/500000000000000000),(164199038691719891/1000000000000000000),(139835101043672037/1000000000000000000)⟩
theorem valid830 : certificate830.Valid := by decide +kernel
theorem sound830 : certificate830.Sound := rat_cut_bin_certificate_sound certificate830 profilesValid830 numericValid830 valid830

def retention831 : RatCutRetentionCertificate := ⟨(193/4000),(97/2000),(1/2),(10180413471473862009/1000000000000000000),(21/20),(16216803464812504189216381169486686801559/16288661554358179214400000000000000000000),false,MergedCutProfiles.Batch140.profile5628,(fun _ => MergedCutProfiles.Batch140.profile5628)⟩
theorem profilesValid831 : retention831.ProfilesValid := by
  exact MergedCutProfiles.Batch140.valid5628
theorem numericValid831 : retention831.NumericValid := by decide +kernel
def certificate831 : RatCutBinCertificate := ⟨⟨retention831,(1059984774357008223/500000000000000000),(55890737994639571/500000000000000000),(3234869281085007603/250000000000000000),(132493373275799381101/500000000000000000),(244089505419679119/250000000000000000)⟩,(99287721034258331/100000000000000000),(486546291629447791/1000000000000000000),(162934376258484771/1000000000000000000),(138339134119044801/1000000000000000000)⟩
theorem valid831 : certificate831.Valid := by decide +kernel
theorem sound831 : certificate831.Sound := rat_cut_bin_certificate_sound certificate831 profilesValid831 numericValid831 valid831

def retention832 : RatCutRetentionCertificate := ⟨(193/4000),(97/2000),(3070481028827508458/6816647260342427109),(3687748415883501937/1000000000000000000),(6/5),(4578269117327155099644084879204611127/4190623199867615837500000000000000000),false,MergedCutProfiles.Batch140.profile5629,(fun _ => MergedCutProfiles.Batch140.profile5629)⟩
theorem profilesValid832 : retention832.ProfilesValid := by
  exact MergedCutProfiles.Batch140.valid5629
theorem numericValid832 : retention832.NumericValid := by decide +kernel
def certificate832 : RatCutBinCertificate := ⟨⟨retention832,(1262098832857008223/500000000000000000),(55890737994639571/500000000000000000),(3234869281085007603/250000000000000000),(132493373275799381101/500000000000000000),(1066333444512737781/1000000000000000000)⟩,(991517631906718853/1000000000000000000),(95988965833915931/250000000000000000),(124254392903408737/500000000000000000),(182195215283893139/1000000000000000000)⟩
theorem valid832 : certificate832.Valid := by decide +kernel
theorem sound832 : certificate832.Sound := rat_cut_bin_certificate_sound certificate832 profilesValid832 numericValid832 valid832

def retention833 : RatCutRetentionCertificate := ⟨(193/4000),(97/2000),(10074419643856111783/20449941781027281327),(4605721543241262687/500000000000000000),(21/20),(3713772222245933620159161895727450963951/3684577234593010149600000000000000000000),false,MergedCutProfiles.Batch140.profile5630,(fun _ => MergedCutProfiles.Batch140.profile5630)⟩
theorem profilesValid833 : retention833.ProfilesValid := by
  exact MergedCutProfiles.Batch140.valid5630
theorem numericValid833 : retention833.NumericValid := by decide +kernel
def certificate833 : RatCutBinCertificate := ⟨⟨retention833,(1262098832857008223/500000000000000000),(55890737994639571/500000000000000000),(3234869281085007603/250000000000000000),(132493373275799381101/500000000000000000),(492513120978860681/500000000000000000)⟩,(991517631906718853/1000000000000000000),(103912200724179633/250000000000000000),(219446212748009019/1000000000000000000),(185998762363435529/1000000000000000000)⟩
theorem valid833 : certificate833.Valid := by decide +kernel
theorem sound833 : certificate833.Sound := rat_cut_bin_certificate_sound certificate833 profilesValid833 numericValid833 valid833

def retention834 : RatCutRetentionCertificate := ⟨(193/4000),(97/2000),(10175163840294672901/20449941781027281327),(10074419643856111783/1000000000000000000),(21/20),(16121561384947389757921194403382833301511/16119071430169778852800000000000000000000),false,MergedCutProfiles.Batch140.profile5631,(fun _ => MergedCutProfiles.Batch140.profile5631)⟩
theorem profilesValid834 : retention834.ProfilesValid := by
  exact MergedCutProfiles.Batch140.valid5631
theorem numericValid834 : retention834.NumericValid := by decide +kernel
def certificate834 : RatCutBinCertificate := ⟨⟨retention834,(1262098832857008223/500000000000000000),(55890737994639571/500000000000000000),(3234869281085007603/250000000000000000),(132493373275799381101/500000000000000000),(97725723497397513/100000000000000000)⟩,(991517631906718853/1000000000000000000),(418953130904662481/1000000000000000000),(108279237930392171/500000000000000000),(11476056781117263/62500000000000000)⟩
theorem valid834 : certificate834.Valid := by decide +kernel
theorem sound834 : certificate834.Sound := rat_cut_bin_certificate_sound certificate834 profilesValid834 numericValid834 valid834

def retention835 : RatCutRetentionCertificate := ⟨(193/4000),(97/2000),(1/2),(10175163840294672901/1000000000000000000),(21/20),(16208287623096096440724884153999010673359/16280262144471476641600000000000000000000),false,MergedCutProfiles.Batch140.profile5628,(fun _ => MergedCutProfiles.Batch140.profile5628)⟩
theorem profilesValid835 : retention835.ProfilesValid := by
  exact MergedCutProfiles.Batch140.valid5628
theorem numericValid835 : retention835.NumericValid := by decide +kernel
def certificate835 : RatCutBinCertificate := ⟨⟨retention835,(1262098832857008223/500000000000000000),(55890737994639571/500000000000000000),(3234869281085007603/250000000000000000),(132493373275799381101/500000000000000000),(972681803211144571/1000000000000000000)⟩,(991517631906718853/1000000000000000000),(3288467649279781/7812500000000000),(214848622374455959/1000000000000000000),(22691029741773497/125000000000000000)⟩
theorem valid835 : certificate835.Valid := by decide +kernel
theorem sound835 : certificate835.Sound := rat_cut_bin_certificate_sound certificate835 profilesValid835 numericValid835 valid835

def retention836 : RatCutRetentionCertificate := ⟨(97/2000),(39/800),(845787120413644167/20212032053131816613),(837412990508558581/1000000000000000000),(59/20),(20855222321841525253/10000000000000000000),true,MergedCutProfiles.Batch140.profile5632,![MergedCutProfiles.Batch140.profile5632,MergedCutProfiles.Batch140.profile5633,MergedCutProfiles.Batch140.profile5634,MergedCutProfiles.Batch140.profile5635,MergedCutProfiles.Batch140.profile5636,MergedCutProfiles.Batch140.profile5637,MergedCutProfiles.Batch140.profile5638,MergedCutProfiles.Batch140.profile5639,MergedCutProfiles.Batch141.profile5640,MergedCutProfiles.Batch141.profile5641,MergedCutProfiles.Batch141.profile5642,MergedCutProfiles.Batch141.profile5643,MergedCutProfiles.Batch141.profile5644,MergedCutProfiles.Batch141.profile5645,MergedCutProfiles.Batch141.profile5646,MergedCutProfiles.Batch141.profile5647]⟩
theorem profilesValid836 : retention836.ProfilesValid := by
  change ∀ j : Fin 16, (retention836.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch140.valid5632
  · exact MergedCutProfiles.Batch140.valid5633
  · exact MergedCutProfiles.Batch140.valid5634
  · exact MergedCutProfiles.Batch140.valid5635
  · exact MergedCutProfiles.Batch140.valid5636
  · exact MergedCutProfiles.Batch140.valid5637
  · exact MergedCutProfiles.Batch140.valid5638
  · exact MergedCutProfiles.Batch140.valid5639
  · exact MergedCutProfiles.Batch141.valid5640
  · exact MergedCutProfiles.Batch141.valid5641
  · exact MergedCutProfiles.Batch141.valid5642
  · exact MergedCutProfiles.Batch141.valid5643
  · exact MergedCutProfiles.Batch141.valid5644
  · exact MergedCutProfiles.Batch141.valid5645
  · exact MergedCutProfiles.Batch141.valid5646
  · exact MergedCutProfiles.Batch141.valid5647
theorem numericValid836 : retention836.NumericValid := by decide +kernel
def certificate836 : RatCutBinCertificate := ⟨⟨retention836,(430671974922658799/200000000000000000),(5654114764730837/50000000000000000),(12992805386102834049/1000000000000000000),(131491975698769558831/500000000000000000),(507556170183553129/250000000000000000)⟩,(992720273333164311/1000000000000000000),(14999181777385421/40000000000000000),(257206263029566701/1000000000000000000),(68625408742902567/500000000000000000)⟩
theorem valid836 : certificate836.Valid := by decide +kernel
theorem sound836 : certificate836.Sound := rat_cut_bin_certificate_sound certificate836 profilesValid836 numericValid836 valid836

def retention837 : RatCutRetentionCertificate := ⟨(97/2000),(39/800),(858301601000000000/20212032053131816613),(845787120413644167/1000000000000000000),(29/10),(166205859323884163421/80000000000000000000),true,MergedCutProfiles.Batch141.profile5648,![MergedCutProfiles.Batch141.profile5648,MergedCutProfiles.Batch141.profile5649,MergedCutProfiles.Batch141.profile5650,MergedCutProfiles.Batch141.profile5651,MergedCutProfiles.Batch141.profile5652,MergedCutProfiles.Batch141.profile5653,MergedCutProfiles.Batch141.profile5654,MergedCutProfiles.Batch141.profile5655,MergedCutProfiles.Batch141.profile5656,MergedCutProfiles.Batch141.profile5657,MergedCutProfiles.Batch141.profile5658,MergedCutProfiles.Batch141.profile5659,MergedCutProfiles.Batch141.profile5660,MergedCutProfiles.Batch141.profile5661,MergedCutProfiles.Batch141.profile5662,MergedCutProfiles.Batch141.profile5663]⟩
theorem profilesValid837 : retention837.ProfilesValid := by
  change ∀ j : Fin 16, (retention837.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch141.valid5648
  · exact MergedCutProfiles.Batch141.valid5649
  · exact MergedCutProfiles.Batch141.valid5650
  · exact MergedCutProfiles.Batch141.valid5651
  · exact MergedCutProfiles.Batch141.valid5652
  · exact MergedCutProfiles.Batch141.valid5653
  · exact MergedCutProfiles.Batch141.valid5654
  · exact MergedCutProfiles.Batch141.valid5655
  · exact MergedCutProfiles.Batch141.valid5656
  · exact MergedCutProfiles.Batch141.valid5657
  · exact MergedCutProfiles.Batch141.valid5658
  · exact MergedCutProfiles.Batch141.valid5659
  · exact MergedCutProfiles.Batch141.valid5660
  · exact MergedCutProfiles.Batch141.valid5661
  · exact MergedCutProfiles.Batch141.valid5662
  · exact MergedCutProfiles.Batch141.valid5663
theorem numericValid837 : retention837.NumericValid := by decide +kernel
def certificate837 : RatCutBinCertificate := ⟨⟨retention837,(430671974922658799/200000000000000000),(5654114764730837/50000000000000000),(12992805386102834049/1000000000000000000),(131491975698769558831/500000000000000000),(2023212868905221493/1000000000000000000)⟩,(992720273333164311/1000000000000000000),(9368377630851817/25000000000000000),(257446088849473183/1000000000000000000),(17328757234966891/125000000000000000)⟩
theorem valid837 : certificate837.Valid := by decide +kernel
theorem sound837 : certificate837.Sound := rat_cut_bin_certificate_sound certificate837 profilesValid837 numericValid837 valid837

def retention838 : RatCutRetentionCertificate := ⟨(97/2000),(39/800),(915866254873779023/20212032053131816613),(858301601/1000000000),(29/10),(33195878563591998647/16000000000000000000),true,MergedCutProfiles.Batch141.profile5664,![MergedCutProfiles.Batch141.profile5664,MergedCutProfiles.Batch141.profile5665,MergedCutProfiles.Batch141.profile5666,MergedCutProfiles.Batch141.profile5667,MergedCutProfiles.Batch141.profile5668,MergedCutProfiles.Batch141.profile5669,MergedCutProfiles.Batch141.profile5670,MergedCutProfiles.Batch141.profile5671,MergedCutProfiles.Batch141.profile5672,MergedCutProfiles.Batch141.profile5673,MergedCutProfiles.Batch141.profile5674,MergedCutProfiles.Batch141.profile5644,MergedCutProfiles.Batch141.profile5675,MergedCutProfiles.Batch141.profile5676,MergedCutProfiles.Batch141.profile5663,MergedCutProfiles.Batch141.profile5677]⟩
theorem profilesValid838 : retention838.ProfilesValid := by
  change ∀ j : Fin 16, (retention838.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch141.valid5664
  · exact MergedCutProfiles.Batch141.valid5665
  · exact MergedCutProfiles.Batch141.valid5666
  · exact MergedCutProfiles.Batch141.valid5667
  · exact MergedCutProfiles.Batch141.valid5668
  · exact MergedCutProfiles.Batch141.valid5669
  · exact MergedCutProfiles.Batch141.valid5670
  · exact MergedCutProfiles.Batch141.valid5671
  · exact MergedCutProfiles.Batch141.valid5672
  · exact MergedCutProfiles.Batch141.valid5673
  · exact MergedCutProfiles.Batch141.valid5674
  · exact MergedCutProfiles.Batch141.valid5644
  · exact MergedCutProfiles.Batch141.valid5675
  · exact MergedCutProfiles.Batch141.valid5676
  · exact MergedCutProfiles.Batch141.valid5663
  · exact MergedCutProfiles.Batch141.valid5677
theorem numericValid838 : retention838.NumericValid := by decide +kernel
def certificate838 : RatCutBinCertificate := ⟨⟨retention838,(430671974922658799/200000000000000000),(5654114764730837/50000000000000000),(12992805386102834049/1000000000000000000),(131491975698769558831/500000000000000000),(404076435301560147/200000000000000000)⟩,(992720273333164311/1000000000000000000),(373005750193275757/1000000000000000000),(32393420201983097/125000000000000000),(139847248469200421/1000000000000000000)⟩
theorem valid838 : certificate838.Valid := by decide +kernel
theorem sound838 : certificate838.Sound := rat_cut_bin_certificate_sound certificate838 profilesValid838 numericValid838 valid838

def retention839 : RatCutRetentionCertificate := ⟨(97/2000),(39/800),(82642264521491893/1188943061948930389),(915866254873779023/1000000000000000000),(27/10),(636967794403660686759/320000000000000000000),true,MergedCutProfiles.Batch141.profile5678,![MergedCutProfiles.Batch141.profile5678,MergedCutProfiles.Batch141.profile5679,MergedCutProfiles.Batch142.profile5680,MergedCutProfiles.Batch142.profile5681,MergedCutProfiles.Batch142.profile5682,MergedCutProfiles.Batch142.profile5683,MergedCutProfiles.Batch142.profile5684,MergedCutProfiles.Batch142.profile5685,MergedCutProfiles.Batch142.profile5686,MergedCutProfiles.Batch142.profile5687,MergedCutProfiles.Batch142.profile5688,MergedCutProfiles.Batch142.profile5689,MergedCutProfiles.Batch142.profile5690,MergedCutProfiles.Batch142.profile5691,MergedCutProfiles.Batch142.profile5692,MergedCutProfiles.Batch142.profile5693]⟩
theorem profilesValid839 : retention839.ProfilesValid := by
  change ∀ j : Fin 16, (retention839.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch141.valid5678
  · exact MergedCutProfiles.Batch141.valid5679
  · exact MergedCutProfiles.Batch142.valid5680
  · exact MergedCutProfiles.Batch142.valid5681
  · exact MergedCutProfiles.Batch142.valid5682
  · exact MergedCutProfiles.Batch142.valid5683
  · exact MergedCutProfiles.Batch142.valid5684
  · exact MergedCutProfiles.Batch142.valid5685
  · exact MergedCutProfiles.Batch142.valid5686
  · exact MergedCutProfiles.Batch142.valid5687
  · exact MergedCutProfiles.Batch142.valid5688
  · exact MergedCutProfiles.Batch142.valid5689
  · exact MergedCutProfiles.Batch142.valid5690
  · exact MergedCutProfiles.Batch142.valid5691
  · exact MergedCutProfiles.Batch142.valid5692
  · exact MergedCutProfiles.Batch142.valid5693
theorem numericValid839 : retention839.NumericValid := by decide +kernel
def certificate839 : RatCutBinCertificate := ⟨⟨retention839,(430671974922658799/200000000000000000),(5654114764730837/50000000000000000),(12992805386102834049/1000000000000000000),(131491975698769558831/500000000000000000),(96995652401754801/50000000000000000)⟩,(992720273333164311/1000000000000000000),(189252369382079673/500000000000000000),(126882626845219767/500000000000000000),(140062835727891241/1000000000000000000)⟩
theorem valid839 : certificate839.Valid := by decide +kernel
theorem sound839 : certificate839.Sound := rat_cut_bin_certificate_sound certificate839 profilesValid839 numericValid839 valid839

def certificates : List RatCutBinCertificate := [certificate828,certificate829,certificate830,certificate831,certificate832,certificate833,certificate834,certificate835,certificate836,certificate837,certificate838,certificate839]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound828,List.forall_mem_cons.mpr ⟨sound829,List.forall_mem_cons.mpr ⟨sound830,List.forall_mem_cons.mpr ⟨sound831,List.forall_mem_cons.mpr ⟨sound832,List.forall_mem_cons.mpr ⟨sound833,List.forall_mem_cons.mpr ⟨sound834,List.forall_mem_cons.mpr ⟨sound835,List.forall_mem_cons.mpr ⟨sound836,List.forall_mem_cons.mpr ⟨sound837,List.forall_mem_cons.mpr ⟨sound838,List.forall_mem_cons.mpr ⟨sound839,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch069
