import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch066
import Cycle12.MergedCutProfiles.Batch067
import Cycle12.MergedCutProfiles.Batch068

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch033

def retention396 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(20013169109032200763/40970350049210168724),(7277830026242678583/500000000000000000),(21/20),(1985561244293071058643246643332105076917/1940754673664714288800000000000000000000),false,MergedCutProfiles.Batch066.profile2643,(fun _ => MergedCutProfiles.Batch066.profile2643)⟩
theorem profilesValid396 : retention396.ProfilesValid := by
  exact MergedCutProfiles.Batch066.valid2643
theorem numericValid396 : retention396.NumericValid := by decide +kernel
def certificate396 : RatCutBinCertificate := ⟨⟨retention396,(1018656151474196381/500000000000000000),(14082027828820247/250000000000000000),(10530164287713757123/1000000000000000000),(54069082130495480293/125000000000000000),(1011644169534717187/1000000000000000000)⟩,(995546191717510047/1000000000000000000),(478117554619533671/1000000000000000000),(84540020027425463/500000000000000000),(152537639161001977/1000000000000000000)⟩
theorem valid396 : certificate396.Valid := by decide +kernel
theorem sound396 : certificate396.Sound := rat_cut_bin_certificate_sound certificate396 profilesValid396 numericValid396 valid396

def retention397 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(20415433808123747999/40970350049210168724),(20013169109032200763/1000000000000000000),1,(79435602878693070913760037018531651651/80052676436128803052000000000000000000),false,MergedCutProfiles.Batch066.profile2644,(fun _ => MergedCutProfiles.Batch066.profile2644)⟩
theorem profilesValid397 : retention397.ProfilesValid := by
  exact MergedCutProfiles.Batch066.valid2644
theorem numericValid397 : retention397.NumericValid := by decide +kernel
def certificate397 : RatCutBinCertificate := ⟨⟨retention397,(1018656151474196381/500000000000000000),(14082027828820247/250000000000000000),(10530164287713757123/1000000000000000000),(54069082130495480293/125000000000000000),(19627871279406761/20000000000000000)⟩,(995546191717510047/1000000000000000000),(486467581358601809/1000000000000000000),(6519643484395849/40000000000000000),(75892137748786631/500000000000000000)⟩
theorem valid397 : certificate397.Valid := by decide +kernel
theorem sound397 : certificate397.Sound := rat_cut_bin_certificate_sound certificate397 profilesValid397 numericValid397 valid397

def retention398 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(1/2),(20415433808123747999/1000000000000000000),1,(20195229414390599985135059564643907101/20415433808123747999000000000000000000),false,MergedCutProfiles.Batch066.profile2645,(fun _ => MergedCutProfiles.Batch066.profile2645)⟩
theorem profilesValid398 : retention398.ProfilesValid := by
  exact MergedCutProfiles.Batch066.valid2645
theorem numericValid398 : retention398.NumericValid := by decide +kernel
def certificate398 : RatCutBinCertificate := ⟨⟨retention398,(1018656151474196381/500000000000000000),(14082027828820247/250000000000000000),(10530164287713757123/1000000000000000000),(54069082130495480293/125000000000000000),(19566314731734659/20000000000000000)⟩,(995546191717510047/1000000000000000000),(487661296464687369/1000000000000000000),(20266547576351993/125000000000000000),(15067185609527707/100000000000000000)⟩
theorem valid398 : certificate398.Valid := by decide +kernel
theorem sound398 : certificate398.Sound := rat_cut_bin_certificate_sound certificate398 profilesValid398 numericValid398 valid398

def retention399 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(17540475691687716895/40970350049210168724),(3751702829296014991/1000000000000000000),(5/4),(54927662151784193203386489116815957091/48021796214988991884800000000000000000),false,MergedCutProfiles.Batch066.profile2646,(fun _ => MergedCutProfiles.Batch066.profile2646)⟩
theorem profilesValid399 : retention399.ProfilesValid := by
  exact MergedCutProfiles.Batch066.valid2646
theorem numericValid399 : retention399.NumericValid := by decide +kernel
def certificate399 : RatCutBinCertificate := ⟨⟨retention399,(1210456236474196381/500000000000000000),(14082027828820247/250000000000000000),(10530164287713757123/1000000000000000000),(54069082130495480293/125000000000000000),(1127618980328885659/1000000000000000000)⟩,(497353669696169093/500000000000000000),(176366272060456309/500000000000000000),(8740588505089009/31250000000000000),(105198730533224067/500000000000000000)⟩
theorem valid399 : certificate399.Valid := by decide +kernel
theorem sound399 : certificate399.Sound := rat_cut_bin_certificate_sound certificate399 profilesValid399 numericValid399 valid399

def retention400 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(10181973870235770595/20485175024605084362),(3508095138337543379/200000000000000000),1,(69667924935375268002112026969468577131/70161902766750867580000000000000000000),false,MergedCutProfiles.Batch066.profile2647,(fun _ => MergedCutProfiles.Batch066.profile2647)⟩
theorem profilesValid400 : retention400.ProfilesValid := by
  exact MergedCutProfiles.Batch066.valid2647
theorem numericValid400 : retention400.NumericValid := by decide +kernel
def certificate400 : RatCutBinCertificate := ⟨⟨retention400,(1210456236474196381/500000000000000000),(14082027828820247/250000000000000000),(10530164287713757123/1000000000000000000),(54069082130495480293/125000000000000000),(980009380759942659/1000000000000000000)⟩,(497353669696169093/500000000000000000),(6341583297875007/15625000000000000),(5703865876058991/25000000000000000),(52653387835887391/250000000000000000)⟩
theorem valid400 : certificate400.Valid := by decide +kernel
theorem sound400 : certificate400.Sound := rat_cut_bin_certificate_sound certificate400 profilesValid400 numericValid400 valid400

def retention401 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(1/2),(2036394774047154119/100000000000000000),1,(20143666316660785457993121855435392379/20363947740471541190000000000000000000),false,MergedCutProfiles.Batch066.profile2645,(fun _ => MergedCutProfiles.Batch066.profile2645)⟩
theorem profilesValid401 : retention401.ProfilesValid := by
  exact MergedCutProfiles.Batch066.valid2645
theorem numericValid401 : retention401.NumericValid := by decide +kernel
def certificate401 : RatCutBinCertificate := ⟨⟨retention401,(1210456236474196381/500000000000000000),(14082027828820247/250000000000000000),(10530164287713757123/1000000000000000000),(54069082130495480293/125000000000000000),(488116355131346351/500000000000000000)⟩,(497353669696169093/500000000000000000),(407431453124949981/1000000000000000000),(113370936622902837/500000000000000000),(210084662845107121/1000000000000000000)⟩
theorem valid401 : certificate401.Valid := by decide +kernel
theorem sound401 : certificate401.Sound := rat_cut_bin_certificate_sound certificate401 profilesValid401 numericValid401 valid401

def retention402 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(769090601116200517/39735965222884822823),(380737921344653721/500000000000000000),(17/5),(1403593717230627499461/640000000000000000000),true,MergedCutProfiles.Batch066.profile2648,![MergedCutProfiles.Batch066.profile2648,MergedCutProfiles.Batch066.profile2649,MergedCutProfiles.Batch066.profile2650,MergedCutProfiles.Batch066.profile2651,MergedCutProfiles.Batch066.profile2652,MergedCutProfiles.Batch066.profile2653,MergedCutProfiles.Batch066.profile2654,MergedCutProfiles.Batch066.profile2655,MergedCutProfiles.Batch066.profile2656,MergedCutProfiles.Batch066.profile2657,MergedCutProfiles.Batch066.profile2658,MergedCutProfiles.Batch066.profile2659,MergedCutProfiles.Batch066.profile2660,MergedCutProfiles.Batch066.profile2661,MergedCutProfiles.Batch066.profile2662,MergedCutProfiles.Batch066.profile2663]⟩
theorem profilesValid402 : retention402.ProfilesValid := by
  change ∀ j : Fin 16, (retention402.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch066.valid2648
  · exact MergedCutProfiles.Batch066.valid2649
  · exact MergedCutProfiles.Batch066.valid2650
  · exact MergedCutProfiles.Batch066.valid2651
  · exact MergedCutProfiles.Batch066.valid2652
  · exact MergedCutProfiles.Batch066.valid2653
  · exact MergedCutProfiles.Batch066.valid2654
  · exact MergedCutProfiles.Batch066.valid2655
  · exact MergedCutProfiles.Batch066.valid2656
  · exact MergedCutProfiles.Batch066.valid2657
  · exact MergedCutProfiles.Batch066.valid2658
  · exact MergedCutProfiles.Batch066.valid2659
  · exact MergedCutProfiles.Batch066.valid2660
  · exact MergedCutProfiles.Batch066.valid2661
  · exact MergedCutProfiles.Batch066.valid2662
  · exact MergedCutProfiles.Batch066.valid2663
theorem numericValid402 : retention402.NumericValid := by decide +kernel
def certificate402 : RatCutBinCertificate := ⟨⟨retention402,(2041151659260645091/1000000000000000000),(3628243259175483/62500000000000000),(663008666071467203/62500000000000000),(211315119221540813759/500000000000000000),(2155135230080100577/1000000000000000000)⟩,(248860287188808163/250000000000000000),(6498284001254637/15625000000000000),(27404297997536527/125000000000000000),(11103807880528423/100000000000000000)⟩
theorem valid402 : certificate402.Valid := by decide +kernel
theorem sound402 : certificate402.Sound := rat_cut_bin_certificate_sound certificate402 profilesValid402 numericValid402 valid402

def retention403 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(884049813626494608/39735965222884822823),(769090601116200517/1000000000000000000),(67/20),(2786100830049809173893/1280000000000000000000),true,MergedCutProfiles.Batch066.profile2664,![MergedCutProfiles.Batch066.profile2664,MergedCutProfiles.Batch066.profile2665,MergedCutProfiles.Batch066.profile2666,MergedCutProfiles.Batch066.profile2667,MergedCutProfiles.Batch066.profile2668,MergedCutProfiles.Batch066.profile2669,MergedCutProfiles.Batch066.profile2670,MergedCutProfiles.Batch066.profile2671,MergedCutProfiles.Batch066.profile2672,MergedCutProfiles.Batch066.profile2673,MergedCutProfiles.Batch066.profile2674,MergedCutProfiles.Batch066.profile2675,MergedCutProfiles.Batch066.profile2662,MergedCutProfiles.Batch066.profile2676,MergedCutProfiles.Batch066.profile2677,MergedCutProfiles.Batch066.profile2678]⟩
theorem profilesValid403 : retention403.ProfilesValid := by
  change ∀ j : Fin 16, (retention403.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch066.valid2664
  · exact MergedCutProfiles.Batch066.valid2665
  · exact MergedCutProfiles.Batch066.valid2666
  · exact MergedCutProfiles.Batch066.valid2667
  · exact MergedCutProfiles.Batch066.valid2668
  · exact MergedCutProfiles.Batch066.valid2669
  · exact MergedCutProfiles.Batch066.valid2670
  · exact MergedCutProfiles.Batch066.valid2671
  · exact MergedCutProfiles.Batch066.valid2672
  · exact MergedCutProfiles.Batch066.valid2673
  · exact MergedCutProfiles.Batch066.valid2674
  · exact MergedCutProfiles.Batch066.valid2675
  · exact MergedCutProfiles.Batch066.valid2662
  · exact MergedCutProfiles.Batch066.valid2676
  · exact MergedCutProfiles.Batch066.valid2677
  · exact MergedCutProfiles.Batch066.valid2678
theorem numericValid403 : retention403.NumericValid := by decide +kernel
def certificate403 : RatCutBinCertificate := ⟨⟨retention403,(2041151659260645091/1000000000000000000),(3628243259175483/62500000000000000),(663008666071467203/62500000000000000),(211315119221540813759/500000000000000000),(1069609919712131723/500000000000000000)⟩,(248860287188808163/250000000000000000),(83393776472674243/200000000000000000),(54572355785083193/250000000000000000),(27777754328539729/250000000000000000)⟩
theorem valid403 : certificate403.Valid := by decide +kernel
theorem sound403 : certificate403.Sound := rat_cut_bin_certificate_sound certificate403 profilesValid403 numericValid403 valid403

def retention404 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(974034011000000000/39735965222884822823),(55253113351655913/62500000000000000),(59/20),(43102772839633887453/20000000000000000000),true,MergedCutProfiles.Batch066.profile2679,![MergedCutProfiles.Batch066.profile2679,MergedCutProfiles.Batch067.profile2680,MergedCutProfiles.Batch067.profile2681,MergedCutProfiles.Batch067.profile2682,MergedCutProfiles.Batch067.profile2683,MergedCutProfiles.Batch067.profile2684,MergedCutProfiles.Batch067.profile2685,MergedCutProfiles.Batch067.profile2686,MergedCutProfiles.Batch067.profile2687,MergedCutProfiles.Batch066.profile2674,MergedCutProfiles.Batch067.profile2688,MergedCutProfiles.Batch067.profile2689,MergedCutProfiles.Batch067.profile2690,MergedCutProfiles.Batch067.profile2691,MergedCutProfiles.Batch067.profile2692,MergedCutProfiles.Batch067.profile2693]⟩
theorem profilesValid404 : retention404.ProfilesValid := by
  change ∀ j : Fin 16, (retention404.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch066.valid2679
  · exact MergedCutProfiles.Batch067.valid2680
  · exact MergedCutProfiles.Batch067.valid2681
  · exact MergedCutProfiles.Batch067.valid2682
  · exact MergedCutProfiles.Batch067.valid2683
  · exact MergedCutProfiles.Batch067.valid2684
  · exact MergedCutProfiles.Batch067.valid2685
  · exact MergedCutProfiles.Batch067.valid2686
  · exact MergedCutProfiles.Batch067.valid2687
  · exact MergedCutProfiles.Batch066.valid2674
  · exact MergedCutProfiles.Batch067.valid2688
  · exact MergedCutProfiles.Batch067.valid2689
  · exact MergedCutProfiles.Batch067.valid2690
  · exact MergedCutProfiles.Batch067.valid2691
  · exact MergedCutProfiles.Batch067.valid2692
  · exact MergedCutProfiles.Batch067.valid2693
theorem numericValid404 : retention404.NumericValid := by decide +kernel
def certificate404 : RatCutBinCertificate := ⟨⟨retention404,(2041151659260645091/1000000000000000000),(3628243259175483/62500000000000000),(663008666071467203/62500000000000000),(211315119221540813759/500000000000000000),(424437092015094519/200000000000000000)⟩,(248860287188808163/250000000000000000),(393897288496446397/1000000000000000000),(59780185461323153/250000000000000000),(1341123393601307/10000000000000000)⟩
theorem valid404 : certificate404.Valid := by decide +kernel
theorem sound404 : certificate404.Sound := rat_cut_bin_certificate_sound certificate404 profilesValid404 numericValid404 valid404

def retention405 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(1122508679389741635/39735965222884822823),(974034011/1000000000),(11/4),(34237765156052660153/16000000000000000000),true,MergedCutProfiles.Batch067.profile2694,![MergedCutProfiles.Batch067.profile2694,MergedCutProfiles.Batch067.profile2695,MergedCutProfiles.Batch067.profile2696,MergedCutProfiles.Batch067.profile2697,MergedCutProfiles.Batch067.profile2698,MergedCutProfiles.Batch067.profile2699,MergedCutProfiles.Batch067.profile2700,MergedCutProfiles.Batch067.profile2701,MergedCutProfiles.Batch067.profile2702,MergedCutProfiles.Batch067.profile2703,MergedCutProfiles.Batch066.profile2676,MergedCutProfiles.Batch067.profile2704,MergedCutProfiles.Batch067.profile2692,MergedCutProfiles.Batch067.profile2705,MergedCutProfiles.Batch067.profile2706,MergedCutProfiles.Batch067.profile2707]⟩
theorem profilesValid405 : retention405.ProfilesValid := by
  change ∀ j : Fin 16, (retention405.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch067.valid2694
  · exact MergedCutProfiles.Batch067.valid2695
  · exact MergedCutProfiles.Batch067.valid2696
  · exact MergedCutProfiles.Batch067.valid2697
  · exact MergedCutProfiles.Batch067.valid2698
  · exact MergedCutProfiles.Batch067.valid2699
  · exact MergedCutProfiles.Batch067.valid2700
  · exact MergedCutProfiles.Batch067.valid2701
  · exact MergedCutProfiles.Batch067.valid2702
  · exact MergedCutProfiles.Batch067.valid2703
  · exact MergedCutProfiles.Batch066.valid2676
  · exact MergedCutProfiles.Batch067.valid2704
  · exact MergedCutProfiles.Batch067.valid2692
  · exact MergedCutProfiles.Batch067.valid2705
  · exact MergedCutProfiles.Batch067.valid2706
  · exact MergedCutProfiles.Batch067.valid2707
theorem numericValid405 : retention405.NumericValid := by decide +kernel
def certificate405 : RatCutBinCertificate := ⟨⟨retention405,(2041151659260645091/1000000000000000000),(3628243259175483/62500000000000000),(663008666071467203/62500000000000000),(211315119221540813759/500000000000000000),(2109141297044993581/1000000000000000000)⟩,(248860287188808163/250000000000000000),(379904344598304449/1000000000000000000),(252408186792552929/1000000000000000000),(149700399567051037/1000000000000000000)⟩
theorem valid405 : certificate405.Valid := by decide +kernel
theorem sound405 : certificate405.Sound := rat_cut_bin_certificate_sound certificate405 profilesValid405 numericValid405 valid405

def retention406 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(2917706419043174004/39735965222884822823),(224501735877948327/200000000000000000),(49/20),(505712177785456679967/256000000000000000000),true,MergedCutProfiles.Batch067.profile2681,![MergedCutProfiles.Batch067.profile2681,MergedCutProfiles.Batch067.profile2684,MergedCutProfiles.Batch067.profile2687,MergedCutProfiles.Batch067.profile2689,MergedCutProfiles.Batch067.profile2692,MergedCutProfiles.Batch067.profile2708,MergedCutProfiles.Batch067.profile2709,MergedCutProfiles.Batch067.profile2710,MergedCutProfiles.Batch067.profile2711,MergedCutProfiles.Batch067.profile2712,MergedCutProfiles.Batch067.profile2713,MergedCutProfiles.Batch067.profile2714,MergedCutProfiles.Batch067.profile2715,MergedCutProfiles.Batch067.profile2716,MergedCutProfiles.Batch067.profile2717,MergedCutProfiles.Batch067.profile2718]⟩
theorem profilesValid406 : retention406.ProfilesValid := by
  change ∀ j : Fin 16, (retention406.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch067.valid2681
  · exact MergedCutProfiles.Batch067.valid2684
  · exact MergedCutProfiles.Batch067.valid2687
  · exact MergedCutProfiles.Batch067.valid2689
  · exact MergedCutProfiles.Batch067.valid2692
  · exact MergedCutProfiles.Batch067.valid2708
  · exact MergedCutProfiles.Batch067.valid2709
  · exact MergedCutProfiles.Batch067.valid2710
  · exact MergedCutProfiles.Batch067.valid2711
  · exact MergedCutProfiles.Batch067.valid2712
  · exact MergedCutProfiles.Batch067.valid2713
  · exact MergedCutProfiles.Batch067.valid2714
  · exact MergedCutProfiles.Batch067.valid2715
  · exact MergedCutProfiles.Batch067.valid2716
  · exact MergedCutProfiles.Batch067.valid2717
  · exact MergedCutProfiles.Batch067.valid2718
theorem numericValid406 : retention406.NumericValid := by decide +kernel
def certificate406 : RatCutBinCertificate := ⟨⟨retention406,(2041151659260645091/1000000000000000000),(3628243259175483/62500000000000000),(663008666071467203/62500000000000000),(211315119221540813759/500000000000000000),(121754398260293829/62500000000000000)⟩,(248860287188808163/250000000000000000),(388201114637413487/1000000000000000000),(122234377181451721/500000000000000000),(149994462649090523/1000000000000000000)⟩
theorem valid406 : certificate406.Valid := by decide +kernel
theorem sound406 : certificate406.Sound := rat_cut_bin_certificate_sound certificate406 profilesValid406 numericValid406 valid406

def retention407 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(13777673887245052739/39735965222884822823),(729426604760793501/250000000000000000),(13/10),(415753491623115361929/320000000000000000000),true,MergedCutProfiles.Batch067.profile2719,![MergedCutProfiles.Batch067.profile2719,MergedCutProfiles.Batch068.profile2720,MergedCutProfiles.Batch068.profile2721,MergedCutProfiles.Batch068.profile2722,MergedCutProfiles.Batch068.profile2723,MergedCutProfiles.Batch068.profile2724,MergedCutProfiles.Batch068.profile2725,MergedCutProfiles.Batch068.profile2726,MergedCutProfiles.Batch068.profile2727,MergedCutProfiles.Batch068.profile2728,MergedCutProfiles.Batch068.profile2729,MergedCutProfiles.Batch068.profile2730,MergedCutProfiles.Batch068.profile2731,MergedCutProfiles.Batch068.profile2732,MergedCutProfiles.Batch068.profile2733,MergedCutProfiles.Batch068.profile2734]⟩
theorem profilesValid407 : retention407.ProfilesValid := by
  change ∀ j : Fin 16, (retention407.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch067.valid2719
  · exact MergedCutProfiles.Batch068.valid2720
  · exact MergedCutProfiles.Batch068.valid2721
  · exact MergedCutProfiles.Batch068.valid2722
  · exact MergedCutProfiles.Batch068.valid2723
  · exact MergedCutProfiles.Batch068.valid2724
  · exact MergedCutProfiles.Batch068.valid2725
  · exact MergedCutProfiles.Batch068.valid2726
  · exact MergedCutProfiles.Batch068.valid2727
  · exact MergedCutProfiles.Batch068.valid2728
  · exact MergedCutProfiles.Batch068.valid2729
  · exact MergedCutProfiles.Batch068.valid2730
  · exact MergedCutProfiles.Batch068.valid2731
  · exact MergedCutProfiles.Batch068.valid2732
  · exact MergedCutProfiles.Batch068.valid2733
  · exact MergedCutProfiles.Batch068.valid2734
theorem numericValid407 : retention407.NumericValid := by decide +kernel
def certificate407 : RatCutBinCertificate := ⟨⟨retention407,(2041151659260645091/1000000000000000000),(3628243259175483/62500000000000000),(663008666071467203/62500000000000000),(211315119221540813759/500000000000000000),(32117703977405059/25000000000000000)⟩,(248860287188808163/250000000000000000),(55896873725238079/125000000000000000),(192935909254857169/1000000000000000000),(150488898390268669/1000000000000000000)⟩
theorem valid407 : certificate407.Valid := by decide +kernel
theorem sound407 : certificate407.Sound := rat_cut_bin_certificate_sound certificate407 profilesValid407 numericValid407 valid407

def certificates : List RatCutBinCertificate := [certificate396,certificate397,certificate398,certificate399,certificate400,certificate401,certificate402,certificate403,certificate404,certificate405,certificate406,certificate407]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound396,List.forall_mem_cons.mpr ⟨sound397,List.forall_mem_cons.mpr ⟨sound398,List.forall_mem_cons.mpr ⟨sound399,List.forall_mem_cons.mpr ⟨sound400,List.forall_mem_cons.mpr ⟨sound401,List.forall_mem_cons.mpr ⟨sound402,List.forall_mem_cons.mpr ⟨sound403,List.forall_mem_cons.mpr ⟨sound404,List.forall_mem_cons.mpr ⟨sound405,List.forall_mem_cons.mpr ⟨sound406,List.forall_mem_cons.mpr ⟨sound407,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch033
