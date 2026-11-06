import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch063
import Cycle12.MergedCutProfiles.Batch064
import Cycle12.MergedCutProfiles.Batch065
import Cycle12.MergedCutProfiles.Batch066

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch032

def retention384 : RatCutRetentionCertificate := ⟨(139/4000),(7/200),(2619802048432497869/5282438719400437649),(20750907314316814803/1000000000000000000),1,(9198087366743086192672320168890787179/9222625473029695468000000000000000000),false,MergedCutProfiles.Batch063.profile2550,(fun _ => MergedCutProfiles.Batch063.profile2550)⟩
theorem profilesValid384 : retention384.ProfilesValid := by
  exact MergedCutProfiles.Batch063.valid2550
theorem numericValid384 : retention384.NumericValid := by decide +kernel
def certificate384 : RatCutBinCertificate := ⟨⟨retention384,(2023751653844675581/1000000000000000000),(853665110250683/15625000000000000),(5245761250897765603/500000000000000000),(221972292908710853387/500000000000000000),(246700153900909269/250000000000000000)⟩,(995685607421386069/1000000000000000000),(244575565135273497/500000000000000000),(161064757450619447/1000000000000000000),(75526238500932661/500000000000000000)⟩
theorem valid384 : certificate384.Valid := by decide +kernel
theorem sound384 : certificate384.Sound := rat_cut_bin_certificate_sound certificate384 profilesValid384 numericValid384 valid384

def retention385 : RatCutRetentionCertificate := ⟨(139/4000),(7/200),(1/2),(2619802048432497869/125000000000000000),1,(16591208812865404546206481075897142603/16766733109967986361600000000000000000),false,MergedCutProfiles.Batch063.profile2551,(fun _ => MergedCutProfiles.Batch063.profile2551)⟩
theorem profilesValid385 : retention385.ProfilesValid := by
  exact MergedCutProfiles.Batch063.valid2551
theorem numericValid385 : retention385.NumericValid := by decide +kernel
def certificate385 : RatCutBinCertificate := ⟨⟨retention385,(2023751653844675581/1000000000000000000),(853665110250683/15625000000000000),(5245761250897765603/500000000000000000),(221972292908710853387/500000000000000000),(195798530786200953/200000000000000000)⟩,(995685607421386069/1000000000000000000),(246443231606934323/500000000000000000),(39601979146181399/250000000000000000),(73752111710242663/500000000000000000)⟩
theorem valid385 : certificate385.Valid := by decide +kernel
theorem sound385 : certificate385.Sound := rat_cut_bin_certificate_sound certificate385 profilesValid385 numericValid385 valid385

def retention386 : RatCutRetentionCertificate := ⟨(139/4000),(7/200),(18074379570209746313/42259509755203501192),(3789725155809587821/1000000000000000000),(5/4),(277695292930007691996047890538392741951/242542409971813620544000000000000000000),false,MergedCutProfiles.Batch063.profile2552,(fun _ => MergedCutProfiles.Batch063.profile2552)⟩
theorem profilesValid386 : retention386.ProfilesValid := by
  exact MergedCutProfiles.Batch063.valid2552
theorem numericValid386 : retention386.NumericValid := by decide +kernel
def certificate386 : RatCutBinCertificate := ⟨⟨retention386,(2415616985844675581/1000000000000000000),(853665110250683/15625000000000000),(5245761250897765603/500000000000000000),(221972292908710853387/500000000000000000),(564605220039448753/500000000000000000)⟩,(994849953545382419/1000000000000000000),(351955002474162847/1000000000000000000),(280509803119512011/1000000000000000000),(211633758420199923/1000000000000000000)⟩
theorem valid386 : certificate386.Valid := by decide +kernel
theorem sound386 : certificate386.Sound := rat_cut_bin_certificate_sound certificate386 profilesValid386 numericValid386 valid386

def retention387 : RatCutRetentionCertificate := ⟨(139/4000),(7/200),(2622974196073406535/5282438719400437649),(18074379570209746313/1000000000000000000),1,(2246533857033744655023696959488756593/2259297446276218289125000000000000000),false,MergedCutProfiles.Batch063.profile2553,(fun _ => MergedCutProfiles.Batch063.profile2553)⟩
theorem profilesValid387 : retention387.ProfilesValid := by
  exact MergedCutProfiles.Batch063.valid2553
theorem numericValid387 : retention387.NumericValid := by decide +kernel
def certificate387 : RatCutBinCertificate := ⟨⟨retention387,(2415616985844675581/1000000000000000000),(853665110250683/15625000000000000),(5245761250897765603/500000000000000000),(221972292908710853387/500000000000000000),(981771235224197719/1000000000000000000)⟩,(994849953545382419/1000000000000000000),(80962091569338209/200000000000000000),(114551789184590487/500000000000000000),(106106888397984009/500000000000000000)⟩
theorem valid387 : certificate387.Valid := by decide +kernel
theorem sound387 : certificate387.Sound := rat_cut_bin_certificate_sound certificate387 profilesValid387 numericValid387 valid387

def retention388 : RatCutRetentionCertificate := ⟨(139/4000),(7/200),(1/2),(524594839214681307/25000000000000000),1,(3322308183731123053570700072174883023/3357406970973960364800000000000000000),false,MergedCutProfiles.Batch063.profile2551,(fun _ => MergedCutProfiles.Batch063.profile2551)⟩
theorem profilesValid388 : retention388.ProfilesValid := by
  exact MergedCutProfiles.Batch063.valid2551
theorem numericValid388 : retention388.NumericValid := by decide +kernel
def certificate388 : RatCutBinCertificate := ⟨⟨retention388,(2415616985844675581/1000000000000000000),(853665110250683/15625000000000000),(5245761250897765603/500000000000000000),(221972292908710853387/500000000000000000),(976966473693012441/1000000000000000000)⟩,(994849953545382419/1000000000000000000),(406801332423922909/1000000000000000000),(1775844642842761/7812500000000000),(211077340893618269/1000000000000000000)⟩
theorem valid388 : certificate388.Valid := by decide +kernel
theorem sound388 : certificate388.Sound := rat_cut_bin_certificate_sound certificate388 profilesValid388 numericValid388 valid388

def retention389 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(765429620382317009/40970350049210168724),(757851109289422781/1000000000000000000),(17/5),(175502934824588651473/80000000000000000000),true,MergedCutProfiles.Batch063.profile2554,![MergedCutProfiles.Batch063.profile2554,MergedCutProfiles.Batch063.profile2555,MergedCutProfiles.Batch063.profile2556,MergedCutProfiles.Batch063.profile2557,MergedCutProfiles.Batch063.profile2558,MergedCutProfiles.Batch063.profile2559,MergedCutProfiles.Batch064.profile2560,MergedCutProfiles.Batch064.profile2561,MergedCutProfiles.Batch064.profile2562,MergedCutProfiles.Batch064.profile2563,MergedCutProfiles.Batch064.profile2564,MergedCutProfiles.Batch064.profile2565,MergedCutProfiles.Batch064.profile2566,MergedCutProfiles.Batch064.profile2567,MergedCutProfiles.Batch064.profile2568,MergedCutProfiles.Batch064.profile2569]⟩
theorem profilesValid389 : retention389.ProfilesValid := by
  change ∀ j : Fin 16, (retention389.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch063.valid2554
  · exact MergedCutProfiles.Batch063.valid2555
  · exact MergedCutProfiles.Batch063.valid2556
  · exact MergedCutProfiles.Batch063.valid2557
  · exact MergedCutProfiles.Batch063.valid2558
  · exact MergedCutProfiles.Batch063.valid2559
  · exact MergedCutProfiles.Batch064.valid2560
  · exact MergedCutProfiles.Batch064.valid2561
  · exact MergedCutProfiles.Batch064.valid2562
  · exact MergedCutProfiles.Batch064.valid2563
  · exact MergedCutProfiles.Batch064.valid2564
  · exact MergedCutProfiles.Batch064.valid2565
  · exact MergedCutProfiles.Batch064.valid2566
  · exact MergedCutProfiles.Batch064.valid2567
  · exact MergedCutProfiles.Batch064.valid2568
  · exact MergedCutProfiles.Batch064.valid2569
theorem numericValid389 : retention389.NumericValid := by decide +kernel
def certificate389 : RatCutBinCertificate := ⟨⟨retention389,(1018656151474196381/500000000000000000),(14082027828820247/250000000000000000),(10530164287713757123/1000000000000000000),(54069082130495480293/125000000000000000),(539182885108121977/250000000000000000)⟩,(995546191717510047/1000000000000000000),(209161935821933589/500000000000000000),(217106386990046983/1000000000000000000),(109935645171802227/1000000000000000000)⟩
theorem valid389 : certificate389.Valid := by decide +kernel
theorem sound389 : certificate389.Sound := rat_cut_bin_certificate_sound certificate389 profilesValid389 numericValid389 valid389

def retention390 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(32586726321397621/1517420372192969212),(765429620382317009/1000000000000000000),(67/20),(2787611017185541670561/1280000000000000000000),true,MergedCutProfiles.Batch064.profile2570,![MergedCutProfiles.Batch064.profile2570,MergedCutProfiles.Batch064.profile2571,MergedCutProfiles.Batch064.profile2572,MergedCutProfiles.Batch064.profile2573,MergedCutProfiles.Batch064.profile2574,MergedCutProfiles.Batch064.profile2575,MergedCutProfiles.Batch064.profile2576,MergedCutProfiles.Batch064.profile2577,MergedCutProfiles.Batch064.profile2578,MergedCutProfiles.Batch064.profile2579,MergedCutProfiles.Batch064.profile2580,MergedCutProfiles.Batch064.profile2581,MergedCutProfiles.Batch064.profile2582,MergedCutProfiles.Batch064.profile2583,MergedCutProfiles.Batch064.profile2584,MergedCutProfiles.Batch064.profile2585]⟩
theorem profilesValid390 : retention390.ProfilesValid := by
  change ∀ j : Fin 16, (retention390.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch064.valid2570
  · exact MergedCutProfiles.Batch064.valid2571
  · exact MergedCutProfiles.Batch064.valid2572
  · exact MergedCutProfiles.Batch064.valid2573
  · exact MergedCutProfiles.Batch064.valid2574
  · exact MergedCutProfiles.Batch064.valid2575
  · exact MergedCutProfiles.Batch064.valid2576
  · exact MergedCutProfiles.Batch064.valid2577
  · exact MergedCutProfiles.Batch064.valid2578
  · exact MergedCutProfiles.Batch064.valid2579
  · exact MergedCutProfiles.Batch064.valid2580
  · exact MergedCutProfiles.Batch064.valid2581
  · exact MergedCutProfiles.Batch064.valid2582
  · exact MergedCutProfiles.Batch064.valid2583
  · exact MergedCutProfiles.Batch064.valid2584
  · exact MergedCutProfiles.Batch064.valid2585
theorem numericValid390 : retention390.NumericValid := by decide +kernel
def certificate390 : RatCutBinCertificate := ⟨⟨retention390,(1018656151474196381/500000000000000000),(14082027828820247/250000000000000000),(10530164287713757123/1000000000000000000),(54069082130495480293/125000000000000000),(1070655440952345759/500000000000000000)⟩,(995546191717510047/1000000000000000000),(419294954966180531/1000000000000000000),(108130618790891849/500000000000000000),(110073655517393433/1000000000000000000)⟩
theorem valid390 : certificate390.Valid := by decide +kernel
theorem sound390 : certificate390.Sound := rat_cut_bin_certificate_sound certificate390 profilesValid390 numericValid390 valid390

def retention391 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(242413618750000000/10242587512302542181),(879841610677735767/1000000000000000000),3,(554227240651940155439/256000000000000000000),true,MergedCutProfiles.Batch064.profile2586,![MergedCutProfiles.Batch064.profile2586,MergedCutProfiles.Batch064.profile2587,MergedCutProfiles.Batch064.profile2588,MergedCutProfiles.Batch064.profile2589,MergedCutProfiles.Batch064.profile2590,MergedCutProfiles.Batch064.profile2591,MergedCutProfiles.Batch064.profile2592,MergedCutProfiles.Batch064.profile2593,MergedCutProfiles.Batch064.profile2594,MergedCutProfiles.Batch064.profile2595,MergedCutProfiles.Batch064.profile2567,MergedCutProfiles.Batch064.profile2596,MergedCutProfiles.Batch064.profile2597,MergedCutProfiles.Batch064.profile2598,MergedCutProfiles.Batch064.profile2599,MergedCutProfiles.Batch065.profile2600]⟩
theorem profilesValid391 : retention391.ProfilesValid := by
  change ∀ j : Fin 16, (retention391.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch064.valid2586
  · exact MergedCutProfiles.Batch064.valid2587
  · exact MergedCutProfiles.Batch064.valid2588
  · exact MergedCutProfiles.Batch064.valid2589
  · exact MergedCutProfiles.Batch064.valid2590
  · exact MergedCutProfiles.Batch064.valid2591
  · exact MergedCutProfiles.Batch064.valid2592
  · exact MergedCutProfiles.Batch064.valid2593
  · exact MergedCutProfiles.Batch064.valid2594
  · exact MergedCutProfiles.Batch064.valid2595
  · exact MergedCutProfiles.Batch064.valid2567
  · exact MergedCutProfiles.Batch064.valid2596
  · exact MergedCutProfiles.Batch064.valid2597
  · exact MergedCutProfiles.Batch064.valid2598
  · exact MergedCutProfiles.Batch064.valid2599
  · exact MergedCutProfiles.Batch065.valid2600
theorem numericValid391 : retention391.NumericValid := by decide +kernel
def certificate391 : RatCutBinCertificate := ⟨⟨retention391,(1018656151474196381/500000000000000000),(14082027828820247/250000000000000000),(10530164287713757123/1000000000000000000),(54069082130495480293/125000000000000000),(213225448206211829/100000000000000000)⟩,(995546191717510047/1000000000000000000),(24651019948525521/62500000000000000),(238637545888222217/1000000000000000000),(16617103218354753/125000000000000000)⟩
theorem valid391 : certificate391.Valid := by decide +kernel
theorem sound391 : certificate391.Sound := rat_cut_bin_certificate_sound certificate391 profilesValid391 numericValid391 valid391

def retention392 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(981611435112178597/40970350049210168724),(38786179/40000000),(11/4),(34479451795449588137/16000000000000000000),true,MergedCutProfiles.Batch065.profile2601,![MergedCutProfiles.Batch065.profile2601,MergedCutProfiles.Batch065.profile2602,MergedCutProfiles.Batch065.profile2603,MergedCutProfiles.Batch065.profile2604,MergedCutProfiles.Batch065.profile2605,MergedCutProfiles.Batch065.profile2606,MergedCutProfiles.Batch064.profile2562,MergedCutProfiles.Batch065.profile2607,MergedCutProfiles.Batch064.profile2579,MergedCutProfiles.Batch065.profile2608,MergedCutProfiles.Batch065.profile2609,MergedCutProfiles.Batch065.profile2610,MergedCutProfiles.Batch065.profile2611,MergedCutProfiles.Batch065.profile2612,MergedCutProfiles.Batch065.profile2613,MergedCutProfiles.Batch065.profile2614]⟩
theorem profilesValid392 : retention392.ProfilesValid := by
  change ∀ j : Fin 16, (retention392.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch065.valid2601
  · exact MergedCutProfiles.Batch065.valid2602
  · exact MergedCutProfiles.Batch065.valid2603
  · exact MergedCutProfiles.Batch065.valid2604
  · exact MergedCutProfiles.Batch065.valid2605
  · exact MergedCutProfiles.Batch065.valid2606
  · exact MergedCutProfiles.Batch064.valid2562
  · exact MergedCutProfiles.Batch065.valid2607
  · exact MergedCutProfiles.Batch064.valid2579
  · exact MergedCutProfiles.Batch065.valid2608
  · exact MergedCutProfiles.Batch065.valid2609
  · exact MergedCutProfiles.Batch065.valid2610
  · exact MergedCutProfiles.Batch065.valid2611
  · exact MergedCutProfiles.Batch065.valid2612
  · exact MergedCutProfiles.Batch065.valid2613
  · exact MergedCutProfiles.Batch065.valid2614
theorem numericValid392 : retention392.NumericValid := by decide +kernel
def certificate392 : RatCutBinCertificate := ⟨⟨retention392,(1018656151474196381/500000000000000000),(14082027828820247/250000000000000000),(10530164287713757123/1000000000000000000),(54069082130495480293/125000000000000000),(2124994715193940763/1000000000000000000)⟩,(995546191717510047/1000000000000000000),(5924803826552489/15625000000000000),(253102652547861409/1000000000000000000),(3017077569570943/20000000000000000)⟩
theorem valid392 : certificate392.Valid := by decide +kernel
theorem sound392 : certificate392.Sound := rat_cut_bin_certificate_sound certificate392 profilesValid392 numericValid392 valid392

def retention393 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(1139620402401431093/40970350049210168724),(981611435112178597/1000000000000000000),(27/10),(2731922466204861443321/1280000000000000000000),true,MergedCutProfiles.Batch065.profile2615,![MergedCutProfiles.Batch065.profile2615,MergedCutProfiles.Batch065.profile2616,MergedCutProfiles.Batch065.profile2617,MergedCutProfiles.Batch065.profile2618,MergedCutProfiles.Batch065.profile2619,MergedCutProfiles.Batch064.profile2562,MergedCutProfiles.Batch064.profile2578,MergedCutProfiles.Batch065.profile2620,MergedCutProfiles.Batch065.profile2621,MergedCutProfiles.Batch064.profile2582,MergedCutProfiles.Batch064.profile2597,MergedCutProfiles.Batch065.profile2622,MergedCutProfiles.Batch065.profile2623,MergedCutProfiles.Batch065.profile2624,MergedCutProfiles.Batch065.profile2625,MergedCutProfiles.Batch065.profile2626]⟩
theorem profilesValid393 : retention393.ProfilesValid := by
  change ∀ j : Fin 16, (retention393.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch065.valid2615
  · exact MergedCutProfiles.Batch065.valid2616
  · exact MergedCutProfiles.Batch065.valid2617
  · exact MergedCutProfiles.Batch065.valid2618
  · exact MergedCutProfiles.Batch065.valid2619
  · exact MergedCutProfiles.Batch064.valid2562
  · exact MergedCutProfiles.Batch064.valid2578
  · exact MergedCutProfiles.Batch065.valid2620
  · exact MergedCutProfiles.Batch065.valid2621
  · exact MergedCutProfiles.Batch064.valid2582
  · exact MergedCutProfiles.Batch064.valid2597
  · exact MergedCutProfiles.Batch065.valid2622
  · exact MergedCutProfiles.Batch065.valid2623
  · exact MergedCutProfiles.Batch065.valid2624
  · exact MergedCutProfiles.Batch065.valid2625
  · exact MergedCutProfiles.Batch065.valid2626
theorem numericValid393 : retention393.NumericValid := by decide +kernel
def certificate393 : RatCutBinCertificate := ⟨⟨retention393,(1018656151474196381/500000000000000000),(14082027828820247/250000000000000000),(10530164287713757123/1000000000000000000),(54069082130495480293/125000000000000000),(16444440028056661/7812500000000000)⟩,(995546191717510047/1000000000000000000),(380812594494009977/1000000000000000000),(251530299592730893/1000000000000000000),(37684570860982421/250000000000000000)⟩
theorem valid393 : certificate393.Valid := by decide +kernel
theorem sound393 : certificate393.Sound := rat_cut_bin_certificate_sound certificate393 profilesValid393 numericValid393 valid393

def retention394 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(3113285634953378597/40970350049210168724),(1139620402401431093/1000000000000000000),(12/5),(2514657546928571137881/1280000000000000000000),true,MergedCutProfiles.Batch065.profile2627,![MergedCutProfiles.Batch065.profile2627,MergedCutProfiles.Batch065.profile2628,MergedCutProfiles.Batch065.profile2629,MergedCutProfiles.Batch065.profile2630,MergedCutProfiles.Batch065.profile2600,MergedCutProfiles.Batch065.profile2631,MergedCutProfiles.Batch065.profile2632,MergedCutProfiles.Batch065.profile2633,MergedCutProfiles.Batch065.profile2634,MergedCutProfiles.Batch065.profile2635,MergedCutProfiles.Batch065.profile2636,MergedCutProfiles.Batch065.profile2637,MergedCutProfiles.Batch065.profile2638,MergedCutProfiles.Batch065.profile2639,MergedCutProfiles.Batch066.profile2640,MergedCutProfiles.Batch066.profile2641]⟩
theorem profilesValid394 : retention394.ProfilesValid := by
  change ∀ j : Fin 16, (retention394.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch065.valid2627
  · exact MergedCutProfiles.Batch065.valid2628
  · exact MergedCutProfiles.Batch065.valid2629
  · exact MergedCutProfiles.Batch065.valid2630
  · exact MergedCutProfiles.Batch065.valid2600
  · exact MergedCutProfiles.Batch065.valid2631
  · exact MergedCutProfiles.Batch065.valid2632
  · exact MergedCutProfiles.Batch065.valid2633
  · exact MergedCutProfiles.Batch065.valid2634
  · exact MergedCutProfiles.Batch065.valid2635
  · exact MergedCutProfiles.Batch065.valid2636
  · exact MergedCutProfiles.Batch065.valid2637
  · exact MergedCutProfiles.Batch065.valid2638
  · exact MergedCutProfiles.Batch065.valid2639
  · exact MergedCutProfiles.Batch066.valid2640
  · exact MergedCutProfiles.Batch066.valid2641
theorem numericValid394 : retention394.NumericValid := by decide +kernel
def certificate394 : RatCutBinCertificate := ⟨⟨retention394,(1018656151474196381/500000000000000000),(14082027828820247/250000000000000000),(10530164287713757123/1000000000000000000),(54069082130495480293/125000000000000000),(1938419712236442951/1000000000000000000)⟩,(995546191717510047/1000000000000000000),(12160454093204899/31250000000000000),(243586700065729827/1000000000000000000),(75552752586831479/500000000000000000)⟩
theorem valid394 : certificate394.Valid := by decide +kernel
theorem sound394 : certificate394.Sound := rat_cut_bin_certificate_sound certificate394 profilesValid394 numericValid394 valid394

def retention395 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(2425943342080892861/6828391674868361454),(3113285634953378597/1000000000000000000),(13/10),(1602447376283121923200631361897532917519/1245314253981351438800000000000000000000),false,MergedCutProfiles.Batch066.profile2642,(fun _ => MergedCutProfiles.Batch066.profile2642)⟩
theorem profilesValid395 : retention395.ProfilesValid := by
  exact MergedCutProfiles.Batch066.valid2642
theorem numericValid395 : retention395.NumericValid := by decide +kernel
def certificate395 : RatCutBinCertificate := ⟨⟨retention395,(1018656151474196381/500000000000000000),(14082027828820247/250000000000000000),(10530164287713757123/1000000000000000000),(54069082130495480293/125000000000000000),(79538352668000821/62500000000000000)⟩,(995546191717510047/1000000000000000000),(446461354899629241/1000000000000000000),(2418885111912781/12500000000000000),(30357090166131689/200000000000000000)⟩
theorem valid395 : certificate395.Valid := by decide +kernel
theorem sound395 : certificate395.Sound := rat_cut_bin_certificate_sound certificate395 profilesValid395 numericValid395 valid395

def certificates : List RatCutBinCertificate := [certificate384,certificate385,certificate386,certificate387,certificate388,certificate389,certificate390,certificate391,certificate392,certificate393,certificate394,certificate395]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound384,List.forall_mem_cons.mpr ⟨sound385,List.forall_mem_cons.mpr ⟨sound386,List.forall_mem_cons.mpr ⟨sound387,List.forall_mem_cons.mpr ⟨sound388,List.forall_mem_cons.mpr ⟨sound389,List.forall_mem_cons.mpr ⟨sound390,List.forall_mem_cons.mpr ⟨sound391,List.forall_mem_cons.mpr ⟨sound392,List.forall_mem_cons.mpr ⟨sound393,List.forall_mem_cons.mpr ⟨sound394,List.forall_mem_cons.mpr ⟨sound395,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch032
