import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch412
import Cycle12.MergedCutProfiles.Batch413
import Cycle12.MergedCutProfiles.Batch414

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch219

def retention2628 : RatCutRetentionCertificate := ⟨(31/500),(1/16),(195388449800000000/4532740045392556597),(939338018005505913/1000000000000000000),(13/5),(106061588869200917981/51200000000000000000),true,MergedCutProfiles.Batch412.profile16499,![MergedCutProfiles.Batch412.profile16499,MergedCutProfiles.Batch412.profile16500,MergedCutProfiles.Batch412.profile16501,MergedCutProfiles.Batch412.profile16502,MergedCutProfiles.Batch412.profile16503,MergedCutProfiles.Batch412.profile16504,MergedCutProfiles.Batch412.profile16505,MergedCutProfiles.Batch412.profile16506,MergedCutProfiles.Batch412.profile16507,MergedCutProfiles.Batch412.profile16508,MergedCutProfiles.Batch412.profile16509,MergedCutProfiles.Batch412.profile16510,MergedCutProfiles.Batch412.profile16511,MergedCutProfiles.Batch412.profile16512,MergedCutProfiles.Batch412.profile16513,MergedCutProfiles.Batch412.profile16514]⟩
theorem profilesValid2628 : retention2628.ProfilesValid := by
  change ∀ j : Fin 16, (retention2628.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch412.valid16499
  · exact MergedCutProfiles.Batch412.valid16500
  · exact MergedCutProfiles.Batch412.valid16501
  · exact MergedCutProfiles.Batch412.valid16502
  · exact MergedCutProfiles.Batch412.valid16503
  · exact MergedCutProfiles.Batch412.valid16504
  · exact MergedCutProfiles.Batch412.valid16505
  · exact MergedCutProfiles.Batch412.valid16506
  · exact MergedCutProfiles.Batch412.valid16507
  · exact MergedCutProfiles.Batch412.valid16508
  · exact MergedCutProfiles.Batch412.valid16509
  · exact MergedCutProfiles.Batch412.valid16510
  · exact MergedCutProfiles.Batch412.valid16511
  · exact MergedCutProfiles.Batch412.valid16512
  · exact MergedCutProfiles.Batch412.valid16513
  · exact MergedCutProfiles.Batch412.valid16514
theorem numericValid2628 : retention2628.NumericValid := by decide +kernel
def certificate2628 : RatCutBinCertificate := ⟨⟨retention2628,(2300964834594250959/1000000000000000000),(50258241146397749/250000000000000000),(2057940274574033059/125000000000000000),(374284969214866128027/1000000000000000000),(999224029055956349/500000000000000000)⟩,(497529304158783303/500000000000000000),(11764861780570907/40000000000000000),(172958358918709597/500000000000000000),(201034633757186403/1000000000000000000)⟩
theorem valid2628 : certificate2628.Valid := by decide +kernel
theorem sound2628 : certificate2628.Sound := rat_cut_bin_certificate_sound certificate2628 profilesValid2628 numericValid2628 valid2628

def retention2629 : RatCutRetentionCertificate := ⟨(31/500),(1/16),(1017168471648652324/22663700226962782985),(976942249/1000000000),(51/20),(8285410678094473359/4000000000000000000),true,MergedCutProfiles.Batch412.profile16515,![MergedCutProfiles.Batch412.profile16515,MergedCutProfiles.Batch412.profile16516,MergedCutProfiles.Batch412.profile16517,MergedCutProfiles.Batch412.profile16518,MergedCutProfiles.Batch412.profile16519,MergedCutProfiles.Batch413.profile16520,MergedCutProfiles.Batch413.profile16521,MergedCutProfiles.Batch413.profile16522,MergedCutProfiles.Batch413.profile16523,MergedCutProfiles.Batch413.profile16524,MergedCutProfiles.Batch413.profile16525,MergedCutProfiles.Batch412.profile16495,MergedCutProfiles.Batch413.profile16526,MergedCutProfiles.Batch413.profile16527,MergedCutProfiles.Batch413.profile16528,MergedCutProfiles.Batch413.profile16529]⟩
theorem profilesValid2629 : retention2629.ProfilesValid := by
  change ∀ j : Fin 16, (retention2629.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch412.valid16515
  · exact MergedCutProfiles.Batch412.valid16516
  · exact MergedCutProfiles.Batch412.valid16517
  · exact MergedCutProfiles.Batch412.valid16518
  · exact MergedCutProfiles.Batch412.valid16519
  · exact MergedCutProfiles.Batch413.valid16520
  · exact MergedCutProfiles.Batch413.valid16521
  · exact MergedCutProfiles.Batch413.valid16522
  · exact MergedCutProfiles.Batch413.valid16523
  · exact MergedCutProfiles.Batch413.valid16524
  · exact MergedCutProfiles.Batch413.valid16525
  · exact MergedCutProfiles.Batch412.valid16495
  · exact MergedCutProfiles.Batch413.valid16526
  · exact MergedCutProfiles.Batch413.valid16527
  · exact MergedCutProfiles.Batch413.valid16528
  · exact MergedCutProfiles.Batch413.valid16529
theorem numericValid2629 : retention2629.NumericValid := by decide +kernel
def certificate2629 : RatCutBinCertificate := ⟨⟨retention2629,(2300964834594250959/1000000000000000000),(50258241146397749/250000000000000000),(2057940274574033059/125000000000000000),(374284969214866128027/1000000000000000000),(1999690770810125053/1000000000000000000)⟩,(497529304158783303/500000000000000000),(289478137127969877/1000000000000000000),(351632463527428797/1000000000000000000),(52121707676103929/250000000000000000)⟩
theorem valid2629 : certificate2629.Valid := by decide +kernel
theorem sound2629 : certificate2629.Sound := rat_cut_bin_certificate_sound certificate2629 profilesValid2629 numericValid2629 valid2629

def retention2630 : RatCutRetentionCertificate := ⟨(31/500),(1/16),(73607700452054579/1192826327734883315),(254292117912163081/250000000000000000),(49/20),(645437856835826176633/320000000000000000000),true,MergedCutProfiles.Batch413.profile16530,![MergedCutProfiles.Batch413.profile16530,MergedCutProfiles.Batch413.profile16531,MergedCutProfiles.Batch413.profile16532,MergedCutProfiles.Batch413.profile16533,MergedCutProfiles.Batch413.profile16534,MergedCutProfiles.Batch413.profile16535,MergedCutProfiles.Batch412.profile16508,MergedCutProfiles.Batch413.profile16525,MergedCutProfiles.Batch413.profile16536,MergedCutProfiles.Batch413.profile16537,MergedCutProfiles.Batch413.profile16538,MergedCutProfiles.Batch413.profile16539,MergedCutProfiles.Batch413.profile16540,MergedCutProfiles.Batch413.profile16541,MergedCutProfiles.Batch413.profile16542,MergedCutProfiles.Batch413.profile16543]⟩
theorem profilesValid2630 : retention2630.ProfilesValid := by
  change ∀ j : Fin 16, (retention2630.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch413.valid16530
  · exact MergedCutProfiles.Batch413.valid16531
  · exact MergedCutProfiles.Batch413.valid16532
  · exact MergedCutProfiles.Batch413.valid16533
  · exact MergedCutProfiles.Batch413.valid16534
  · exact MergedCutProfiles.Batch413.valid16535
  · exact MergedCutProfiles.Batch412.valid16508
  · exact MergedCutProfiles.Batch413.valid16525
  · exact MergedCutProfiles.Batch413.valid16536
  · exact MergedCutProfiles.Batch413.valid16537
  · exact MergedCutProfiles.Batch413.valid16538
  · exact MergedCutProfiles.Batch413.valid16539
  · exact MergedCutProfiles.Batch413.valid16540
  · exact MergedCutProfiles.Batch413.valid16541
  · exact MergedCutProfiles.Batch413.valid16542
  · exact MergedCutProfiles.Batch413.valid16543
theorem numericValid2630 : retention2630.NumericValid := by decide +kernel
def certificate2630 : RatCutBinCertificate := ⟨⟨retention2630,(2300964834594250959/1000000000000000000),(50258241146397749/250000000000000000),(2057940274574033059/125000000000000000),(374284969214866128027/1000000000000000000),(1948141679558090799/1000000000000000000)⟩,(497529304158783303/500000000000000000),(146307390593182597/500000000000000000),(43470425548800903/125000000000000000),(208396952163887183/1000000000000000000)⟩
theorem valid2630 : certificate2630.Valid := by decide +kernel
theorem sound2630 : certificate2630.Sound := rat_cut_bin_certificate_sound certificate2630 profilesValid2630 numericValid2630 valid2630

def retention2631 : RatCutRetentionCertificate := ⟨(31/500),(1/16),(236207428075816514/1333158836880163705),(1398546308589037001/1000000000000000000),(19/10),(2161536180679591007077/1280000000000000000000),true,MergedCutProfiles.Batch413.profile16544,![MergedCutProfiles.Batch413.profile16544,MergedCutProfiles.Batch413.profile16545,MergedCutProfiles.Batch413.profile16546,MergedCutProfiles.Batch413.profile16547,MergedCutProfiles.Batch413.profile16548,MergedCutProfiles.Batch413.profile16549,MergedCutProfiles.Batch413.profile16550,MergedCutProfiles.Batch413.profile16551,MergedCutProfiles.Batch413.profile16552,MergedCutProfiles.Batch413.profile16553,MergedCutProfiles.Batch413.profile16554,MergedCutProfiles.Batch413.profile16555,MergedCutProfiles.Batch413.profile16556,MergedCutProfiles.Batch413.profile16557,MergedCutProfiles.Batch413.profile16558,MergedCutProfiles.Batch413.profile16559]⟩
theorem profilesValid2631 : retention2631.ProfilesValid := by
  change ∀ j : Fin 16, (retention2631.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch413.valid16544
  · exact MergedCutProfiles.Batch413.valid16545
  · exact MergedCutProfiles.Batch413.valid16546
  · exact MergedCutProfiles.Batch413.valid16547
  · exact MergedCutProfiles.Batch413.valid16548
  · exact MergedCutProfiles.Batch413.valid16549
  · exact MergedCutProfiles.Batch413.valid16550
  · exact MergedCutProfiles.Batch413.valid16551
  · exact MergedCutProfiles.Batch413.valid16552
  · exact MergedCutProfiles.Batch413.valid16553
  · exact MergedCutProfiles.Batch413.valid16554
  · exact MergedCutProfiles.Batch413.valid16555
  · exact MergedCutProfiles.Batch413.valid16556
  · exact MergedCutProfiles.Batch413.valid16557
  · exact MergedCutProfiles.Batch413.valid16558
  · exact MergedCutProfiles.Batch413.valid16559
theorem numericValid2631 : retention2631.NumericValid := by decide +kernel
def certificate2631 : RatCutBinCertificate := ⟨⟨retention2631,(2300964834594250959/1000000000000000000),(50258241146397749/250000000000000000),(2057940274574033059/125000000000000000),(374284969214866128027/1000000000000000000),(817652860055849493/500000000000000000)⟩,(497529304158783303/500000000000000000),(312906218770816339/1000000000000000000),(323526891361909121/1000000000000000000),(8363934925973867/40000000000000000)⟩
theorem valid2631 : certificate2631.Valid := by decide +kernel
theorem sound2631 : certificate2631.Sound := rat_cut_bin_certificate_sound certificate2631 profilesValid2631 numericValid2631 valid2631

def retention2632 : RatCutRetentionCertificate := ⟨(31/500),(1/16),(9543375041351143926/22663700226962782985),(2007763138644440369/500000000000000000),(11/10),(723164533261862300597/640000000000000000000),true,MergedCutProfiles.Batch414.profile16560,![MergedCutProfiles.Batch414.profile16560,MergedCutProfiles.Batch414.profile16561,MergedCutProfiles.Batch414.profile16562,MergedCutProfiles.Batch414.profile16563,MergedCutProfiles.Batch414.profile16564,MergedCutProfiles.Batch414.profile16565,MergedCutProfiles.Batch414.profile16566,MergedCutProfiles.Batch414.profile16567,MergedCutProfiles.Batch414.profile16568,MergedCutProfiles.Batch414.profile16569,MergedCutProfiles.Batch414.profile16570,MergedCutProfiles.Batch414.profile16571,MergedCutProfiles.Batch414.profile16572,MergedCutProfiles.Batch414.profile16573,MergedCutProfiles.Batch414.profile16574,MergedCutProfiles.Batch414.profile16575]⟩
theorem profilesValid2632 : retention2632.ProfilesValid := by
  change ∀ j : Fin 16, (retention2632.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch414.valid16560
  · exact MergedCutProfiles.Batch414.valid16561
  · exact MergedCutProfiles.Batch414.valid16562
  · exact MergedCutProfiles.Batch414.valid16563
  · exact MergedCutProfiles.Batch414.valid16564
  · exact MergedCutProfiles.Batch414.valid16565
  · exact MergedCutProfiles.Batch414.valid16566
  · exact MergedCutProfiles.Batch414.valid16567
  · exact MergedCutProfiles.Batch414.valid16568
  · exact MergedCutProfiles.Batch414.valid16569
  · exact MergedCutProfiles.Batch414.valid16570
  · exact MergedCutProfiles.Batch414.valid16571
  · exact MergedCutProfiles.Batch414.valid16572
  · exact MergedCutProfiles.Batch414.valid16573
  · exact MergedCutProfiles.Batch414.valid16574
  · exact MergedCutProfiles.Batch414.valid16575
theorem numericValid2632 : retention2632.NumericValid := by decide +kernel
def certificate2632 : RatCutBinCertificate := ⟨⟨retention2632,(2300964834594250959/1000000000000000000),(50258241146397749/250000000000000000),(2057940274574033059/125000000000000000),(374284969214866128027/1000000000000000000),(549517256320499593/500000000000000000)⟩,(497529304158783303/500000000000000000),(373292153852374013/1000000000000000000),(129432528134379167/500000000000000000),(20976006900617393/100000000000000000)⟩
theorem valid2632 : certificate2632.Valid := by decide +kernel
theorem sound2632 : certificate2632.Sound := rat_cut_bin_certificate_sound certificate2632 profilesValid2632 numericValid2632 valid2632

def retention2633 : RatCutRetentionCertificate := ⟨(31/500),(1/16),(11079562152461554147/22663700226962782985),(4771687520675571963/500000000000000000),(21/20),(3878899885574629404256683142001745471191/3817350016540457570400000000000000000000),false,MergedCutProfiles.Batch414.profile16576,(fun _ => MergedCutProfiles.Batch414.profile16576)⟩
theorem profilesValid2633 : retention2633.ProfilesValid := by
  exact MergedCutProfiles.Batch414.valid16576
theorem numericValid2633 : retention2633.NumericValid := by decide +kernel
def certificate2633 : RatCutBinCertificate := ⟨⟨retention2633,(2300964834594250959/1000000000000000000),(50258241146397749/250000000000000000),(2057940274574033059/125000000000000000),(374284969214866128027/1000000000000000000),(986620655055979577/1000000000000000000)⟩,(497529304158783303/500000000000000000),(383999001480483647/1000000000000000000),(62116874494973167/250000000000000000),(26542083524956687/125000000000000000)⟩
theorem valid2633 : certificate2633.Valid := by decide +kernel
theorem sound2633 : certificate2633.Sound := rat_cut_bin_certificate_sound certificate2633 profilesValid2633 numericValid2633 valid2633

def retention2634 : RatCutRetentionCertificate := ⟨(31/500),(1/16),(11302261351726031386/22663700226962782985),(11079562152461554147/1000000000000000000),(21/20),(17721287938158068964896746907129411787671/17727299443938486635200000000000000000000),false,MergedCutProfiles.Batch414.profile16577,(fun _ => MergedCutProfiles.Batch414.profile16577)⟩
theorem profilesValid2634 : retention2634.ProfilesValid := by
  exact MergedCutProfiles.Batch414.valid16577
theorem numericValid2634 : retention2634.NumericValid := by decide +kernel
def certificate2634 : RatCutBinCertificate := ⟨⟨retention2634,(2300964834594250959/1000000000000000000),(50258241146397749/250000000000000000),(2057940274574033059/125000000000000000),(374284969214866128027/1000000000000000000),(970158047842621381/1000000000000000000)⟩,(497529304158783303/500000000000000000),(96813822105416471/250000000000000000),(3067060294704439/12500000000000000),(208935112620265811/1000000000000000000)⟩
theorem valid2634 : certificate2634.Valid := by decide +kernel
theorem sound2634 : certificate2634.Sound := rat_cut_bin_certificate_sound certificate2634 profilesValid2634 numericValid2634 valid2634

def retention2635 : RatCutRetentionCertificate := ⟨(31/500),(1/16),(1/2),(5651130675863015693/500000000000000000),(21/20),(4509172369229526019343934354957619084791/4520904540690412554400000000000000000000),false,MergedCutProfiles.Batch414.profile16578,(fun _ => MergedCutProfiles.Batch414.profile16578)⟩
theorem profilesValid2635 : retention2635.ProfilesValid := by
  exact MergedCutProfiles.Batch414.valid16578
theorem numericValid2635 : retention2635.NumericValid := by decide +kernel
def certificate2635 : RatCutBinCertificate := ⟨⟨retention2635,(2300964834594250959/1000000000000000000),(50258241146397749/250000000000000000),(2057940274574033059/125000000000000000),(374284969214866128027/1000000000000000000),(967902090926164687/1000000000000000000)⟩,(497529304158783303/500000000000000000),(193878967810984097/500000000000000000),(122444166009916759/500000000000000000),(26047811247870647/125000000000000000)⟩
theorem valid2635 : certificate2635.Valid := by decide +kernel
theorem sound2635 : certificate2635.Sound := rat_cut_bin_certificate_sound certificate2635 profilesValid2635 numericValid2635 valid2635

def retention2636 : RatCutRetentionCertificate := ⟨(31/500),(1/16),(10258331069542897543/22663700226962782985),(5011154568274861473/1000000000000000000),(21/20),(8510603769796454637604198080812572177151/8017847309239778356800000000000000000000),false,MergedCutProfiles.Batch414.profile16579,(fun _ => MergedCutProfiles.Batch414.profile16579)⟩
theorem profilesValid2636 : retention2636.ProfilesValid := by
  exact MergedCutProfiles.Batch414.valid16579
theorem numericValid2636 : retention2636.NumericValid := by decide +kernel
def certificate2636 : RatCutBinCertificate := ⟨⟨retention2636,(2549286605594250959/1000000000000000000),(50258241146397749/250000000000000000),(2057940274574033059/125000000000000000),(374284969214866128027/1000000000000000000),(257192203488945653/250000000000000000)⟩,(994524612608797431/1000000000000000000),(44990734876131223/200000000000000000),(87857386512253819/200000000000000000),(360667274514388341/1000000000000000000)⟩
theorem valid2636 : certificate2636.Valid := by decide +kernel
theorem sound2636 : certificate2636.Sound := rat_cut_bin_certificate_sound certificate2636 profilesValid2636 numericValid2636 valid2636

def retention2637 : RatCutRetentionCertificate := ⟨(31/500),(1/16),(11219385613079475513/22663700226962782985),(10258331069542897543/1000000000000000000),1,(40484704187024031741120177903081327147/41033324278171590172000000000000000000),false,MergedCutProfiles.Batch414.profile16580,(fun _ => MergedCutProfiles.Batch414.profile16580)⟩
theorem profilesValid2637 : retention2637.ProfilesValid := by
  exact MergedCutProfiles.Batch414.valid16580
theorem numericValid2637 : retention2637.NumericValid := by decide +kernel
def certificate2637 : RatCutBinCertificate := ⟨⟨retention2637,(2549286605594250959/1000000000000000000),(50258241146397749/250000000000000000),(2057940274574033059/125000000000000000),(374284969214866128027/1000000000000000000),(477749700701873593/500000000000000000)⟩,(994524612608797431/1000000000000000000),(242203526708222311/1000000000000000000),(82850792727364823/200000000000000000),(360006652203597099/1000000000000000000)⟩
theorem valid2637 : certificate2637.Valid := by decide +kernel
theorem sound2637 : certificate2637.Sound := rat_cut_bin_certificate_sound certificate2637 profilesValid2637 numericValid2637 valid2637

def retention2638 : RatCutRetentionCertificate := ⟨(31/500),(1/16),(11331579469210270269/22663700226962782985),(11219385613079475513/1000000000000000000),1,(10987001439038290952858362655757787553/11219385613079475513000000000000000000),false,MergedCutProfiles.Batch414.profile16581,(fun _ => MergedCutProfiles.Batch414.profile16581)⟩
theorem profilesValid2638 : retention2638.ProfilesValid := by
  exact MergedCutProfiles.Batch414.valid16581
theorem numericValid2638 : retention2638.NumericValid := by decide +kernel
def certificate2638 : RatCutBinCertificate := ⟨⟨retention2638,(2549286605594250959/1000000000000000000),(50258241146397749/250000000000000000),(2057940274574033059/125000000000000000),(374284969214866128027/1000000000000000000),(474078457819365041/500000000000000000)⟩,(994524612608797431/1000000000000000000),(122039570123096251/500000000000000000),(41160644123708477/100000000000000000),(178895360600321467/500000000000000000)⟩
theorem valid2638 : certificate2638.Valid := by decide +kernel
theorem sound2638 : certificate2638.Sound := rat_cut_bin_certificate_sound certificate2638 profilesValid2638 numericValid2638 valid2638

def retention2639 : RatCutRetentionCertificate := ⟨(31/500),(1/16),(1/2),(11331579469210270269/1000000000000000000),1,(1387390072669612202779973342146452799/1416447433651283783625000000000000000),false,MergedCutProfiles.Batch414.profile16578,(fun _ => MergedCutProfiles.Batch414.profile16578)⟩
theorem profilesValid2639 : retention2639.ProfilesValid := by
  exact MergedCutProfiles.Batch414.valid16578
theorem numericValid2639 : retention2639.NumericValid := by decide +kernel
def certificate2639 : RatCutBinCertificate := ⟨⟨retention2639,(2549286605594250959/1000000000000000000),(50258241146397749/250000000000000000),(2057940274574033059/125000000000000000),(374284969214866128027/1000000000000000000),(7586843308589941/8000000000000000)⟩,(994524612608797431/1000000000000000000),(61007013160680303/250000000000000000),(102919591353659493/250000000000000000),(358199604383683279/1000000000000000000)⟩
theorem valid2639 : certificate2639.Valid := by decide +kernel
theorem sound2639 : certificate2639.Sound := rat_cut_bin_certificate_sound certificate2639 profilesValid2639 numericValid2639 valid2639

def certificates : List RatCutBinCertificate := [certificate2628,certificate2629,certificate2630,certificate2631,certificate2632,certificate2633,certificate2634,certificate2635,certificate2636,certificate2637,certificate2638,certificate2639]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2628,List.forall_mem_cons.mpr ⟨sound2629,List.forall_mem_cons.mpr ⟨sound2630,List.forall_mem_cons.mpr ⟨sound2631,List.forall_mem_cons.mpr ⟨sound2632,List.forall_mem_cons.mpr ⟨sound2633,List.forall_mem_cons.mpr ⟨sound2634,List.forall_mem_cons.mpr ⟨sound2635,List.forall_mem_cons.mpr ⟨sound2636,List.forall_mem_cons.mpr ⟨sound2637,List.forall_mem_cons.mpr ⟨sound2638,List.forall_mem_cons.mpr ⟨sound2639,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch219
