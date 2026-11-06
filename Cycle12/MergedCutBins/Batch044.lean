import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch088
import Cycle12.MergedCutProfiles.Batch089
import Cycle12.MergedCutProfiles.Batch090

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch044

def retention528 : RatCutRetentionCertificate := ⟨(81/2000),(41/1000),(14864051447003939548/29829875809522449283),(58867530483183919/4000000000000000),(21/20),(236341770609977435168151124825464523319/235470121932735676000000000000000000000),false,MergedCutProfiles.Batch088.profile3528,(fun _ => MergedCutProfiles.Batch088.profile3528)⟩
theorem profilesValid528 : retention528.ProfilesValid := by
  exact MergedCutProfiles.Batch088.valid3528
theorem numericValid528 : retention528.NumericValid := by decide +kernel
def certificate528 : RatCutBinCertificate := ⟨⟨retention528,(207210314825986613/100000000000000000),(77009395027439323/1000000000000000000),(2287828182800729229/200000000000000000),(342151075683948305859/1000000000000000000),(247263611836094587/250000000000000000)⟩,(248598831217909067/250000000000000000),(242982243621033059/500000000000000000),(163353867986571431/1000000000000000000),(144190841551451909/1000000000000000000)⟩
theorem valid528 : certificate528.Valid := by decide +kernel
theorem sound528 : certificate528.Sound := rat_cut_bin_certificate_sound certificate528 profilesValid528 numericValid528 valid528

def retention529 : RatCutRetentionCertificate := ⟨(81/2000),(41/1000),(1/2),(3716012861750984887/250000000000000000),(21/20),(371746920639271626730221766480465864619/371601286175098488700000000000000000000),false,MergedCutProfiles.Batch088.profile3529,(fun _ => MergedCutProfiles.Batch088.profile3529)⟩
theorem profilesValid529 : retention529.ProfilesValid := by
  exact MergedCutProfiles.Batch088.valid3529
theorem numericValid529 : retention529.NumericValid := by decide +kernel
def certificate529 : RatCutBinCertificate := ⟨⟨retention529,(207210314825986613/100000000000000000),(77009395027439323/1000000000000000000),(2287828182800729229/200000000000000000),(342151075683948305859/1000000000000000000),(123218077761877883/125000000000000000)⟩,(248598831217909067/250000000000000000),(243693536491740223/500000000000000000),(162329386229432421/1000000000000000000),(5716631906136673/40000000000000000)⟩
theorem valid529 : certificate529.Valid := by decide +kernel
theorem sound529 : certificate529.Sound := rat_cut_bin_certificate_sound certificate529 profilesValid529 numericValid529 valid529

def retention530 : RatCutRetentionCertificate := ⟨(81/2000),(41/1000),(13088047769167417584/29829875809522449283),(1867892073501326683/500000000000000000),(6/5),(416753260110707277052747425348583416719/373578414700265336600000000000000000000),false,MergedCutProfiles.Batch088.profile3530,(fun _ => MergedCutProfiles.Batch088.profile3530)⟩
theorem profilesValid530 : retention530.ProfilesValid := by
  exact MergedCutProfiles.Batch088.valid3530
theorem numericValid530 : retention530.NumericValid := by decide +kernel
def certificate530 : RatCutBinCertificate := ⟨⟨retention530,(246563178925986613/100000000000000000),(77009395027439323/1000000000000000000),(2287828182800729229/200000000000000000),(342151075683948305859/1000000000000000000),(1095651394666573917/1000000000000000000)⟩,(993330323700211679/1000000000000000000),(184883942381828621/500000000000000000),(131177108493745447/500000000000000000),(197565189131683669/1000000000000000000)⟩
theorem valid530 : certificate530.Valid := by decide +kernel
theorem sound530 : certificate530.Sound := rat_cut_bin_certificate_sound certificate530 profilesValid530 numericValid530 valid530

def retention531 : RatCutRetentionCertificate := ⟨(81/2000),(41/1000),(14747939821860734408/29829875809522449283),(818002985572963599/62500000000000000),1,(812394643792913469200530491868957847/818002985572963599000000000000000000),false,MergedCutProfiles.Batch088.profile3531,(fun _ => MergedCutProfiles.Batch088.profile3531)⟩
theorem profilesValid531 : retention531.ProfilesValid := by
  exact MergedCutProfiles.Batch088.valid3531
theorem numericValid531 : retention531.NumericValid := by decide +kernel
def certificate531 : RatCutBinCertificate := ⟨⟨retention531,(246563178925986613/100000000000000000),(77009395027439323/1000000000000000000),(2287828182800729229/200000000000000000),(342151075683948305859/1000000000000000000),(244136176517984907/250000000000000000)⟩,(993330323700211679/1000000000000000000),(5185844233822059/12500000000000000),(27516601288267791/125000000000000000),(198664618125571499/1000000000000000000)⟩
theorem valid531 : certificate531.Valid := by decide +kernel
theorem sound531 : certificate531.Sound := rat_cut_bin_certificate_sound certificate531 profilesValid531 numericValid531 valid531

def retention532 : RatCutRetentionCertificate := ⟨(81/2000),(41/1000),(14895419220079341753/29829875809522449283),(1843492477732591801/125000000000000000),1,(726909346438284501737724978558614267/737396991093036720400000000000000000),false,MergedCutProfiles.Batch088.profile3532,(fun _ => MergedCutProfiles.Batch088.profile3532)⟩
theorem profilesValid532 : retention532.ProfilesValid := by
  exact MergedCutProfiles.Batch088.valid3532
theorem numericValid532 : retention532.NumericValid := by decide +kernel
def certificate532 : RatCutBinCertificate := ⟨⟨retention532,(246563178925986613/100000000000000000),(77009395027439323/1000000000000000000),(2287828182800729229/200000000000000000),(342151075683948305859/1000000000000000000),(121147294386534531/125000000000000000)⟩,(993330323700211679/1000000000000000000),(52252598362769443/125000000000000000),(13585664231741863/62500000000000000),(196322097507273441/1000000000000000000)⟩
theorem valid532 : certificate532.Valid := by decide +kernel
theorem sound532 : certificate532.Sound := rat_cut_bin_certificate_sound certificate532 profilesValid532 numericValid532 valid532

def retention533 : RatCutRetentionCertificate := ⟨(81/2000),(41/1000),(1/2),(14895419220079341753/1000000000000000000),1,(19556287545774936066071046552775792137/19860558960105789004000000000000000000),false,MergedCutProfiles.Batch088.profile3529,(fun _ => MergedCutProfiles.Batch088.profile3529)⟩
theorem profilesValid533 : retention533.ProfilesValid := by
  exact MergedCutProfiles.Batch088.valid3529
theorem numericValid533 : retention533.NumericValid := by decide +kernel
def certificate533 : RatCutBinCertificate := ⟨⟨retention533,(246563178925986613/100000000000000000),(77009395027439323/1000000000000000000),(2287828182800729229/200000000000000000),(342151075683948305859/1000000000000000000),(968080493990097981/1000000000000000000)⟩,(993330323700211679/1000000000000000000),(41849484744225617/100000000000000000),(10847871034759981/50000000000000000),(195860425178696027/1000000000000000000)⟩
theorem valid533 : certificate533.Valid := by decide +kernel
theorem sound533 : certificate533.Sound := rat_cut_bin_certificate_sound certificate533 profilesValid533 numericValid533 valid533

def retention534 : RatCutRetentionCertificate := ⟨(41/1000),(83/2000),(797357017725650885/29036633862227320134),(789462393787773153/1000000000000000000),(16/5),(171802336609423089057/80000000000000000000),true,MergedCutProfiles.Batch088.profile3533,![MergedCutProfiles.Batch088.profile3533,MergedCutProfiles.Batch088.profile3534,MergedCutProfiles.Batch088.profile3535,MergedCutProfiles.Batch088.profile3536,MergedCutProfiles.Batch088.profile3537,MergedCutProfiles.Batch088.profile3538,MergedCutProfiles.Batch088.profile3539,MergedCutProfiles.Batch088.profile3540,MergedCutProfiles.Batch088.profile3541,MergedCutProfiles.Batch088.profile3542,MergedCutProfiles.Batch088.profile3543,MergedCutProfiles.Batch088.profile3544,MergedCutProfiles.Batch088.profile3545,MergedCutProfiles.Batch088.profile3546,MergedCutProfiles.Batch088.profile3547,MergedCutProfiles.Batch088.profile3548]⟩
theorem profilesValid534 : retention534.ProfilesValid := by
  change ∀ j : Fin 16, (retention534.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch088.valid3533
  · exact MergedCutProfiles.Batch088.valid3534
  · exact MergedCutProfiles.Batch088.valid3535
  · exact MergedCutProfiles.Batch088.valid3536
  · exact MergedCutProfiles.Batch088.valid3537
  · exact MergedCutProfiles.Batch088.valid3538
  · exact MergedCutProfiles.Batch088.valid3539
  · exact MergedCutProfiles.Batch088.valid3540
  · exact MergedCutProfiles.Batch088.valid3541
  · exact MergedCutProfiles.Batch088.valid3542
  · exact MergedCutProfiles.Batch088.valid3543
  · exact MergedCutProfiles.Batch088.valid3544
  · exact MergedCutProfiles.Batch088.valid3545
  · exact MergedCutProfiles.Batch088.valid3546
  · exact MergedCutProfiles.Batch088.valid3547
  · exact MergedCutProfiles.Batch088.valid3548
theorem numericValid534 : retention534.NumericValid := by decide +kernel
def certificate534 : RatCutBinCertificate := ⟨⟨retention534,(1037835275846982131/500000000000000000),(19770779397321387/250000000000000000),(92221564524269007/8000000000000000),(335633625337807551309/1000000000000000000),(1050979018256854333/500000000000000000)⟩,(994289149259070193/1000000000000000000),(40250964563979549/100000000000000000),(231190753102921623/1000000000000000000),(1496414643787951/12500000000000000)⟩
theorem valid534 : certificate534.Valid := by decide +kernel
theorem sound534 : certificate534.Sound := rat_cut_bin_certificate_sound certificate534 profilesValid534 numericValid534 valid534

def retention535 : RatCutRetentionCertificate := ⟨(41/1000),(83/2000),(889585985667964433/29036633862227320134),(159471403545130177/200000000000000000),(63/20),(8523458109171662463/4000000000000000000),true,MergedCutProfiles.Batch088.profile3549,![MergedCutProfiles.Batch088.profile3549,MergedCutProfiles.Batch088.profile3550,MergedCutProfiles.Batch088.profile3551,MergedCutProfiles.Batch088.profile3552,MergedCutProfiles.Batch088.profile3553,MergedCutProfiles.Batch088.profile3554,MergedCutProfiles.Batch088.profile3555,MergedCutProfiles.Batch088.profile3556,MergedCutProfiles.Batch088.profile3542,MergedCutProfiles.Batch088.profile3557,MergedCutProfiles.Batch088.profile3558,MergedCutProfiles.Batch088.profile3559,MergedCutProfiles.Batch089.profile3560,MergedCutProfiles.Batch089.profile3561,MergedCutProfiles.Batch089.profile3562,MergedCutProfiles.Batch089.profile3563]⟩
theorem profilesValid535 : retention535.ProfilesValid := by
  change ∀ j : Fin 16, (retention535.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch088.valid3549
  · exact MergedCutProfiles.Batch088.valid3550
  · exact MergedCutProfiles.Batch088.valid3551
  · exact MergedCutProfiles.Batch088.valid3552
  · exact MergedCutProfiles.Batch088.valid3553
  · exact MergedCutProfiles.Batch088.valid3554
  · exact MergedCutProfiles.Batch088.valid3555
  · exact MergedCutProfiles.Batch088.valid3556
  · exact MergedCutProfiles.Batch088.valid3542
  · exact MergedCutProfiles.Batch088.valid3557
  · exact MergedCutProfiles.Batch088.valid3558
  · exact MergedCutProfiles.Batch088.valid3559
  · exact MergedCutProfiles.Batch089.valid3560
  · exact MergedCutProfiles.Batch089.valid3561
  · exact MergedCutProfiles.Batch089.valid3562
  · exact MergedCutProfiles.Batch089.valid3563
theorem numericValid535 : retention535.NumericValid := by decide +kernel
def certificate535 : RatCutBinCertificate := ⟨⟨retention535,(1037835275846982131/500000000000000000),(19770779397321387/250000000000000000),(92221564524269007/8000000000000000),(335633625337807551309/1000000000000000000),(2086005381410426629/1000000000000000000)⟩,(994289149259070193/1000000000000000000),(80750400901073721/200000000000000000),(230062123069941521/1000000000000000000),(59877131987378447/500000000000000000)⟩
theorem valid535 : certificate535.Valid := by decide +kernel
theorem sound535 : certificate535.Sound := rat_cut_bin_certificate_sound certificate535 profilesValid535 numericValid535 valid535

def retention536 : RatCutRetentionCertificate := ⟨(41/1000),(83/2000),(457388458000000000/14518316931113660067),(889585985667964433/1000000000000000000),(29/10),(2721908648656099904133/1280000000000000000000),true,MergedCutProfiles.Batch089.profile3564,![MergedCutProfiles.Batch089.profile3564,MergedCutProfiles.Batch089.profile3565,MergedCutProfiles.Batch089.profile3566,MergedCutProfiles.Batch089.profile3567,MergedCutProfiles.Batch089.profile3568,MergedCutProfiles.Batch089.profile3569,MergedCutProfiles.Batch089.profile3570,MergedCutProfiles.Batch089.profile3571,MergedCutProfiles.Batch089.profile3572,MergedCutProfiles.Batch089.profile3573,MergedCutProfiles.Batch089.profile3574,MergedCutProfiles.Batch089.profile3575,MergedCutProfiles.Batch089.profile3576,MergedCutProfiles.Batch089.profile3577,MergedCutProfiles.Batch089.profile3578,MergedCutProfiles.Batch089.profile3579]⟩
theorem profilesValid536 : retention536.ProfilesValid := by
  change ∀ j : Fin 16, (retention536.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch089.valid3564
  · exact MergedCutProfiles.Batch089.valid3565
  · exact MergedCutProfiles.Batch089.valid3566
  · exact MergedCutProfiles.Batch089.valid3567
  · exact MergedCutProfiles.Batch089.valid3568
  · exact MergedCutProfiles.Batch089.valid3569
  · exact MergedCutProfiles.Batch089.valid3570
  · exact MergedCutProfiles.Batch089.valid3571
  · exact MergedCutProfiles.Batch089.valid3572
  · exact MergedCutProfiles.Batch089.valid3573
  · exact MergedCutProfiles.Batch089.valid3574
  · exact MergedCutProfiles.Batch089.valid3575
  · exact MergedCutProfiles.Batch089.valid3576
  · exact MergedCutProfiles.Batch089.valid3577
  · exact MergedCutProfiles.Batch089.valid3578
  · exact MergedCutProfiles.Batch089.valid3579
theorem numericValid536 : retention536.NumericValid := by decide +kernel
def certificate536 : RatCutBinCertificate := ⟨⟨retention536,(1037835275846982131/500000000000000000),(19770779397321387/250000000000000000),(92221564524269007/8000000000000000),(335633625337807551309/1000000000000000000),(2085192337852365347/1000000000000000000)⟩,(994289149259070193/1000000000000000000),(192434456367706763/500000000000000000),(247635932449555273/1000000000000000000),(138316824766953823/1000000000000000000)⟩
theorem valid536 : certificate536.Valid := by decide +kernel
theorem sound536 : certificate536.Sound := rat_cut_bin_certificate_sound certificate536 profilesValid536 numericValid536 valid536

def retention537 : RatCutRetentionCertificate := ⟨(41/1000),(83/2000),(74840545485496435/2233587220171332318),(228694229/250000000),(14/5),(6759046794498741551/3200000000000000000),true,MergedCutProfiles.Batch089.profile3580,![MergedCutProfiles.Batch089.profile3580,MergedCutProfiles.Batch089.profile3581,MergedCutProfiles.Batch089.profile3582,MergedCutProfiles.Batch089.profile3583,MergedCutProfiles.Batch089.profile3584,MergedCutProfiles.Batch089.profile3585,MergedCutProfiles.Batch089.profile3586,MergedCutProfiles.Batch089.profile3587,MergedCutProfiles.Batch088.profile3543,MergedCutProfiles.Batch089.profile3588,MergedCutProfiles.Batch088.profile3559,MergedCutProfiles.Batch089.profile3589,MergedCutProfiles.Batch089.profile3590,MergedCutProfiles.Batch089.profile3591,MergedCutProfiles.Batch089.profile3592,MergedCutProfiles.Batch089.profile3593]⟩
theorem profilesValid537 : retention537.ProfilesValid := by
  change ∀ j : Fin 16, (retention537.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch089.valid3580
  · exact MergedCutProfiles.Batch089.valid3581
  · exact MergedCutProfiles.Batch089.valid3582
  · exact MergedCutProfiles.Batch089.valid3583
  · exact MergedCutProfiles.Batch089.valid3584
  · exact MergedCutProfiles.Batch089.valid3585
  · exact MergedCutProfiles.Batch089.valid3586
  · exact MergedCutProfiles.Batch089.valid3587
  · exact MergedCutProfiles.Batch088.valid3543
  · exact MergedCutProfiles.Batch089.valid3588
  · exact MergedCutProfiles.Batch088.valid3559
  · exact MergedCutProfiles.Batch089.valid3589
  · exact MergedCutProfiles.Batch089.valid3590
  · exact MergedCutProfiles.Batch089.valid3591
  · exact MergedCutProfiles.Batch089.valid3592
  · exact MergedCutProfiles.Batch089.valid3593
theorem numericValid537 : retention537.NumericValid := by decide +kernel
def certificate537 : RatCutBinCertificate := ⟨⟨retention537,(1037835275846982131/500000000000000000),(19770779397321387/250000000000000000),(92221564524269007/8000000000000000),(335633625337807551309/1000000000000000000),(207232739951844493/100000000000000000)⟩,(994289149259070193/1000000000000000000),(382696945743008413/1000000000000000000),(249715840183054051/1000000000000000000),(142428565960166897/1000000000000000000)⟩
theorem valid537 : certificate537.Valid := by decide +kernel
theorem sound537 : certificate537.Sound := rat_cut_bin_certificate_sound certificate537 profilesValid537 numericValid537 valid537

def retention538 : RatCutRetentionCertificate := ⟨(41/1000),(83/2000),(792132106289517275/14518316931113660067),(194585418262290731/200000000000000000),(53/20),(130356158631121370357/64000000000000000000),true,MergedCutProfiles.Batch088.profile3534,![MergedCutProfiles.Batch088.profile3534,MergedCutProfiles.Batch088.profile3536,MergedCutProfiles.Batch088.profile3538,MergedCutProfiles.Batch088.profile3540,MergedCutProfiles.Batch089.profile3594,MergedCutProfiles.Batch089.profile3595,MergedCutProfiles.Batch089.profile3596,MergedCutProfiles.Batch089.profile3597,MergedCutProfiles.Batch089.profile3563,MergedCutProfiles.Batch089.profile3598,MergedCutProfiles.Batch089.profile3599,MergedCutProfiles.Batch090.profile3600,MergedCutProfiles.Batch090.profile3601,MergedCutProfiles.Batch090.profile3602,MergedCutProfiles.Batch090.profile3603,MergedCutProfiles.Batch090.profile3604]⟩
theorem profilesValid538 : retention538.ProfilesValid := by
  change ∀ j : Fin 16, (retention538.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch088.valid3534
  · exact MergedCutProfiles.Batch088.valid3536
  · exact MergedCutProfiles.Batch088.valid3538
  · exact MergedCutProfiles.Batch088.valid3540
  · exact MergedCutProfiles.Batch089.valid3594
  · exact MergedCutProfiles.Batch089.valid3595
  · exact MergedCutProfiles.Batch089.valid3596
  · exact MergedCutProfiles.Batch089.valid3597
  · exact MergedCutProfiles.Batch089.valid3563
  · exact MergedCutProfiles.Batch089.valid3598
  · exact MergedCutProfiles.Batch089.valid3599
  · exact MergedCutProfiles.Batch090.valid3600
  · exact MergedCutProfiles.Batch090.valid3601
  · exact MergedCutProfiles.Batch090.valid3602
  · exact MergedCutProfiles.Batch090.valid3603
  · exact MergedCutProfiles.Batch090.valid3604
theorem numericValid538 : retention538.NumericValid := by decide +kernel
def certificate538 : RatCutBinCertificate := ⟨⟨retention538,(1037835275846982131/500000000000000000),(19770779397321387/250000000000000000),(92221564524269007/8000000000000000),(335633625337807551309/1000000000000000000),(999538211746677027/500000000000000000)⟩,(994289149259070193/1000000000000000000),(77348004676851273/200000000000000000),(12292697657840491/50000000000000000),(142525347482330499/1000000000000000000)⟩
theorem valid538 : certificate538.Valid := by decide +kernel
theorem sound538 : certificate538.Sound := rat_cut_bin_certificate_sound certificate538 profilesValid538 numericValid538 valid538

def retention539 : RatCutRetentionCertificate := ⟨(41/1000),(83/2000),(1052803493329386532/4839438977037886689),(31685284251580691/20000000000000000),(37/20),(40360749064986074293603056159213602719/25348227401264552800000000000000000000),false,MergedCutProfiles.Batch090.profile3605,(fun _ => MergedCutProfiles.Batch090.profile3605)⟩
theorem profilesValid539 : retention539.ProfilesValid := by
  exact MergedCutProfiles.Batch090.valid3605
theorem numericValid539 : retention539.NumericValid := by decide +kernel
def certificate539 : RatCutBinCertificate := ⟨⟨retention539,(1037835275846982131/500000000000000000),(19770779397321387/250000000000000000),(92221564524269007/8000000000000000),(335633625337807551309/1000000000000000000),(1565905846634366221/1000000000000000000)⟩,(994289149259070193/1000000000000000000),(416382200065001627/1000000000000000000),(54700754506207509/250000000000000000),(71379504675262381/500000000000000000)⟩
theorem valid539 : certificate539.Valid := by decide +kernel
theorem sound539 : certificate539.Sound := rat_cut_bin_certificate_sound certificate539 profilesValid539 numericValid539 valid539

def certificates : List RatCutBinCertificate := [certificate528,certificate529,certificate530,certificate531,certificate532,certificate533,certificate534,certificate535,certificate536,certificate537,certificate538,certificate539]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound528,List.forall_mem_cons.mpr ⟨sound529,List.forall_mem_cons.mpr ⟨sound530,List.forall_mem_cons.mpr ⟨sound531,List.forall_mem_cons.mpr ⟨sound532,List.forall_mem_cons.mpr ⟨sound533,List.forall_mem_cons.mpr ⟨sound534,List.forall_mem_cons.mpr ⟨sound535,List.forall_mem_cons.mpr ⟨sound536,List.forall_mem_cons.mpr ⟨sound537,List.forall_mem_cons.mpr ⟨sound538,List.forall_mem_cons.mpr ⟨sound539,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch044
