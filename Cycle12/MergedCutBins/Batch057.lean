import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch113
import Cycle12.MergedCutProfiles.Batch114
import Cycle12.MergedCutProfiles.Batch115

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch057

def retention684 : RatCutRetentionCertificate := ⟨(9/200),(181/4000),(1/2),(742862081965503777/62500000000000000),(21/20),(74140845815136247532885108672329951151/74286208196550377700000000000000000000),false,MergedCutProfiles.Batch113.profile4535,(fun _ => MergedCutProfiles.Batch113.profile4535)⟩
theorem profilesValid684 : retention684.ProfilesValid := by
  exact MergedCutProfiles.Batch113.valid4535
theorem numericValid684 : retention684.NumericValid := by decide +kernel
def certificate684 : RatCutBinCertificate := ⟨⟨retention684,(2493425594114026477/1000000000000000000),(11965748524255287/125000000000000000),(3068906201132341919/250000000000000000),(29410909641871090571/100000000000000000),(488813308909241827/500000000000000000)⟩,(496158731657900961/500000000000000000),(51065083874379107/125000000000000000),(45153074667604079/200000000000000000),(38810698649493539/200000000000000000)⟩
theorem valid684 : certificate684.Valid := by decide +kernel
theorem sound684 : certificate684.Sound := rat_cut_bin_certificate_sound certificate684 profilesValid684 numericValid684 valid684

def retention685 : RatCutRetentionCertificate := ⟨(181/4000),(91/2000),(414259828528182711/11815244441221309253),(820316492135015269/1000000000000000000),(61/20),(84567728632697050247/40000000000000000000),true,MergedCutProfiles.Batch113.profile4538,![MergedCutProfiles.Batch113.profile4538,MergedCutProfiles.Batch113.profile4539,MergedCutProfiles.Batch113.profile4540,MergedCutProfiles.Batch113.profile4541,MergedCutProfiles.Batch113.profile4542,MergedCutProfiles.Batch113.profile4543,MergedCutProfiles.Batch113.profile4544,MergedCutProfiles.Batch113.profile4545,MergedCutProfiles.Batch113.profile4546,MergedCutProfiles.Batch113.profile4547,MergedCutProfiles.Batch113.profile4548,MergedCutProfiles.Batch113.profile4549,MergedCutProfiles.Batch113.profile4550,MergedCutProfiles.Batch113.profile4551,MergedCutProfiles.Batch113.profile4552,MergedCutProfiles.Batch113.profile4553]⟩
theorem profilesValid685 : retention685.ProfilesValid := by
  change ∀ j : Fin 16, (retention685.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch113.valid4538
  · exact MergedCutProfiles.Batch113.valid4539
  · exact MergedCutProfiles.Batch113.valid4540
  · exact MergedCutProfiles.Batch113.valid4541
  · exact MergedCutProfiles.Batch113.valid4542
  · exact MergedCutProfiles.Batch113.valid4543
  · exact MergedCutProfiles.Batch113.valid4544
  · exact MergedCutProfiles.Batch113.valid4545
  · exact MergedCutProfiles.Batch113.valid4546
  · exact MergedCutProfiles.Batch113.valid4547
  · exact MergedCutProfiles.Batch113.valid4548
  · exact MergedCutProfiles.Batch113.valid4549
  · exact MergedCutProfiles.Batch113.valid4550
  · exact MergedCutProfiles.Batch113.valid4551
  · exact MergedCutProfiles.Batch113.valid4552
  · exact MergedCutProfiles.Batch113.valid4553
theorem numericValid685 : retention685.NumericValid := by decide +kernel
def certificate685 : RatCutBinCertificate := ⟨⟨retention685,(66196049199494737/31250000000000000),(969058462737911/10000000000000000),(3081204787884955729/250000000000000000),(145823326486021788289/500000000000000000),(206338792013831021/100000000000000000)⟩,(993427451853441161/1000000000000000000),(385254261936191023/1000000000000000000),(61817049426029767/250000000000000000),(3266403052093667/25000000000000000)⟩
theorem valid685 : certificate685.Valid := by decide +kernel
theorem sound685 : certificate685.Sound := rat_cut_bin_certificate_sound certificate685 profilesValid685 numericValid685 valid685

def retention686 : RatCutRetentionCertificate := ⟨(181/4000),(91/2000),(441593435500000000/11815244441221309253),(414259828528182711/500000000000000000),3,(16811082424080783789/8000000000000000000),true,MergedCutProfiles.Batch113.profile4554,![MergedCutProfiles.Batch113.profile4554,MergedCutProfiles.Batch113.profile4555,MergedCutProfiles.Batch113.profile4556,MergedCutProfiles.Batch113.profile4557,MergedCutProfiles.Batch113.profile4558,MergedCutProfiles.Batch113.profile4559,MergedCutProfiles.Batch114.profile4560,MergedCutProfiles.Batch114.profile4561,MergedCutProfiles.Batch114.profile4562,MergedCutProfiles.Batch114.profile4563,MergedCutProfiles.Batch114.profile4564,MergedCutProfiles.Batch114.profile4565,MergedCutProfiles.Batch114.profile4566,MergedCutProfiles.Batch114.profile4567,MergedCutProfiles.Batch113.profile4553,MergedCutProfiles.Batch114.profile4568]⟩
theorem profilesValid686 : retention686.ProfilesValid := by
  change ∀ j : Fin 16, (retention686.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch113.valid4554
  · exact MergedCutProfiles.Batch113.valid4555
  · exact MergedCutProfiles.Batch113.valid4556
  · exact MergedCutProfiles.Batch113.valid4557
  · exact MergedCutProfiles.Batch113.valid4558
  · exact MergedCutProfiles.Batch113.valid4559
  · exact MergedCutProfiles.Batch114.valid4560
  · exact MergedCutProfiles.Batch114.valid4561
  · exact MergedCutProfiles.Batch114.valid4562
  · exact MergedCutProfiles.Batch114.valid4563
  · exact MergedCutProfiles.Batch114.valid4564
  · exact MergedCutProfiles.Batch114.valid4565
  · exact MergedCutProfiles.Batch114.valid4566
  · exact MergedCutProfiles.Batch114.valid4567
  · exact MergedCutProfiles.Batch113.valid4553
  · exact MergedCutProfiles.Batch114.valid4568
theorem numericValid686 : retention686.NumericValid := by decide +kernel
def certificate686 : RatCutBinCertificate := ⟨⟨retention686,(66196049199494737/31250000000000000),(969058462737911/10000000000000000),(3081204787884955729/250000000000000000),(145823326486021788289/500000000000000000),(256426604653859161/125000000000000000)⟩,(993427451853441161/1000000000000000000),(617367017308431/1600000000000000),(30837034075043523/125000000000000000),(131269683021798259/1000000000000000000)⟩
theorem valid686 : certificate686.Valid := by decide +kernel
theorem sound686 : certificate686.Sound := rat_cut_bin_certificate_sound certificate686 profilesValid686 numericValid686 valid686

def retention687 : RatCutRetentionCertificate := ⟨(181/4000),(91/2000),(971504456763800387/23630488882442618506),(883186871/1000000000),(57/20),(3338083103130785557/1600000000000000000),true,MergedCutProfiles.Batch114.profile4569,![MergedCutProfiles.Batch114.profile4569,MergedCutProfiles.Batch114.profile4570,MergedCutProfiles.Batch114.profile4571,MergedCutProfiles.Batch114.profile4572,MergedCutProfiles.Batch114.profile4573,MergedCutProfiles.Batch114.profile4574,MergedCutProfiles.Batch114.profile4575,MergedCutProfiles.Batch114.profile4576,MergedCutProfiles.Batch114.profile4577,MergedCutProfiles.Batch114.profile4564,MergedCutProfiles.Batch114.profile4578,MergedCutProfiles.Batch114.profile4579,MergedCutProfiles.Batch114.profile4580,MergedCutProfiles.Batch114.profile4581,MergedCutProfiles.Batch114.profile4582,MergedCutProfiles.Batch114.profile4583]⟩
theorem profilesValid687 : retention687.ProfilesValid := by
  change ∀ j : Fin 16, (retention687.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch114.valid4569
  · exact MergedCutProfiles.Batch114.valid4570
  · exact MergedCutProfiles.Batch114.valid4571
  · exact MergedCutProfiles.Batch114.valid4572
  · exact MergedCutProfiles.Batch114.valid4573
  · exact MergedCutProfiles.Batch114.valid4574
  · exact MergedCutProfiles.Batch114.valid4575
  · exact MergedCutProfiles.Batch114.valid4576
  · exact MergedCutProfiles.Batch114.valid4577
  · exact MergedCutProfiles.Batch114.valid4564
  · exact MergedCutProfiles.Batch114.valid4578
  · exact MergedCutProfiles.Batch114.valid4579
  · exact MergedCutProfiles.Batch114.valid4580
  · exact MergedCutProfiles.Batch114.valid4581
  · exact MergedCutProfiles.Batch114.valid4582
  · exact MergedCutProfiles.Batch114.valid4583
theorem numericValid687 : retention687.NumericValid := by decide +kernel
def certificate687 : RatCutBinCertificate := ⟨⟨retention687,(66196049199494737/31250000000000000),(969058462737911/10000000000000000),(3081204787884955729/250000000000000000),(145823326486021788289/500000000000000000),(2038828176436573911/1000000000000000000)⟩,(993427451853441161/1000000000000000000),(37796744709611451/100000000000000000),(127143793886227123/500000000000000000),(2196206792045001/15625000000000000)⟩
theorem valid687 : certificate687.Valid := by decide +kernel
theorem sound687 : certificate687.Sound := rat_cut_bin_certificate_sound certificate687 profilesValid687 numericValid687 valid687

def retention688 : RatCutRetentionCertificate := ⟨(181/4000),(91/2000),(873727197645097117/11815244441221309253),(971504456763800387/1000000000000000000),(53/20),(2534552725826490217819/1280000000000000000000),true,MergedCutProfiles.Batch113.profile4555,![MergedCutProfiles.Batch113.profile4555,MergedCutProfiles.Batch114.profile4584,MergedCutProfiles.Batch114.profile4585,MergedCutProfiles.Batch114.profile4586,MergedCutProfiles.Batch114.profile4577,MergedCutProfiles.Batch114.profile4587,MergedCutProfiles.Batch114.profile4588,MergedCutProfiles.Batch114.profile4589,MergedCutProfiles.Batch114.profile4590,MergedCutProfiles.Batch114.profile4591,MergedCutProfiles.Batch114.profile4592,MergedCutProfiles.Batch114.profile4593,MergedCutProfiles.Batch114.profile4594,MergedCutProfiles.Batch114.profile4595,MergedCutProfiles.Batch114.profile4596,MergedCutProfiles.Batch114.profile4597]⟩
theorem profilesValid688 : retention688.ProfilesValid := by
  change ∀ j : Fin 16, (retention688.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch113.valid4555
  · exact MergedCutProfiles.Batch114.valid4584
  · exact MergedCutProfiles.Batch114.valid4585
  · exact MergedCutProfiles.Batch114.valid4586
  · exact MergedCutProfiles.Batch114.valid4577
  · exact MergedCutProfiles.Batch114.valid4587
  · exact MergedCutProfiles.Batch114.valid4588
  · exact MergedCutProfiles.Batch114.valid4589
  · exact MergedCutProfiles.Batch114.valid4590
  · exact MergedCutProfiles.Batch114.valid4591
  · exact MergedCutProfiles.Batch114.valid4592
  · exact MergedCutProfiles.Batch114.valid4593
  · exact MergedCutProfiles.Batch114.valid4594
  · exact MergedCutProfiles.Batch114.valid4595
  · exact MergedCutProfiles.Batch114.valid4596
  · exact MergedCutProfiles.Batch114.valid4597
theorem numericValid688 : retention688.NumericValid := by decide +kernel
def certificate688 : RatCutBinCertificate := ⟨⟨retention688,(66196049199494737/31250000000000000),(969058462737911/10000000000000000),(3081204787884955729/250000000000000000),(145823326486021788289/500000000000000000),(1935977176084588579/1000000000000000000)⟩,(993427451853441161/1000000000000000000),(383147926915471981/1000000000000000000),(249282962932020817/1000000000000000000),(28153318188071649/200000000000000000)⟩
theorem valid688 : certificate688.Valid := by decide +kernel
theorem sound688 : certificate688.Sound := rat_cut_bin_certificate_sound certificate688 profilesValid688 numericValid688 valid688

def retention689 : RatCutRetentionCertificate := ⟨(181/4000),(91/2000),(3122566520254984031/11815244441221309253),(873727197645097117/500000000000000000),(17/10),(950830345752799382737/640000000000000000000),true,MergedCutProfiles.Batch114.profile4598,![MergedCutProfiles.Batch114.profile4598,MergedCutProfiles.Batch114.profile4599,MergedCutProfiles.Batch115.profile4600,MergedCutProfiles.Batch115.profile4601,MergedCutProfiles.Batch115.profile4602,MergedCutProfiles.Batch115.profile4603,MergedCutProfiles.Batch115.profile4604,MergedCutProfiles.Batch115.profile4605,MergedCutProfiles.Batch115.profile4606,MergedCutProfiles.Batch115.profile4607,MergedCutProfiles.Batch115.profile4608,MergedCutProfiles.Batch115.profile4609,MergedCutProfiles.Batch115.profile4610,MergedCutProfiles.Batch115.profile4611,MergedCutProfiles.Batch115.profile4612,MergedCutProfiles.Batch115.profile4613]⟩
theorem profilesValid689 : retention689.ProfilesValid := by
  change ∀ j : Fin 16, (retention689.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch114.valid4598
  · exact MergedCutProfiles.Batch114.valid4599
  · exact MergedCutProfiles.Batch115.valid4600
  · exact MergedCutProfiles.Batch115.valid4601
  · exact MergedCutProfiles.Batch115.valid4602
  · exact MergedCutProfiles.Batch115.valid4603
  · exact MergedCutProfiles.Batch115.valid4604
  · exact MergedCutProfiles.Batch115.valid4605
  · exact MergedCutProfiles.Batch115.valid4606
  · exact MergedCutProfiles.Batch115.valid4607
  · exact MergedCutProfiles.Batch115.valid4608
  · exact MergedCutProfiles.Batch115.valid4609
  · exact MergedCutProfiles.Batch115.valid4610
  · exact MergedCutProfiles.Batch115.valid4611
  · exact MergedCutProfiles.Batch115.valid4612
  · exact MergedCutProfiles.Batch115.valid4613
theorem numericValid689 : retention689.NumericValid := by decide +kernel
def certificate689 : RatCutBinCertificate := ⟨⟨retention689,(66196049199494737/31250000000000000),(969058462737911/10000000000000000),(3081204787884955729/250000000000000000),(145823326486021788289/500000000000000000),(1457355302729310989/1000000000000000000)⟩,(993427451853441161/1000000000000000000),(210545373565227377/500000000000000000),(214704250366605883/1000000000000000000),(70880026807322559/500000000000000000)⟩
theorem valid689 : certificate689.Valid := by decide +kernel
theorem sound689 : certificate689.Sound := rat_cut_bin_certificate_sound certificate689 profilesValid689 numericValid689 valid689

def retention690 : RatCutRetentionCertificate := ⟨(181/4000),(91/2000),(5397432962562294914/11815244441221309253),(3122566520254984031/500000000000000000),1,(133616324759905854671/128000000000000000000),true,MergedCutProfiles.Batch115.profile4614,![MergedCutProfiles.Batch115.profile4614,MergedCutProfiles.Batch115.profile4615,MergedCutProfiles.Batch115.profile4616,MergedCutProfiles.Batch115.profile4617,MergedCutProfiles.Batch115.profile4618,MergedCutProfiles.Batch115.profile4619,MergedCutProfiles.Batch115.profile4620,MergedCutProfiles.Batch115.profile4621,MergedCutProfiles.Batch115.profile4622,MergedCutProfiles.Batch115.profile4623,MergedCutProfiles.Batch115.profile4624,MergedCutProfiles.Batch115.profile4625,MergedCutProfiles.Batch115.profile4626,MergedCutProfiles.Batch115.profile4627,MergedCutProfiles.Batch115.profile4628,MergedCutProfiles.Batch115.profile4629]⟩
theorem profilesValid690 : retention690.ProfilesValid := by
  change ∀ j : Fin 16, (retention690.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch115.valid4614
  · exact MergedCutProfiles.Batch115.valid4615
  · exact MergedCutProfiles.Batch115.valid4616
  · exact MergedCutProfiles.Batch115.valid4617
  · exact MergedCutProfiles.Batch115.valid4618
  · exact MergedCutProfiles.Batch115.valid4619
  · exact MergedCutProfiles.Batch115.valid4620
  · exact MergedCutProfiles.Batch115.valid4621
  · exact MergedCutProfiles.Batch115.valid4622
  · exact MergedCutProfiles.Batch115.valid4623
  · exact MergedCutProfiles.Batch115.valid4624
  · exact MergedCutProfiles.Batch115.valid4625
  · exact MergedCutProfiles.Batch115.valid4626
  · exact MergedCutProfiles.Batch115.valid4627
  · exact MergedCutProfiles.Batch115.valid4628
  · exact MergedCutProfiles.Batch115.valid4629
theorem numericValid690 : retention690.NumericValid := by decide +kernel
def certificate690 : RatCutBinCertificate := ⟨⟨retention690,(66196049199494737/31250000000000000),(969058462737911/10000000000000000),(3081204787884955729/250000000000000000),(145823326486021788289/500000000000000000),(4012583550550609/3906250000000000)⟩,(993427451853441161/1000000000000000000),(121245549698424421/250000000000000000),(164063697258212531/1000000000000000000),(17962363208089841/125000000000000000)⟩
theorem valid690 : certificate690.Valid := by decide +kernel
theorem sound690 : certificate690.Sound := rat_cut_bin_certificate_sound certificate690 profilesValid690 numericValid690 valid690

def retention691 : RatCutRetentionCertificate := ⟨(181/4000),(91/2000),(5844646476688615265/11815244441221309253),(2698716481281147457/250000000000000000),(21/20),(1087092548845820585673797784663137102111/1079486592512458982800000000000000000000),false,MergedCutProfiles.Batch115.profile4630,(fun _ => MergedCutProfiles.Batch115.profile4630)⟩
theorem profilesValid691 : retention691.ProfilesValid := by
  exact MergedCutProfiles.Batch115.valid4630
theorem numericValid691 : retention691.NumericValid := by decide +kernel
def certificate691 : RatCutBinCertificate := ⟨⟨retention691,(66196049199494737/31250000000000000),(969058462737911/10000000000000000),(3081204787884955729/250000000000000000),(145823326486021788289/500000000000000000),(123694670469333003/125000000000000000)⟩,(993427451853441161/1000000000000000000),(242164645159591859/500000000000000000),(82268303843033707/500000000000000000),(142176970001006841/1000000000000000000)⟩
theorem valid691 : certificate691.Valid := by decide +kernel
theorem sound691 : certificate691.Sound := rat_cut_bin_certificate_sound certificate691 profilesValid691 numericValid691 valid691

def retention692 : RatCutRetentionCertificate := ⟨(181/4000),(91/2000),(536644812859591038/1074113131020119023),(1168929295337723053/100000000000000000),(21/20),(37352118357264087274942952447513021419/37405737450807137696000000000000000000),false,MergedCutProfiles.Batch115.profile4631,(fun _ => MergedCutProfiles.Batch115.profile4631)⟩
theorem profilesValid692 : retention692.ProfilesValid := by
  exact MergedCutProfiles.Batch115.valid4631
theorem numericValid692 : retention692.NumericValid := by decide +kernel
def certificate692 : RatCutBinCertificate := ⟨⟨retention692,(66196049199494737/31250000000000000),(969058462737911/10000000000000000),(3081204787884955729/250000000000000000),(145823326486021788289/500000000000000000),(490539027829141137/500000000000000000)⟩,(993427451853441161/1000000000000000000),(97298118152555429/200000000000000000),(81487253743720043/500000000000000000),(140534293371714351/1000000000000000000)⟩
theorem valid692 : certificate692.Valid := by decide +kernel
theorem sound692 : certificate692.Sound := rat_cut_bin_certificate_sound certificate692 profilesValid692 numericValid692 valid692

def retention693 : RatCutRetentionCertificate := ⟨(181/4000),(91/2000),(1/2),(2951546470727750709/250000000000000000),(21/20),(1178200347699453591801585871596061082039/1180618588291100283600000000000000000000),false,MergedCutProfiles.Batch115.profile4632,(fun _ => MergedCutProfiles.Batch115.profile4632)⟩
theorem profilesValid693 : retention693.ProfilesValid := by
  exact MergedCutProfiles.Batch115.valid4632
theorem numericValid693 : retention693.NumericValid := by decide +kernel
def certificate693 : RatCutBinCertificate := ⟨⟨retention693,(66196049199494737/31250000000000000),(969058462737911/10000000000000000),(3081204787884955729/250000000000000000),(145823326486021788289/500000000000000000),(980463223378979159/1000000000000000000)⟩,(993427451853441161/1000000000000000000),(486553568978166001/1000000000000000000),(162929133562437761/1000000000000000000),(8782004509797149/62500000000000000)⟩
theorem valid693 : certificate693.Valid := by decide +kernel
theorem sound693 : certificate693.Sound := rat_cut_bin_certificate_sound certificate693 profilesValid693 numericValid693 valid693

def retention694 : RatCutRetentionCertificate := ⟨(181/4000),(91/2000),(5285289164781931058/11815244441221309253),(3793125823660242777/1000000000000000000),(6/5),(417140950151475665495519860353655525511/379312582366024277700000000000000000000),false,MergedCutProfiles.Batch115.profile4633,(fun _ => MergedCutProfiles.Batch115.profile4633)⟩
theorem profilesValid694 : retention694.ProfilesValid := by
  exact MergedCutProfiles.Batch115.valid4633
theorem numericValid694 : retention694.NumericValid := by decide +kernel
def certificate694 : RatCutBinCertificate := ⟨⟨retention694,(77999483324494737/31250000000000000),(969058462737911/10000000000000000),(3081204787884955729/250000000000000000),(145823326486021788289/500000000000000000),(538088473277420429/500000000000000000)⟩,(992254538380019607/1000000000000000000),(370154459254699757/1000000000000000000),(261969860665900713/1000000000000000000),(24326599654611679/125000000000000000)⟩
theorem valid694 : certificate694.Valid := by decide +kernel
theorem sound694 : certificate694.Sound := rat_cut_bin_certificate_sound certificate694 profilesValid694 numericValid694 valid694

def retention695 : RatCutRetentionCertificate := ⟨(181/4000),(91/2000),(11676494701228453183/23630488882442618506),(2642644582390965529/250000000000000000),(21/20),(1065243725205903363360026120364135412719/1057057832956386211600000000000000000000),false,MergedCutProfiles.Batch115.profile4634,(fun _ => MergedCutProfiles.Batch115.profile4634)⟩
theorem profilesValid695 : retention695.ProfilesValid := by
  exact MergedCutProfiles.Batch115.valid4634
theorem numericValid695 : retention695.NumericValid := by decide +kernel
def certificate695 : RatCutBinCertificate := ⟨⟨retention695,(77999483324494737/31250000000000000),(969058462737911/10000000000000000),(3081204787884955729/250000000000000000),(145823326486021788289/500000000000000000),(987137098171290329/1000000000000000000)⟩,(992254538380019607/1000000000000000000),(100885605568958701/250000000000000000),(115126125664678773/500000000000000000),(197955507891266047/1000000000000000000)⟩
theorem valid695 : certificate695.Valid := by decide +kernel
theorem sound695 : certificate695.Sound := rat_cut_bin_certificate_sound certificate695 profilesValid695 numericValid695 valid695

def certificates : List RatCutBinCertificate := [certificate684,certificate685,certificate686,certificate687,certificate688,certificate689,certificate690,certificate691,certificate692,certificate693,certificate694,certificate695]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound684,List.forall_mem_cons.mpr ⟨sound685,List.forall_mem_cons.mpr ⟨sound686,List.forall_mem_cons.mpr ⟨sound687,List.forall_mem_cons.mpr ⟨sound688,List.forall_mem_cons.mpr ⟨sound689,List.forall_mem_cons.mpr ⟨sound690,List.forall_mem_cons.mpr ⟨sound691,List.forall_mem_cons.mpr ⟨sound692,List.forall_mem_cons.mpr ⟨sound693,List.forall_mem_cons.mpr ⟨sound694,List.forall_mem_cons.mpr ⟨sound695,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch057
