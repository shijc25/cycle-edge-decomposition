import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch115
import Cycle12.MergedCutProfiles.Batch116
import Cycle12.MergedCutProfiles.Batch117
import Cycle12.MergedCutProfiles.Batch118

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch058

def retention696 : RatCutRetentionCertificate := ⟨(181/4000),(91/2000),(11793259648240737715/23630488882442618506),(11676494701228453183/1000000000000000000),(21/20),(18675427026806986783083533767653176196911/18682391521965525092800000000000000000000),false,MergedCutProfiles.Batch115.profile4635,(fun _ => MergedCutProfiles.Batch115.profile4635)⟩
theorem profilesValid696 : retention696.ProfilesValid := by
  exact MergedCutProfiles.Batch115.valid4635
theorem numericValid696 : retention696.NumericValid := by decide +kernel
def certificate696 : RatCutBinCertificate := ⟨⟨retention696,(77999483324494737/31250000000000000),(969058462737911/10000000000000000),(3081204787884955729/250000000000000000),(145823326486021788289/500000000000000000),(244755084562768577/250000000000000000)⟩,(992254538380019607/1000000000000000000),(12715252180881593/31250000000000000),(227230112209144487/1000000000000000000),(24414294454896739/125000000000000000)⟩
theorem valid696 : certificate696.Valid := by decide +kernel
theorem sound696 : certificate696.Sound := rat_cut_bin_certificate_sound certificate696 profilesValid696 numericValid696 valid696

def retention697 : RatCutRetentionCertificate := ⟨(181/4000),(91/2000),(1/2),(2358651929648147543/200000000000000000),(21/20),(753211164057406306047030740159904903519/754768617487407213760000000000000000000),false,MergedCutProfiles.Batch115.profile4632,(fun _ => MergedCutProfiles.Batch115.profile4632)⟩
theorem profilesValid697 : retention697.ProfilesValid := by
  exact MergedCutProfiles.Batch115.valid4632
theorem numericValid697 : retention697.NumericValid := by decide +kernel
def certificate697 : RatCutBinCertificate := ⟨⟨retention697,(77999483324494737/31250000000000000),(969058462737911/10000000000000000),(3081204787884955729/250000000000000000),(145823326486021788289/500000000000000000),(122166205385763721/125000000000000000)⟩,(992254538380019607/1000000000000000000),(407591950712256653/1000000000000000000),(1812782416978897/8000000000000000),(19459469368746389/100000000000000000)⟩
theorem valid697 : certificate697.Valid := by decide +kernel
theorem sound697 : certificate697.Sound := rat_cut_bin_certificate_sound certificate697 profilesValid697 numericValid697 valid697

def retention698 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(416537682484907993/11527616169144297356),(412413547014760389/500000000000000000),3,(16827832980256703367/8000000000000000000),true,MergedCutProfiles.Batch115.profile4636,![MergedCutProfiles.Batch115.profile4636,MergedCutProfiles.Batch115.profile4637,MergedCutProfiles.Batch115.profile4638,MergedCutProfiles.Batch115.profile4639,MergedCutProfiles.Batch116.profile4640,MergedCutProfiles.Batch116.profile4641,MergedCutProfiles.Batch116.profile4642,MergedCutProfiles.Batch116.profile4643,MergedCutProfiles.Batch116.profile4644,MergedCutProfiles.Batch116.profile4645,MergedCutProfiles.Batch116.profile4646,MergedCutProfiles.Batch116.profile4647,MergedCutProfiles.Batch116.profile4648,MergedCutProfiles.Batch116.profile4649,MergedCutProfiles.Batch116.profile4650,MergedCutProfiles.Batch116.profile4651]⟩
theorem profilesValid698 : retention698.ProfilesValid := by
  change ∀ j : Fin 16, (retention698.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch115.valid4636
  · exact MergedCutProfiles.Batch115.valid4637
  · exact MergedCutProfiles.Batch115.valid4638
  · exact MergedCutProfiles.Batch115.valid4639
  · exact MergedCutProfiles.Batch116.valid4640
  · exact MergedCutProfiles.Batch116.valid4641
  · exact MergedCutProfiles.Batch116.valid4642
  · exact MergedCutProfiles.Batch116.valid4643
  · exact MergedCutProfiles.Batch116.valid4644
  · exact MergedCutProfiles.Batch116.valid4645
  · exact MergedCutProfiles.Batch116.valid4646
  · exact MergedCutProfiles.Batch116.valid4647
  · exact MergedCutProfiles.Batch116.valid4648
  · exact MergedCutProfiles.Batch116.valid4649
  · exact MergedCutProfiles.Batch116.valid4650
  · exact MergedCutProfiles.Batch116.valid4651
theorem numericValid698 : retention698.NumericValid := by decide +kernel
def certificate698 : RatCutBinCertificate := ⟨⟨retention698,(105932082452006859/50000000000000000),(19858540071699249/200000000000000000),(1546784460960759961/125000000000000000),(17880499278205887779/62500000000000000),(1026235625326630771/500000000000000000)⟩,(993307171608962287/1000000000000000000),(96117351815924299/250000000000000000),(9920703338224253/40000000000000000),(131878774556687107/1000000000000000000)⟩
theorem valid698 : certificate698.Valid := by decide +kernel
theorem sound698 : certificate698.Sound := rat_cut_bin_certificate_sound certificate698 profilesValid698 numericValid698 valid698

def retention699 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(108299585875000000/2881904042286074339),(416537682484907993/500000000000000000),3,(269178692827986243441/128000000000000000000),true,MergedCutProfiles.Batch116.profile4652,![MergedCutProfiles.Batch116.profile4652,MergedCutProfiles.Batch116.profile4653,MergedCutProfiles.Batch116.profile4654,MergedCutProfiles.Batch116.profile4655,MergedCutProfiles.Batch116.profile4656,MergedCutProfiles.Batch116.profile4657,MergedCutProfiles.Batch116.profile4658,MergedCutProfiles.Batch116.profile4659,MergedCutProfiles.Batch116.profile4660,MergedCutProfiles.Batch116.profile4661,MergedCutProfiles.Batch116.profile4662,MergedCutProfiles.Batch116.profile4663,MergedCutProfiles.Batch116.profile4664,MergedCutProfiles.Batch116.profile4665,MergedCutProfiles.Batch116.profile4666,MergedCutProfiles.Batch116.profile4667]⟩
theorem profilesValid699 : retention699.ProfilesValid := by
  change ∀ j : Fin 16, (retention699.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch116.valid4652
  · exact MergedCutProfiles.Batch116.valid4653
  · exact MergedCutProfiles.Batch116.valid4654
  · exact MergedCutProfiles.Batch116.valid4655
  · exact MergedCutProfiles.Batch116.valid4656
  · exact MergedCutProfiles.Batch116.valid4657
  · exact MergedCutProfiles.Batch116.valid4658
  · exact MergedCutProfiles.Batch116.valid4659
  · exact MergedCutProfiles.Batch116.valid4660
  · exact MergedCutProfiles.Batch116.valid4661
  · exact MergedCutProfiles.Batch116.valid4662
  · exact MergedCutProfiles.Batch116.valid4663
  · exact MergedCutProfiles.Batch116.valid4664
  · exact MergedCutProfiles.Batch116.valid4665
  · exact MergedCutProfiles.Batch116.valid4666
  · exact MergedCutProfiles.Batch116.valid4667
theorem numericValid699 : retention699.NumericValid := by decide +kernel
def certificate699 : RatCutBinCertificate := ⟨⟨retention699,(105932082452006859/50000000000000000),(19858540071699249/200000000000000000),(1546784460960759961/125000000000000000),(17880499278205887779/62500000000000000),(2051950736665119889/1000000000000000000)⟩,(993307171608962287/1000000000000000000),(382947943938516717/1000000000000000000),(249474852416556677/1000000000000000000),(13291352777222649/100000000000000000)⟩
theorem valid699 : certificate699.Valid := by decide +kernel
theorem sound699 : certificate699.Sound := rat_cut_bin_certificate_sound certificate699 profilesValid699 numericValid699 valid699

def retention700 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(437785290537001043/11527616169144297356),(866396687/1000000000),(29/10),(33583353950043242059/16000000000000000000),true,MergedCutProfiles.Batch116.profile4652,![MergedCutProfiles.Batch116.profile4652,MergedCutProfiles.Batch116.profile4668,MergedCutProfiles.Batch116.profile4669,MergedCutProfiles.Batch116.profile4670,MergedCutProfiles.Batch116.profile4671,MergedCutProfiles.Batch116.profile4672,MergedCutProfiles.Batch116.profile4673,MergedCutProfiles.Batch116.profile4674,MergedCutProfiles.Batch116.profile4675,MergedCutProfiles.Batch116.profile4676,MergedCutProfiles.Batch116.profile4677,MergedCutProfiles.Batch116.profile4678,MergedCutProfiles.Batch116.profile4679,MergedCutProfiles.Batch117.profile4680,MergedCutProfiles.Batch117.profile4681,MergedCutProfiles.Batch117.profile4682]⟩
theorem profilesValid700 : retention700.ProfilesValid := by
  change ∀ j : Fin 16, (retention700.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch116.valid4652
  · exact MergedCutProfiles.Batch116.valid4668
  · exact MergedCutProfiles.Batch116.valid4669
  · exact MergedCutProfiles.Batch116.valid4670
  · exact MergedCutProfiles.Batch116.valid4671
  · exact MergedCutProfiles.Batch116.valid4672
  · exact MergedCutProfiles.Batch116.valid4673
  · exact MergedCutProfiles.Batch116.valid4674
  · exact MergedCutProfiles.Batch116.valid4675
  · exact MergedCutProfiles.Batch116.valid4676
  · exact MergedCutProfiles.Batch116.valid4677
  · exact MergedCutProfiles.Batch116.valid4678
  · exact MergedCutProfiles.Batch116.valid4679
  · exact MergedCutProfiles.Batch117.valid4680
  · exact MergedCutProfiles.Batch117.valid4681
  · exact MergedCutProfiles.Batch117.valid4682
theorem numericValid700 : retention700.NumericValid := by decide +kernel
def certificate700 : RatCutBinCertificate := ⟨⟨retention700,(105932082452006859/50000000000000000),(19858540071699249/200000000000000000),(1546784460960759961/125000000000000000),(17880499278205887779/62500000000000000),(81986084686666477/40000000000000000)⟩,(993307171608962287/1000000000000000000),(377143841112161527/1000000000000000000),(255089747406621279/1000000000000000000),(69800285926980033/500000000000000000)⟩
theorem valid700 : certificate700.Valid := by decide +kernel
theorem sound700 : certificate700.Sound := rat_cut_bin_certificate_sound certificate700 profilesValid700 numericValid700 valid700

def retention701 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(967174636213487543/23055232338288594712),(437785290537001043/500000000000000000),(57/20),(1331714130542327195027/640000000000000000000),true,MergedCutProfiles.Batch117.profile4683,![MergedCutProfiles.Batch117.profile4683,MergedCutProfiles.Batch117.profile4684,MergedCutProfiles.Batch117.profile4685,MergedCutProfiles.Batch117.profile4686,MergedCutProfiles.Batch117.profile4687,MergedCutProfiles.Batch117.profile4688,MergedCutProfiles.Batch117.profile4689,MergedCutProfiles.Batch117.profile4690,MergedCutProfiles.Batch117.profile4691,MergedCutProfiles.Batch117.profile4692,MergedCutProfiles.Batch117.profile4693,MergedCutProfiles.Batch117.profile4694,MergedCutProfiles.Batch117.profile4695,MergedCutProfiles.Batch117.profile4696,MergedCutProfiles.Batch117.profile4697,MergedCutProfiles.Batch117.profile4698]⟩
theorem profilesValid701 : retention701.ProfilesValid := by
  change ∀ j : Fin 16, (retention701.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch117.valid4683
  · exact MergedCutProfiles.Batch117.valid4684
  · exact MergedCutProfiles.Batch117.valid4685
  · exact MergedCutProfiles.Batch117.valid4686
  · exact MergedCutProfiles.Batch117.valid4687
  · exact MergedCutProfiles.Batch117.valid4688
  · exact MergedCutProfiles.Batch117.valid4689
  · exact MergedCutProfiles.Batch117.valid4690
  · exact MergedCutProfiles.Batch117.valid4691
  · exact MergedCutProfiles.Batch117.valid4692
  · exact MergedCutProfiles.Batch117.valid4693
  · exact MergedCutProfiles.Batch117.valid4694
  · exact MergedCutProfiles.Batch117.valid4695
  · exact MergedCutProfiles.Batch117.valid4696
  · exact MergedCutProfiles.Batch117.valid4697
  · exact MergedCutProfiles.Batch117.valid4698
theorem numericValid701 : retention701.NumericValid := by decide +kernel
def certificate701 : RatCutBinCertificate := ⟨⟨retention701,(105932082452006859/50000000000000000),(19858540071699249/200000000000000000),(1546784460960759961/125000000000000000),(17880499278205887779/62500000000000000),(2032345907590762743/1000000000000000000)⟩,(993307171608962287/1000000000000000000),(47338569424716697/125000000000000000),(126783655256772203/500000000000000000),(27904439143257989/200000000000000000)⟩
theorem valid701 : certificate701.Valid := by decide +kernel
theorem sound701 : certificate701.Sound := rat_cut_bin_certificate_sound certificate701 profilesValid701 numericValid701 valid701

def retention702 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(448094983552925409/5763808084572148678),(967174636213487543/1000000000000000000),(13/5),(628182091227076172827/320000000000000000000),true,MergedCutProfiles.Batch117.profile4699,![MergedCutProfiles.Batch117.profile4699,MergedCutProfiles.Batch117.profile4700,MergedCutProfiles.Batch117.profile4701,MergedCutProfiles.Batch117.profile4702,MergedCutProfiles.Batch117.profile4703,MergedCutProfiles.Batch117.profile4704,MergedCutProfiles.Batch117.profile4705,MergedCutProfiles.Batch117.profile4706,MergedCutProfiles.Batch117.profile4707,MergedCutProfiles.Batch117.profile4708,MergedCutProfiles.Batch117.profile4709,MergedCutProfiles.Batch117.profile4710,MergedCutProfiles.Batch117.profile4711,MergedCutProfiles.Batch117.profile4712,MergedCutProfiles.Batch117.profile4713,MergedCutProfiles.Batch117.profile4714]⟩
theorem profilesValid702 : retention702.ProfilesValid := by
  change ∀ j : Fin 16, (retention702.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch117.valid4699
  · exact MergedCutProfiles.Batch117.valid4700
  · exact MergedCutProfiles.Batch117.valid4701
  · exact MergedCutProfiles.Batch117.valid4702
  · exact MergedCutProfiles.Batch117.valid4703
  · exact MergedCutProfiles.Batch117.valid4704
  · exact MergedCutProfiles.Batch117.valid4705
  · exact MergedCutProfiles.Batch117.valid4706
  · exact MergedCutProfiles.Batch117.valid4707
  · exact MergedCutProfiles.Batch117.valid4708
  · exact MergedCutProfiles.Batch117.valid4709
  · exact MergedCutProfiles.Batch117.valid4710
  · exact MergedCutProfiles.Batch117.valid4711
  · exact MergedCutProfiles.Batch117.valid4712
  · exact MergedCutProfiles.Batch117.valid4713
  · exact MergedCutProfiles.Batch117.valid4714
theorem numericValid702 : retention702.NumericValid := by decide +kernel
def certificate702 : RatCutBinCertificate := ⟨⟨retention702,(105932082452006859/50000000000000000),(19858540071699249/200000000000000000),(1546784460960759961/125000000000000000),(17880499278205887779/62500000000000000),(1918862311830732787/1000000000000000000)⟩,(993307171608962287/1000000000000000000),(385504142630617413/1000000000000000000),(247029945042786053/1000000000000000000),(17479738763456459/125000000000000000)⟩
theorem valid702 : certificate702.Valid := by decide +kernel
theorem sound702 : certificate702.Sound := rat_cut_bin_certificate_sound certificate702 profilesValid702 numericValid702 valid702

def retention703 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(1585566832097651923/5763808084572148678),(448094983552925409/250000000000000000),(33/20),(466814836872639409113/320000000000000000000),true,MergedCutProfiles.Batch117.profile4715,![MergedCutProfiles.Batch117.profile4715,MergedCutProfiles.Batch117.profile4716,MergedCutProfiles.Batch117.profile4717,MergedCutProfiles.Batch117.profile4718,MergedCutProfiles.Batch117.profile4719,MergedCutProfiles.Batch118.profile4720,MergedCutProfiles.Batch118.profile4721,MergedCutProfiles.Batch118.profile4722,MergedCutProfiles.Batch118.profile4723,MergedCutProfiles.Batch118.profile4724,MergedCutProfiles.Batch118.profile4725,MergedCutProfiles.Batch118.profile4726,MergedCutProfiles.Batch118.profile4727,MergedCutProfiles.Batch118.profile4728,MergedCutProfiles.Batch118.profile4729,MergedCutProfiles.Batch118.profile4730]⟩
theorem profilesValid703 : retention703.ProfilesValid := by
  change ∀ j : Fin 16, (retention703.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch117.valid4715
  · exact MergedCutProfiles.Batch117.valid4716
  · exact MergedCutProfiles.Batch117.valid4717
  · exact MergedCutProfiles.Batch117.valid4718
  · exact MergedCutProfiles.Batch117.valid4719
  · exact MergedCutProfiles.Batch118.valid4720
  · exact MergedCutProfiles.Batch118.valid4721
  · exact MergedCutProfiles.Batch118.valid4722
  · exact MergedCutProfiles.Batch118.valid4723
  · exact MergedCutProfiles.Batch118.valid4724
  · exact MergedCutProfiles.Batch118.valid4725
  · exact MergedCutProfiles.Batch118.valid4726
  · exact MergedCutProfiles.Batch118.valid4727
  · exact MergedCutProfiles.Batch118.valid4728
  · exact MergedCutProfiles.Batch118.valid4729
  · exact MergedCutProfiles.Batch118.valid4730
theorem numericValid703 : retention703.NumericValid := by decide +kernel
def certificate703 : RatCutBinCertificate := ⟨⟨retention703,(105932082452006859/50000000000000000),(19858540071699249/200000000000000000),(1546784460960759961/125000000000000000),(17880499278205887779/62500000000000000),(357685669542338613/250000000000000000)⟩,(993307171608962287/1000000000000000000),(84989126837218983/200000000000000000),(211387803065545993/1000000000000000000),(2197640843182519/15625000000000000)⟩
theorem valid703 : certificate703.Valid := by decide +kernel
theorem sound703 : certificate703.Sound := rat_cut_bin_certificate_sound certificate703 profilesValid703 numericValid703 valid703

def retention704 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(10640351633797305461/23055232338288594712),(1585566832097651923/250000000000000000),1,(66269619968444938543/64000000000000000000),true,MergedCutProfiles.Batch117.profile4693,![MergedCutProfiles.Batch117.profile4693,MergedCutProfiles.Batch118.profile4731,MergedCutProfiles.Batch118.profile4732,MergedCutProfiles.Batch118.profile4733,MergedCutProfiles.Batch118.profile4734,MergedCutProfiles.Batch118.profile4735,MergedCutProfiles.Batch118.profile4736,MergedCutProfiles.Batch118.profile4737,MergedCutProfiles.Batch118.profile4738,MergedCutProfiles.Batch118.profile4739,MergedCutProfiles.Batch118.profile4740,MergedCutProfiles.Batch118.profile4741,MergedCutProfiles.Batch118.profile4742,MergedCutProfiles.Batch118.profile4743,MergedCutProfiles.Batch118.profile4744,MergedCutProfiles.Batch118.profile4745]⟩
theorem profilesValid704 : retention704.ProfilesValid := by
  change ∀ j : Fin 16, (retention704.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch117.valid4693
  · exact MergedCutProfiles.Batch118.valid4731
  · exact MergedCutProfiles.Batch118.valid4732
  · exact MergedCutProfiles.Batch118.valid4733
  · exact MergedCutProfiles.Batch118.valid4734
  · exact MergedCutProfiles.Batch118.valid4735
  · exact MergedCutProfiles.Batch118.valid4736
  · exact MergedCutProfiles.Batch118.valid4737
  · exact MergedCutProfiles.Batch118.valid4738
  · exact MergedCutProfiles.Batch118.valid4739
  · exact MergedCutProfiles.Batch118.valid4740
  · exact MergedCutProfiles.Batch118.valid4741
  · exact MergedCutProfiles.Batch118.valid4742
  · exact MergedCutProfiles.Batch118.valid4743
  · exact MergedCutProfiles.Batch118.valid4744
  · exact MergedCutProfiles.Batch118.valid4745
theorem numericValid704 : retention704.NumericValid := by decide +kernel
def certificate704 : RatCutBinCertificate := ⟨⟨retention704,(105932082452006859/50000000000000000),(19858540071699249/200000000000000000),(1546784460960759961/125000000000000000),(17880499278205887779/62500000000000000),(1018461642188154661/1000000000000000000)⟩,(993307171608962287/1000000000000000000),(15256403714023403/31250000000000000),(161742291156326027/1000000000000000000),(140911848675603247/1000000000000000000)⟩
theorem valid704 : certificate704.Valid := by decide +kernel
theorem sound704 : certificate704.Sound := rat_cut_bin_certificate_sound certificate704 profilesValid704 numericValid704 valid704

def retention705 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(11407897145443673219/23055232338288594712),(10640351633797305461/1000000000000000000),(21/20),(17135726903075707110679774752546317293439/17024562614075688737600000000000000000000),false,MergedCutProfiles.Batch118.profile4746,(fun _ => MergedCutProfiles.Batch118.profile4746)⟩
theorem profilesValid705 : retention705.ProfilesValid := by
  exact MergedCutProfiles.Batch118.valid4746
theorem numericValid705 : retention705.NumericValid := by decide +kernel
def certificate705 : RatCutBinCertificate := ⟨⟨retention705,(105932082452006859/50000000000000000),(19858540071699249/200000000000000000),(1546784460960759961/125000000000000000),(17880499278205887779/62500000000000000),(123584854425700357/125000000000000000)⟩,(993307171608962287/1000000000000000000),(30317689265943627/62500000000000000),(163990743495625953/1000000000000000000),(70706464748576051/500000000000000000)⟩
theorem valid705 : certificate705.Valid := by decide +kernel
theorem sound705 : certificate705.Sound := rat_cut_bin_certificate_sound certificate705 profilesValid705 numericValid705 valid705

def retention706 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(1440247014612263744/2881904042286074339),(11407897145443673219/1000000000000000000),(21/20),(18215049196280059497524129400942466115399/18252635432709877150400000000000000000000),false,MergedCutProfiles.Batch118.profile4747,(fun _ => MergedCutProfiles.Batch118.profile4747)⟩
theorem profilesValid706 : retention706.ProfilesValid := by
  exact MergedCutProfiles.Batch118.valid4747
theorem numericValid706 : retention706.NumericValid := by decide +kernel
def certificate706 : RatCutBinCertificate := ⟨⟨retention706,(105932082452006859/50000000000000000),(19858540071699249/200000000000000000),(1546784460960759961/125000000000000000),(17880499278205887779/62500000000000000),(19601800177378949/20000000000000000)⟩,(993307171608962287/1000000000000000000),(487548407391802977/1000000000000000000),(32442692574263957/200000000000000000),(34871306374248211/250000000000000000)⟩
theorem valid706 : certificate706.Valid := by decide +kernel
theorem sound706 : certificate706.Sound := rat_cut_bin_certificate_sound certificate706 profilesValid706 numericValid706 valid706

def retention707 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(1/2),(22503859603316621/1953125000000000),(21/20),(1122499670030005043703147046585894679/1125192980165831050000000000000000000),false,MergedCutProfiles.Batch118.profile4748,(fun _ => MergedCutProfiles.Batch118.profile4748)⟩
theorem profilesValid707 : retention707.ProfilesValid := by
  exact MergedCutProfiles.Batch118.valid4748
theorem numericValid707 : retention707.NumericValid := by decide +kernel
def certificate707 : RatCutBinCertificate := ⟨⟨retention707,(105932082452006859/50000000000000000),(19858540071699249/200000000000000000),(1546784460960759961/125000000000000000),(17880499278205887779/62500000000000000),(489877796786990879/500000000000000000)⟩,(993307171608962287/1000000000000000000),(487469659234527457/1000000000000000000),(162270038990232659/1000000000000000000),(139589970151926793/1000000000000000000)⟩
theorem valid707 : certificate707.Valid := by decide +kernel
theorem sound707 : certificate707.Sound := rat_cut_bin_certificate_sound certificate707 profilesValid707 numericValid707 valid707

def certificates : List RatCutBinCertificate := [certificate696,certificate697,certificate698,certificate699,certificate700,certificate701,certificate702,certificate703,certificate704,certificate705,certificate706,certificate707]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound696,List.forall_mem_cons.mpr ⟨sound697,List.forall_mem_cons.mpr ⟨sound698,List.forall_mem_cons.mpr ⟨sound699,List.forall_mem_cons.mpr ⟨sound700,List.forall_mem_cons.mpr ⟨sound701,List.forall_mem_cons.mpr ⟨sound702,List.forall_mem_cons.mpr ⟨sound703,List.forall_mem_cons.mpr ⟨sound704,List.forall_mem_cons.mpr ⟨sound705,List.forall_mem_cons.mpr ⟨sound706,List.forall_mem_cons.mpr ⟨sound707,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch058
