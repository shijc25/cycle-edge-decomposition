import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch118
import Cycle12.MergedCutProfiles.Batch119
import Cycle12.MergedCutProfiles.Batch120

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch059

def retention708 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(10305505926944312503/23055232338288594712),(1849003878437226449/500000000000000000),(6/5),(101625997959325364833384907513593648079/92450193921861322450000000000000000000),false,MergedCutProfiles.Batch118.profile4749,(fun _ => MergedCutProfiles.Batch118.profile4749)⟩
theorem profilesValid708 : retention708.ProfilesValid := by
  exact MergedCutProfiles.Batch118.valid4749
theorem numericValid708 : retention708.NumericValid := by decide +kernel
def certificate708 : RatCutBinCertificate := ⟨⟨retention708,(124982427752006859/50000000000000000),(19858540071699249/200000000000000000),(1546784460960759961/125000000000000000),(17880499278205887779/62500000000000000),(1075180457730978879/1000000000000000000)⟩,(496051271949990771/500000000000000000),(382191487813902389/1000000000000000000),(50040327701032711/200000000000000000),(184910250508201373/1000000000000000000)⟩
theorem valid708 : certificate708.Valid := by decide +kernel
theorem sound708 : certificate708.Sound := rat_cut_bin_certificate_sound certificate708 profilesValid708 numericValid708 valid708

def retention709 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(18390452117058145/37245932695135048),(10305505926944312503/1000000000000000000),(21/20),(16620923525348258107081175416319577606911/16488809483110900004800000000000000000000),false,MergedCutProfiles.Batch118.profile4750,(fun _ => MergedCutProfiles.Batch118.profile4750)⟩
theorem profilesValid709 : retention709.ProfilesValid := by
  exact MergedCutProfiles.Batch118.valid4750
theorem numericValid709 : retention709.NumericValid := by decide +kernel
def certificate709 : RatCutBinCertificate := ⟨⟨retention709,(124982427752006859/50000000000000000),(19858540071699249/200000000000000000),(1546784460960759961/125000000000000000),(17880499278205887779/62500000000000000),(493475655235903747/500000000000000000)⟩,(496051271949990771/500000000000000000),(41635774171290649/100000000000000000),(218824447352204257/1000000000000000000),(187689549674915997/1000000000000000000)⟩
theorem valid709 : certificate709.Valid := by decide +kernel
theorem sound709 : certificate709.Sound := rat_cut_bin_certificate_sound certificate709 profilesValid709 numericValid709 valid709

def retention710 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(11497526759063581673/23055232338288594712),(2276737972091798351/200000000000000000),(21/20),(728551200838235390596192768585639431839/728556151069375472320000000000000000000),false,MergedCutProfiles.Batch118.profile4751,(fun _ => MergedCutProfiles.Batch118.profile4751)⟩
theorem profilesValid710 : retention710.ProfilesValid := by
  exact MergedCutProfiles.Batch118.valid4751
theorem numericValid710 : retention710.NumericValid := by decide +kernel
def certificate710 : RatCutBinCertificate := ⟨⟨retention710,(124982427752006859/50000000000000000),(19858540071699249/200000000000000000),(1546784460960759961/125000000000000000),(17880499278205887779/62500000000000000),(978932234144080501/1000000000000000000)⟩,(496051271949990771/500000000000000000),(419768401198805519/1000000000000000000),(107925002677340919/500000000000000000),(92574853526647937/500000000000000000)⟩
theorem valid710 : certificate710.Valid := by decide +kernel
theorem sound710 : certificate710.Sound := rat_cut_bin_certificate_sound certificate710 profilesValid710 numericValid710 valid710

def retention711 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(1/2),(11497526759063581673/1000000000000000000),(21/20),(18351438969525263304508118431704198702831/18396042814501730676800000000000000000000),false,MergedCutProfiles.Batch118.profile4748,(fun _ => MergedCutProfiles.Batch118.profile4748)⟩
theorem profilesValid711 : retention711.ProfilesValid := by
  exact MergedCutProfiles.Batch118.valid4748
theorem numericValid711 : retention711.NumericValid := by decide +kernel
def certificate711 : RatCutBinCertificate := ⟨⟨retention711,(124982427752006859/50000000000000000),(19858540071699249/200000000000000000),(1546784460960759961/125000000000000000),(17880499278205887779/62500000000000000),(488257195655980757/500000000000000000)⟩,(496051271949990771/500000000000000000),(1315024202614899/3125000000000000),(26868638736185087/125000000000000000),(184086505694702757/1000000000000000000)⟩
theorem valid711 : certificate711.Valid := by decide +kernel
theorem sound711 : certificate711.Sound := rat_cut_bin_certificate_sound certificate711 profilesValid711 numericValid711 valid711

def retention712 : RatCutRetentionCertificate := ⟨(23/500),(37/800),(837724156380069776/22774827094450476843),(829429857802049283/1000000000000000000),3,(33663635385964754979/16000000000000000000),true,MergedCutProfiles.Batch118.profile4752,![MergedCutProfiles.Batch118.profile4752,MergedCutProfiles.Batch118.profile4753,MergedCutProfiles.Batch118.profile4754,MergedCutProfiles.Batch118.profile4755,MergedCutProfiles.Batch118.profile4756,MergedCutProfiles.Batch118.profile4757,MergedCutProfiles.Batch118.profile4758,MergedCutProfiles.Batch118.profile4759,MergedCutProfiles.Batch119.profile4760,MergedCutProfiles.Batch119.profile4761,MergedCutProfiles.Batch119.profile4762,MergedCutProfiles.Batch119.profile4763,MergedCutProfiles.Batch119.profile4764,MergedCutProfiles.Batch119.profile4765,MergedCutProfiles.Batch119.profile4766,MergedCutProfiles.Batch119.profile4767]⟩
theorem profilesValid712 : retention712.ProfilesValid := by
  change ∀ j : Fin 16, (retention712.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch118.valid4752
  · exact MergedCutProfiles.Batch118.valid4753
  · exact MergedCutProfiles.Batch118.valid4754
  · exact MergedCutProfiles.Batch118.valid4755
  · exact MergedCutProfiles.Batch118.valid4756
  · exact MergedCutProfiles.Batch118.valid4757
  · exact MergedCutProfiles.Batch118.valid4758
  · exact MergedCutProfiles.Batch118.valid4759
  · exact MergedCutProfiles.Batch119.valid4760
  · exact MergedCutProfiles.Batch119.valid4761
  · exact MergedCutProfiles.Batch119.valid4762
  · exact MergedCutProfiles.Batch119.valid4763
  · exact MergedCutProfiles.Batch119.valid4764
  · exact MergedCutProfiles.Batch119.valid4765
  · exact MergedCutProfiles.Batch119.valid4766
  · exact MergedCutProfiles.Batch119.valid4767
theorem numericValid712 : retention712.NumericValid := by decide +kernel
def certificate712 : RatCutBinCertificate := ⟨⟨retention712,(1063479516989765619/500000000000000000),(100499784855757983/1000000000000000000),(311855683291598777/25000000000000000),(284495464265982334187/1000000000000000000),(128285111079830831/62500000000000000)⟩,(496630485685780807/500000000000000000),(190523732941024219/500000000000000000),(251303632388345719/1000000000000000000),(33446225101316287/250000000000000000)⟩
theorem valid712 : certificate712.Valid := by decide +kernel
theorem sound712 : certificate712.Sound := rat_cut_bin_certificate_sound certificate712 profilesValid712 numericValid712 valid712

def retention713 : RatCutRetentionCertificate := ⟨(23/500),(37/800),(290473248000000000/7591609031483492281),(52357759773754361/62500000000000000),(59/20),(41871891302698487581/20000000000000000000),true,MergedCutProfiles.Batch119.profile4768,![MergedCutProfiles.Batch119.profile4768,MergedCutProfiles.Batch119.profile4769,MergedCutProfiles.Batch119.profile4770,MergedCutProfiles.Batch119.profile4771,MergedCutProfiles.Batch119.profile4772,MergedCutProfiles.Batch119.profile4773,MergedCutProfiles.Batch119.profile4774,MergedCutProfiles.Batch119.profile4775,MergedCutProfiles.Batch119.profile4776,MergedCutProfiles.Batch119.profile4777,MergedCutProfiles.Batch119.profile4778,MergedCutProfiles.Batch119.profile4779,MergedCutProfiles.Batch119.profile4780,MergedCutProfiles.Batch119.profile4781,MergedCutProfiles.Batch119.profile4782,MergedCutProfiles.Batch119.profile4783]⟩
theorem profilesValid713 : retention713.ProfilesValid := by
  change ∀ j : Fin 16, (retention713.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch119.valid4768
  · exact MergedCutProfiles.Batch119.valid4769
  · exact MergedCutProfiles.Batch119.valid4770
  · exact MergedCutProfiles.Batch119.valid4771
  · exact MergedCutProfiles.Batch119.valid4772
  · exact MergedCutProfiles.Batch119.valid4773
  · exact MergedCutProfiles.Batch119.valid4774
  · exact MergedCutProfiles.Batch119.valid4775
  · exact MergedCutProfiles.Batch119.valid4776
  · exact MergedCutProfiles.Batch119.valid4777
  · exact MergedCutProfiles.Batch119.valid4778
  · exact MergedCutProfiles.Batch119.valid4779
  · exact MergedCutProfiles.Batch119.valid4780
  · exact MergedCutProfiles.Batch119.valid4781
  · exact MergedCutProfiles.Batch119.valid4782
  · exact MergedCutProfiles.Batch119.valid4783
theorem numericValid713 : retention713.NumericValid := by decide +kernel
def certificate713 : RatCutBinCertificate := ⟨⟨retention713,(1063479516989765619/500000000000000000),(100499784855757983/1000000000000000000),(311855683291598777/25000000000000000),(284495464265982334187/1000000000000000000),(2043036005317353939/1000000000000000000)⟩,(496630485685780807/500000000000000000),(381225174376364927/1000000000000000000),(62783056871721827/250000000000000000),(134770338276476441/1000000000000000000)⟩
theorem valid713 : certificate713.Valid := by decide +kernel
theorem sound713 : certificate713.Sound := rat_cut_bin_certificate_sound certificate713 profilesValid713 numericValid713 valid713

def retention714 : RatCutRetentionCertificate := ⟨(23/500),(37/800),(934622324510149549/22774827094450476843),(27231867/31250000),(29/10),(16726254644424575263/8000000000000000000),true,MergedCutProfiles.Batch119.profile4784,![MergedCutProfiles.Batch119.profile4784,MergedCutProfiles.Batch119.profile4785,MergedCutProfiles.Batch119.profile4786,MergedCutProfiles.Batch119.profile4787,MergedCutProfiles.Batch119.profile4788,MergedCutProfiles.Batch119.profile4789,MergedCutProfiles.Batch119.profile4790,MergedCutProfiles.Batch119.profile4791,MergedCutProfiles.Batch119.profile4792,MergedCutProfiles.Batch119.profile4793,MergedCutProfiles.Batch119.profile4794,MergedCutProfiles.Batch119.profile4795,MergedCutProfiles.Batch119.profile4796,MergedCutProfiles.Batch119.profile4797,MergedCutProfiles.Batch119.profile4798,MergedCutProfiles.Batch119.profile4799]⟩
theorem profilesValid714 : retention714.ProfilesValid := by
  change ∀ j : Fin 16, (retention714.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch119.valid4784
  · exact MergedCutProfiles.Batch119.valid4785
  · exact MergedCutProfiles.Batch119.valid4786
  · exact MergedCutProfiles.Batch119.valid4787
  · exact MergedCutProfiles.Batch119.valid4788
  · exact MergedCutProfiles.Batch119.valid4789
  · exact MergedCutProfiles.Batch119.valid4790
  · exact MergedCutProfiles.Batch119.valid4791
  · exact MergedCutProfiles.Batch119.valid4792
  · exact MergedCutProfiles.Batch119.valid4793
  · exact MergedCutProfiles.Batch119.valid4794
  · exact MergedCutProfiles.Batch119.valid4795
  · exact MergedCutProfiles.Batch119.valid4796
  · exact MergedCutProfiles.Batch119.valid4797
  · exact MergedCutProfiles.Batch119.valid4798
  · exact MergedCutProfiles.Batch119.valid4799
theorem numericValid714 : retention714.NumericValid := by decide +kernel
def certificate714 : RatCutBinCertificate := ⟨⟨retention714,(1063479516989765619/500000000000000000),(100499784855757983/1000000000000000000),(311855683291598777/25000000000000000),(284495464265982334187/1000000000000000000),(510270088103790243/250000000000000000)⟩,(496630485685780807/500000000000000000),(375401797728175471/1000000000000000000),(64198088511688899/250000000000000000),(17530386270418963/125000000000000000)⟩
theorem valid714 : certificate714.Valid := by decide +kernel
theorem sound714 : certificate714.Sound := rat_cut_bin_certificate_sound certificate714 profilesValid714 numericValid714 valid714

def retention715 : RatCutRetentionCertificate := ⟨(23/500),(37/800),(71753451636165039/1084515575926213183),(934622324510149549/1000000000000000000),(27/10),(640620638252962503517/320000000000000000000),true,MergedCutProfiles.Batch120.profile4800,![MergedCutProfiles.Batch120.profile4800,MergedCutProfiles.Batch120.profile4801,MergedCutProfiles.Batch120.profile4802,MergedCutProfiles.Batch120.profile4803,MergedCutProfiles.Batch119.profile4760,MergedCutProfiles.Batch120.profile4804,MergedCutProfiles.Batch120.profile4805,MergedCutProfiles.Batch120.profile4806,MergedCutProfiles.Batch120.profile4807,MergedCutProfiles.Batch120.profile4808,MergedCutProfiles.Batch120.profile4809,MergedCutProfiles.Batch120.profile4810,MergedCutProfiles.Batch120.profile4811,MergedCutProfiles.Batch120.profile4812,MergedCutProfiles.Batch120.profile4813,MergedCutProfiles.Batch120.profile4814]⟩
theorem profilesValid715 : retention715.ProfilesValid := by
  change ∀ j : Fin 16, (retention715.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch120.valid4800
  · exact MergedCutProfiles.Batch120.valid4801
  · exact MergedCutProfiles.Batch120.valid4802
  · exact MergedCutProfiles.Batch120.valid4803
  · exact MergedCutProfiles.Batch119.valid4760
  · exact MergedCutProfiles.Batch120.valid4804
  · exact MergedCutProfiles.Batch120.valid4805
  · exact MergedCutProfiles.Batch120.valid4806
  · exact MergedCutProfiles.Batch120.valid4807
  · exact MergedCutProfiles.Batch120.valid4808
  · exact MergedCutProfiles.Batch120.valid4809
  · exact MergedCutProfiles.Batch120.valid4810
  · exact MergedCutProfiles.Batch120.valid4811
  · exact MergedCutProfiles.Batch120.valid4812
  · exact MergedCutProfiles.Batch120.valid4813
  · exact MergedCutProfiles.Batch120.valid4814
theorem numericValid715 : retention715.NumericValid := by decide +kernel
def certificate715 : RatCutBinCertificate := ⟨⟨retention715,(1063479516989765619/500000000000000000),(100499784855757983/1000000000000000000),(311855683291598777/25000000000000000),(284495464265982334187/1000000000000000000),(48891642380716629/25000000000000000)⟩,(496630485685780807/500000000000000000),(95234676549008531/250000000000000000),(3142607188133567/12500000000000000),(70183446844285409/500000000000000000)⟩
theorem valid715 : certificate715.Valid := by decide +kernel
theorem sound715 : certificate715.Sound := rat_cut_bin_certificate_sound certificate715 profilesValid715 numericValid715 valid715

def retention716 : RatCutRetentionCertificate := ⟨(23/500),(37/800),(1707928999158302787/7591609031483492281),(1506822484359465819/1000000000000000000),(19/10),(951065058229933717156931849276816663159/602728993743786327600000000000000000000),false,MergedCutProfiles.Batch120.profile4815,(fun _ => MergedCutProfiles.Batch120.profile4815)⟩
theorem profilesValid716 : retention716.ProfilesValid := by
  exact MergedCutProfiles.Batch120.valid4815
theorem numericValid716 : retention716.NumericValid := by decide +kernel
def certificate716 : RatCutBinCertificate := ⟨⟨retention716,(1063479516989765619/500000000000000000),(100499784855757983/1000000000000000000),(311855683291598777/25000000000000000),(284495464265982334187/1000000000000000000),(309073796987951509/200000000000000000)⟩,(496630485685780807/500000000000000000),(410128589720613139/1000000000000000000),(56082288528860911/250000000000000000),(70492212311578369/500000000000000000)⟩
theorem valid716 : certificate716.Valid := by decide +kernel
theorem sound716 : certificate716.Sound := rat_cut_bin_certificate_sound certificate716 profilesValid716 numericValid716 valid716

def retention717 : RatCutRetentionCertificate := ⟨(23/500),(37/800),(1454346259404981128/3253546727778639549),(5123786997474908361/1000000000000000000),(21/20),(1375051410524778702849/1280000000000000000000),true,MergedCutProfiles.Batch120.profile4816,![MergedCutProfiles.Batch120.profile4816,MergedCutProfiles.Batch120.profile4817,MergedCutProfiles.Batch120.profile4818,MergedCutProfiles.Batch120.profile4819,MergedCutProfiles.Batch120.profile4820,MergedCutProfiles.Batch120.profile4821,MergedCutProfiles.Batch120.profile4822,MergedCutProfiles.Batch120.profile4823,MergedCutProfiles.Batch120.profile4824,MergedCutProfiles.Batch120.profile4825,MergedCutProfiles.Batch120.profile4826,MergedCutProfiles.Batch120.profile4827,MergedCutProfiles.Batch120.profile4828,MergedCutProfiles.Batch120.profile4829,MergedCutProfiles.Batch120.profile4830,MergedCutProfiles.Batch120.profile4831]⟩
theorem profilesValid717 : retention717.ProfilesValid := by
  change ∀ j : Fin 16, (retention717.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch120.valid4816
  · exact MergedCutProfiles.Batch120.valid4817
  · exact MergedCutProfiles.Batch120.valid4818
  · exact MergedCutProfiles.Batch120.valid4819
  · exact MergedCutProfiles.Batch120.valid4820
  · exact MergedCutProfiles.Batch120.valid4821
  · exact MergedCutProfiles.Batch120.valid4822
  · exact MergedCutProfiles.Batch120.valid4823
  · exact MergedCutProfiles.Batch120.valid4824
  · exact MergedCutProfiles.Batch120.valid4825
  · exact MergedCutProfiles.Batch120.valid4826
  · exact MergedCutProfiles.Batch120.valid4827
  · exact MergedCutProfiles.Batch120.valid4828
  · exact MergedCutProfiles.Batch120.valid4829
  · exact MergedCutProfiles.Batch120.valid4830
  · exact MergedCutProfiles.Batch120.valid4831
theorem numericValid717 : retention717.NumericValid := by decide +kernel
def certificate717 : RatCutBinCertificate := ⟨⟨retention717,(1063479516989765619/500000000000000000),(100499784855757983/1000000000000000000),(311855683291598777/25000000000000000),(284495464265982334187/1000000000000000000),(211252977083427461/200000000000000000)⟩,(496630485685780807/500000000000000000),(239331921095426117/500000000000000000),(168677249185146743/1000000000000000000),(35475959862707517/250000000000000000)⟩
theorem valid717 : certificate717.Valid := by decide +kernel
theorem sound717 : certificate717.Sound := rat_cut_bin_certificate_sound certificate717 profilesValid717 numericValid717 valid717

def retention718 : RatCutRetentionCertificate := ⟨(23/500),(37/800),(11245521393034356616/22774827094450476843),(1272552976979358487/125000000000000000),(21/20),(1025944286229250752064774255377400214399/1018042381583486789600000000000000000000),false,MergedCutProfiles.Batch120.profile4832,(fun _ => MergedCutProfiles.Batch120.profile4832)⟩
theorem profilesValid718 : retention718.ProfilesValid := by
  exact MergedCutProfiles.Batch120.valid4832
theorem numericValid718 : retention718.NumericValid := by decide +kernel
def certificate718 : RatCutBinCertificate := ⟨⟨retention718,(1063479516989765619/500000000000000000),(100499784855757983/1000000000000000000),(311855683291598777/25000000000000000),(284495464265982334187/1000000000000000000),(494884209965918397/500000000000000000)⟩,(496630485685780807/500000000000000000),(484019390815405783/1000000000000000000),(82380690011560589/500000000000000000),(70857449581213453/500000000000000000)⟩
theorem valid718 : certificate718.Valid := by decide +kernel
theorem sound718 : certificate718.Sound := rat_cut_bin_certificate_sound certificate718 profilesValid718 numericValid718 valid718

def retention719 : RatCutRetentionCertificate := ⟨(23/500),(37/800),(11357976606964700183/22774827094450476843),(1405690174129294577/125000000000000000),(21/20),(281077567973593645247869649301961618871/281138034825858915400000000000000000000),false,MergedCutProfiles.Batch120.profile4833,(fun _ => MergedCutProfiles.Batch120.profile4833)⟩
theorem profilesValid719 : retention719.ProfilesValid := by
  exact MergedCutProfiles.Batch120.valid4833
theorem numericValid719 : retention719.NumericValid := by decide +kernel
def certificate719 : RatCutBinCertificate := ⟨⟨retention719,(1063479516989765619/500000000000000000),(100499784855757983/1000000000000000000),(311855683291598777/25000000000000000),(284495464265982334187/1000000000000000000),(98179153520765457/100000000000000000)⟩,(496630485685780807/500000000000000000),(485358765070456279/1000000000000000000),(163791344943870977/1000000000000000000),(140914097243569197/1000000000000000000)⟩
theorem valid719 : certificate719.Valid := by decide +kernel
theorem sound719 : certificate719.Sound := rat_cut_bin_certificate_sound certificate719 profilesValid719 numericValid719 valid719

def certificates : List RatCutBinCertificate := [certificate708,certificate709,certificate710,certificate711,certificate712,certificate713,certificate714,certificate715,certificate716,certificate717,certificate718,certificate719]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound708,List.forall_mem_cons.mpr ⟨sound709,List.forall_mem_cons.mpr ⟨sound710,List.forall_mem_cons.mpr ⟨sound711,List.forall_mem_cons.mpr ⟨sound712,List.forall_mem_cons.mpr ⟨sound713,List.forall_mem_cons.mpr ⟨sound714,List.forall_mem_cons.mpr ⟨sound715,List.forall_mem_cons.mpr ⟨sound716,List.forall_mem_cons.mpr ⟨sound717,List.forall_mem_cons.mpr ⟨sound718,List.forall_mem_cons.mpr ⟨sound719,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch059
