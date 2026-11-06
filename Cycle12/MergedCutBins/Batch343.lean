import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch390
import Cycle12.MergedCutProfiles.Batch506
import Cycle12.MergedCutProfiles.Batch507
import Cycle12.MergedCutProfiles.Batch508
import Cycle12.MergedCutProfiles.Batch618
import Cycle12.MergedCutProfiles.Batch619
import Cycle12.MergedCutProfiles.Batch620

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch343

def retention4116 : RatCutRetentionCertificate := ⟨(109/2000),(11/200),(64000000000000000000/306286155555872753049),(2527807769359586691/100000000000000000),1,(40501825390707081423761576266375007051/25278077693595866910000000000000000000),false,MergedCutProfiles.Batch618.profile24742,(fun _ => MergedCutProfiles.Batch618.profile24742)⟩
theorem profilesValid4116 : retention4116.ProfilesValid := by
  exact MergedCutProfiles.Batch618.valid24742
theorem numericValid4116 : retention4116.NumericValid := by decide +kernel
def certificate4116 : RatCutBinCertificate := ⟨⟨retention4116,(377090286933863393/200000000000000000),(14887102204219317/100000000000000000),(14384765127274286941/1000000000000000000),(2209443003729267056791/500000000000000000),(1582738037443990579/1000000000000000000)⟩,(999635492700545069/1000000000000000000),(33760518500271813/1000000000000000000),(13021815332201833/15625000000000000),(1240860201074516681/1000000000000000000)⟩
theorem valid4116 : certificate4116.Valid := by decide +kernel
theorem sound4116 : certificate4116.Sound := rat_cut_bin_certificate_sound certificate4116 profilesValid4116 numericValid4116 valid4116

def retention4117 : RatCutRetentionCertificate := ⟨(109/2000),(11/200),(1/2),64,1,(255400295568475156950441867733842600231/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch618.profile24743,(fun _ => MergedCutProfiles.Batch618.profile24743)⟩
theorem profilesValid4117 : retention4117.ProfilesValid := by
  exact MergedCutProfiles.Batch618.valid24743
theorem numericValid4117 : retention4117.NumericValid := by decide +kernel
def certificate4117 : RatCutBinCertificate := ⟨⟨retention4117,(377090286933863393/200000000000000000),(14887102204219317/100000000000000000),(14384765127274286941/1000000000000000000),(2209443003729267056791/500000000000000000),(978144452676585061/1000000000000000000)⟩,(999635492700545069/1000000000000000000),(54627981223013949/1000000000000000000),(77606755294401659/100000000000000000),(373701744193116669/500000000000000000)⟩
theorem valid4117 : certificate4117.Valid := by decide +kernel
theorem sound4117 : certificate4117.Sound := rat_cut_bin_certificate_sound certificate4117 profilesValid4117 numericValid4117 valid4117

def retention4118 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(356601907078928095/146848210218663784712),(173057148871508469/250000000000000000),4,(4759300683906663537/2000000000000000000),true,MergedCutProfiles.Batch618.profile24744,![MergedCutProfiles.Batch618.profile24744,MergedCutProfiles.Batch618.profile24745,MergedCutProfiles.Batch618.profile24746,MergedCutProfiles.Batch618.profile24747,MergedCutProfiles.Batch618.profile24748,MergedCutProfiles.Batch618.profile24749,MergedCutProfiles.Batch507.profile20298,MergedCutProfiles.Batch618.profile24750,MergedCutProfiles.Batch618.profile24751,MergedCutProfiles.Batch618.profile24752,MergedCutProfiles.Batch618.profile24753,MergedCutProfiles.Batch618.profile24754,MergedCutProfiles.Batch618.profile24755,MergedCutProfiles.Batch506.profile20254,MergedCutProfiles.Batch618.profile24756,MergedCutProfiles.Batch618.profile24757]⟩
theorem profilesValid4118 : retention4118.ProfilesValid := by
  change ∀ j : Fin 16, (retention4118.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch618.valid24744
  · exact MergedCutProfiles.Batch618.valid24745
  · exact MergedCutProfiles.Batch618.valid24746
  · exact MergedCutProfiles.Batch618.valid24747
  · exact MergedCutProfiles.Batch618.valid24748
  · exact MergedCutProfiles.Batch618.valid24749
  · exact MergedCutProfiles.Batch507.valid20298
  · exact MergedCutProfiles.Batch618.valid24750
  · exact MergedCutProfiles.Batch618.valid24751
  · exact MergedCutProfiles.Batch618.valid24752
  · exact MergedCutProfiles.Batch618.valid24753
  · exact MergedCutProfiles.Batch618.valid24754
  · exact MergedCutProfiles.Batch618.valid24755
  · exact MergedCutProfiles.Batch506.valid20254
  · exact MergedCutProfiles.Batch618.valid24756
  · exact MergedCutProfiles.Batch618.valid24757
theorem numericValid4118 : retention4118.NumericValid := by decide +kernel
def certificate4118 : RatCutBinCertificate := ⟨⟨retention4118,(40101515667270571/20000000000000000),(155212952940275013/1000000000000000000),(14510694735717310067/1000000000000000000),(4287112671482551050437/1000000000000000000),(1146930215483000379/500000000000000000)⟩,(199920380111261873/200000000000000000),(67912551043380243/125000000000000000),(125235874023858759/1000000000000000000),(59467758474635857/1000000000000000000)⟩
theorem valid4118 : certificate4118.Valid := by decide +kernel
theorem sound4118 : certificate4118.Sound := rat_cut_bin_certificate_sound certificate4118 profilesValid4118 numericValid4118 valid4118

def retention4119 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(69045159937500000/18356026277332973089),(71320381415785619/100000000000000000),(79/20),(303356561944707537643/128000000000000000000),true,MergedCutProfiles.Batch618.profile24758,![MergedCutProfiles.Batch618.profile24758,MergedCutProfiles.Batch618.profile24759,MergedCutProfiles.Batch506.profile20252,MergedCutProfiles.Batch507.profile20283,MergedCutProfiles.Batch619.profile24760,MergedCutProfiles.Batch619.profile24761,MergedCutProfiles.Batch618.profile24753,MergedCutProfiles.Batch507.profile20284,MergedCutProfiles.Batch506.profile20254,MergedCutProfiles.Batch619.profile24762,MergedCutProfiles.Batch506.profile20270,MergedCutProfiles.Batch507.profile20285,MergedCutProfiles.Batch619.profile24763,MergedCutProfiles.Batch619.profile24764,MergedCutProfiles.Batch506.profile20271,MergedCutProfiles.Batch619.profile24765]⟩
theorem profilesValid4119 : retention4119.ProfilesValid := by
  change ∀ j : Fin 16, (retention4119.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch618.valid24758
  · exact MergedCutProfiles.Batch618.valid24759
  · exact MergedCutProfiles.Batch506.valid20252
  · exact MergedCutProfiles.Batch507.valid20283
  · exact MergedCutProfiles.Batch619.valid24760
  · exact MergedCutProfiles.Batch619.valid24761
  · exact MergedCutProfiles.Batch618.valid24753
  · exact MergedCutProfiles.Batch507.valid20284
  · exact MergedCutProfiles.Batch506.valid20254
  · exact MergedCutProfiles.Batch619.valid24762
  · exact MergedCutProfiles.Batch506.valid20270
  · exact MergedCutProfiles.Batch507.valid20285
  · exact MergedCutProfiles.Batch619.valid24763
  · exact MergedCutProfiles.Batch619.valid24764
  · exact MergedCutProfiles.Batch506.valid20271
  · exact MergedCutProfiles.Batch619.valid24765
theorem numericValid4119 : retention4119.NumericValid := by decide +kernel
def certificate4119 : RatCutBinCertificate := ⟨⟨retention4119,(40101515667270571/20000000000000000),(155212952940275013/1000000000000000000),(14510694735717310067/1000000000000000000),(4287112671482551050437/1000000000000000000),(2285255622061140597/1000000000000000000)⟩,(199920380111261873/200000000000000000),(267837801212826491/500000000000000000),(129941466551805937/1000000000000000000),(389618354804211/6250000000000000)⟩
theorem valid4119 : certificate4119.Valid := by decide +kernel
theorem sound4119 : certificate4119.Sound := rat_cut_bin_certificate_sound certificate4119 profilesValid4119 numericValid4119 valid4119

def retention4120 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(839115622392637493/146848210218663784712),(1104722559/1000000000),(27/10),(7433670862483014891/3200000000000000000),true,MergedCutProfiles.Batch619.profile24766,![MergedCutProfiles.Batch619.profile24766,MergedCutProfiles.Batch506.profile20252,MergedCutProfiles.Batch619.profile24767,MergedCutProfiles.Batch506.profile20253,MergedCutProfiles.Batch619.profile24768,MergedCutProfiles.Batch506.profile20254,MergedCutProfiles.Batch619.profile24769,MergedCutProfiles.Batch506.profile20255,MergedCutProfiles.Batch619.profile24770,MergedCutProfiles.Batch506.profile20256,MergedCutProfiles.Batch619.profile24771,MergedCutProfiles.Batch506.profile20257,MergedCutProfiles.Batch507.profile20287,MergedCutProfiles.Batch506.profile20258,MergedCutProfiles.Batch619.profile24772,MergedCutProfiles.Batch506.profile20259]⟩
theorem profilesValid4120 : retention4120.ProfilesValid := by
  change ∀ j : Fin 16, (retention4120.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch619.valid24766
  · exact MergedCutProfiles.Batch506.valid20252
  · exact MergedCutProfiles.Batch619.valid24767
  · exact MergedCutProfiles.Batch506.valid20253
  · exact MergedCutProfiles.Batch619.valid24768
  · exact MergedCutProfiles.Batch506.valid20254
  · exact MergedCutProfiles.Batch619.valid24769
  · exact MergedCutProfiles.Batch506.valid20255
  · exact MergedCutProfiles.Batch619.valid24770
  · exact MergedCutProfiles.Batch506.valid20256
  · exact MergedCutProfiles.Batch619.valid24771
  · exact MergedCutProfiles.Batch506.valid20257
  · exact MergedCutProfiles.Batch507.valid20287
  · exact MergedCutProfiles.Batch506.valid20258
  · exact MergedCutProfiles.Batch619.valid24772
  · exact MergedCutProfiles.Batch506.valid20259
theorem numericValid4120 : retention4120.NumericValid := by decide +kernel
def certificate4120 : RatCutBinCertificate := ⟨⟨retention4120,(40101515667270571/20000000000000000),(155212952940275013/1000000000000000000),(14510694735717310067/1000000000000000000),(4287112671482551050437/1000000000000000000),(2265114008891107997/1000000000000000000)⟩,(199920380111261873/200000000000000000),(213162661547407963/500000000000000000),(105104668648713699/500000000000000000),(137574259656516363/1000000000000000000)⟩
theorem valid4120 : certificate4120.Valid := by decide +kernel
theorem sound4120 : certificate4120.Sound := rat_cut_bin_certificate_sound certificate4120 profilesValid4120 numericValid4120 valid4120

def retention4121 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(35605210169935319945/293696420437327569424),(839115622392637493/500000000000000000),(41/20),(1248191335233427642031870670741247322631/671292497914109994400000000000000000000),false,MergedCutProfiles.Batch619.profile24773,(fun _ => MergedCutProfiles.Batch619.profile24773)⟩
theorem profilesValid4121 : retention4121.ProfilesValid := by
  exact MergedCutProfiles.Batch619.valid24773
theorem numericValid4121 : retention4121.NumericValid := by decide +kernel
def certificate4121 : RatCutBinCertificate := ⟨⟨retention4121,(40101515667270571/20000000000000000),(155212952940275013/1000000000000000000),(14510694735717310067/1000000000000000000),(4287112671482551050437/1000000000000000000),(1815417982432856001/1000000000000000000)⟩,(199920380111261873/200000000000000000),(6926502687281567/15625000000000000),(196074432701501087/1000000000000000000),(138028428100278331/1000000000000000000)⟩
theorem valid4121 : certificate4121.Valid := by decide +kernel
theorem sound4121 : certificate4121.Sound := rat_cut_bin_certificate_sound certificate4121 profilesValid4121 numericValid4121 valid4121

def retention4122 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(4000000000000000000/18356026277332973089),(7121042033987063989/200000000000000000),1,(9051628210902293768697035028202203163/5696833627189651191200000000000000000),false,MergedCutProfiles.Batch619.profile24774,(fun _ => MergedCutProfiles.Batch619.profile24774)⟩
theorem profilesValid4122 : retention4122.ProfilesValid := by
  exact MergedCutProfiles.Batch619.valid24774
theorem numericValid4122 : retention4122.NumericValid := by decide +kernel
def certificate4122 : RatCutBinCertificate := ⟨⟨retention4122,(40101515667270571/20000000000000000),(155212952940275013/1000000000000000000),(14510694735717310067/1000000000000000000),(4287112671482551050437/1000000000000000000),(391860090891607381/250000000000000000)⟩,(199920380111261873/200000000000000000),(325006551856174311/1000000000000000000),(154851839045984307/500000000000000000),(232392090369320251/500000000000000000)⟩
theorem valid4122 : certificate4122.Valid := by decide +kernel
theorem sound4122 : certificate4122.Sound := rat_cut_bin_certificate_sound certificate4122 profilesValid4122 numericValid4122 valid4122

def retention4123 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(1/2),64,1,(63850233265400851274717381691339297319/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch508.profile20331,(fun _ => MergedCutProfiles.Batch508.profile20331)⟩
theorem profilesValid4123 : retention4123.ProfilesValid := by
  exact MergedCutProfiles.Batch508.valid20331
theorem numericValid4123 : retention4123.NumericValid := by decide +kernel
def certificate4123 : RatCutBinCertificate := ⟨⟨retention4123,(40101515667270571/20000000000000000),(155212952940275013/1000000000000000000),(14510694735717310067/1000000000000000000),(4287112671482551050437/1000000000000000000),(19524253706444239/20000000000000000)⟩,(199920380111261873/200000000000000000),(515201991946880981/1000000000000000000),(143117955999589319/1000000000000000000),(13755913099630967/100000000000000000)⟩
theorem valid4123 : certificate4123.Valid := by decide +kernel
theorem sound4123 : certificate4123.Sound := rat_cut_bin_certificate_sound certificate4123 profilesValid4123 numericValid4123 valid4123

def retention4124 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(4000000000000000000/18356026277332973089),(6291194853624526439/250000000000000000),1,(31835751478637384000135298814370315363/20131823531598484604800000000000000000),false,MergedCutProfiles.Batch619.profile24774,(fun _ => MergedCutProfiles.Batch619.profile24774)⟩
theorem profilesValid4124 : retention4124.ProfilesValid := by
  exact MergedCutProfiles.Batch619.valid24774
theorem numericValid4124 : retention4124.NumericValid := by decide +kernel
def certificate4124 : RatCutBinCertificate := ⟨⟨retention4124,(37763882887270571/20000000000000000),(155212952940275013/1000000000000000000),(14510694735717310067/1000000000000000000),(4287112671482551050437/1000000000000000000),(62446700545140217/40000000000000000)⟩,(12495313855506251/12500000000000000),(17082494334298433/500000000000000000),(416118923342392117/500000000000000000),(305724172488163057/250000000000000000)⟩
theorem valid4124 : certificate4124.Valid := by decide +kernel
theorem sound4124 : certificate4124.Sound := rat_cut_bin_certificate_sound certificate4124 profilesValid4124 numericValid4124 valid4124

def retention4125 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(1/2),64,1,(63850233265400851274717381691339297319/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch508.profile20331,(fun _ => MergedCutProfiles.Batch508.profile20331)⟩
theorem profilesValid4125 : retention4125.ProfilesValid := by
  exact MergedCutProfiles.Batch508.valid20331
theorem numericValid4125 : retention4125.NumericValid := by decide +kernel
def certificate4125 : RatCutBinCertificate := ⟨⟨retention4125,(37763882887270571/20000000000000000),(155212952940275013/1000000000000000000),(14510694735717310067/1000000000000000000),(4287112671482551050437/1000000000000000000),(97746290489658101/100000000000000000)⟩,(12495313855506251/12500000000000000),(682088166027931/12500000000000000),(776228027451925411/1000000000000000000),(149407424293778169/200000000000000000)⟩
theorem valid4125 : certificate4125.Valid := by decide +kernel
theorem sound4125 : certificate4125.Sound := rat_cut_bin_certificate_sound certificate4125 profilesValid4125 numericValid4125 valid4125

def retention4126 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(355704617096674445/140896379138290870909),(352182789204628163/500000000000000000),(79/20),(1523621255646110497459/640000000000000000000),true,MergedCutProfiles.Batch619.profile24775,![MergedCutProfiles.Batch619.profile24775,MergedCutProfiles.Batch619.profile24776,MergedCutProfiles.Batch619.profile24777,MergedCutProfiles.Batch619.profile24778,MergedCutProfiles.Batch619.profile24779,MergedCutProfiles.Batch619.profile24780,MergedCutProfiles.Batch619.profile24781,MergedCutProfiles.Batch619.profile24782,MergedCutProfiles.Batch619.profile24783,MergedCutProfiles.Batch619.profile24784,MergedCutProfiles.Batch619.profile24785,MergedCutProfiles.Batch619.profile24786,MergedCutProfiles.Batch619.profile24787,MergedCutProfiles.Batch619.profile24788,MergedCutProfiles.Batch619.profile24789,MergedCutProfiles.Batch619.profile24790]⟩
theorem profilesValid4126 : retention4126.ProfilesValid := by
  change ∀ j : Fin 16, (retention4126.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch619.valid24775
  · exact MergedCutProfiles.Batch619.valid24776
  · exact MergedCutProfiles.Batch619.valid24777
  · exact MergedCutProfiles.Batch619.valid24778
  · exact MergedCutProfiles.Batch619.valid24779
  · exact MergedCutProfiles.Batch619.valid24780
  · exact MergedCutProfiles.Batch619.valid24781
  · exact MergedCutProfiles.Batch619.valid24782
  · exact MergedCutProfiles.Batch619.valid24783
  · exact MergedCutProfiles.Batch619.valid24784
  · exact MergedCutProfiles.Batch619.valid24785
  · exact MergedCutProfiles.Batch619.valid24786
  · exact MergedCutProfiles.Batch619.valid24787
  · exact MergedCutProfiles.Batch619.valid24788
  · exact MergedCutProfiles.Batch619.valid24789
  · exact MergedCutProfiles.Batch619.valid24790
theorem numericValid4126 : retention4126.NumericValid := by decide +kernel
def certificate4126 : RatCutBinCertificate := ⟨⟨retention4126,(100898051761738163/50000000000000000),(161735409484216873/1000000000000000000),(14767649492315503689/1000000000000000000),(837271614066183087231/200000000000000000),(45867182751714137/20000000000000000)⟩,(249898188644278969/250000000000000000),(264114008202401679/500000000000000000),(8415153559232041/62500000000000000),(4040295402477301/62500000000000000)⟩
theorem valid4126 : certificate4126.Valid := by decide +kernel
theorem sound4126 : certificate4126.Sound := rat_cut_bin_certificate_sound certificate4126 profilesValid4126 numericValid4126 valid4126

def retention4127 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(1080481155841704411/281792758276581741818),(71140923419334889/100000000000000000),(79/20),(12133917903100019913/5120000000000000000),true,MergedCutProfiles.Batch619.profile24791,![MergedCutProfiles.Batch619.profile24791,MergedCutProfiles.Batch619.profile24777,MergedCutProfiles.Batch619.profile24792,MergedCutProfiles.Batch619.profile24780,MergedCutProfiles.Batch619.profile24793,MergedCutProfiles.Batch619.profile24783,MergedCutProfiles.Batch619.profile24794,MergedCutProfiles.Batch619.profile24786,MergedCutProfiles.Batch390.profile15633,MergedCutProfiles.Batch619.profile24795,MergedCutProfiles.Batch619.profile24796,MergedCutProfiles.Batch619.profile24797,MergedCutProfiles.Batch619.profile24798,MergedCutProfiles.Batch619.profile24799,MergedCutProfiles.Batch620.profile24800,MergedCutProfiles.Batch620.profile24801]⟩
theorem profilesValid4127 : retention4127.ProfilesValid := by
  change ∀ j : Fin 16, (retention4127.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch619.valid24791
  · exact MergedCutProfiles.Batch619.valid24777
  · exact MergedCutProfiles.Batch619.valid24792
  · exact MergedCutProfiles.Batch619.valid24780
  · exact MergedCutProfiles.Batch619.valid24793
  · exact MergedCutProfiles.Batch619.valid24783
  · exact MergedCutProfiles.Batch619.valid24794
  · exact MergedCutProfiles.Batch619.valid24786
  · exact MergedCutProfiles.Batch390.valid15633
  · exact MergedCutProfiles.Batch619.valid24795
  · exact MergedCutProfiles.Batch619.valid24796
  · exact MergedCutProfiles.Batch619.valid24797
  · exact MergedCutProfiles.Batch619.valid24798
  · exact MergedCutProfiles.Batch619.valid24799
  · exact MergedCutProfiles.Batch620.valid24800
  · exact MergedCutProfiles.Batch620.valid24801
theorem numericValid4127 : retention4127.NumericValid := by decide +kernel
def certificate4127 : RatCutBinCertificate := ⟨⟨retention4127,(100898051761738163/50000000000000000),(161735409484216873/1000000000000000000),(14767649492315503689/1000000000000000000),(837271614066183087231/200000000000000000),(91304271123597631/40000000000000000)⟩,(249898188644278969/250000000000000000),(527581286508815409/1000000000000000000),(16881951651227043/125000000000000000),(15796282454313/244140625000000)⟩
theorem valid4127 : certificate4127.Valid := by decide +kernel
theorem sound4127 : certificate4127.Sound := rat_cut_bin_certificate_sound certificate4127 profilesValid4127 numericValid4127 valid4127

def certificates : List RatCutBinCertificate := [certificate4116,certificate4117,certificate4118,certificate4119,certificate4120,certificate4121,certificate4122,certificate4123,certificate4124,certificate4125,certificate4126,certificate4127]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4116,List.forall_mem_cons.mpr ⟨sound4117,List.forall_mem_cons.mpr ⟨sound4118,List.forall_mem_cons.mpr ⟨sound4119,List.forall_mem_cons.mpr ⟨sound4120,List.forall_mem_cons.mpr ⟨sound4121,List.forall_mem_cons.mpr ⟨sound4122,List.forall_mem_cons.mpr ⟨sound4123,List.forall_mem_cons.mpr ⟨sound4124,List.forall_mem_cons.mpr ⟨sound4125,List.forall_mem_cons.mpr ⟨sound4126,List.forall_mem_cons.mpr ⟨sound4127,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch343
