import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch015
import Cycle12.MergedCutProfiles.Batch016

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch007

def retention84 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(8000000000000000000/42638322951968710323),(11134578879319473663/1000000000000000000),(21/20),(29180095675573184131772305635202504375151/17815326206911157860800000000000000000000),false,MergedCutProfiles.Batch015.profile609,(fun _ => MergedCutProfiles.Batch015.profile609)⟩
theorem profilesValid84 : retention84.ProfilesValid := by
  exact MergedCutProfiles.Batch015.valid609
theorem numericValid84 : retention84.NumericValid := by decide +kernel
def certificate84 : RatCutBinCertificate := ⟨⟨retention84,(1872784232002174223/1000000000000000000),(21663071517499/3125000000000000),(7713422769448688937/1000000000000000000),(660788289044395744131/250000000000000000),(51129802253685319/31250000000000000)⟩,(499647813225836113/500000000000000000),(142828251082770919/500000000000000000),(89098038674546747/250000000000000000),(122418319488816291/250000000000000000)⟩
theorem valid84 : certificate84.Valid := by decide +kernel
theorem sound84 : certificate84.Sound := rat_cut_bin_certificate_sound certificate84 profilesValid84 numericValid84 valid84

def retention85 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(1/2),64,1,(63842362441861810878166029772824077959/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch015.profile610,(fun _ => MergedCutProfiles.Batch015.profile610)⟩
theorem profilesValid85 : retention85.ProfilesValid := by
  exact MergedCutProfiles.Batch015.valid610
theorem numericValid85 : retention85.NumericValid := by decide +kernel
def certificate85 : RatCutBinCertificate := ⟨⟨retention85,(1872784232002174223/1000000000000000000),(21663071517499/3125000000000000),(7713422769448688937/1000000000000000000),(660788289044395744131/250000000000000000),(995853810370597019/1000000000000000000)⟩,(499647813225836113/500000000000000000),(434849986385790421/1000000000000000000),(203026420755368811/1000000000000000000),(39789080552462297/200000000000000000)⟩
theorem valid85 : certificate85.Valid := by decide +kernel
theorem sound85 : certificate85.Sound := rat_cut_bin_certificate_sound certificate85 profilesValid85 numericValid85 valid85

def retention86 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(8000000000000000000/42638322951968710323),(3337885108138372131/1000000000000000000),(27/20),(8796019499074582244316894537756769023191/5340616173021395409600000000000000000000),false,MergedCutProfiles.Batch015.profile609,(fun _ => MergedCutProfiles.Batch015.profile609)⟩
theorem profilesValid86 : retention86.ProfilesValid := by
  exact MergedCutProfiles.Batch015.valid609
theorem numericValid86 : retention86.NumericValid := by decide +kernel
def certificate86 : RatCutBinCertificate := ⟨⟨retention86,(2233742459002174223/1000000000000000000),(21663071517499/3125000000000000),(7713422769448688937/1000000000000000000),(660788289044395744131/250000000000000000),(411073622157659753/250000000000000000)⟩,(62447491603012969/62500000000000000),(242778909146471773/1000000000000000000),(4134402669224541/10000000000000000),(79211729990623999/200000000000000000)⟩
theorem valid86 : certificate86.Valid := by decide +kernel
theorem sound86 : certificate86.Sound := rat_cut_bin_certificate_sound certificate86 profilesValid86 numericValid86 valid86

def retention87 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(1/2),64,1,(63842362441861810878166029772824077959/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch015.profile610,(fun _ => MergedCutProfiles.Batch015.profile610)⟩
theorem profilesValid87 : retention87.ProfilesValid := by
  exact MergedCutProfiles.Batch015.valid610
theorem numericValid87 : retention87.NumericValid := by decide +kernel
def certificate87 : RatCutBinCertificate := ⟨⟨retention87,(2233742459002174223/1000000000000000000),(21663071517499/3125000000000000),(7713422769448688937/1000000000000000000),(660788289044395744131/250000000000000000),(248882352780641123/250000000000000000)⟩,(62447491603012969/62500000000000000),(400992695750858843/1000000000000000000),(232574035802033479/1000000000000000000),(227795030714001551/1000000000000000000)⟩
theorem valid87 : certificate87.Valid := by decide +kernel
theorem sound87 : certificate87.Sound := rat_cut_bin_certificate_sound certificate87 profilesValid87 numericValid87 valid87

def retention88 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(628132703644681829/292768462186150238680),(76207426718585373/125000000000000000),4,(14425394571358497567/6400000000000000000),true,MergedCutProfiles.Batch015.profile611,![MergedCutProfiles.Batch015.profile611,MergedCutProfiles.Batch015.profile612,MergedCutProfiles.Batch015.profile613,MergedCutProfiles.Batch015.profile614,MergedCutProfiles.Batch015.profile615,MergedCutProfiles.Batch015.profile616,MergedCutProfiles.Batch015.profile617,MergedCutProfiles.Batch015.profile618,MergedCutProfiles.Batch015.profile619,MergedCutProfiles.Batch015.profile620,MergedCutProfiles.Batch015.profile621,MergedCutProfiles.Batch015.profile622,MergedCutProfiles.Batch015.profile623,MergedCutProfiles.Batch015.profile624,MergedCutProfiles.Batch015.profile625,MergedCutProfiles.Batch015.profile626]⟩
theorem profilesValid88 : retention88.ProfilesValid := by
  change ∀ j : Fin 16, (retention88.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch015.valid611
  · exact MergedCutProfiles.Batch015.valid612
  · exact MergedCutProfiles.Batch015.valid613
  · exact MergedCutProfiles.Batch015.valid614
  · exact MergedCutProfiles.Batch015.valid615
  · exact MergedCutProfiles.Batch015.valid616
  · exact MergedCutProfiles.Batch015.valid617
  · exact MergedCutProfiles.Batch015.valid618
  · exact MergedCutProfiles.Batch015.valid619
  · exact MergedCutProfiles.Batch015.valid620
  · exact MergedCutProfiles.Batch015.valid621
  · exact MergedCutProfiles.Batch015.valid622
  · exact MergedCutProfiles.Batch015.valid623
  · exact MergedCutProfiles.Batch015.valid624
  · exact MergedCutProfiles.Batch015.valid625
  · exact MergedCutProfiles.Batch015.valid626
theorem numericValid88 : retention88.NumericValid := by decide +kernel
def certificate88 : RatCutBinCertificate := ⟨⟨retention88,(1880388806451898253/1000000000000000000),(1008381335301397/125000000000000000),(3905245260140692883/500000000000000000),(2297201253456370845709/1000000000000000000),(2246199266189672047/1000000000000000000)⟩,(999187113353714051/1000000000000000000),(262432303771420809/500000000000000000),(27359960893018027/200000000000000000),(1949422281400407/31250000000000000)⟩
theorem valid88 : certificate88.Valid := by decide +kernel
theorem sound88 : certificate88.Sound := rat_cut_bin_certificate_sound certificate88 profilesValid88 numericValid88 valid88

def retention89 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(31127342475000000/7319211554653755967),(628132703644681829/1000000000000000000),4,(579062559281595342173/256000000000000000000),true,MergedCutProfiles.Batch015.profile612,![MergedCutProfiles.Batch015.profile612,MergedCutProfiles.Batch015.profile614,MergedCutProfiles.Batch015.profile627,MergedCutProfiles.Batch015.profile628,MergedCutProfiles.Batch015.profile620,MergedCutProfiles.Batch015.profile629,MergedCutProfiles.Batch015.profile624,MergedCutProfiles.Batch015.profile626,MergedCutProfiles.Batch015.profile630,MergedCutProfiles.Batch015.profile631,MergedCutProfiles.Batch015.profile632,MergedCutProfiles.Batch015.profile633,MergedCutProfiles.Batch015.profile634,MergedCutProfiles.Batch015.profile635,MergedCutProfiles.Batch015.profile636,MergedCutProfiles.Batch015.profile637]⟩
theorem profilesValid89 : retention89.ProfilesValid := by
  change ∀ j : Fin 16, (retention89.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch015.valid612
  · exact MergedCutProfiles.Batch015.valid614
  · exact MergedCutProfiles.Batch015.valid627
  · exact MergedCutProfiles.Batch015.valid628
  · exact MergedCutProfiles.Batch015.valid620
  · exact MergedCutProfiles.Batch015.valid629
  · exact MergedCutProfiles.Batch015.valid624
  · exact MergedCutProfiles.Batch015.valid626
  · exact MergedCutProfiles.Batch015.valid630
  · exact MergedCutProfiles.Batch015.valid631
  · exact MergedCutProfiles.Batch015.valid632
  · exact MergedCutProfiles.Batch015.valid633
  · exact MergedCutProfiles.Batch015.valid634
  · exact MergedCutProfiles.Batch015.valid635
  · exact MergedCutProfiles.Batch015.valid636
  · exact MergedCutProfiles.Batch015.valid637
theorem numericValid89 : retention89.NumericValid := by decide +kernel
def certificate89 : RatCutBinCertificate := ⟨⟨retention89,(1880388806451898253/1000000000000000000),(1008381335301397/125000000000000000),(3905245260140692883/500000000000000000),(2297201253456370845709/1000000000000000000),(2254194486937645829/1000000000000000000)⟩,(999187113353714051/1000000000000000000),(102642482031710943/200000000000000000),(36110320884080423/250000000000000000),(6642344633241181/100000000000000000)⟩
theorem valid89 : certificate89.Valid := by decide +kernel
theorem sound89 : certificate89.Sound := rat_cut_bin_certificate_sound certificate89 profilesValid89 numericValid89 valid89

def retention90 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(2135897368820784567/292768462186150238680),(1245093699/1000000000),(12/5),(448830891287494997/200000000000000000),true,MergedCutProfiles.Batch015.profile638,![MergedCutProfiles.Batch015.profile638,MergedCutProfiles.Batch015.profile639,MergedCutProfiles.Batch016.profile640,MergedCutProfiles.Batch016.profile641,MergedCutProfiles.Batch016.profile642,MergedCutProfiles.Batch016.profile643,MergedCutProfiles.Batch015.profile633,MergedCutProfiles.Batch016.profile644,MergedCutProfiles.Batch016.profile645,MergedCutProfiles.Batch016.profile646,MergedCutProfiles.Batch016.profile647,MergedCutProfiles.Batch016.profile648,MergedCutProfiles.Batch016.profile649,MergedCutProfiles.Batch016.profile650,MergedCutProfiles.Batch016.profile651,MergedCutProfiles.Batch016.profile652]⟩
theorem profilesValid90 : retention90.ProfilesValid := by
  change ∀ j : Fin 16, (retention90.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch015.valid638
  · exact MergedCutProfiles.Batch015.valid639
  · exact MergedCutProfiles.Batch016.valid640
  · exact MergedCutProfiles.Batch016.valid641
  · exact MergedCutProfiles.Batch016.valid642
  · exact MergedCutProfiles.Batch016.valid643
  · exact MergedCutProfiles.Batch015.valid633
  · exact MergedCutProfiles.Batch016.valid644
  · exact MergedCutProfiles.Batch016.valid645
  · exact MergedCutProfiles.Batch016.valid646
  · exact MergedCutProfiles.Batch016.valid647
  · exact MergedCutProfiles.Batch016.valid648
  · exact MergedCutProfiles.Batch016.valid649
  · exact MergedCutProfiles.Batch016.valid650
  · exact MergedCutProfiles.Batch016.valid651
  · exact MergedCutProfiles.Batch016.valid652
theorem numericValid90 : retention90.NumericValid := by decide +kernel
def certificate90 : RatCutBinCertificate := ⟨⟨retention90,(1880388806451898253/1000000000000000000),(1008381335301397/125000000000000000),(3905245260140692883/500000000000000000),(2297201253456370845709/1000000000000000000),(223949327632090797/100000000000000000)⟩,(999187113353714051/1000000000000000000),(355424275956267273/1000000000000000000),(276904567322906817/1000000000000000000),(98359163349908437/500000000000000000)⟩
theorem valid90 : certificate90.Valid := by decide +kernel
theorem sound90 : certificate90.Sound := rat_cut_bin_certificate_sound certificate90 profilesValid90 numericValid90 valid90

def retention91 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(9943893456042867/58741665767686645),(2135897368820784567/1000000000000000000),(7/4),(233613808247397732578571207171925831559/136697431604530212288000000000000000000),false,MergedCutProfiles.Batch016.profile653,(fun _ => MergedCutProfiles.Batch016.profile653)⟩
theorem profilesValid91 : retention91.ProfilesValid := by
  exact MergedCutProfiles.Batch016.valid653
theorem numericValid91 : retention91.NumericValid := by decide +kernel
def certificate91 : RatCutBinCertificate := ⟨⟨retention91,(1880388806451898253/1000000000000000000),(1008381335301397/125000000000000000),(3905245260140692883/500000000000000000),(2297201253456370845709/1000000000000000000),(341117168787623419/200000000000000000)⟩,(999187113353714051/1000000000000000000),(47104221841717059/125000000000000000),(12769610260782543/50000000000000000),(49313070802617271/250000000000000000)⟩
theorem valid91 : certificate91.Valid := by decide +kernel
theorem sound91 : certificate91.Sound := rat_cut_bin_certificate_sound certificate91 profilesValid91 numericValid91 valid91

def retention92 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(1600000000000000000/7319211554653755967),(6195045623114706141/125000000000000000),1,(62655490408627354772865727687467365827/39648291987934119302400000000000000000),false,MergedCutProfiles.Batch016.profile654,(fun _ => MergedCutProfiles.Batch016.profile654)⟩
theorem profilesValid92 : retention92.ProfilesValid := by
  exact MergedCutProfiles.Batch016.valid654
theorem numericValid92 : retention92.NumericValid := by decide +kernel
def certificate92 : RatCutBinCertificate := ⟨⟨retention92,(1880388806451898253/1000000000000000000),(1008381335301397/125000000000000000),(3905245260140692883/500000000000000000),(2297201253456370845709/1000000000000000000),(315668010365212747/200000000000000000)⟩,(999187113353714051/1000000000000000000),(138676067384545397/500000000000000000),(2293193298065077/6250000000000000),(280387786647620757/500000000000000000)⟩
theorem valid92 : certificate92.Valid := by decide +kernel
theorem sound92 : certificate92.Sound := rat_cut_bin_certificate_sound certificate92 profilesValid92 numericValid92 valid92

def retention93 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(1/2),64,1,(255369632393373974456752157088663284991/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch016.profile655,(fun _ => MergedCutProfiles.Batch016.profile655)⟩
theorem profilesValid93 : retention93.ProfilesValid := by
  exact MergedCutProfiles.Batch016.valid655
theorem numericValid93 : retention93.NumericValid := by decide +kernel
def certificate93 : RatCutBinCertificate := ⟨⟨retention93,(1880388806451898253/1000000000000000000),(1008381335301397/125000000000000000),(3905245260140692883/500000000000000000),(2297201253456370845709/1000000000000000000),(199119094066104147/200000000000000000)⟩,(999187113353714051/1000000000000000000),(437600659663554921/1000000000000000000),(10037225296828981/50000000000000000),(196637578250619617/1000000000000000000)⟩
theorem valid93 : certificate93.Valid := by decide +kernel
theorem sound93 : certificate93.Sound := rat_cut_bin_certificate_sound certificate93 profilesValid93 numericValid93 valid93

def retention94 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(1600000000000000000/7319211554653755967),(3374372767283928863/1000000000000000000),(27/20),(8533141417484559461826110720385349338519/5398996427654286180800000000000000000000),false,MergedCutProfiles.Batch016.profile654,(fun _ => MergedCutProfiles.Batch016.profile654)⟩
theorem profilesValid94 : retention94.ProfilesValid := by
  exact MergedCutProfiles.Batch016.valid654
theorem numericValid94 : retention94.NumericValid := by decide +kernel
def certificate94 : RatCutBinCertificate := ⟨⟨retention94,(2242561021451898253/1000000000000000000),(1008381335301397/125000000000000000),(3905245260140692883/500000000000000000),(2297201253456370845709/1000000000000000000),(7886890995760819/5000000000000000)⟩,(499515273146196913/500000000000000000),(251639992755275121/1000000000000000000),(80215371532027691/200000000000000000),(372576186776055511/1000000000000000000)⟩
theorem valid94 : certificate94.Valid := by decide +kernel
theorem sound94 : certificate94.Sound := rat_cut_bin_certificate_sound certificate94 profilesValid94 numericValid94 valid94

def retention95 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(1/2),64,1,(255369632393373974456752157088663284991/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch016.profile655,(fun _ => MergedCutProfiles.Batch016.profile655)⟩
theorem profilesValid95 : retention95.ProfilesValid := by
  exact MergedCutProfiles.Batch016.valid655
theorem numericValid95 : retention95.NumericValid := by decide +kernel
def certificate95 : RatCutBinCertificate := ⟨⟨retention95,(2242561021451898253/1000000000000000000),(1008381335301397/125000000000000000),(3905245260140692883/500000000000000000),(2297201253456370845709/1000000000000000000),(995221401407846627/1000000000000000000)⟩,(499515273146196913/500000000000000000),(199418661036367203/500000000000000000),(234549357358591891/1000000000000000000),(57407461271506269/250000000000000000)⟩
theorem valid95 : certificate95.Valid := by decide +kernel
theorem sound95 : certificate95.Sound := rat_cut_bin_certificate_sound certificate95 profilesValid95 numericValid95 valid95

def certificates : List RatCutBinCertificate := [certificate84,certificate85,certificate86,certificate87,certificate88,certificate89,certificate90,certificate91,certificate92,certificate93,certificate94,certificate95]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound84,List.forall_mem_cons.mpr ⟨sound85,List.forall_mem_cons.mpr ⟨sound86,List.forall_mem_cons.mpr ⟨sound87,List.forall_mem_cons.mpr ⟨sound88,List.forall_mem_cons.mpr ⟨sound89,List.forall_mem_cons.mpr ⟨sound90,List.forall_mem_cons.mpr ⟨sound91,List.forall_mem_cons.mpr ⟨sound92,List.forall_mem_cons.mpr ⟨sound93,List.forall_mem_cons.mpr ⟨sound94,List.forall_mem_cons.mpr ⟨sound95,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch007
