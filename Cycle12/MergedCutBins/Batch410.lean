import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch690
import Cycle12.MergedCutProfiles.Batch691

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch410

def retention4920 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(1/40),(27501154760111989969/500000000000000000),(21/20),(2209558777145067673/1000000000000000000),false,MergedCutProfiles.Batch690.profile27611,(fun _ => MergedCutProfiles.Batch690.profile27611)⟩
theorem profilesValid4920 : retention4920.ProfilesValid := by
  exact MergedCutProfiles.Batch690.valid27611
theorem numericValid4920 : retention4920.NumericValid := by decide +kernel
def certificate4920 : RatCutBinCertificate := ⟨⟨retention4920,(466481940255100343/250000000000000000),(19858540071699249/200000000000000000),(12376146356452482367/1000000000000000000),(894160117241170598371/31250000000000000),(68557503076567983/31250000000000000)⟩,(39997644271043399/40000000000000000),(27925663529488929/40000000000000000),(3187053578593143/62500000000000000),(12852120134469021/125000000000000000)⟩
theorem valid4920 : certificate4920.Valid := by decide +kernel
theorem sound4920 : certificate4920.Sound := rat_cut_bin_certificate_sound certificate4920 profilesValid4920 numericValid4920 valid4920

def retention4921 : RatCutRetentionCertificate := ⟨(23/500),(93/2000),(617383262172180308/2249909717982827983939),(593293179960146709/1000000000000000000),4,(579933006489142287781/256000000000000000000),true,MergedCutProfiles.Batch690.profile27612,![MergedCutProfiles.Batch690.profile27612,MergedCutProfiles.Batch690.profile27613,MergedCutProfiles.Batch690.profile27614,MergedCutProfiles.Batch690.profile27615,MergedCutProfiles.Batch690.profile27616,MergedCutProfiles.Batch690.profile27617,MergedCutProfiles.Batch690.profile27618,MergedCutProfiles.Batch690.profile27619,MergedCutProfiles.Batch690.profile27620,MergedCutProfiles.Batch690.profile27621,MergedCutProfiles.Batch690.profile27622,MergedCutProfiles.Batch690.profile27623,MergedCutProfiles.Batch690.profile27624,MergedCutProfiles.Batch690.profile27625,MergedCutProfiles.Batch690.profile27626,MergedCutProfiles.Batch690.profile27627]⟩
theorem profilesValid4921 : retention4921.ProfilesValid := by
  change ∀ j : Fin 16, (retention4921.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch690.valid27612
  · exact MergedCutProfiles.Batch690.valid27613
  · exact MergedCutProfiles.Batch690.valid27614
  · exact MergedCutProfiles.Batch690.valid27615
  · exact MergedCutProfiles.Batch690.valid27616
  · exact MergedCutProfiles.Batch690.valid27617
  · exact MergedCutProfiles.Batch690.valid27618
  · exact MergedCutProfiles.Batch690.valid27619
  · exact MergedCutProfiles.Batch690.valid27620
  · exact MergedCutProfiles.Batch690.valid27621
  · exact MergedCutProfiles.Batch690.valid27622
  · exact MergedCutProfiles.Batch690.valid27623
  · exact MergedCutProfiles.Batch690.valid27624
  · exact MergedCutProfiles.Batch690.valid27625
  · exact MergedCutProfiles.Batch690.valid27626
  · exact MergedCutProfiles.Batch690.valid27627
theorem numericValid4921 : retention4921.NumericValid := by decide +kernel
def certificate4921 : RatCutBinCertificate := ⟨⟨retention4921,(954145832639322461/500000000000000000),(50858016999050421/500000000000000000),(12476149680667381057/1000000000000000000),(3518599610248635872887/125000000000000000),(2203131236472636523/1000000000000000000)⟩,(499969468964997737/500000000000000000),(701544037429804181/1000000000000000000),(24889260708276713/500000000000000000),(11125476598311589/500000000000000000)⟩
theorem valid4921 : certificate4921.Valid := by decide +kernel
theorem sound4921 : certificate4921.Sound := rat_cut_bin_certificate_sound certificate4921 profilesValid4921 numericValid4921 valid4921

def retention4922 : RatCutRetentionCertificate := ⟨(23/500),(93/2000),(1125789323000000000/2249909717982827983939),(154345815543045077/250000000000000000),4,(284745659561836105502765026947637371/123476652434436061600000000000000000),true,MergedCutProfiles.Batch690.profile27613,![MergedCutProfiles.Batch690.profile27613,MergedCutProfiles.Batch690.profile27615,MergedCutProfiles.Batch690.profile27628,MergedCutProfiles.Batch690.profile27618,MergedCutProfiles.Batch690.profile27620,MergedCutProfiles.Batch690.profile27622,MergedCutProfiles.Batch690.profile27624,MergedCutProfiles.Batch690.profile27626,MergedCutProfiles.Batch690.profile27629,MergedCutProfiles.Batch690.profile27630,MergedCutProfiles.Batch690.profile27631,MergedCutProfiles.Batch690.profile27632,MergedCutProfiles.Batch690.profile27633,MergedCutProfiles.Batch690.profile27634,MergedCutProfiles.Batch690.profile27635,MergedCutProfiles.Batch690.profile27636]⟩
theorem profilesValid4922 : retention4922.ProfilesValid := by
  change ∀ j : Fin 16, (retention4922.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch690.valid27613
  · exact MergedCutProfiles.Batch690.valid27615
  · exact MergedCutProfiles.Batch690.valid27628
  · exact MergedCutProfiles.Batch690.valid27618
  · exact MergedCutProfiles.Batch690.valid27620
  · exact MergedCutProfiles.Batch690.valid27622
  · exact MergedCutProfiles.Batch690.valid27624
  · exact MergedCutProfiles.Batch690.valid27626
  · exact MergedCutProfiles.Batch690.valid27629
  · exact MergedCutProfiles.Batch690.valid27630
  · exact MergedCutProfiles.Batch690.valid27631
  · exact MergedCutProfiles.Batch690.valid27632
  · exact MergedCutProfiles.Batch690.valid27633
  · exact MergedCutProfiles.Batch690.valid27634
  · exact MergedCutProfiles.Batch690.valid27635
  · exact MergedCutProfiles.Batch690.valid27636
theorem numericValid4922 : retention4922.NumericValid := by decide +kernel
def certificate4922 : RatCutBinCertificate := ⟨⟨retention4922,(954145832639322461/500000000000000000),(50858016999050421/500000000000000000),(12476149680667381057/1000000000000000000),(3518599610248635872887/125000000000000000),(2243836764786955729/1000000000000000000)⟩,(499969468964997737/500000000000000000),(335478919059143017/500000000000000000),(3064856100491381/50000000000000000),(5603648499440813/200000000000000000)⟩
theorem valid4922 : certificate4922.Valid := by decide +kernel
theorem sound4922 : certificate4922.Sound := rat_cut_bin_certificate_sound certificate4922 profilesValid4922 numericValid4922 valid4922

def retention4923 : RatCutRetentionCertificate := ⟨(23/500),(93/2000),(3522047940960782259/2249909717982827983939),(1125789323/1000000000),(14/5),(670994139362809935112809864262503951/281447330750000000000000000000000000),true,MergedCutProfiles.Batch690.profile27617,![MergedCutProfiles.Batch690.profile27617,MergedCutProfiles.Batch690.profile27622,MergedCutProfiles.Batch690.profile27637,MergedCutProfiles.Batch690.profile27638,MergedCutProfiles.Batch690.profile27636,MergedCutProfiles.Batch690.profile27639,MergedCutProfiles.Batch691.profile27640,MergedCutProfiles.Batch691.profile27641,MergedCutProfiles.Batch691.profile27642,MergedCutProfiles.Batch691.profile27643,MergedCutProfiles.Batch691.profile27644,MergedCutProfiles.Batch691.profile27645,MergedCutProfiles.Batch691.profile27646,MergedCutProfiles.Batch691.profile27647,MergedCutProfiles.Batch691.profile27648,MergedCutProfiles.Batch691.profile27649]⟩
theorem profilesValid4923 : retention4923.ProfilesValid := by
  change ∀ j : Fin 16, (retention4923.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch690.valid27617
  · exact MergedCutProfiles.Batch690.valid27622
  · exact MergedCutProfiles.Batch690.valid27637
  · exact MergedCutProfiles.Batch690.valid27638
  · exact MergedCutProfiles.Batch690.valid27636
  · exact MergedCutProfiles.Batch690.valid27639
  · exact MergedCutProfiles.Batch691.valid27640
  · exact MergedCutProfiles.Batch691.valid27641
  · exact MergedCutProfiles.Batch691.valid27642
  · exact MergedCutProfiles.Batch691.valid27643
  · exact MergedCutProfiles.Batch691.valid27644
  · exact MergedCutProfiles.Batch691.valid27645
  · exact MergedCutProfiles.Batch691.valid27646
  · exact MergedCutProfiles.Batch691.valid27647
  · exact MergedCutProfiles.Batch691.valid27648
  · exact MergedCutProfiles.Batch691.valid27649
theorem numericValid4923 : retention4923.NumericValid := by decide +kernel
def certificate4923 : RatCutBinCertificate := ⟨⟨retention4923,(954145832639322461/500000000000000000),(50858016999050421/500000000000000000),(12476149680667381057/1000000000000000000),(3518599610248635872887/125000000000000000),(2340521785033189503/1000000000000000000)⟩,(499969468964997737/500000000000000000),(226406384729325027/500000000000000000),(47108509183972617/250000000000000000),(124489056034444049/1000000000000000000)⟩
theorem valid4923 : certificate4923.Valid := by decide +kernel
theorem sound4923 : certificate4923.Sound := rat_cut_bin_certificate_sound certificate4923 profilesValid4923 numericValid4923 valid4923

def retention4924 : RatCutRetentionCertificate := ⟨(23/500),(93/2000),(64000000000000000000/2249909717982827983939),(3522047940960782259/1000000000000000000),(7/5),(2759586736725012967983/1280000000000000000000),true,MergedCutProfiles.Batch691.profile27650,![MergedCutProfiles.Batch691.profile27650,MergedCutProfiles.Batch691.profile27651,MergedCutProfiles.Batch691.profile27652,MergedCutProfiles.Batch691.profile27653,MergedCutProfiles.Batch691.profile27654,MergedCutProfiles.Batch691.profile27655,MergedCutProfiles.Batch691.profile27656,MergedCutProfiles.Batch691.profile27657,MergedCutProfiles.Batch691.profile27658,MergedCutProfiles.Batch691.profile27659,MergedCutProfiles.Batch691.profile27660,MergedCutProfiles.Batch691.profile27661,MergedCutProfiles.Batch691.profile27662,MergedCutProfiles.Batch691.profile27663,MergedCutProfiles.Batch691.profile27664,MergedCutProfiles.Batch691.profile27665]⟩
theorem profilesValid4924 : retention4924.ProfilesValid := by
  change ∀ j : Fin 16, (retention4924.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch691.valid27650
  · exact MergedCutProfiles.Batch691.valid27651
  · exact MergedCutProfiles.Batch691.valid27652
  · exact MergedCutProfiles.Batch691.valid27653
  · exact MergedCutProfiles.Batch691.valid27654
  · exact MergedCutProfiles.Batch691.valid27655
  · exact MergedCutProfiles.Batch691.valid27656
  · exact MergedCutProfiles.Batch691.valid27657
  · exact MergedCutProfiles.Batch691.valid27658
  · exact MergedCutProfiles.Batch691.valid27659
  · exact MergedCutProfiles.Batch691.valid27660
  · exact MergedCutProfiles.Batch691.valid27661
  · exact MergedCutProfiles.Batch691.valid27662
  · exact MergedCutProfiles.Batch691.valid27663
  · exact MergedCutProfiles.Batch691.valid27664
  · exact MergedCutProfiles.Batch691.valid27665
theorem numericValid4924 : retention4924.NumericValid := by decide +kernel
def certificate4924 : RatCutBinCertificate := ⟨⟨retention4924,(954145832639322461/500000000000000000),(50858016999050421/500000000000000000),(12476149680667381057/1000000000000000000),(3518599610248635872887/125000000000000000),(2134145930725584911/1000000000000000000)⟩,(499969468964997737/500000000000000000),(324055454386199229/1000000000000000000),(155386854837097663/500000000000000000),(90460911939594657/250000000000000000)⟩
theorem valid4924 : certificate4924.Valid := by decide +kernel
theorem sound4924 : certificate4924.Sound := rat_cut_bin_certificate_sound certificate4924 profilesValid4924 numericValid4924 valid4924

def retention4925 : RatCutRetentionCertificate := ⟨(23/500),(93/2000),(1/2),64,1,(255390044232855513941585133376155068679/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch691.profile27666,(fun _ => MergedCutProfiles.Batch691.profile27666)⟩
theorem profilesValid4925 : retention4925.ProfilesValid := by
  exact MergedCutProfiles.Batch691.valid27666
theorem numericValid4925 : retention4925.NumericValid := by decide +kernel
def certificate4925 : RatCutBinCertificate := ⟨⟨retention4925,(954145832639322461/500000000000000000),(50858016999050421/500000000000000000),(12476149680667381057/1000000000000000000),(3518599610248635872887/125000000000000000),(982059365564163303/1000000000000000000)⟩,(499969468964997737/500000000000000000),(537748128733788433/1000000000000000000),(64325872919545027/500000000000000000),(124426575314178981/1000000000000000000)⟩
theorem valid4925 : certificate4925.Valid := by decide +kernel
theorem sound4925 : certificate4925.Sound := rat_cut_bin_certificate_sound certificate4925 profilesValid4925 numericValid4925 valid4925

def retention4926 : RatCutRetentionCertificate := ⟨(23/500),(93/2000),(64000000000000000000/2249909717982827983939),(34375797063276508917/1000000000000000000),1,(26958625246255236679520626334649383257/12500289841191457788000000000000000000),false,MergedCutProfiles.Batch691.profile27667,(fun _ => MergedCutProfiles.Batch691.profile27667)⟩
theorem profilesValid4926 : retention4926.ProfilesValid := by
  exact MergedCutProfiles.Batch691.valid27667
theorem numericValid4926 : retention4926.NumericValid := by decide +kernel
def certificate4926 : RatCutBinCertificate := ⟨⟨retention4926,(873251295639322461/500000000000000000),(50858016999050421/500000000000000000),(12476149680667381057/1000000000000000000),(3518599610248635872887/125000000000000000),(1071200528955642479/500000000000000000)⟩,(999944114935588933/1000000000000000000),(1923537148378899/100000000000000000),(876328096161051397/1000000000000000000),(1767202062360472707/1000000000000000000)⟩
theorem valid4926 : certificate4926.Valid := by decide +kernel
theorem sound4926 : certificate4926.Sound := rat_cut_bin_certificate_sound certificate4926 profilesValid4926 numericValid4926 valid4926

def retention4927 : RatCutRetentionCertificate := ⟨(23/500),(93/2000),(1/2),64,1,(255390044232855513941585133376155068679/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch691.profile27666,(fun _ => MergedCutProfiles.Batch691.profile27666)⟩
theorem profilesValid4927 : retention4927.ProfilesValid := by
  exact MergedCutProfiles.Batch691.valid27666
theorem numericValid4927 : retention4927.NumericValid := by decide +kernel
def certificate4927 : RatCutBinCertificate := ⟨⟨retention4927,(873251295639322461/500000000000000000),(50858016999050421/500000000000000000),(12476149680667381057/1000000000000000000),(3518599610248635872887/125000000000000000),(245844601459288501/250000000000000000)⟩,(999944114935588933/1000000000000000000),(41906431920379579/1000000000000000000),(810436719072495051/1000000000000000000),(196215332569008317/250000000000000000)⟩
theorem valid4927 : certificate4927.Valid := by decide +kernel
theorem sound4927 : certificate4927.Sound := rat_cut_bin_certificate_sound certificate4927 profilesValid4927 numericValid4927 valid4927

def retention4928 : RatCutRetentionCertificate := ⟨(23/500),(93/2000),(706070021784661279/2249909717982827983939),(349539614744881821/500000000000000000),4,(560634928751374412776753350022475877/233026409829921214000000000000000000),false,MergedCutProfiles.Batch691.profile27668,(fun _ => MergedCutProfiles.Batch691.profile27668)⟩
theorem profilesValid4928 : retention4928.ProfilesValid := by
  exact MergedCutProfiles.Batch691.valid27668
theorem numericValid4928 : retention4928.NumericValid := by decide +kernel
def certificate4928 : RatCutBinCertificate := ⟨⟨retention4928,(935022573639322461/500000000000000000),(50858016999050421/500000000000000000),(12476149680667381057/1000000000000000000),(3518599610248635872887/125000000000000000),(586225252336368157/250000000000000000)⟩,(999940161761240739/1000000000000000000),(214527995862149583/250000000000000000),(10579144904306371/1000000000000000000),(5126574169323111/1000000000000000000)⟩
theorem valid4928 : certificate4928.Valid := by decide +kernel
theorem sound4928 : certificate4928.Sound := rat_cut_bin_certificate_sound certificate4928 profilesValid4928 numericValid4928 valid4928

def retention4929 : RatCutRetentionCertificate := ⟨(23/500),(93/2000),(870155004168362538/2249909717982827983939),(706070021784661279/1000000000000000000),4,(1360700656972225411889106923457281099/564856017427729023200000000000000000),false,MergedCutProfiles.Batch691.profile27669,(fun _ => MergedCutProfiles.Batch691.profile27669)⟩
theorem profilesValid4929 : retention4929.ProfilesValid := by
  exact MergedCutProfiles.Batch691.valid27669
theorem numericValid4929 : retention4929.NumericValid := by decide +kernel
def certificate4929 : RatCutBinCertificate := ⟨⟨retention4929,(935022573639322461/500000000000000000),(50858016999050421/500000000000000000),(12476149680667381057/1000000000000000000),(3518599610248635872887/125000000000000000),(586987212051107369/250000000000000000)⟩,(999940161761240739/1000000000000000000),(854934060099384851/1000000000000000000),(11071324690664811/1000000000000000000),(134502165882017/25000000000000000)⟩
theorem valid4929 : certificate4929.Valid := by decide +kernel
theorem sound4929 : certificate4929.Sound := rat_cut_bin_certificate_sound certificate4929 profilesValid4929 numericValid4929 valid4929

def retention4930 : RatCutRetentionCertificate := ⟨(23/500),(93/2000),(4191540625105192636/2249909717982827983939),(435077502084181269/500000000000000000),(73/20),(837097176918545426994433706428627140311/348062001667345015200000000000000000000),false,MergedCutProfiles.Batch691.profile27670,(fun _ => MergedCutProfiles.Batch691.profile27670)⟩
theorem profilesValid4930 : retention4930.ProfilesValid := by
  exact MergedCutProfiles.Batch691.valid27670
theorem numericValid4930 : retention4930.NumericValid := by decide +kernel
def certificate4930 : RatCutBinCertificate := ⟨⟨retention4930,(935022573639322461/500000000000000000),(50858016999050421/500000000000000000),(12476149680667381057/1000000000000000000),(3518599610248635872887/125000000000000000),(2349374558868188229/1000000000000000000)⟩,(999940161761240739/1000000000000000000),(815517666564520111/1000000000000000000),(9086013354126489/500000000000000000),(2431247384814947/250000000000000000)⟩
theorem valid4930 : certificate4930.Valid := by decide +kernel
theorem sound4930 : certificate4930.Sound := rat_cut_bin_certificate_sound certificate4930 profilesValid4930 numericValid4930 valid4930

def retention4931 : RatCutRetentionCertificate := ⟨(23/500),(93/2000),(52481062698066780020/2249909717982827983939),(1047885156276298159/250000000000000000),(3/2),(9300481192589318356196716312610742119/4191540625105192636000000000000000000),false,MergedCutProfiles.Batch691.profile27671,(fun _ => MergedCutProfiles.Batch691.profile27671)⟩
theorem profilesValid4931 : retention4931.ProfilesValid := by
  exact MergedCutProfiles.Batch691.valid27671
theorem numericValid4931 : retention4931.NumericValid := by decide +kernel
def certificate4931 : RatCutBinCertificate := ⟨⟨retention4931,(935022573639322461/500000000000000000),(50858016999050421/500000000000000000),(12476149680667381057/1000000000000000000),(3518599610248635872887/125000000000000000),(2196000113243264673/1000000000000000000)⟩,(999940161761240739/1000000000000000000),(18264514770667349/25000000000000000),(1252458403560501/31250000000000000),(9518006103017591/200000000000000000)⟩
theorem valid4931 : certificate4931.Valid := by decide +kernel
theorem sound4931 : certificate4931.Sound := rat_cut_bin_certificate_sound certificate4931 profilesValid4931 numericValid4931 valid4931

def certificates : List RatCutBinCertificate := [certificate4920,certificate4921,certificate4922,certificate4923,certificate4924,certificate4925,certificate4926,certificate4927,certificate4928,certificate4929,certificate4930,certificate4931]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4920,List.forall_mem_cons.mpr ⟨sound4921,List.forall_mem_cons.mpr ⟨sound4922,List.forall_mem_cons.mpr ⟨sound4923,List.forall_mem_cons.mpr ⟨sound4924,List.forall_mem_cons.mpr ⟨sound4925,List.forall_mem_cons.mpr ⟨sound4926,List.forall_mem_cons.mpr ⟨sound4927,List.forall_mem_cons.mpr ⟨sound4928,List.forall_mem_cons.mpr ⟨sound4929,List.forall_mem_cons.mpr ⟨sound4930,List.forall_mem_cons.mpr ⟨sound4931,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch410
