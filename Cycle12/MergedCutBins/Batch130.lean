import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch251
import Cycle12.MergedCutProfiles.Batch252
import Cycle12.MergedCutProfiles.Batch253

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch130

def retention1560 : RatCutRetentionCertificate := ⟨(63/1000),(101/1600),(5435018586135136681/11065360034428862023),(4920251424542041561/1000000000000000000),(11/10),(1978338208347838779832919571526658819119/1968100569816816624400000000000000000000),false,MergedCutProfiles.Batch251.profile10075,(fun _ => MergedCutProfiles.Batch251.profile10075)⟩
theorem profilesValid1560 : retention1560.ProfilesValid := by
  exact MergedCutProfiles.Batch251.valid10075
theorem numericValid1560 : retention1560.NumericValid := by decide +kernel
def certificate1560 : RatCutBinCertificate := ⟨⟨retention1560,(235080847894458661/100000000000000000),(205886892695735953/1000000000000000000),(4192221140517765803/250000000000000000),(185698677009292092909/1000000000000000000),(973445960198976461/1000000000000000000)⟩,(197981462140580407/200000000000000000),(86839279325780129/200000000000000000),(203571182190868013/1000000000000000000),(30622397366291817/200000000000000000)⟩
theorem valid1560 : certificate1560.Valid := by decide +kernel
theorem sound1560 : certificate1560.Sound := rat_cut_bin_certificate_sound certificate1560 profilesValid1560 numericValid1560 valid1560

def retention1561 : RatCutRetentionCertificate := ⟨(63/1000),(101/1600),(5489368771996488048/11065360034428862023),(5435018586135136681/1000000000000000000),(11/10),(2172885807107647402242420425641330674439/2174007434454054672400000000000000000000),false,MergedCutProfiles.Batch251.profile10076,(fun _ => MergedCutProfiles.Batch251.profile10076)⟩
theorem profilesValid1561 : retention1561.ProfilesValid := by
  exact MergedCutProfiles.Batch251.valid10076
theorem numericValid1561 : retention1561.NumericValid := by decide +kernel
def certificate1561 : RatCutBinCertificate := ⟨⟨retention1561,(235080847894458661/100000000000000000),(205886892695735953/1000000000000000000),(4192221140517765803/250000000000000000),(185698677009292092909/1000000000000000000),(483864431875704277/500000000000000000)⟩,(197981462140580407/200000000000000000),(86569634348043447/200000000000000000),(51174506250169749/250000000000000000),(155250708497135049/1000000000000000000)⟩
theorem valid1561 : certificate1561.Valid := by decide +kernel
theorem sound1561 : certificate1561.Sound := rat_cut_bin_certificate_sound certificate1561 profilesValid1561 numericValid1561 valid1561

def retention1562 : RatCutRetentionCertificate := ⟨(63/1000),(101/1600),(1/2),(343085548249780503/62500000000000000),(11/10),(181568757313735349270622074707315322373/182978959066549601600000000000000000000),false,MergedCutProfiles.Batch251.profile10077,(fun _ => MergedCutProfiles.Batch251.profile10077)⟩
theorem profilesValid1562 : retention1562.ProfilesValid := by
  exact MergedCutProfiles.Batch251.valid10077
theorem numericValid1562 : retention1562.NumericValid := by decide +kernel
def certificate1562 : RatCutBinCertificate := ⟨⟨retention1562,(235080847894458661/100000000000000000),(205886892695735953/1000000000000000000),(4192221140517765803/250000000000000000),(185698677009292092909/1000000000000000000),(240134485398800397/250000000000000000)⟩,(197981462140580407/200000000000000000),(435715509253750931/1000000000000000000),(2023065261788827/10000000000000000),(76317892308202657/500000000000000000)⟩
theorem valid1562 : certificate1562.Valid := by decide +kernel
theorem sound1562 : certificate1562.Sound := rat_cut_bin_certificate_sound certificate1562 profilesValid1562 numericValid1562 valid1562

def retention1563 : RatCutRetentionCertificate := ⟨(63/1000),(101/1600),(1/2),64,1,(255413005905542638087981993351007299671/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch251.profile10077,(fun _ => MergedCutProfiles.Batch251.profile10077)⟩
theorem profilesValid1563 : retention1563.ProfilesValid := by
  exact MergedCutProfiles.Batch251.valid10077
theorem numericValid1563 : retention1563.NumericValid := by decide +kernel
def certificate1563 : RatCutBinCertificate := ⟨⟨retention1563,(235080847894458661/100000000000000000),(205886892695735953/1000000000000000000),(4192221140517765803/250000000000000000),(185698677009292092909/1000000000000000000),(968843534152414059/1000000000000000000)⟩,(197981462140580407/200000000000000000),(39816144802482671/100000000000000000),(47034233232337889/200000000000000000),(222158694067113953/1000000000000000000)⟩
theorem valid1563 : certificate1563.Valid := by decide +kernel
theorem sound1563 : certificate1563.Sound := rat_cut_bin_certificate_sound certificate1563 profilesValid1563 numericValid1563 valid1563

def retention1564 : RatCutRetentionCertificate := ⟨(63/1000),(101/1600),(5164449123984085367/11065360034428862023),(660073319808676499/200000000000000000),(6/5),(13940634799069268299381137514336127031/13201466396173529980000000000000000000),false,MergedCutProfiles.Batch251.profile10078,(fun _ => MergedCutProfiles.Batch251.profile10078)⟩
theorem profilesValid1564 : retention1564.ProfilesValid := by
  exact MergedCutProfiles.Batch251.valid10078
theorem numericValid1564 : retention1564.NumericValid := by decide +kernel
def certificate1564 : RatCutBinCertificate := ⟨⟨retention1564,(267200357894458661/100000000000000000),(205886892695735953/1000000000000000000),(4192221140517765803/250000000000000000),(185698677009292092909/1000000000000000000),(1016612414730790483/1000000000000000000)⟩,(988524252939402303/1000000000000000000),(96280564437896383/250000000000000000),(247394124535117369/1000000000000000000),(170440417297282759/1000000000000000000)⟩
theorem valid1564 : certificate1564.Valid := by decide +kernel
theorem sound1564 : certificate1564.Sound := rat_cut_bin_certificate_sound certificate1564 profilesValid1564 numericValid1564 valid1564

def retention1565 : RatCutRetentionCertificate := ⟨(63/1000),(101/1600),(5482166811862788823/11065360034428862023),(5164449123984085367/1000000000000000000),(11/10),(2063606091456905369485489631355947979871/2065779649593634146800000000000000000000),false,MergedCutProfiles.Batch251.profile10079,(fun _ => MergedCutProfiles.Batch251.profile10079)⟩
theorem profilesValid1565 : retention1565.ProfilesValid := by
  exact MergedCutProfiles.Batch251.valid10079
theorem numericValid1565 : retention1565.NumericValid := by decide +kernel
def certificate1565 : RatCutBinCertificate := ⟨⟨retention1565,(267200357894458661/100000000000000000),(205886892695735953/1000000000000000000),(4192221140517765803/250000000000000000),(185698677009292092909/1000000000000000000),(481426747897164161/500000000000000000)⟩,(988524252939402303/1000000000000000000),(406624756652536947/1000000000000000000),(113733482149732599/500000000000000000),(170373709538114603/1000000000000000000)⟩
theorem valid1565 : certificate1565.Valid := by decide +kernel
theorem sound1565 : certificate1565.Sound := rat_cut_bin_certificate_sound certificate1565 profilesValid1565 numericValid1565 valid1565

def retention1566 : RatCutRetentionCertificate := ⟨(63/1000),(101/1600),(1/2),(5482166811862788823/1000000000000000000),(11/10),(2175874362653757831424635789669473129951/2192866724745115529200000000000000000000),false,MergedCutProfiles.Batch251.profile10077,(fun _ => MergedCutProfiles.Batch251.profile10077)⟩
theorem profilesValid1566 : retention1566.ProfilesValid := by
  exact MergedCutProfiles.Batch251.valid10077
theorem numericValid1566 : retention1566.NumericValid := by decide +kernel
def certificate1566 : RatCutBinCertificate := ⟨⟨retention1566,(267200357894458661/100000000000000000),(205886892695735953/1000000000000000000),(4192221140517765803/250000000000000000),(185698677009292092909/1000000000000000000),(956157151191509803/1000000000000000000)⟩,(988524252939402303/1000000000000000000),(409472509755873029/1000000000000000000),(22491441299140567/100000000000000000),(168751891995758411/1000000000000000000)⟩
theorem valid1566 : certificate1566.Valid := by decide +kernel
theorem sound1566 : certificate1566.Sound := rat_cut_bin_certificate_sound certificate1566 profilesValid1566 numericValid1566 valid1566

def retention1567 : RatCutRetentionCertificate := ⟨(101/1600),(253/4000),(1429063557769693805/11013057205697723371),(228312522824057483/250000000000000000),(5/2),(23260584784899075103/12800000000000000000),true,MergedCutProfiles.Batch252.profile10080,![MergedCutProfiles.Batch252.profile10080,MergedCutProfiles.Batch252.profile10081,MergedCutProfiles.Batch252.profile10082,MergedCutProfiles.Batch252.profile10083,MergedCutProfiles.Batch252.profile10084,MergedCutProfiles.Batch252.profile10085,MergedCutProfiles.Batch252.profile10086,MergedCutProfiles.Batch252.profile10087,MergedCutProfiles.Batch252.profile10088,MergedCutProfiles.Batch252.profile10089,MergedCutProfiles.Batch252.profile10090,MergedCutProfiles.Batch252.profile10091,MergedCutProfiles.Batch252.profile10092,MergedCutProfiles.Batch252.profile10093,MergedCutProfiles.Batch252.profile10094,MergedCutProfiles.Batch252.profile10095]⟩
theorem profilesValid1567 : retention1567.ProfilesValid := by
  change ∀ j : Fin 16, (retention1567.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch252.valid10080
  · exact MergedCutProfiles.Batch252.valid10081
  · exact MergedCutProfiles.Batch252.valid10082
  · exact MergedCutProfiles.Batch252.valid10083
  · exact MergedCutProfiles.Batch252.valid10084
  · exact MergedCutProfiles.Batch252.valid10085
  · exact MergedCutProfiles.Batch252.valid10086
  · exact MergedCutProfiles.Batch252.valid10087
  · exact MergedCutProfiles.Batch252.valid10088
  · exact MergedCutProfiles.Batch252.valid10089
  · exact MergedCutProfiles.Batch252.valid10090
  · exact MergedCutProfiles.Batch252.valid10091
  · exact MergedCutProfiles.Batch252.valid10092
  · exact MergedCutProfiles.Batch252.valid10093
  · exact MergedCutProfiles.Batch252.valid10094
  · exact MergedCutProfiles.Batch252.valid10095
theorem numericValid1567 : retention1567.NumericValid := by decide +kernel
def certificate1567 : RatCutBinCertificate := ⟨⟨retention1567,(47074083761169197/20000000000000000),(206867685175350651/1000000000000000000),(1680838030226467533/100000000000000000),(92628182321493895023/500000000000000000),(872388870047372633/500000000000000000)⟩,(494941483250681637/500000000000000000),(171318207926964997/500000000000000000),(145181782823951999/500000000000000000),(153296582952959427/1000000000000000000)⟩
theorem valid1567 : certificate1567.Valid := by decide +kernel
theorem sound1567 : certificate1567.Sound := rat_cut_bin_certificate_sound certificate1567 profilesValid1567 numericValid1567 valid1567

def retention1568 : RatCutRetentionCertificate := ⟨(101/1600),(253/4000),(3105408229434216389/11013057205697723371),(285812711553938761/200000000000000000),(7/4),(73799768478361917781/51200000000000000000),true,MergedCutProfiles.Batch252.profile10096,![MergedCutProfiles.Batch252.profile10096,MergedCutProfiles.Batch252.profile10097,MergedCutProfiles.Batch252.profile10098,MergedCutProfiles.Batch252.profile10099,MergedCutProfiles.Batch252.profile10100,MergedCutProfiles.Batch252.profile10101,MergedCutProfiles.Batch252.profile10102,MergedCutProfiles.Batch252.profile10103,MergedCutProfiles.Batch252.profile10104,MergedCutProfiles.Batch252.profile10105,MergedCutProfiles.Batch252.profile10106,MergedCutProfiles.Batch252.profile10107,MergedCutProfiles.Batch252.profile10108,MergedCutProfiles.Batch252.profile10109,MergedCutProfiles.Batch252.profile10110,MergedCutProfiles.Batch252.profile10111]⟩
theorem profilesValid1568 : retention1568.ProfilesValid := by
  change ∀ j : Fin 16, (retention1568.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch252.valid10096
  · exact MergedCutProfiles.Batch252.valid10097
  · exact MergedCutProfiles.Batch252.valid10098
  · exact MergedCutProfiles.Batch252.valid10099
  · exact MergedCutProfiles.Batch252.valid10100
  · exact MergedCutProfiles.Batch252.valid10101
  · exact MergedCutProfiles.Batch252.valid10102
  · exact MergedCutProfiles.Batch252.valid10103
  · exact MergedCutProfiles.Batch252.valid10104
  · exact MergedCutProfiles.Batch252.valid10105
  · exact MergedCutProfiles.Batch252.valid10106
  · exact MergedCutProfiles.Batch252.valid10107
  · exact MergedCutProfiles.Batch252.valid10108
  · exact MergedCutProfiles.Batch252.valid10109
  · exact MergedCutProfiles.Batch252.valid10110
  · exact MergedCutProfiles.Batch252.valid10111
theorem numericValid1568 : retention1568.NumericValid := by decide +kernel
def certificate1568 : RatCutBinCertificate := ⟨⟨retention1568,(47074083761169197/20000000000000000),(206867685175350651/1000000000000000000),(1680838030226467533/100000000000000000),(92628182321493895023/500000000000000000),(1390685074409578371/1000000000000000000)⟩,(494941483250681637/500000000000000000),(186870469613186891/500000000000000000),(258423134291284061/1000000000000000000),(153958717294288413/1000000000000000000)⟩
theorem valid1568 : certificate1568.Valid := by decide +kernel
theorem sound1568 : certificate1568.Sound := rat_cut_bin_certificate_sound certificate1568 profilesValid1568 numericValid1568 valid1568

def retention1569 : RatCutRetentionCertificate := ⟨(101/1600),(253/4000),(4859376171957100988/11013057205697723371),(3105408229434216389/1000000000000000000),(11/10),(1383989604083024647457/1280000000000000000000),true,MergedCutProfiles.Batch252.profile10112,![MergedCutProfiles.Batch252.profile10112,MergedCutProfiles.Batch252.profile10113,MergedCutProfiles.Batch252.profile10114,MergedCutProfiles.Batch252.profile10115,MergedCutProfiles.Batch252.profile10116,MergedCutProfiles.Batch252.profile10117,MergedCutProfiles.Batch252.profile10118,MergedCutProfiles.Batch252.profile10119,MergedCutProfiles.Batch253.profile10120,MergedCutProfiles.Batch253.profile10121,MergedCutProfiles.Batch253.profile10122,MergedCutProfiles.Batch253.profile10123,MergedCutProfiles.Batch253.profile10124,MergedCutProfiles.Batch253.profile10125,MergedCutProfiles.Batch253.profile10126,MergedCutProfiles.Batch253.profile10127]⟩
theorem profilesValid1569 : retention1569.ProfilesValid := by
  change ∀ j : Fin 16, (retention1569.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch252.valid10112
  · exact MergedCutProfiles.Batch252.valid10113
  · exact MergedCutProfiles.Batch252.valid10114
  · exact MergedCutProfiles.Batch252.valid10115
  · exact MergedCutProfiles.Batch252.valid10116
  · exact MergedCutProfiles.Batch252.valid10117
  · exact MergedCutProfiles.Batch252.valid10118
  · exact MergedCutProfiles.Batch252.valid10119
  · exact MergedCutProfiles.Batch253.valid10120
  · exact MergedCutProfiles.Batch253.valid10121
  · exact MergedCutProfiles.Batch253.valid10122
  · exact MergedCutProfiles.Batch253.valid10123
  · exact MergedCutProfiles.Batch253.valid10124
  · exact MergedCutProfiles.Batch253.valid10125
  · exact MergedCutProfiles.Batch253.valid10126
  · exact MergedCutProfiles.Batch253.valid10127
theorem numericValid1569 : retention1569.NumericValid := by decide +kernel
def certificate1569 : RatCutBinCertificate := ⟨⟨retention1569,(47074083761169197/20000000000000000),(206867685175350651/1000000000000000000),(1680838030226467533/100000000000000000),(92628182321493895023/500000000000000000),(524683325101581237/500000000000000000)⟩,(494941483250681637/500000000000000000),(424201095565075741/1000000000000000000),(26503201584148009/125000000000000000),(156276021097840537/1000000000000000000)⟩
theorem valid1569 : certificate1569.Valid := by decide +kernel
theorem sound1569 : certificate1569.Sound := rat_cut_bin_certificate_sound certificate1569 profilesValid1569 numericValid1569 valid1569

def retention1570 : RatCutRetentionCertificate := ⟨(101/1600),(253/4000),(5367774435239815706/11013057205697723371),(1214844042989275247/250000000000000000),(11/10),(15365611292344781313834825770485419407/15185550537365940587500000000000000000),false,MergedCutProfiles.Batch253.profile10128,(fun _ => MergedCutProfiles.Batch253.profile10128)⟩
theorem profilesValid1570 : retention1570.ProfilesValid := by
  exact MergedCutProfiles.Batch253.valid10128
theorem numericValid1570 : retention1570.NumericValid := by decide +kernel
def certificate1570 : RatCutBinCertificate := ⟨⟨retention1570,(47074083761169197/20000000000000000),(206867685175350651/1000000000000000000),(1680838030226467533/100000000000000000),(92628182321493895023/500000000000000000),(489992952983008467/500000000000000000)⟩,(494941483250681637/500000000000000000),(6731343963949891/15625000000000000),(206412855822619257/1000000000000000000),(155862962115763439/1000000000000000000)⟩
theorem valid1570 : certificate1570.Valid := by decide +kernel
theorem sound1570 : certificate1570.Sound := rat_cut_bin_certificate_sound certificate1570 profilesValid1570 numericValid1570 valid1570

def retention1571 : RatCutRetentionCertificate := ⟨(101/1600),(253/4000),(5475666701388136003/11013057205697723371),(2683887217619907853/500000000000000000),(11/10),(66891475561010786848497180923885487997/67097180440497696325000000000000000000),false,MergedCutProfiles.Batch253.profile10129,(fun _ => MergedCutProfiles.Batch253.profile10129)⟩
theorem profilesValid1571 : retention1571.ProfilesValid := by
  exact MergedCutProfiles.Batch253.valid10129
theorem numericValid1571 : retention1571.NumericValid := by decide +kernel
def certificate1571 : RatCutBinCertificate := ⟨⟨retention1571,(47074083761169197/20000000000000000),(206867685175350651/1000000000000000000),(1680838030226467533/100000000000000000),(92628182321493895023/500000000000000000),(482531693468603527/500000000000000000)⟩,(494941483250681637/500000000000000000),(433478144769843341/1000000000000000000),(20417097342406351/100000000000000000),(154225858796911197/1000000000000000000)⟩
theorem valid1571 : certificate1571.Valid := by decide +kernel
theorem sound1571 : certificate1571.Sound := rat_cut_bin_certificate_sound certificate1571 profilesValid1571 numericValid1571 valid1571

def certificates : List RatCutBinCertificate := [certificate1560,certificate1561,certificate1562,certificate1563,certificate1564,certificate1565,certificate1566,certificate1567,certificate1568,certificate1569,certificate1570,certificate1571]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1560,List.forall_mem_cons.mpr ⟨sound1561,List.forall_mem_cons.mpr ⟨sound1562,List.forall_mem_cons.mpr ⟨sound1563,List.forall_mem_cons.mpr ⟨sound1564,List.forall_mem_cons.mpr ⟨sound1565,List.forall_mem_cons.mpr ⟨sound1566,List.forall_mem_cons.mpr ⟨sound1567,List.forall_mem_cons.mpr ⟨sound1568,List.forall_mem_cons.mpr ⟨sound1569,List.forall_mem_cons.mpr ⟨sound1570,List.forall_mem_cons.mpr ⟨sound1571,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch130
