import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch066
import Cycle12.MergedCutProfiles.Batch067
import Cycle12.MergedCutProfiles.Batch068
import Cycle12.MergedCutProfiles.Batch660
import Cycle12.MergedCutProfiles.Batch661

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch388

def retention4656 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(1/2),64,1,(63845003975624907895713189606753985359/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch066.profile2645,(fun _ => MergedCutProfiles.Batch066.profile2645)⟩
theorem profilesValid4656 : retention4656.ProfilesValid := by
  exact MergedCutProfiles.Batch066.valid2645
theorem numericValid4656 : retention4656.NumericValid := by decide +kernel
def certificate4656 : RatCutBinCertificate := ⟨⟨retention4656,(233818033493685491/125000000000000000),(14082027828820247/250000000000000000),(52653784351561313/5000000000000000),(432576998846285068239/10000000000000000),(987572806766468567/1000000000000000000)⟩,(124994890065598909/125000000000000000),(512210836360805491/1000000000000000000),(36277593904153551/250000000000000000),(70561748387943137/500000000000000000)⟩
theorem valid4656 : certificate4656.Valid := by decide +kernel
theorem sound4656 : certificate4656.Sound := rat_cut_bin_certificate_sound certificate4656 profilesValid4656 numericValid4656 valid4656

def retention4657 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(12800000000000000000/819407000984203374491),(13861464289384307547/500000000000000000),1,(48955512047299163425658544476006032123/22178342863014892075200000000000000000),false,MergedCutProfiles.Batch660.profile26406,(fun _ => MergedCutProfiles.Batch660.profile26406)⟩
theorem profilesValid4657 : retention4657.ProfilesValid := by
  exact MergedCutProfiles.Batch660.valid26406
theorem numericValid4657 : retention4657.NumericValid := by decide +kernel
def certificate4657 : RatCutBinCertificate := ⟨⟨retention4657,(219639668368685491/125000000000000000),(14082027828820247/250000000000000000),(52653784351561313/5000000000000000),(432576998846285068239/10000000000000000),(34343093048560973/15625000000000000)⟩,(499980799699327109/500000000000000000),(5572456015629283/250000000000000000),(86707872561696051/100000000000000000),(1765735010266627713/1000000000000000000)⟩
theorem valid4657 : certificate4657.Valid := by decide +kernel
theorem sound4657 : certificate4657.Sound := rat_cut_bin_certificate_sound certificate4657 profilesValid4657 numericValid4657 valid4657

def retention4658 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(1/2),64,1,(63845003975624907895713189606753985359/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch066.profile2645,(fun _ => MergedCutProfiles.Batch066.profile2645)⟩
theorem profilesValid4658 : retention4658.ProfilesValid := by
  exact MergedCutProfiles.Batch066.valid2645
theorem numericValid4658 : retention4658.NumericValid := by decide +kernel
def certificate4658 : RatCutBinCertificate := ⟨⟨retention4658,(219639668368685491/125000000000000000),(14082027828820247/250000000000000000),(52653784351561313/5000000000000000),(432576998846285068239/10000000000000000),(988179517607950759/1000000000000000000)⟩,(499980799699327109/500000000000000000),(49578133571072599/1000000000000000000),(789500780176894409/1000000000000000000),(384137917416265271/500000000000000000)⟩
theorem valid4658 : certificate4658.Valid := by decide +kernel
theorem sound4658 : certificate4658.Sound := rat_cut_bin_certificate_sound certificate4658 profilesValid4658 numericValid4658 valid4658

def retention4659 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(690895421840426913/4097035004921016872455),(684054873109333577/1000000000000000000),4,(1631817926389918647104626384812711691/684054873109333577000000000000000000),false,MergedCutProfiles.Batch660.profile26407,(fun _ => MergedCutProfiles.Batch660.profile26407)⟩
theorem profilesValid4659 : retention4659.ProfilesValid := by
  exact MergedCutProfiles.Batch660.valid26407
theorem numericValid4659 : retention4659.NumericValid := by decide +kernel
def certificate4659 : RatCutBinCertificate := ⟨⟨retention4659,(227909465368685491/125000000000000000),(14082027828820247/250000000000000000),(52653784351561313/5000000000000000),(432576998846285068239/10000000000000000),(586624287640614349/250000000000000000)⟩,(999960153549134151/1000000000000000000),(848165369357690567/1000000000000000000),(12159053484214459/1000000000000000000),(1468318696148753/250000000000000000)⟩
theorem valid4659 : certificate4659.Valid := by decide +kernel
theorem sound4659 : certificate4659.Sound := rat_cut_bin_certificate_sound certificate4659 profilesValid4659 numericValid4659 valid4659

def retention4660 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(978724358708534177/4097035004921016872455),(690895421840426913/1000000000000000000),4,(6601315738100036802825214649090920583/2763581687361707652000000000000000000),false,MergedCutProfiles.Batch660.profile26408,(fun _ => MergedCutProfiles.Batch660.profile26408)⟩
theorem profilesValid4660 : retention4660.ProfilesValid := by
  exact MergedCutProfiles.Batch660.valid26408
theorem numericValid4660 : retention4660.NumericValid := by decide +kernel
def certificate4660 : RatCutBinCertificate := ⟨⟨retention4660,(227909465368685491/125000000000000000),(14082027828820247/250000000000000000),(52653784351561313/5000000000000000),(432576998846285068239/10000000000000000),(469934208960017499/200000000000000000)⟩,(999960153549134151/1000000000000000000),(844749800922490587/1000000000000000000),(12728414613005029/1000000000000000000),(6165933928963891/1000000000000000000)⟩
theorem valid4660 : certificate4660.Valid := by decide +kernel
theorem sound4660 : certificate4660.Sound := rat_cut_bin_certificate_sound certificate4660 profilesValid4660 numericValid4660 valid4660

def retention4661 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(2355232787641620212/819407000984203374491),(978724358708534177/1000000000000000000),(67/20),(3714563761656661791863670635290027431319/1565958973933654683200000000000000000000),false,MergedCutProfiles.Batch660.profile26409,(fun _ => MergedCutProfiles.Batch660.profile26409)⟩
theorem profilesValid4661 : retention4661.ProfilesValid := by
  exact MergedCutProfiles.Batch660.valid26409
theorem numericValid4661 : retention4661.NumericValid := by decide +kernel
def certificate4661 : RatCutBinCertificate := ⟨⟨retention4661,(227909465368685491/125000000000000000),(14082027828820247/250000000000000000),(52653784351561313/5000000000000000),(432576998846285068239/10000000000000000),(2339398616146816563/1000000000000000000)⟩,(999960153549134151/1000000000000000000),(24419125894841127/31250000000000000),(25850582515462661/1000000000000000000),(7440865331148371/500000000000000000)⟩
theorem valid4661 : certificate4661.Valid := by decide +kernel
theorem sound4661 : certificate4661.Sound := rat_cut_bin_certificate_sound certificate4661 profilesValid4661 numericValid4661 valid4661

def retention4662 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(1/40),(588808196910405053/50000000000000000),(23/20),(103259364953036694433684437115269108399/47104655752832404240000000000000000000),false,MergedCutProfiles.Batch660.profile26410,(fun _ => MergedCutProfiles.Batch660.profile26410)⟩
theorem profilesValid4662 : retention4662.ProfilesValid := by
  exact MergedCutProfiles.Batch660.valid26410
theorem numericValid4662 : retention4662.NumericValid := by decide +kernel
def certificate4662 : RatCutBinCertificate := ⟨⟨retention4662,(227909465368685491/125000000000000000),(14082027828820247/250000000000000000),(52653784351561313/5000000000000000),(432576998846285068239/10000000000000000),(545227772374339453/250000000000000000)⟩,(999960153549134151/1000000000000000000),(679911985611225951/1000000000000000000),(14445865642901491/250000000000000000),(19223713060659621/200000000000000000)⟩
theorem valid4662 : certificate4662.Valid := by decide +kernel
theorem sound4662 : certificate4662.Sound := rat_cut_bin_certificate_sound certificate4662 profilesValid4662 numericValid4662 valid4662

def retention4663 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(620759587032082100/3973596522288482282311),(114652212763835309/200000000000000000),4,(141901321353879475561/64000000000000000000),true,MergedCutProfiles.Batch660.profile26411,![MergedCutProfiles.Batch660.profile26411,MergedCutProfiles.Batch660.profile26412,MergedCutProfiles.Batch660.profile26413,MergedCutProfiles.Batch660.profile26414,MergedCutProfiles.Batch660.profile26415,MergedCutProfiles.Batch660.profile26416,MergedCutProfiles.Batch660.profile26417,MergedCutProfiles.Batch660.profile26418,MergedCutProfiles.Batch660.profile26419,MergedCutProfiles.Batch660.profile26420,MergedCutProfiles.Batch660.profile26421,MergedCutProfiles.Batch660.profile26422,MergedCutProfiles.Batch660.profile26423,MergedCutProfiles.Batch660.profile26423,MergedCutProfiles.Batch660.profile26424,MergedCutProfiles.Batch660.profile26425]⟩
theorem profilesValid4663 : retention4663.ProfilesValid := by
  change ∀ j : Fin 16, (retention4663.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch660.valid26411
  · exact MergedCutProfiles.Batch660.valid26412
  · exact MergedCutProfiles.Batch660.valid26413
  · exact MergedCutProfiles.Batch660.valid26414
  · exact MergedCutProfiles.Batch660.valid26415
  · exact MergedCutProfiles.Batch660.valid26416
  · exact MergedCutProfiles.Batch660.valid26417
  · exact MergedCutProfiles.Batch660.valid26418
  · exact MergedCutProfiles.Batch660.valid26419
  · exact MergedCutProfiles.Batch660.valid26420
  · exact MergedCutProfiles.Batch660.valid26421
  · exact MergedCutProfiles.Batch660.valid26422
  · exact MergedCutProfiles.Batch660.valid26423
  · exact MergedCutProfiles.Batch660.valid26423
  · exact MergedCutProfiles.Batch660.valid26424
  · exact MergedCutProfiles.Batch660.valid26425
theorem numericValid4663 : retention4663.NumericValid := by decide +kernel
def certificate4663 : RatCutBinCertificate := ⟨⟨retention4663,(1872186469182606451/1000000000000000000),(3628243259175483/62500000000000000),(1060876861835579491/100000000000000000),(21132766810810694409729/500000000000000000),(1088114601396188693/500000000000000000)⟩,(999958199175574961/1000000000000000000),(708668145283014631/1000000000000000000),(591115974252369/12500000000000000),(20793274818039667/1000000000000000000)⟩
theorem valid4663 : certificate4663.Valid := by decide +kernel
theorem sound4663 : certificate4663.Sound := rat_cut_bin_certificate_sound certificate4663 profilesValid4663 numericValid4663 valid4663

def retention4664 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(1172949024000000000/3973596522288482282311),(6207595870320821/10000000000000000),4,(57262674272242378238223407695149319/24830383481283284000000000000000000),true,MergedCutProfiles.Batch660.profile26426,![MergedCutProfiles.Batch660.profile26426,MergedCutProfiles.Batch660.profile26414,MergedCutProfiles.Batch660.profile26416,MergedCutProfiles.Batch660.profile26427,MergedCutProfiles.Batch660.profile26419,MergedCutProfiles.Batch660.profile26421,MergedCutProfiles.Batch660.profile26423,MergedCutProfiles.Batch660.profile26424,MergedCutProfiles.Batch660.profile26428,MergedCutProfiles.Batch660.profile26429,MergedCutProfiles.Batch660.profile26430,MergedCutProfiles.Batch660.profile26431,MergedCutProfiles.Batch660.profile26432,MergedCutProfiles.Batch660.profile26433,MergedCutProfiles.Batch660.profile26434,MergedCutProfiles.Batch660.profile26435]⟩
theorem profilesValid4664 : retention4664.ProfilesValid := by
  change ∀ j : Fin 16, (retention4664.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch660.valid26426
  · exact MergedCutProfiles.Batch660.valid26414
  · exact MergedCutProfiles.Batch660.valid26416
  · exact MergedCutProfiles.Batch660.valid26427
  · exact MergedCutProfiles.Batch660.valid26419
  · exact MergedCutProfiles.Batch660.valid26421
  · exact MergedCutProfiles.Batch660.valid26423
  · exact MergedCutProfiles.Batch660.valid26424
  · exact MergedCutProfiles.Batch660.valid26428
  · exact MergedCutProfiles.Batch660.valid26429
  · exact MergedCutProfiles.Batch660.valid26430
  · exact MergedCutProfiles.Batch660.valid26431
  · exact MergedCutProfiles.Batch660.valid26432
  · exact MergedCutProfiles.Batch660.valid26433
  · exact MergedCutProfiles.Batch660.valid26434
  · exact MergedCutProfiles.Batch660.valid26435
theorem numericValid4664 : retention4664.NumericValid := by decide +kernel
def certificate4664 : RatCutBinCertificate := ⟨⟨retention4664,(1872186469182606451/1000000000000000000),(3628243259175483/62500000000000000),(1060876861835579491/100000000000000000),(21132766810810694409729/500000000000000000),(453034899625603337/200000000000000000)⟩,(999958199175574961/1000000000000000000),(129110188450700531/200000000000000000),(8990367949103561/125000000000000000),(33163940360526219/1000000000000000000)⟩
theorem valid4664 : certificate4664.Valid := by decide +kernel
theorem sound4664 : certificate4664.Sound := rat_cut_bin_certificate_sound certificate4664 profilesValid4664 numericValid4664 valid4664

def retention4665 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(5882391296850768254/3973596522288482282311),(36654657/31250000),(27/10),(11107773835748727631867885812120314711/4691796096000000000000000000000000000),true,MergedCutProfiles.Batch660.profile26419,![MergedCutProfiles.Batch660.profile26419,MergedCutProfiles.Batch660.profile26429,MergedCutProfiles.Batch660.profile26434,MergedCutProfiles.Batch660.profile26436,MergedCutProfiles.Batch660.profile26437,MergedCutProfiles.Batch660.profile26438,MergedCutProfiles.Batch660.profile26439,MergedCutProfiles.Batch661.profile26440,MergedCutProfiles.Batch661.profile26441,MergedCutProfiles.Batch661.profile26442,MergedCutProfiles.Batch661.profile26443,MergedCutProfiles.Batch661.profile26444,MergedCutProfiles.Batch066.profile2648,MergedCutProfiles.Batch661.profile26445,MergedCutProfiles.Batch066.profile2664,MergedCutProfiles.Batch661.profile26446]⟩
theorem profilesValid4665 : retention4665.ProfilesValid := by
  change ∀ j : Fin 16, (retention4665.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch660.valid26419
  · exact MergedCutProfiles.Batch660.valid26429
  · exact MergedCutProfiles.Batch660.valid26434
  · exact MergedCutProfiles.Batch660.valid26436
  · exact MergedCutProfiles.Batch660.valid26437
  · exact MergedCutProfiles.Batch660.valid26438
  · exact MergedCutProfiles.Batch660.valid26439
  · exact MergedCutProfiles.Batch661.valid26440
  · exact MergedCutProfiles.Batch661.valid26441
  · exact MergedCutProfiles.Batch661.valid26442
  · exact MergedCutProfiles.Batch661.valid26443
  · exact MergedCutProfiles.Batch661.valid26444
  · exact MergedCutProfiles.Batch066.valid2648
  · exact MergedCutProfiles.Batch661.valid26445
  · exact MergedCutProfiles.Batch066.valid2664
  · exact MergedCutProfiles.Batch661.valid26446
theorem numericValid4665 : retention4665.NumericValid := by decide +kernel
def certificate4665 : RatCutBinCertificate := ⟨⟨retention4665,(1872186469182606451/1000000000000000000),(3628243259175483/62500000000000000),(1060876861835579491/100000000000000000),(21132766810810694409729/500000000000000000),(1169913915822387383/500000000000000000)⟩,(999958199175574961/1000000000000000000),(430841197676661199/1000000000000000000),(206383229495910629/1000000000000000000),(70209763626908641/500000000000000000)⟩
theorem valid4665 : certificate4665.Valid := by decide +kernel
theorem sound4665 : certificate4665.Sound := rat_cut_bin_certificate_sound certificate4665 profilesValid4665 numericValid4665 valid4665

def retention4666 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(64000000000000000000/3973596522288482282311),(2941195648425384127/500000000000000000),(6/5),(1411998081410584451067/640000000000000000000),true,MergedCutProfiles.Batch661.profile26447,![MergedCutProfiles.Batch661.profile26447,MergedCutProfiles.Batch661.profile26448,MergedCutProfiles.Batch661.profile26449,MergedCutProfiles.Batch661.profile26450,MergedCutProfiles.Batch661.profile26451,MergedCutProfiles.Batch066.profile2652,MergedCutProfiles.Batch661.profile26452,MergedCutProfiles.Batch661.profile26453,MergedCutProfiles.Batch661.profile26454,MergedCutProfiles.Batch661.profile26455,MergedCutProfiles.Batch661.profile26456,MergedCutProfiles.Batch066.profile2657,MergedCutProfiles.Batch661.profile26457,MergedCutProfiles.Batch067.profile2701,MergedCutProfiles.Batch661.profile26458,MergedCutProfiles.Batch661.profile26459]⟩
theorem profilesValid4666 : retention4666.ProfilesValid := by
  change ∀ j : Fin 16, (retention4666.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch661.valid26447
  · exact MergedCutProfiles.Batch661.valid26448
  · exact MergedCutProfiles.Batch661.valid26449
  · exact MergedCutProfiles.Batch661.valid26450
  · exact MergedCutProfiles.Batch661.valid26451
  · exact MergedCutProfiles.Batch066.valid2652
  · exact MergedCutProfiles.Batch661.valid26452
  · exact MergedCutProfiles.Batch661.valid26453
  · exact MergedCutProfiles.Batch661.valid26454
  · exact MergedCutProfiles.Batch661.valid26455
  · exact MergedCutProfiles.Batch661.valid26456
  · exact MergedCutProfiles.Batch066.valid2657
  · exact MergedCutProfiles.Batch661.valid26457
  · exact MergedCutProfiles.Batch067.valid2701
  · exact MergedCutProfiles.Batch661.valid26458
  · exact MergedCutProfiles.Batch661.valid26459
theorem numericValid4666 : retention4666.NumericValid := by decide +kernel
def certificate4666 : RatCutBinCertificate := ⟨⟨retention4666,(1872186469182606451/1000000000000000000),(3628243259175483/62500000000000000),(1060876861835579491/100000000000000000),(21132766810810694409729/500000000000000000),(2193953324167111437/1000000000000000000)⟩,(999958199175574961/1000000000000000000),(273166314756568373/1000000000000000000),(46538252012017409/125000000000000000),(108125660179506743/200000000000000000)⟩
theorem valid4666 : certificate4666.Valid := by decide +kernel
theorem sound4666 : certificate4666.Sound := rat_cut_bin_certificate_sound certificate4666 profilesValid4666 numericValid4666 valid4666

def retention4667 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(1/2),64,1,(3990318709263329641199665529711342191/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch068.profile2737,(fun _ => MergedCutProfiles.Batch068.profile2737)⟩
theorem profilesValid4667 : retention4667.ProfilesValid := by
  exact MergedCutProfiles.Batch068.valid2737
theorem numericValid4667 : retention4667.NumericValid := by decide +kernel
def certificate4667 : RatCutBinCertificate := ⟨⟨retention4667,(1872186469182606451/1000000000000000000),(3628243259175483/62500000000000000),(1060876861835579491/100000000000000000),(21132766810810694409729/500000000000000000),(197466989478387091/200000000000000000)⟩,(999958199175574961/1000000000000000000),(513361588668567139/1000000000000000000),(18042724194305303/125000000000000000),(70171302232485541/500000000000000000)⟩
theorem valid4667 : certificate4667.Valid := by decide +kernel
theorem sound4667 : certificate4667.Sound := rat_cut_bin_certificate_sound certificate4667 profilesValid4667 numericValid4667 valid4667

def certificates : List RatCutBinCertificate := [certificate4656,certificate4657,certificate4658,certificate4659,certificate4660,certificate4661,certificate4662,certificate4663,certificate4664,certificate4665,certificate4666,certificate4667]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4656,List.forall_mem_cons.mpr ⟨sound4657,List.forall_mem_cons.mpr ⟨sound4658,List.forall_mem_cons.mpr ⟨sound4659,List.forall_mem_cons.mpr ⟨sound4660,List.forall_mem_cons.mpr ⟨sound4661,List.forall_mem_cons.mpr ⟨sound4662,List.forall_mem_cons.mpr ⟨sound4663,List.forall_mem_cons.mpr ⟨sound4664,List.forall_mem_cons.mpr ⟨sound4665,List.forall_mem_cons.mpr ⟨sound4666,List.forall_mem_cons.mpr ⟨sound4667,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch388
