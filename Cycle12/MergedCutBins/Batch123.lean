import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch239
import Cycle12.MergedCutProfiles.Batch240

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch123

def retention1476 : RatCutRetentionCertificate := ⟨(247/4000),(31/500),(5413855256021390001/11551178452882143772),(691950162740474947/200000000000000000),(6/5),(1824350498937859879090167701434293637/1729875406851187367500000000000000000),false,MergedCutProfiles.Batch239.profile9574,(fun _ => MergedCutProfiles.Batch239.profile9574)⟩
theorem profilesValid1476 : retention1476.ProfilesValid := by
  exact MergedCutProfiles.Batch239.valid9574
theorem numericValid1476 : retention1476.NumericValid := by decide +kernel
def certificate1476 : RatCutBinCertificate := ⟨⟨retention1476,(666651282666809633/250000000000000000),(24651154762240763/125000000000000000),(4095364330316275257/250000000000000000),(189518456652147863977/1000000000000000000),(127010204860781727/125000000000000000)⟩,(494322662261000329/500000000000000000),(393299820561837317/1000000000000000000),(119838902986505783/500000000000000000),(83219265139588187/500000000000000000)⟩
theorem valid1476 : certificate1476.Valid := by decide +kernel
theorem sound1476 : certificate1476.Sound := rat_cut_bin_certificate_sound certificate1476 profilesValid1476 numericValid1476 valid1476

def retention1477 : RatCutRetentionCertificate := ⟨(247/4000),(31/500),(5690016283865189435/11551178452882143772),(5413855256021390001/1000000000000000000),(11/10),(2178646958424108376544554962343349615639/2165542102408556000400000000000000000000),false,MergedCutProfiles.Batch239.profile9575,(fun _ => MergedCutProfiles.Batch239.profile9575)⟩
theorem profilesValid1477 : retention1477.ProfilesValid := by
  exact MergedCutProfiles.Batch239.valid9575
theorem numericValid1477 : retention1477.NumericValid := by decide +kernel
def certificate1477 : RatCutBinCertificate := ⟨⟨retention1477,(666651282666809633/250000000000000000),(24651154762240763/125000000000000000),(4095364330316275257/250000000000000000),(189518456652147863977/1000000000000000000),(97073305676759033/100000000000000000)⟩,(494322662261000329/500000000000000000),(411673140688993789/1000000000000000000),(44591094057939549/200000000000000000),(6770310041876877/40000000000000000)⟩
theorem valid1477 : certificate1477.Valid := by decide +kernel
theorem sound1477 : certificate1477.Sound := rat_cut_bin_certificate_sound certificate1477 profilesValid1477 numericValid1477 valid1477

def retention1478 : RatCutRetentionCertificate := ⟨(247/4000),(31/500),(2873458223351920665/5775589226441071886),(1138003256773037887/200000000000000000),(21/20),(358219038553565187676795206514162612559/364161042167372123840000000000000000000),false,MergedCutProfiles.Batch239.profile9576,(fun _ => MergedCutProfiles.Batch239.profile9576)⟩
theorem profilesValid1478 : retention1478.ProfilesValid := by
  exact MergedCutProfiles.Batch239.valid9576
theorem numericValid1478 : retention1478.NumericValid := by decide +kernel
def certificate1478 : RatCutBinCertificate := ⟨⟨retention1478,(666651282666809633/250000000000000000),(24651154762240763/125000000000000000),(4095364330316275257/250000000000000000),(189518456652147863977/1000000000000000000),(474984979218905009/500000000000000000)⟩,(494322662261000329/500000000000000000),(420670909327816101/1000000000000000000),(53766892769097959/250000000000000000),(41728740252476573/250000000000000000)⟩
theorem valid1478 : certificate1478.Valid := by decide +kernel
theorem sound1478 : certificate1478.Sound := rat_cut_bin_certificate_sound certificate1478 profilesValid1478 numericValid1478 valid1478

def retention1479 : RatCutRetentionCertificate := ⟨(247/4000),(31/500),(1/2),(574691644670384133/100000000000000000),(21/20),(2001304445090887945643918347807641931/2043348069939143584000000000000000000),false,MergedCutProfiles.Batch239.profile9573,(fun _ => MergedCutProfiles.Batch239.profile9573)⟩
theorem profilesValid1479 : retention1479.ProfilesValid := by
  exact MergedCutProfiles.Batch239.valid9573
theorem numericValid1479 : retention1479.NumericValid := by decide +kernel
def certificate1479 : RatCutBinCertificate := ⟨⟨retention1479,(666651282666809633/250000000000000000),(24651154762240763/125000000000000000),(4095364330316275257/250000000000000000),(189518456652147863977/1000000000000000000),(945711132590231201/1000000000000000000)⟩,(494322662261000329/500000000000000000),(422565318815270087/1000000000000000000),(213431493597516933/1000000000000000000),(165215394131765627/1000000000000000000)⟩
theorem valid1479 : certificate1479.Valid := by decide +kernel
theorem sound1479 : certificate1479.Sound := rat_cut_bin_certificate_sound certificate1479 profilesValid1479 numericValid1479 valid1479

def retention1480 : RatCutRetentionCertificate := ⟨(31/500),(497/8000),(1385958753543660713/11495823748135086563),(451753199865233743/500000000000000000),(51/20),(1179434096764219329447/640000000000000000000),true,MergedCutProfiles.Batch239.profile9577,![MergedCutProfiles.Batch239.profile9577,MergedCutProfiles.Batch239.profile9578,MergedCutProfiles.Batch239.profile9579,MergedCutProfiles.Batch239.profile9580,MergedCutProfiles.Batch239.profile9581,MergedCutProfiles.Batch239.profile9582,MergedCutProfiles.Batch239.profile9583,MergedCutProfiles.Batch239.profile9584,MergedCutProfiles.Batch239.profile9585,MergedCutProfiles.Batch239.profile9586,MergedCutProfiles.Batch239.profile9587,MergedCutProfiles.Batch239.profile9588,MergedCutProfiles.Batch239.profile9589,MergedCutProfiles.Batch239.profile9590,MergedCutProfiles.Batch239.profile9591,MergedCutProfiles.Batch239.profile9592]⟩
theorem profilesValid1480 : retention1480.ProfilesValid := by
  change ∀ j : Fin 16, (retention1480.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch239.valid9577
  · exact MergedCutProfiles.Batch239.valid9578
  · exact MergedCutProfiles.Batch239.valid9579
  · exact MergedCutProfiles.Batch239.valid9580
  · exact MergedCutProfiles.Batch239.valid9581
  · exact MergedCutProfiles.Batch239.valid9582
  · exact MergedCutProfiles.Batch239.valid9583
  · exact MergedCutProfiles.Batch239.valid9584
  · exact MergedCutProfiles.Batch239.valid9585
  · exact MergedCutProfiles.Batch239.valid9586
  · exact MergedCutProfiles.Batch239.valid9587
  · exact MergedCutProfiles.Batch239.valid9588
  · exact MergedCutProfiles.Batch239.valid9589
  · exact MergedCutProfiles.Batch239.valid9590
  · exact MergedCutProfiles.Batch239.valid9591
  · exact MergedCutProfiles.Batch239.valid9592
theorem numericValid1480 : retention1480.NumericValid := by decide +kernel
def certificate1480 : RatCutBinCertificate := ⟨⟨retention1480,(467163169735019277/200000000000000000),(198160259625531349/1000000000000000000),(1028618863260152853/62500000000000000),(189343907653076126043/1000000000000000000),(1771116403262510167/1000000000000000000)⟩,(990071218475946599/1000000000000000000),(346647527782875941/1000000000000000000),(286091473279791083/1000000000000000000),(150842210679656799/1000000000000000000)⟩
theorem valid1480 : certificate1480.Valid := by decide +kernel
theorem sound1480 : certificate1480.Sound := rat_cut_bin_certificate_sound certificate1480 profilesValid1480 numericValid1480 valid1480

def retention1481 : RatCutRetentionCertificate := ⟨(31/500),(497/8000),(3134028604157431999/11495823748135086563),(1385958753543660713/1000000000000000000),(7/4),(373408322996258713349/256000000000000000000),true,MergedCutProfiles.Batch239.profile9593,![MergedCutProfiles.Batch239.profile9593,MergedCutProfiles.Batch239.profile9594,MergedCutProfiles.Batch239.profile9595,MergedCutProfiles.Batch239.profile9596,MergedCutProfiles.Batch239.profile9597,MergedCutProfiles.Batch239.profile9598,MergedCutProfiles.Batch239.profile9599,MergedCutProfiles.Batch240.profile9600,MergedCutProfiles.Batch240.profile9601,MergedCutProfiles.Batch240.profile9602,MergedCutProfiles.Batch240.profile9603,MergedCutProfiles.Batch240.profile9604,MergedCutProfiles.Batch240.profile9605,MergedCutProfiles.Batch240.profile9606,MergedCutProfiles.Batch240.profile9607,MergedCutProfiles.Batch240.profile9608]⟩
theorem profilesValid1481 : retention1481.ProfilesValid := by
  change ∀ j : Fin 16, (retention1481.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch239.valid9593
  · exact MergedCutProfiles.Batch239.valid9594
  · exact MergedCutProfiles.Batch239.valid9595
  · exact MergedCutProfiles.Batch239.valid9596
  · exact MergedCutProfiles.Batch239.valid9597
  · exact MergedCutProfiles.Batch239.valid9598
  · exact MergedCutProfiles.Batch239.valid9599
  · exact MergedCutProfiles.Batch240.valid9600
  · exact MergedCutProfiles.Batch240.valid9601
  · exact MergedCutProfiles.Batch240.valid9602
  · exact MergedCutProfiles.Batch240.valid9603
  · exact MergedCutProfiles.Batch240.valid9604
  · exact MergedCutProfiles.Batch240.valid9605
  · exact MergedCutProfiles.Batch240.valid9606
  · exact MergedCutProfiles.Batch240.valid9607
  · exact MergedCutProfiles.Batch240.valid9608
theorem numericValid1481 : retention1481.NumericValid := by decide +kernel
def certificate1481 : RatCutBinCertificate := ⟨⟨retention1481,(467163169735019277/200000000000000000),(198160259625531349/1000000000000000000),(1028618863260152853/62500000000000000),(189343907653076126043/1000000000000000000),(44043362993659217/31250000000000000)⟩,(990071218475946599/1000000000000000000),(47469063685729991/125000000000000000),(252555157611357851/1000000000000000000),(603528111877833/4000000000000000)⟩
theorem valid1481 : certificate1481.Valid := by decide +kernel
theorem sound1481 : certificate1481.Sound := rat_cut_bin_certificate_sound certificate1481 profilesValid1481 numericValid1481 valid1481

def retention1482 : RatCutRetentionCertificate := ⟨(31/500),(497/8000),(5052762643825385357/11495823748135086563),(3134028604157431999/1000000000000000000),(11/10),(1389103354956758826787/1280000000000000000000),true,MergedCutProfiles.Batch240.profile9609,![MergedCutProfiles.Batch240.profile9609,MergedCutProfiles.Batch240.profile9610,MergedCutProfiles.Batch240.profile9611,MergedCutProfiles.Batch240.profile9612,MergedCutProfiles.Batch240.profile9613,MergedCutProfiles.Batch240.profile9614,MergedCutProfiles.Batch240.profile9615,MergedCutProfiles.Batch240.profile9616,MergedCutProfiles.Batch240.profile9617,MergedCutProfiles.Batch240.profile9618,MergedCutProfiles.Batch240.profile9619,MergedCutProfiles.Batch240.profile9620,MergedCutProfiles.Batch240.profile9621,MergedCutProfiles.Batch240.profile9622,MergedCutProfiles.Batch240.profile9623,MergedCutProfiles.Batch240.profile9624]⟩
theorem profilesValid1482 : retention1482.ProfilesValid := by
  change ∀ j : Fin 16, (retention1482.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch240.valid9609
  · exact MergedCutProfiles.Batch240.valid9610
  · exact MergedCutProfiles.Batch240.valid9611
  · exact MergedCutProfiles.Batch240.valid9612
  · exact MergedCutProfiles.Batch240.valid9613
  · exact MergedCutProfiles.Batch240.valid9614
  · exact MergedCutProfiles.Batch240.valid9615
  · exact MergedCutProfiles.Batch240.valid9616
  · exact MergedCutProfiles.Batch240.valid9617
  · exact MergedCutProfiles.Batch240.valid9618
  · exact MergedCutProfiles.Batch240.valid9619
  · exact MergedCutProfiles.Batch240.valid9620
  · exact MergedCutProfiles.Batch240.valid9621
  · exact MergedCutProfiles.Batch240.valid9622
  · exact MergedCutProfiles.Batch240.valid9623
  · exact MergedCutProfiles.Batch240.valid9624
theorem numericValid1482 : retention1482.NumericValid := by decide +kernel
def certificate1482 : RatCutBinCertificate := ⟨⟨retention1482,(467163169735019277/200000000000000000),(198160259625531349/1000000000000000000),(1028618863260152853/62500000000000000),(189343907653076126043/1000000000000000000),(263572736858727113/250000000000000000)⟩,(990071218475946599/1000000000000000000),(214824747851121377/500000000000000000),(103694145513502623/500000000000000000),(153763456706122621/1000000000000000000)⟩
theorem valid1482 : certificate1482.Valid := by decide +kernel
theorem sound1482 : certificate1482.Sound := rat_cut_bin_certificate_sound certificate1482 profilesValid1482 numericValid1482 valid1482

def retention1483 : RatCutRetentionCertificate := ⟨(31/500),(497/8000),(5637207344928941436/11495823748135086563),(5052762643825385357/1000000000000000000),(11/10),(2036832305011513832986815072183125042671/2021105057530154142800000000000000000000),false,MergedCutProfiles.Batch240.profile9625,(fun _ => MergedCutProfiles.Batch240.profile9625)⟩
theorem profilesValid1483 : retention1483.ProfilesValid := by
  exact MergedCutProfiles.Batch240.valid9625
theorem numericValid1483 : retention1483.NumericValid := by decide +kernel
def certificate1483 : RatCutBinCertificate := ⟨⟨retention1483,(467163169735019277/200000000000000000),(198160259625531349/1000000000000000000),(1028618863260152853/62500000000000000),(189343907653076126043/1000000000000000000),(488419513453352361/500000000000000000)⟩,(990071218475946599/1000000000000000000),(43836714482156883/100000000000000000),(200111726410608429/1000000000000000000),(151553464606826403/1000000000000000000)⟩
theorem valid1483 : certificate1483.Valid := by decide +kernel
theorem sound1483 : certificate1483.Sound := rat_cut_bin_certificate_sound certificate1483 profilesValid1483 numericValid1483 valid1483

def retention1484 : RatCutRetentionCertificate := ⟨(31/500),(497/8000),(5693579418378230851/11495823748135086563),(1409301836232235359/250000000000000000),(11/10),(564971070465587780777034098617053478511/563720734492894143600000000000000000000),false,MergedCutProfiles.Batch240.profile9626,(fun _ => MergedCutProfiles.Batch240.profile9626)⟩
theorem profilesValid1484 : retention1484.ProfilesValid := by
  exact MergedCutProfiles.Batch240.valid9626
theorem numericValid1484 : retention1484.NumericValid := by decide +kernel
def certificate1484 : RatCutBinCertificate := ⟨⟨retention1484,(467163169735019277/200000000000000000),(198160259625531349/1000000000000000000),(1028618863260152853/62500000000000000),(189343907653076126043/1000000000000000000),(485638063855500683/500000000000000000)⟩,(990071218475946599/1000000000000000000),(54570083554642017/125000000000000000),(201605227825983739/1000000000000000000),(154138495587083839/1000000000000000000)⟩
theorem valid1484 : certificate1484.Valid := by decide +kernel
theorem sound1484 : certificate1484.Sound := rat_cut_bin_certificate_sound certificate1484 profilesValid1484 numericValid1484 valid1484

def retention1485 : RatCutRetentionCertificate := ⟨(31/500),(497/8000),(1/2),(5693579418378230851/1000000000000000000),(11/10),(2262435306860086331282245758954671197639/2277431767351292340400000000000000000000),false,MergedCutProfiles.Batch240.profile9627,(fun _ => MergedCutProfiles.Batch240.profile9627)⟩
theorem profilesValid1485 : retention1485.ProfilesValid := by
  exact MergedCutProfiles.Batch240.valid9627
theorem numericValid1485 : retention1485.NumericValid := by decide +kernel
def certificate1485 : RatCutBinCertificate := ⟨⟨retention1485,(467163169735019277/200000000000000000),(198160259625531349/1000000000000000000),(1028618863260152853/62500000000000000),(189343907653076126043/1000000000000000000),(3849893444812173/4000000000000000)⟩,(990071218475946599/1000000000000000000),(22009026142505657/50000000000000000),(198620004810033983/1000000000000000000),(15083572069655441/100000000000000000)⟩
theorem valid1485 : certificate1485.Valid := by decide +kernel
theorem sound1485 : certificate1485.Sound := rat_cut_bin_certificate_sound certificate1485 profilesValid1485 numericValid1485 valid1485

def retention1486 : RatCutRetentionCertificate := ⟨(31/500),(497/8000),(1/2),64,1,(15963211168136796460585064262978589351/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch240.profile9627,(fun _ => MergedCutProfiles.Batch240.profile9627)⟩
theorem profilesValid1486 : retention1486.ProfilesValid := by
  exact MergedCutProfiles.Batch240.valid9627
theorem numericValid1486 : retention1486.NumericValid := by decide +kernel
def certificate1486 : RatCutBinCertificate := ⟨⟨retention1486,(467163169735019277/200000000000000000),(198160259625531349/1000000000000000000),(1028618863260152853/62500000000000000),(189343907653076126043/1000000000000000000),(969576004513165803/1000000000000000000)⟩,(990071218475946599/1000000000000000000),(8064603707085449/20000000000000000),(230535707410463087/1000000000000000000),(217978563686258319/1000000000000000000)⟩
theorem valid1486 : certificate1486.Valid := by decide +kernel
theorem sound1486 : certificate1486.Sound := rat_cut_bin_certificate_sound certificate1486 profilesValid1486 numericValid1486 valid1486

def retention1487 : RatCutRetentionCertificate := ⟨(31/500),(497/8000),(5400153599606260006/11495823748135086563),(3450994702818436267/1000000000000000000),(6/5),(90800721338272089253298844753708679989/86274867570460906675000000000000000000),false,MergedCutProfiles.Batch240.profile9628,(fun _ => MergedCutProfiles.Batch240.profile9628)⟩
theorem profilesValid1487 : retention1487.ProfilesValid := by
  exact MergedCutProfiles.Batch240.valid9628
theorem numericValid1487 : retention1487.NumericValid := by decide +kernel
def certificate1487 : RatCutBinCertificate := ⟨⟨retention1487,(533869401535019277/200000000000000000),(198160259625531349/1000000000000000000),(1028618863260152853/62500000000000000),(189343907653076126043/1000000000000000000),(506940341709368077/500000000000000000)⟩,(9886495369126001/10000000000000000),(4899411361647869/12500000000000000),(120468481139926387/500000000000000000),(41734995422864603/250000000000000000)⟩
theorem valid1487 : certificate1487.Valid := by decide +kernel
theorem sound1487 : certificate1487.Sound := rat_cut_bin_certificate_sound certificate1487 profilesValid1487 numericValid1487 valid1487

def certificates : List RatCutBinCertificate := [certificate1476,certificate1477,certificate1478,certificate1479,certificate1480,certificate1481,certificate1482,certificate1483,certificate1484,certificate1485,certificate1486,certificate1487]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1476,List.forall_mem_cons.mpr ⟨sound1477,List.forall_mem_cons.mpr ⟨sound1478,List.forall_mem_cons.mpr ⟨sound1479,List.forall_mem_cons.mpr ⟨sound1480,List.forall_mem_cons.mpr ⟨sound1481,List.forall_mem_cons.mpr ⟨sound1482,List.forall_mem_cons.mpr ⟨sound1483,List.forall_mem_cons.mpr ⟨sound1484,List.forall_mem_cons.mpr ⟨sound1485,List.forall_mem_cons.mpr ⟨sound1486,List.forall_mem_cons.mpr ⟨sound1487,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch123
