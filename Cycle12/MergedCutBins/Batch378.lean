import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch034
import Cycle12.MergedCutProfiles.Batch035
import Cycle12.MergedCutProfiles.Batch036
import Cycle12.MergedCutProfiles.Batch326
import Cycle12.MergedCutProfiles.Batch327
import Cycle12.MergedCutProfiles.Batch459
import Cycle12.MergedCutProfiles.Batch460
import Cycle12.MergedCutProfiles.Batch590
import Cycle12.MergedCutProfiles.Batch591
import Cycle12.MergedCutProfiles.Batch652

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch378

def retention4536 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(642818629332061681/4356460485383070622671),(343432907114979637/500000000000000000),4,(16339202770142937295115050871898907/6868658142299592740000000000000000),false,MergedCutProfiles.Batch652.profile26094,(fun _ => MergedCutProfiles.Batch652.profile26094)⟩
theorem profilesValid4536 : retention4536.ProfilesValid := by
  exact MergedCutProfiles.Batch652.valid26094
theorem numericValid4536 : retention4536.NumericValid := by decide +kernel
def certificate4536 : RatCutBinCertificate := ⟨⟨retention4536,(223784453134100611/125000000000000000),(5353370290855499/200000000000000000),(9015103415958768741/1000000000000000000),(39466809037281437695057/500000000000000000),(117877176417336583/50000000000000000)⟩,(999977876583862277/1000000000000000000),(805016529392675617/1000000000000000000),(20381448470841321/1000000000000000000),(2472628109789691/250000000000000000)⟩
theorem valid4536 : certificate4536.Valid := by decide +kernel
theorem sound4536 : certificate4536.Sound := rat_cut_bin_certificate_sound certificate4536 profilesValid4536 numericValid4536 valid4536

def retention4537 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(28197492631157367353/4356460485383070622671),(642818629332061681/500000000000000000),(11/4),(9522551060810655590937876458341194979/4114039227725194758400000000000000000),false,MergedCutProfiles.Batch652.profile26095,(fun _ => MergedCutProfiles.Batch652.profile26095)⟩
theorem profilesValid4537 : retention4537.ProfilesValid := by
  exact MergedCutProfiles.Batch652.valid26095
theorem numericValid4537 : retention4537.NumericValid := by decide +kernel
def certificate4537 : RatCutBinCertificate := ⟨⟨retention4537,(223784453134100611/125000000000000000),(5353370290855499/200000000000000000),(9015103415958768741/1000000000000000000),(39466809037281437695057/500000000000000000),(1150014951599304927/500000000000000000)⟩,(999977876583862277/1000000000000000000),(28494328757912357/40000000000000000),(1438378922360633/31250000000000000),(31131237794029961/1000000000000000000)⟩
theorem valid4537 : certificate4537.Valid := by decide +kernel
theorem sound4537 : certificate4537.Sound := rat_cut_bin_certificate_sound certificate4537 profilesValid4537 numericValid4537 valid4537

def retention4538 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(1/40),(28197492631157367353/500000000000000000),1,(24402314146482480898086159864133116999/11278997052462946941200000000000000000),false,MergedCutProfiles.Batch652.profile26096,(fun _ => MergedCutProfiles.Batch652.profile26096)⟩
theorem profilesValid4538 : retention4538.ProfilesValid := by
  exact MergedCutProfiles.Batch652.valid26096
theorem numericValid4538 : retention4538.NumericValid := by decide +kernel
def certificate4538 : RatCutBinCertificate := ⟨⟨retention4538,(223784453134100611/125000000000000000),(5353370290855499/200000000000000000),(9015103415958768741/1000000000000000000),(39466809037281437695057/500000000000000000),(269775319997247189/125000000000000000)⟩,(999977876583862277/1000000000000000000),(15610747733226147/25000000000000000),(16303187232449301/200000000000000000),(84719808731870933/500000000000000000)⟩
theorem valid4538 : certificate4538.Valid := by decide +kernel
theorem sound4538 : certificate4538.Sound := rat_cut_bin_certificate_sound certificate4538 profilesValid4538 numericValid4538 valid4538

def retention4539 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(683577210601775836/8015987760575257207405),(160990163543941083/250000000000000000),4,(37401702993833057203/16000000000000000000),true,MergedCutProfiles.Batch652.profile26097,![MergedCutProfiles.Batch652.profile26097,MergedCutProfiles.Batch652.profile26098,MergedCutProfiles.Batch652.profile26099,MergedCutProfiles.Batch590.profile23635,MergedCutProfiles.Batch652.profile26100,MergedCutProfiles.Batch652.profile26101,MergedCutProfiles.Batch652.profile26102,MergedCutProfiles.Batch590.profile23636,MergedCutProfiles.Batch591.profile23653,MergedCutProfiles.Batch591.profile23653,MergedCutProfiles.Batch652.profile26103,MergedCutProfiles.Batch590.profile23637,MergedCutProfiles.Batch652.profile26104,MergedCutProfiles.Batch652.profile26104,MergedCutProfiles.Batch652.profile26105,MergedCutProfiles.Batch652.profile26105]⟩
theorem profilesValid4539 : retention4539.ProfilesValid := by
  change ∀ j : Fin 16, (retention4539.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch652.valid26097
  · exact MergedCutProfiles.Batch652.valid26098
  · exact MergedCutProfiles.Batch652.valid26099
  · exact MergedCutProfiles.Batch590.valid23635
  · exact MergedCutProfiles.Batch652.valid26100
  · exact MergedCutProfiles.Batch652.valid26101
  · exact MergedCutProfiles.Batch652.valid26102
  · exact MergedCutProfiles.Batch590.valid23636
  · exact MergedCutProfiles.Batch591.valid23653
  · exact MergedCutProfiles.Batch591.valid23653
  · exact MergedCutProfiles.Batch652.valid26103
  · exact MergedCutProfiles.Batch590.valid23637
  · exact MergedCutProfiles.Batch652.valid26104
  · exact MergedCutProfiles.Batch652.valid26104
  · exact MergedCutProfiles.Batch652.valid26105
  · exact MergedCutProfiles.Batch652.valid26105
theorem numericValid4539 : retention4539.NumericValid := by decide +kernel
def certificate4539 : RatCutBinCertificate := ⟨⟨retention4539,(119611175730592539/62500000000000000),(14531335098101001/500000000000000000),(2284646189452429893/250000000000000000),(73616648279811504845921/1000000000000000000),(2313261516131237951/1000000000000000000)⟩,(99997469927906011/100000000000000000),(481896283049848277/1000000000000000000),(166306627838924113/1000000000000000000),(39270575964701427/500000000000000000)⟩
theorem valid4539 : certificate4539.Valid := by decide +kernel
theorem sound4539 : certificate4539.Sound := rat_cut_bin_certificate_sound certificate4539 profilesValid4539 numericValid4539 valid4539

def retention4540 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(250191483600000000/1603197552115051441481),(170894302650443959/250000000000000000),4,(475545891563451683/200000000000000000),true,MergedCutProfiles.Batch652.profile26098,![MergedCutProfiles.Batch652.profile26098,MergedCutProfiles.Batch590.profile23635,MergedCutProfiles.Batch652.profile26101,MergedCutProfiles.Batch652.profile26102,MergedCutProfiles.Batch591.profile23653,MergedCutProfiles.Batch652.profile26103,MergedCutProfiles.Batch590.profile23637,MergedCutProfiles.Batch652.profile26105,MergedCutProfiles.Batch590.profile23638,MergedCutProfiles.Batch459.profile18390,MergedCutProfiles.Batch590.profile23639,MergedCutProfiles.Batch652.profile26106,MergedCutProfiles.Batch591.profile23640,MergedCutProfiles.Batch591.profile23640,MergedCutProfiles.Batch591.profile23646,MergedCutProfiles.Batch591.profile23641]⟩
theorem profilesValid4540 : retention4540.ProfilesValid := by
  change ∀ j : Fin 16, (retention4540.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch652.valid26098
  · exact MergedCutProfiles.Batch590.valid23635
  · exact MergedCutProfiles.Batch652.valid26101
  · exact MergedCutProfiles.Batch652.valid26102
  · exact MergedCutProfiles.Batch591.valid23653
  · exact MergedCutProfiles.Batch652.valid26103
  · exact MergedCutProfiles.Batch590.valid23637
  · exact MergedCutProfiles.Batch652.valid26105
  · exact MergedCutProfiles.Batch590.valid23638
  · exact MergedCutProfiles.Batch459.valid18390
  · exact MergedCutProfiles.Batch590.valid23639
  · exact MergedCutProfiles.Batch652.valid26106
  · exact MergedCutProfiles.Batch591.valid23640
  · exact MergedCutProfiles.Batch591.valid23640
  · exact MergedCutProfiles.Batch591.valid23646
  · exact MergedCutProfiles.Batch591.valid23641
theorem numericValid4540 : retention4540.NumericValid := by decide +kernel
def certificate4540 : RatCutBinCertificate := ⟨⟨retention4540,(119611175730592539/62500000000000000),(14531335098101001/500000000000000000),(2284646189452429893/250000000000000000),(73616648279811504845921/1000000000000000000),(235338453705017107/100000000000000000)⟩,(99997469927906011/100000000000000000),(455982608789156733/1000000000000000000),(92966870867798731/500000000000000000),(18004066736593647/200000000000000000)⟩
theorem valid4540 : certificate4540.Valid := by decide +kernel
theorem sound4540 : certificate4540.Sound := rat_cut_bin_certificate_sound certificate4540 profilesValid4540 numericValid4540 valid4540

def retention4541 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(692152031362947150/1603197552115051441481),(625478709/500000000),(5/2),(3935034819145202122264995715862014437/1667943224000000000000000000000000000),true,MergedCutProfiles.Batch652.profile26100,![MergedCutProfiles.Batch652.profile26100,MergedCutProfiles.Batch652.profile26103,MergedCutProfiles.Batch652.profile26105,MergedCutProfiles.Batch590.profile23639,MergedCutProfiles.Batch591.profile23640,MergedCutProfiles.Batch652.profile26107,MergedCutProfiles.Batch459.profile18391,MergedCutProfiles.Batch591.profile23642,MergedCutProfiles.Batch591.profile23647,MergedCutProfiles.Batch326.profile13065,MergedCutProfiles.Batch459.profile18392,MergedCutProfiles.Batch591.profile23644,MergedCutProfiles.Batch591.profile23656,MergedCutProfiles.Batch460.profile18402,MergedCutProfiles.Batch460.profile18411,MergedCutProfiles.Batch591.profile23654]⟩
theorem profilesValid4541 : retention4541.ProfilesValid := by
  change ∀ j : Fin 16, (retention4541.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch652.valid26100
  · exact MergedCutProfiles.Batch652.valid26103
  · exact MergedCutProfiles.Batch652.valid26105
  · exact MergedCutProfiles.Batch590.valid23639
  · exact MergedCutProfiles.Batch591.valid23640
  · exact MergedCutProfiles.Batch652.valid26107
  · exact MergedCutProfiles.Batch459.valid18391
  · exact MergedCutProfiles.Batch591.valid23642
  · exact MergedCutProfiles.Batch591.valid23647
  · exact MergedCutProfiles.Batch326.valid13065
  · exact MergedCutProfiles.Batch459.valid18392
  · exact MergedCutProfiles.Batch591.valid23644
  · exact MergedCutProfiles.Batch591.valid23656
  · exact MergedCutProfiles.Batch460.valid18402
  · exact MergedCutProfiles.Batch460.valid18411
  · exact MergedCutProfiles.Batch591.valid23654
theorem numericValid4541 : retention4541.NumericValid := by decide +kernel
def certificate4541 : RatCutBinCertificate := ⟨⟨retention4541,(119611175730592539/62500000000000000),(14531335098101001/500000000000000000),(2284646189452429893/250000000000000000),(73616648279811504845921/1000000000000000000),(1171999156604861089/500000000000000000)⟩,(99997469927906011/100000000000000000),(163404624994691361/500000000000000000),(307683163414047563/1000000000000000000),(221937803663658161/1000000000000000000)⟩
theorem valid4541 : certificate4541.Valid := by decide +kernel
theorem sound4541 : certificate4541.Sound := rat_cut_bin_certificate_sound certificate4541 profilesValid4541 numericValid4541 valid4541

def retention4542 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(12800000000000000000/1603197552115051441481),(13843040627258943/4000000000000000),(7/5),(71829992846562018971/32000000000000000000),true,MergedCutProfiles.Batch327.profile13088,![MergedCutProfiles.Batch327.profile13088,MergedCutProfiles.Batch035.profile1434,MergedCutProfiles.Batch327.profile13089,MergedCutProfiles.Batch035.profile1435,MergedCutProfiles.Batch327.profile13090,MergedCutProfiles.Batch652.profile26108,MergedCutProfiles.Batch652.profile26109,MergedCutProfiles.Batch327.profile13092,MergedCutProfiles.Batch327.profile13093,MergedCutProfiles.Batch034.profile1398,MergedCutProfiles.Batch034.profile1399,MergedCutProfiles.Batch327.profile13094,MergedCutProfiles.Batch327.profile13095,MergedCutProfiles.Batch652.profile26110,MergedCutProfiles.Batch035.profile1414,MergedCutProfiles.Batch036.profile1440]⟩
theorem profilesValid4542 : retention4542.ProfilesValid := by
  change ∀ j : Fin 16, (retention4542.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch327.valid13088
  · exact MergedCutProfiles.Batch035.valid1434
  · exact MergedCutProfiles.Batch327.valid13089
  · exact MergedCutProfiles.Batch035.valid1435
  · exact MergedCutProfiles.Batch327.valid13090
  · exact MergedCutProfiles.Batch652.valid26108
  · exact MergedCutProfiles.Batch652.valid26109
  · exact MergedCutProfiles.Batch327.valid13092
  · exact MergedCutProfiles.Batch327.valid13093
  · exact MergedCutProfiles.Batch034.valid1398
  · exact MergedCutProfiles.Batch034.valid1399
  · exact MergedCutProfiles.Batch327.valid13094
  · exact MergedCutProfiles.Batch327.valid13095
  · exact MergedCutProfiles.Batch652.valid26110
  · exact MergedCutProfiles.Batch035.valid1414
  · exact MergedCutProfiles.Batch036.valid1440
theorem numericValid4542 : retention4542.NumericValid := by decide +kernel
def certificate4542 : RatCutBinCertificate := ⟨⟨retention4542,(119611175730592539/62500000000000000),(14531335098101001/500000000000000000),(2284646189452429893/250000000000000000),(73616648279811504845921/1000000000000000000),(447233310944507083/200000000000000000)⟩,(99997469927906011/100000000000000000),(236931209362534207/1000000000000000000),(210886511131235231/500000000000000000),(506640398284451499/1000000000000000000)⟩
theorem valid4542 : certificate4542.Valid := by decide +kernel
theorem sound4542 : certificate4542.Sound := rat_cut_bin_certificate_sound certificate4542 profilesValid4542 numericValid4542 valid4542

def retention4543 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(1/2),64,1,(255373741328073457130936126923517436199/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch036.profile1465,(fun _ => MergedCutProfiles.Batch036.profile1465)⟩
theorem profilesValid4543 : retention4543.ProfilesValid := by
  exact MergedCutProfiles.Batch036.valid1465
theorem numericValid4543 : retention4543.NumericValid := by decide +kernel
def certificate4543 : RatCutBinCertificate := ⟨⟨retention4543,(119611175730592539/62500000000000000),(14531335098101001/500000000000000000),(2284646189452429893/250000000000000000),(73616648279811504845921/1000000000000000000),(198293489542442369/200000000000000000)⟩,(99997469927906011/100000000000000000),(406795323237806547/1000000000000000000),(22731351897166197/100000000000000000),(110965066763530371/500000000000000000)⟩
theorem valid4543 : certificate4543.Valid := by decide +kernel
theorem sound4543 : certificate4543.Sound := rat_cut_bin_certificate_sound certificate4543 profilesValid4543 numericValid4543 valid4543

def retention4544 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(12800000000000000000/1603197552115051441481),(19169626002582000879/1000000000000000000),1,(19021738093900711905994612583423220747/8519833778925333724000000000000000000),false,MergedCutProfiles.Batch652.profile26111,(fun _ => MergedCutProfiles.Batch652.profile26111)⟩
theorem profilesValid4544 : retention4544.ProfilesValid := by
  exact MergedCutProfiles.Batch652.valid26111
theorem numericValid4544 : retention4544.NumericValid := by decide +kernel
def certificate4544 : RatCutBinCertificate := ⟨⟨retention4544,(112386668918092539/62500000000000000),(14531335098101001/500000000000000000),(2284646189452429893/250000000000000000),(73616648279811504845921/1000000000000000000),(44538466079880709/20000000000000000)⟩,(99997622744186917/100000000000000000),(15915504078941/625000000000000),(857591628653342457/1000000000000000000),(855490301291939623/500000000000000000)⟩
theorem valid4544 : certificate4544.Valid := by decide +kernel
theorem sound4544 : certificate4544.Sound := rat_cut_bin_certificate_sound certificate4544 profilesValid4544 numericValid4544 valid4544

def retention4545 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(1/2),64,1,(255373741328073457130936126923517436199/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch036.profile1465,(fun _ => MergedCutProfiles.Batch036.profile1465)⟩
theorem profilesValid4545 : retention4545.ProfilesValid := by
  exact MergedCutProfiles.Batch036.valid1465
theorem numericValid4545 : retention4545.NumericValid := by decide +kernel
def certificate4545 : RatCutBinCertificate := ⟨⟨retention4545,(112386668918092539/62500000000000000),(14531335098101001/500000000000000000),(2284646189452429893/250000000000000000),(73616648279811504845921/1000000000000000000),(991835055547659459/1000000000000000000)⟩,(99997622744186917/100000000000000000),(28587500899439833/500000000000000000),(384696772930560091/500000000000000000),(751447682645258233/1000000000000000000)⟩
theorem valid4545 : certificate4545.Valid := by decide +kernel
theorem sound4545 : certificate4545.Sound := rat_cut_bin_certificate_sound certificate4545 profilesValid4545 numericValid4545 valid4545

def retention4546 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(664135122034151511/8015987760575257207405),(164389881691621661/250000000000000000),4,(6189253559381732865939197929444041207/2630238107065946576000000000000000000),false,MergedCutProfiles.Batch652.profile26112,(fun _ => MergedCutProfiles.Batch652.profile26112)⟩
theorem profilesValid4546 : retention4546.ProfilesValid := by
  exact MergedCutProfiles.Batch652.valid26112
theorem numericValid4546 : retention4546.NumericValid := by decide +kernel
def certificate4546 : RatCutBinCertificate := ⟨⟨retention4546,(110184817168092539/62500000000000000),(14531335098101001/500000000000000000),(2284646189452429893/250000000000000000),(73616648279811504845921/1000000000000000000),(2330688972236611813/1000000000000000000)⟩,(999976693188231963/1000000000000000000),(442480978940715519/500000000000000000),(3443146133041837/500000000000000000),(3284688781426651/1000000000000000000)⟩
theorem valid4546 : certificate4546.Valid := by decide +kernel
theorem sound4546 : certificate4546.Sound := rat_cut_bin_certificate_sound certificate4546 profilesValid4546 numericValid4546 valid4546

def retention4547 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(1081443322476767786/8015987760575257207405),(664135122034151511/1000000000000000000),4,(1565946440392113011860665373390924259/664135122034151511000000000000000000),false,MergedCutProfiles.Batch652.profile26113,(fun _ => MergedCutProfiles.Batch652.profile26113)⟩
theorem profilesValid4547 : retention4547.ProfilesValid := by
  exact MergedCutProfiles.Batch652.valid26113
theorem numericValid4547 : retention4547.NumericValid := by decide +kernel
def certificate4547 : RatCutBinCertificate := ⟨⟨retention4547,(110184817168092539/62500000000000000),(14531335098101001/500000000000000000),(2284646189452429893/250000000000000000),(73616648279811504845921/1000000000000000000),(1167723457328773573/500000000000000000)⟩,(999976693188231963/1000000000000000000),(440298410262820133/500000000000000000),(7430541828960321/1000000000000000000),(711321623151521/200000000000000000)⟩
theorem valid4547 : certificate4547.Valid := by decide +kernel
theorem sound4547 : certificate4547.Sound := rat_cut_bin_certificate_sound certificate4547 profilesValid4547 numericValid4547 valid4547

def certificates : List RatCutBinCertificate := [certificate4536,certificate4537,certificate4538,certificate4539,certificate4540,certificate4541,certificate4542,certificate4543,certificate4544,certificate4545,certificate4546,certificate4547]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4536,List.forall_mem_cons.mpr ⟨sound4537,List.forall_mem_cons.mpr ⟨sound4538,List.forall_mem_cons.mpr ⟨sound4539,List.forall_mem_cons.mpr ⟨sound4540,List.forall_mem_cons.mpr ⟨sound4541,List.forall_mem_cons.mpr ⟨sound4542,List.forall_mem_cons.mpr ⟨sound4543,List.forall_mem_cons.mpr ⟨sound4544,List.forall_mem_cons.mpr ⟨sound4545,List.forall_mem_cons.mpr ⟨sound4546,List.forall_mem_cons.mpr ⟨sound4547,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch378
