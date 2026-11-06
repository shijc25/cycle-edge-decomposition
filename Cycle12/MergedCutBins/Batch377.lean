import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch033
import Cycle12.MergedCutProfiles.Batch034
import Cycle12.MergedCutProfiles.Batch325
import Cycle12.MergedCutProfiles.Batch326
import Cycle12.MergedCutProfiles.Batch459
import Cycle12.MergedCutProfiles.Batch589
import Cycle12.MergedCutProfiles.Batch590
import Cycle12.MergedCutProfiles.Batch651
import Cycle12.MergedCutProfiles.Batch652

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch377

def retention4524 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(683035195818234654/9500551814030085163711),(676272471107163023/1000000000000000000),4,(25069147671668853587072090404970913/10566757361049422234375000000000000),false,MergedCutProfiles.Batch651.profile26074,(fun _ => MergedCutProfiles.Batch651.profile26074)⟩
theorem profilesValid4524 : retention4524.ProfilesValid := by
  exact MergedCutProfiles.Batch651.valid26074
theorem numericValid4524 : retention4524.NumericValid := by decide +kernel
def certificate4524 : RatCutBinCertificate := ⟨⟨retention4524,(1789879556043966987/1000000000000000000),(12287303118992409/500000000000000000),(4447083476021343527/500000000000000000),(1326750426848419357023/15625000000000000),(1176336205344603781/500000000000000000)⟩,(124997424340558407/125000000000000000),(203412570746558449/250000000000000000),(1159686621990943/62500000000000000),(2241029189765773/250000000000000000)⟩
theorem valid4524 : certificate4524.Valid := by decide +kernel
theorem sound4524 : certificate4524.Sound := rat_cut_bin_certificate_sound certificate4524 profilesValid4524 numericValid4524 valid4524

def retention4525 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(1317206158270331030/9500551814030085163711),(341517597909117327/500000000000000000),4,(6488886027826799017378592578743327287/2732140783272938616000000000000000000),false,MergedCutProfiles.Batch651.profile26075,(fun _ => MergedCutProfiles.Batch651.profile26075)⟩
theorem profilesValid4525 : retention4525.ProfilesValid := by
  exact MergedCutProfiles.Batch651.valid26075
theorem numericValid4525 : retention4525.NumericValid := by decide +kernel
def certificate4525 : RatCutBinCertificate := ⟨⟨retention4525,(1789879556043966987/1000000000000000000),(12287303118992409/500000000000000000),(4447083476021343527/500000000000000000),(1326750426848419357023/15625000000000000),(471047428318378881/200000000000000000)⟩,(124997424340558407/125000000000000000),(810350533874779373/1000000000000000000),(19242175611922057/1000000000000000000),(9320925255664959/1000000000000000000)⟩
theorem valid4525 : certificate4525.Valid := by decide +kernel
theorem sound4525 : certificate4525.Sound := rat_cut_bin_certificate_sound certificate4525 profilesValid4525 numericValid4525 valid4525

def retention4526 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(64000000000000000000/9500551814030085163711),(131720615827033103/100000000000000000),(27/10),(12174943154954286535065673674357640271/5268824633081324120000000000000000000),false,MergedCutProfiles.Batch651.profile26073,(fun _ => MergedCutProfiles.Batch651.profile26073)⟩
theorem profilesValid4526 : retention4526.ProfilesValid := by
  exact MergedCutProfiles.Batch651.valid26073
theorem numericValid4526 : retention4526.NumericValid := by decide +kernel
def certificate4526 : RatCutBinCertificate := ⟨⟨retention4526,(1789879556043966987/1000000000000000000),(12287303118992409/500000000000000000),(4447083476021343527/500000000000000000),(1326750426848419357023/15625000000000000),(459479713016743899/200000000000000000)⟩,(124997424340558407/125000000000000000),(355808394551722253/500000000000000000),(46279985499267863/1000000000000000000),(31775773274821201/1000000000000000000)⟩
theorem valid4526 : certificate4526.Valid := by decide +kernel
theorem sound4526 : certificate4526.Sound := rat_cut_bin_certificate_sound certificate4526 profilesValid4526 numericValid4526 valid4526

def retention4527 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(1/40),64,1,(886842496137115344248498936416864879/409600000000000000000000000000000000),false,MergedCutProfiles.Batch651.profile26076,(fun _ => MergedCutProfiles.Batch651.profile26076)⟩
theorem profilesValid4527 : retention4527.ProfilesValid := by
  exact MergedCutProfiles.Batch651.valid26076
theorem numericValid4527 : retention4527.NumericValid := by decide +kernel
def certificate4527 : RatCutBinCertificate := ⟨⟨retention4527,(1789879556043966987/1000000000000000000),(12287303118992409/500000000000000000),(4447083476021343527/500000000000000000),(1326750426848419357023/15625000000000000),(2160197370980640701/1000000000000000000)⟩,(124997424340558407/125000000000000000),(124631674258983731/200000000000000000),(2052900487433541/25000000000000000),(171591383606564771/1000000000000000000)⟩
theorem valid4527 : certificate4527.Valid := by decide +kernel
theorem sound4527 : certificate4527.Sound := rat_cut_bin_certificate_sound certificate4527 profilesValid4527 numericValid4527 valid4527

def retention4528 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(11949741916027391/161350388347521134173),(63889709254007833/100000000000000000),4,(1489156986953593394653796448829763991/638897092540078330000000000000000000),true,MergedCutProfiles.Batch651.profile26077,![MergedCutProfiles.Batch651.profile26077,MergedCutProfiles.Batch651.profile26078,MergedCutProfiles.Batch651.profile26079,MergedCutProfiles.Batch652.profile26080,MergedCutProfiles.Batch589.profile23598,MergedCutProfiles.Batch652.profile26081,MergedCutProfiles.Batch652.profile26082,MergedCutProfiles.Batch652.profile26083,MergedCutProfiles.Batch589.profile23599,MergedCutProfiles.Batch589.profile23599,MergedCutProfiles.Batch652.profile26084,MergedCutProfiles.Batch652.profile26085,MergedCutProfiles.Batch652.profile26085,MergedCutProfiles.Batch590.profile23600,MergedCutProfiles.Batch652.profile26086,MergedCutProfiles.Batch652.profile26086]⟩
theorem profilesValid4528 : retention4528.ProfilesValid := by
  change ∀ j : Fin 16, (retention4528.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch651.valid26077
  · exact MergedCutProfiles.Batch651.valid26078
  · exact MergedCutProfiles.Batch651.valid26079
  · exact MergedCutProfiles.Batch652.valid26080
  · exact MergedCutProfiles.Batch589.valid23598
  · exact MergedCutProfiles.Batch652.valid26081
  · exact MergedCutProfiles.Batch652.valid26082
  · exact MergedCutProfiles.Batch652.valid26083
  · exact MergedCutProfiles.Batch589.valid23599
  · exact MergedCutProfiles.Batch589.valid23599
  · exact MergedCutProfiles.Batch652.valid26084
  · exact MergedCutProfiles.Batch652.valid26085
  · exact MergedCutProfiles.Batch652.valid26085
  · exact MergedCutProfiles.Batch590.valid23600
  · exact MergedCutProfiles.Batch652.valid26086
  · exact MergedCutProfiles.Batch652.valid26086
theorem numericValid4528 : retention4528.NumericValid := by decide +kernel
def certificate4528 : RatCutBinCertificate := ⟨⟨retention4528,(239598221759100611/125000000000000000),(5353370290855499/200000000000000000),(9015103415958768741/1000000000000000000),(39466809037281437695057/500000000000000000),(1154029938030034433/500000000000000000)⟩,(249994078306937349/250000000000000000),(486522278708105407/1000000000000000000),(2036895953117639/12500000000000000),(38352115313452067/500000000000000000)⟩
theorem valid4528 : certificate4528.Valid := by decide +kernel
theorem sound4528 : certificate4528.Sound := rat_cut_bin_certificate_sound certificate4528 profilesValid4528 numericValid4528 valid4528

def retention4529 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(212254575500000000/1452153495127690207557),(322643031732739557/500000000000000000),4,(74754230657424241917/32000000000000000000),true,MergedCutProfiles.Batch651.profile26078,![MergedCutProfiles.Batch651.profile26078,MergedCutProfiles.Batch652.profile26080,MergedCutProfiles.Batch652.profile26081,MergedCutProfiles.Batch652.profile26083,MergedCutProfiles.Batch589.profile23599,MergedCutProfiles.Batch652.profile26085,MergedCutProfiles.Batch590.profile23600,MergedCutProfiles.Batch652.profile26086,MergedCutProfiles.Batch590.profile23601,MergedCutProfiles.Batch459.profile18368,MergedCutProfiles.Batch590.profile23602,MergedCutProfiles.Batch652.profile26087,MergedCutProfiles.Batch590.profile23603,MergedCutProfiles.Batch590.profile23611,MergedCutProfiles.Batch590.profile23611,MergedCutProfiles.Batch590.profile23604]⟩
theorem profilesValid4529 : retention4529.ProfilesValid := by
  change ∀ j : Fin 16, (retention4529.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch651.valid26078
  · exact MergedCutProfiles.Batch652.valid26080
  · exact MergedCutProfiles.Batch652.valid26081
  · exact MergedCutProfiles.Batch652.valid26083
  · exact MergedCutProfiles.Batch589.valid23599
  · exact MergedCutProfiles.Batch652.valid26085
  · exact MergedCutProfiles.Batch590.valid23600
  · exact MergedCutProfiles.Batch652.valid26086
  · exact MergedCutProfiles.Batch590.valid23601
  · exact MergedCutProfiles.Batch459.valid18368
  · exact MergedCutProfiles.Batch590.valid23602
  · exact MergedCutProfiles.Batch652.valid26087
  · exact MergedCutProfiles.Batch590.valid23603
  · exact MergedCutProfiles.Batch590.valid23611
  · exact MergedCutProfiles.Batch590.valid23611
  · exact MergedCutProfiles.Batch590.valid23604
theorem numericValid4529 : retention4529.NumericValid := by decide +kernel
def certificate4529 : RatCutBinCertificate := ⟨⟨retention4529,(239598221759100611/125000000000000000),(5353370290855499/200000000000000000),(9015103415958768741/1000000000000000000),(39466809037281437695057/500000000000000000),(2313305098718348293/1000000000000000000)⟩,(249994078306937349/250000000000000000),(60288403647184027/125000000000000000),(166006802847099183/1000000000000000000),(19607612293887509/250000000000000000)⟩
theorem valid4529 : certificate4529.Valid := by decide +kernel
theorem sound4529 : certificate4529.Sound := rat_cut_bin_certificate_sound certificate4529 profilesValid4529 numericValid4529 valid4529

def retention4530 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(1985013905673067790/1452153495127690207557),(1273527453/1000000000),(5/2),(37530661484246146603/16000000000000000000),true,MergedCutProfiles.Batch590.profile23601,![MergedCutProfiles.Batch590.profile23601,MergedCutProfiles.Batch590.profile23605,MergedCutProfiles.Batch590.profile23608,MergedCutProfiles.Batch590.profile23610,MergedCutProfiles.Batch326.profile13047,MergedCutProfiles.Batch459.profile18379,MergedCutProfiles.Batch459.profile18374,MergedCutProfiles.Batch652.profile26088,MergedCutProfiles.Batch652.profile26089,MergedCutProfiles.Batch326.profile13048,MergedCutProfiles.Batch033.profile1353,MergedCutProfiles.Batch652.profile26090,MergedCutProfiles.Batch326.profile13056,MergedCutProfiles.Batch325.profile13026,MergedCutProfiles.Batch326.profile13049,MergedCutProfiles.Batch652.profile26091]⟩
theorem profilesValid4530 : retention4530.ProfilesValid := by
  change ∀ j : Fin 16, (retention4530.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch590.valid23601
  · exact MergedCutProfiles.Batch590.valid23605
  · exact MergedCutProfiles.Batch590.valid23608
  · exact MergedCutProfiles.Batch590.valid23610
  · exact MergedCutProfiles.Batch326.valid13047
  · exact MergedCutProfiles.Batch459.valid18379
  · exact MergedCutProfiles.Batch459.valid18374
  · exact MergedCutProfiles.Batch652.valid26088
  · exact MergedCutProfiles.Batch652.valid26089
  · exact MergedCutProfiles.Batch326.valid13048
  · exact MergedCutProfiles.Batch033.valid1353
  · exact MergedCutProfiles.Batch652.valid26090
  · exact MergedCutProfiles.Batch326.valid13056
  · exact MergedCutProfiles.Batch325.valid13026
  · exact MergedCutProfiles.Batch326.valid13049
  · exact MergedCutProfiles.Batch652.valid26091
theorem numericValid4530 : retention4530.NumericValid := by decide +kernel
def certificate4530 : RatCutBinCertificate := ⟨⟨retention4530,(239598221759100611/125000000000000000),(5353370290855499/200000000000000000),(9015103415958768741/1000000000000000000),(39466809037281437695057/500000000000000000),(2331438462290367/1000000000000000)⟩,(249994078306937349/250000000000000000),(1631186606193831/5000000000000000),(77080780138853863/250000000000000000),(222387187863844459/1000000000000000000)⟩
theorem valid4530 : certificate4530.Valid := by decide +kernel
theorem sound4530 : certificate4530.Sound := rat_cut_bin_certificate_sound certificate4530 profilesValid4530 numericValid4530 valid4530

def retention4531 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(32000000000000000000/4356460485383070622671),(595504171701920337/50000000000000000),1,(104573458343437495771777606445033573951/47640333736153626960000000000000000000),false,MergedCutProfiles.Batch652.profile26092,(fun _ => MergedCutProfiles.Batch652.profile26092)⟩
theorem profilesValid4531 : retention4531.ProfilesValid := by
  exact MergedCutProfiles.Batch652.valid26092
theorem numericValid4531 : retention4531.NumericValid := by decide +kernel
def certificate4531 : RatCutBinCertificate := ⟨⟨retention4531,(239598221759100611/125000000000000000),(5353370290855499/200000000000000000),(9015103415958768741/1000000000000000000),(39466809037281437695057/500000000000000000),(2189370262445636357/1000000000000000000)⟩,(249994078306937349/250000000000000000),(198618220500892837/1000000000000000000),(240016960721765229/500000000000000000),(177550937057006281/200000000000000000)⟩
theorem valid4531 : certificate4531.Valid := by decide +kernel
theorem sound4531 : certificate4531.Sound := rat_cut_bin_certificate_sound certificate4531 profilesValid4531 numericValid4531 valid4531

def retention4532 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(1/2),64,1,(255373261473046173696668873617783571559/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch034.profile1386,(fun _ => MergedCutProfiles.Batch034.profile1386)⟩
theorem profilesValid4532 : retention4532.ProfilesValid := by
  exact MergedCutProfiles.Batch034.valid1386
theorem numericValid4532 : retention4532.NumericValid := by decide +kernel
def certificate4532 : RatCutBinCertificate := ⟨⟨retention4532,(239598221759100611/125000000000000000),(5353370290855499/200000000000000000),(9015103415958768741/1000000000000000000),(39466809037281437695057/500000000000000000),(991860651015084793/1000000000000000000)⟩,(249994078306937349/250000000000000000),(406412149680793813/1000000000000000000),(45531666037861087/200000000000000000),(111176971902488411/500000000000000000)⟩
theorem valid4532 : certificate4532.Valid := by decide +kernel
theorem sound4532 : certificate4532.Sound := rat_cut_bin_certificate_sound certificate4532 profilesValid4532 numericValid4532 valid4532

def retention4533 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(32000000000000000000/4356460485383070622671),(18931505681420751009/1000000000000000000),1,(169360261147376304261910634355991761299/75726022725683004036000000000000000000),false,MergedCutProfiles.Batch652.profile26092,(fun _ => MergedCutProfiles.Batch652.profile26092)⟩
theorem profilesValid4533 : retention4533.ProfilesValid := by
  exact MergedCutProfiles.Batch652.valid26092
theorem numericValid4533 : retention4533.NumericValid := by decide +kernel
def certificate4533 : RatCutBinCertificate := ⟨⟨retention4533,(224710120759100611/125000000000000000),(5353370290855499/200000000000000000),(9015103415958768741/1000000000000000000),(39466809037281437695057/500000000000000000),(2231149427836022933/1000000000000000000)⟩,(999977785071957639/1000000000000000000),(805168893181451/31250000000000000),(85670004243334007/100000000000000000),(1709867796354221387/1000000000000000000)⟩
theorem valid4533 : certificate4533.Valid := by decide +kernel
theorem sound4533 : certificate4533.Sound := rat_cut_bin_certificate_sound certificate4533 profilesValid4533 numericValid4533 valid4533

def retention4534 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(1/2),64,1,(255373261473046173696668873617783571559/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch034.profile1386,(fun _ => MergedCutProfiles.Batch034.profile1386)⟩
theorem profilesValid4534 : retention4534.ProfilesValid := by
  exact MergedCutProfiles.Batch034.valid1386
theorem numericValid4534 : retention4534.NumericValid := by decide +kernel
def certificate4534 : RatCutBinCertificate := ⟨⟨retention4534,(224710120759100611/125000000000000000),(5353370290855499/200000000000000000),(9015103415958768741/1000000000000000000),(39466809037281437695057/500000000000000000),(496107143263979593/500000000000000000)⟩,(999977785071957639/1000000000000000000),(14484388219157429/250000000000000000),(767408411494968713/1000000000000000000),(374896115914188953/500000000000000000)⟩
theorem valid4534 : certificate4534.Valid := by decide +kernel
theorem sound4534 : certificate4534.Sound := rat_cut_bin_certificate_sound certificate4534 profilesValid4534 numericValid4534 valid4534

def retention4535 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(343432907114979637/4356460485383070622671),(680065162603920073/1000000000000000000),4,(323229508861829320841343077647951599/136013032520784014600000000000000000),false,MergedCutProfiles.Batch652.profile26093,(fun _ => MergedCutProfiles.Batch652.profile26093)⟩
theorem profilesValid4535 : retention4535.ProfilesValid := by
  exact MergedCutProfiles.Batch652.valid26093
theorem numericValid4535 : retention4535.NumericValid := by decide +kernel
def certificate4535 : RatCutBinCertificate := ⟨⟨retention4535,(223784453134100611/125000000000000000),(5353370290855499/200000000000000000),(9015103415958768741/1000000000000000000),(39466809037281437695057/500000000000000000),(2355197717495907329/1000000000000000000)⟩,(999977876583862277/1000000000000000000),(80818331632092361/100000000000000000),(19700816864177233/1000000000000000000),(148993112203687/15625000000000000)⟩
theorem valid4535 : certificate4535.Valid := by decide +kernel
theorem sound4535 : certificate4535.Sound := rat_cut_bin_certificate_sound certificate4535 profilesValid4535 numericValid4535 valid4535

def certificates : List RatCutBinCertificate := [certificate4524,certificate4525,certificate4526,certificate4527,certificate4528,certificate4529,certificate4530,certificate4531,certificate4532,certificate4533,certificate4534,certificate4535]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4524,List.forall_mem_cons.mpr ⟨sound4525,List.forall_mem_cons.mpr ⟨sound4526,List.forall_mem_cons.mpr ⟨sound4527,List.forall_mem_cons.mpr ⟨sound4528,List.forall_mem_cons.mpr ⟨sound4529,List.forall_mem_cons.mpr ⟨sound4530,List.forall_mem_cons.mpr ⟨sound4531,List.forall_mem_cons.mpr ⟨sound4532,List.forall_mem_cons.mpr ⟨sound4533,List.forall_mem_cons.mpr ⟨sound4534,List.forall_mem_cons.mpr ⟨sound4535,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch377
