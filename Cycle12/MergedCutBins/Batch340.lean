import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch380
import Cycle12.MergedCutProfiles.Batch381
import Cycle12.MergedCutProfiles.Batch382
import Cycle12.MergedCutProfiles.Batch499
import Cycle12.MergedCutProfiles.Batch500
import Cycle12.MergedCutProfiles.Batch501
import Cycle12.MergedCutProfiles.Batch502
import Cycle12.MergedCutProfiles.Batch613
import Cycle12.MergedCutProfiles.Batch614
import Cycle12.MergedCutProfiles.Batch615

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch340

def retention4080 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(1847574112046853951/333738622226756504476),(1110649687/1000000000),(14/5),(4681266099062942977/2000000000000000000),true,MergedCutProfiles.Batch614.profile24570,![MergedCutProfiles.Batch614.profile24570,MergedCutProfiles.Batch614.profile24571,MergedCutProfiles.Batch613.profile24555,MergedCutProfiles.Batch613.profile24557,MergedCutProfiles.Batch614.profile24572,MergedCutProfiles.Batch614.profile24565,MergedCutProfiles.Batch614.profile24573,MergedCutProfiles.Batch614.profile24574,MergedCutProfiles.Batch614.profile24568,MergedCutProfiles.Batch499.profile19996,MergedCutProfiles.Batch614.profile24575,MergedCutProfiles.Batch381.profile15263,MergedCutProfiles.Batch499.profile19973,MergedCutProfiles.Batch380.profile15217,MergedCutProfiles.Batch614.profile24576,MergedCutProfiles.Batch381.profile15249]⟩
theorem profilesValid4080 : retention4080.ProfilesValid := by
  change ∀ j : Fin 16, (retention4080.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch614.valid24570
  · exact MergedCutProfiles.Batch614.valid24571
  · exact MergedCutProfiles.Batch613.valid24555
  · exact MergedCutProfiles.Batch613.valid24557
  · exact MergedCutProfiles.Batch614.valid24572
  · exact MergedCutProfiles.Batch614.valid24565
  · exact MergedCutProfiles.Batch614.valid24573
  · exact MergedCutProfiles.Batch614.valid24574
  · exact MergedCutProfiles.Batch614.valid24568
  · exact MergedCutProfiles.Batch499.valid19996
  · exact MergedCutProfiles.Batch614.valid24575
  · exact MergedCutProfiles.Batch381.valid15263
  · exact MergedCutProfiles.Batch499.valid19973
  · exact MergedCutProfiles.Batch380.valid15217
  · exact MergedCutProfiles.Batch614.valid24576
  · exact MergedCutProfiles.Batch381.valid15249
theorem numericValid4080 : retention4080.NumericValid := by decide +kernel
def certificate4080 : RatCutBinCertificate := ⟨⟨retention4080,(197245753882956873/100000000000000000),(136712609017002193/1000000000000000000),(2755887728889418891/200000000000000000),(4625575734360181354019/1000000000000000000),(2285837300507260743/1000000000000000000)⟩,(124953671131530317/125000000000000000),(437228960546359913/1000000000000000000),(50262962259003219/250000000000000000),(519793717263559/4000000000000000)⟩
theorem valid4080 : certificate4080.Valid := by decide +kernel
theorem sound4080 : certificate4080.Sound := rat_cut_bin_certificate_sound certificate4080 profilesValid4080 numericValid4080 valid4080

def retention4081 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(49771025637821803355/333738622226756504476),(1847574112046853951/1000000000000000000),(39/20),(5261703715910073757405298379836206866359/2956118579274966321600000000000000000000),false,MergedCutProfiles.Batch614.profile24577,(fun _ => MergedCutProfiles.Batch614.profile24577)⟩
theorem profilesValid4081 : retention4081.ProfilesValid := by
  exact MergedCutProfiles.Batch614.valid24577
theorem numericValid4081 : retention4081.NumericValid := by decide +kernel
def certificate4081 : RatCutBinCertificate := ⟨⟨retention4081,(197245753882956873/100000000000000000),(136712609017002193/1000000000000000000),(2755887728889418891/200000000000000000),(4625575734360181354019/1000000000000000000),(174177534562745533/100000000000000000)⟩,(124953671131530317/125000000000000000),(28826208151362089/62500000000000000),(9092566680968171/50000000000000000),(26021399256644331/200000000000000000)⟩
theorem valid4081 : certificate4081.Valid := by decide +kernel
theorem sound4081 : certificate4081.Sound := rat_cut_bin_certificate_sound certificate4081 profilesValid4081 numericValid4081 valid4081

def retention4082 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(16000000000000000000/83434655556689126119),(9954205127564360671/200000000000000000),1,(2575014430868900734803515860261744377/1555344551181931354843750000000000000),false,MergedCutProfiles.Batch614.profile24578,(fun _ => MergedCutProfiles.Batch614.profile24578)⟩
theorem profilesValid4082 : retention4082.ProfilesValid := by
  exact MergedCutProfiles.Batch614.valid24578
theorem numericValid4082 : retention4082.NumericValid := by decide +kernel
def certificate4082 : RatCutBinCertificate := ⟨⟨retention4082,(197245753882956873/100000000000000000),(136712609017002193/1000000000000000000),(2755887728889418891/200000000000000000),(4625575734360181354019/1000000000000000000),(1636021257596004147/1000000000000000000)⟩,(124953671131530317/125000000000000000),(158546285903418289/500000000000000000),(15934629943958747/50000000000000000),(63075659154649929/125000000000000000)⟩
theorem valid4082 : certificate4082.Valid := by decide +kernel
theorem sound4082 : certificate4082.Sound := rat_cut_bin_certificate_sound certificate4082 profilesValid4082 numericValid4082 valid4082

def retention4083 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(1/2),64,1,(15962312511554171806365804663307544671/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch382.profile15294,(fun _ => MergedCutProfiles.Batch382.profile15294)⟩
theorem profilesValid4083 : retention4083.ProfilesValid := by
  exact MergedCutProfiles.Batch382.valid15294
theorem numericValid4083 : retention4083.NumericValid := by decide +kernel
def certificate4083 : RatCutBinCertificate := ⟨⟨retention4083,(197245753882956873/100000000000000000),(136712609017002193/1000000000000000000),(2755887728889418891/200000000000000000),(4625575734360181354019/1000000000000000000),(978074798560044853/1000000000000000000)⟩,(124953671131530317/125000000000000000),(527905480987408339/1000000000000000000),(134848406106597297/1000000000000000000),(129857902813138563/1000000000000000000)⟩
theorem valid4083 : certificate4083.Valid := by decide +kernel
theorem sound4083 : certificate4083.Sound := rat_cut_bin_certificate_sound certificate4083 profilesValid4083 numericValid4083 valid4083

def retention4084 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(16000000000000000000/83434655556689126119),(25261839224497482523/1000000000000000000),1,(259250626473451062457198516350447661/157886495153109265768750000000000000),false,MergedCutProfiles.Batch614.profile24578,(fun _ => MergedCutProfiles.Batch614.profile24578)⟩
theorem profilesValid4084 : retention4084.ProfilesValid := by
  exact MergedCutProfiles.Batch614.valid24578
theorem numericValid4084 : retention4084.NumericValid := by decide +kernel
def certificate4084 : RatCutBinCertificate := ⟨⟨retention4084,(187430184982956873/100000000000000000),(136712609017002193/1000000000000000000),(2755887728889418891/200000000000000000),(4625575734360181354019/1000000000000000000),(1623410447619324919/1000000000000000000)⟩,(499823906895898729/500000000000000000),(6697595131407071/200000000000000000),(208544449499469329/250000000000000000),(317995456232906351/250000000000000000)⟩
theorem valid4084 : certificate4084.Valid := by decide +kernel
theorem sound4084 : certificate4084.Sound := rat_cut_bin_certificate_sound certificate4084 profilesValid4084 numericValid4084 valid4084

def retention4085 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(1/2),64,1,(15962312511554171806365804663307544671/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch382.profile15294,(fun _ => MergedCutProfiles.Batch382.profile15294)⟩
theorem profilesValid4085 : retention4085.ProfilesValid := by
  exact MergedCutProfiles.Batch382.valid15294
theorem numericValid4085 : retention4085.NumericValid := by decide +kernel
def certificate4085 : RatCutBinCertificate := ⟨⟨retention4085,(187430184982956873/100000000000000000),(136712609017002193/1000000000000000000),(2755887728889418891/200000000000000000),(4625575734360181354019/1000000000000000000),(979048650026449513/1000000000000000000)⟩,(499823906895898729/500000000000000000),(27764059298679453/500000000000000000),(773701235067084931/1000000000000000000),(745812342043111483/1000000000000000000)⟩
theorem valid4085 : certificate4085.Valid := by decide +kernel
theorem sound4085 : certificate4085.Sound := rat_cut_bin_certificate_sound certificate4085 profilesValid4085 numericValid4085 valid4085

def retention4086 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(676574675710021472/326573202875387438003),(334937958272287857/500000000000000000),4,(253170056724281299492769891765150159/107180146647132114240000000000000000),true,MergedCutProfiles.Batch614.profile24579,![MergedCutProfiles.Batch614.profile24579,MergedCutProfiles.Batch614.profile24580,MergedCutProfiles.Batch614.profile24581,MergedCutProfiles.Batch614.profile24582,MergedCutProfiles.Batch614.profile24583,MergedCutProfiles.Batch614.profile24584,MergedCutProfiles.Batch614.profile24585,MergedCutProfiles.Batch614.profile24586,MergedCutProfiles.Batch614.profile24587,MergedCutProfiles.Batch614.profile24588,MergedCutProfiles.Batch614.profile24589,MergedCutProfiles.Batch501.profile20044,MergedCutProfiles.Batch614.profile24590,MergedCutProfiles.Batch614.profile24591,MergedCutProfiles.Batch614.profile24592,MergedCutProfiles.Batch614.profile24593]⟩
theorem profilesValid4086 : retention4086.ProfilesValid := by
  change ∀ j : Fin 16, (retention4086.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch614.valid24579
  · exact MergedCutProfiles.Batch614.valid24580
  · exact MergedCutProfiles.Batch614.valid24581
  · exact MergedCutProfiles.Batch614.valid24582
  · exact MergedCutProfiles.Batch614.valid24583
  · exact MergedCutProfiles.Batch614.valid24584
  · exact MergedCutProfiles.Batch614.valid24585
  · exact MergedCutProfiles.Batch614.valid24586
  · exact MergedCutProfiles.Batch614.valid24587
  · exact MergedCutProfiles.Batch614.valid24588
  · exact MergedCutProfiles.Batch614.valid24589
  · exact MergedCutProfiles.Batch501.valid20044
  · exact MergedCutProfiles.Batch614.valid24590
  · exact MergedCutProfiles.Batch614.valid24591
  · exact MergedCutProfiles.Batch614.valid24592
  · exact MergedCutProfiles.Batch614.valid24593
theorem numericValid4086 : retention4086.NumericValid := by decide +kernel
def certificate4086 : RatCutBinCertificate := ⟨⟨retention4086,(1982008282598564961/1000000000000000000),(17460968802135489/125000000000000000),(876051008877953263/62500000000000000),(4590923125678254077949/1000000000000000000),(456617786355356963/200000000000000000)⟩,(499813638359035487/500000000000000000),(574760570738591629/1000000000000000000),(53468015819205463/500000000000000000),(50295131399336027/1000000000000000000)⟩
theorem valid4086 : certificate4086.Valid := by decide +kernel
theorem sound4086 : certificate4086.Sound := rat_cut_bin_certificate_sound certificate4086 profilesValid4086 numericValid4086 valid4086

def retention4087 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(1096651115000000000/326573202875387438003),(21142958615938171/31250000000000000),4,(9415821811276982789/4000000000000000000),true,MergedCutProfiles.Batch614.profile24594,![MergedCutProfiles.Batch614.profile24594,MergedCutProfiles.Batch614.profile24595,MergedCutProfiles.Batch500.profile20027,MergedCutProfiles.Batch501.profile20059,MergedCutProfiles.Batch614.profile24596,MergedCutProfiles.Batch500.profile20028,MergedCutProfiles.Batch614.profile24597,MergedCutProfiles.Batch501.profile20060,MergedCutProfiles.Batch502.profile20086,MergedCutProfiles.Batch614.profile24593,MergedCutProfiles.Batch501.profile20045,MergedCutProfiles.Batch500.profile20030,MergedCutProfiles.Batch614.profile24598,MergedCutProfiles.Batch614.profile24599,MergedCutProfiles.Batch500.profile20031,MergedCutProfiles.Batch501.profile20061]⟩
theorem profilesValid4087 : retention4087.ProfilesValid := by
  change ∀ j : Fin 16, (retention4087.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch614.valid24594
  · exact MergedCutProfiles.Batch614.valid24595
  · exact MergedCutProfiles.Batch500.valid20027
  · exact MergedCutProfiles.Batch501.valid20059
  · exact MergedCutProfiles.Batch614.valid24596
  · exact MergedCutProfiles.Batch500.valid20028
  · exact MergedCutProfiles.Batch614.valid24597
  · exact MergedCutProfiles.Batch501.valid20060
  · exact MergedCutProfiles.Batch502.valid20086
  · exact MergedCutProfiles.Batch614.valid24593
  · exact MergedCutProfiles.Batch501.valid20045
  · exact MergedCutProfiles.Batch500.valid20030
  · exact MergedCutProfiles.Batch614.valid24598
  · exact MergedCutProfiles.Batch614.valid24599
  · exact MergedCutProfiles.Batch500.valid20031
  · exact MergedCutProfiles.Batch501.valid20061
theorem numericValid4087 : retention4087.NumericValid := by decide +kernel
def certificate4087 : RatCutBinCertificate := ⟨⟨retention4087,(1982008282598564961/1000000000000000000),(17460968802135489/125000000000000000),(876051008877953263/62500000000000000),(4590923125678254077949/1000000000000000000),(2274945957863002963/1000000000000000000)⟩,(499813638359035487/500000000000000000),(573305387683818699/1000000000000000000),(107743758021872253/1000000000000000000),(12653426545693249/250000000000000000)⟩
theorem valid4087 : certificate4087.Valid := by decide +kernel
theorem sound4087 : certificate4087.Sound := rat_cut_bin_certificate_sound certificate4087 profilesValid4087 numericValid4087 valid4087

def retention4088 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(122207495517448887/29688472988671585273),(219330223/200000000),(14/5),(37639387005432920879/16000000000000000000),true,MergedCutProfiles.Batch614.profile24580,![MergedCutProfiles.Batch614.profile24580,MergedCutProfiles.Batch614.profile24582,MergedCutProfiles.Batch501.profile20043,MergedCutProfiles.Batch614.profile24586,MergedCutProfiles.Batch614.profile24588,MergedCutProfiles.Batch501.profile20044,MergedCutProfiles.Batch501.profile20074,MergedCutProfiles.Batch615.profile24600,MergedCutProfiles.Batch501.profile20045,MergedCutProfiles.Batch615.profile24601,MergedCutProfiles.Batch615.profile24602,MergedCutProfiles.Batch501.profile20046,MergedCutProfiles.Batch501.profile20061,MergedCutProfiles.Batch615.profile24603,MergedCutProfiles.Batch501.profile20047,MergedCutProfiles.Batch615.profile24604]⟩
theorem profilesValid4088 : retention4088.ProfilesValid := by
  change ∀ j : Fin 16, (retention4088.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch614.valid24580
  · exact MergedCutProfiles.Batch614.valid24582
  · exact MergedCutProfiles.Batch501.valid20043
  · exact MergedCutProfiles.Batch614.valid24586
  · exact MergedCutProfiles.Batch614.valid24588
  · exact MergedCutProfiles.Batch501.valid20044
  · exact MergedCutProfiles.Batch501.valid20074
  · exact MergedCutProfiles.Batch615.valid24600
  · exact MergedCutProfiles.Batch501.valid20045
  · exact MergedCutProfiles.Batch615.valid24601
  · exact MergedCutProfiles.Batch615.valid24602
  · exact MergedCutProfiles.Batch501.valid20046
  · exact MergedCutProfiles.Batch501.valid20061
  · exact MergedCutProfiles.Batch615.valid24603
  · exact MergedCutProfiles.Batch501.valid20047
  · exact MergedCutProfiles.Batch615.valid24604
theorem numericValid4088 : retention4088.NumericValid := by decide +kernel
def certificate4088 : RatCutBinCertificate := ⟨⟨retention4088,(1982008282598564961/1000000000000000000),(17460968802135489/125000000000000000),(876051008877953263/62500000000000000),(4590923125678254077949/1000000000000000000),(459431023029294497/200000000000000000)⟩,(499813638359035487/500000000000000000),(1738064679777743/4000000000000000),(101652265538854087/500000000000000000),(16446028858469097/125000000000000000)⟩
theorem valid4088 : certificate4088.Valid := by decide +kernel
theorem sound4088 : certificate4088.Sound := rat_cut_bin_certificate_sound certificate4088 profilesValid4088 numericValid4088 valid4088

def retention4089 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(16499725621764627701/326573202875387438003),(1344282450691937757/1000000000000000000),(12/5),(17562956796740140453558836130962753479/8401765316824610981250000000000000000),false,MergedCutProfiles.Batch615.profile24605,(fun _ => MergedCutProfiles.Batch615.profile24605)⟩
theorem profilesValid4089 : retention4089.ProfilesValid := by
  exact MergedCutProfiles.Batch615.valid24605
theorem numericValid4089 : retention4089.NumericValid := by decide +kernel
def certificate4089 : RatCutBinCertificate := ⟨⟨retention4089,(1982008282598564961/1000000000000000000),(17460968802135489/125000000000000000),(876051008877953263/62500000000000000),(4590923125678254077949/1000000000000000000),(510745817412449493/250000000000000000)⟩,(499813638359035487/500000000000000000),(444124029423470237/1000000000000000000),(195401738161637219/1000000000000000000),(131552532917667249/1000000000000000000)⟩
theorem valid4089 : certificate4089.Valid := by decide +kernel
theorem sound4089 : certificate4089.Sound := rat_cut_bin_certificate_sound certificate4089 profilesValid4089 numericValid4089 valid4089

def retention4090 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(64000000000000000000/326573202875387438003),(16499725621764627701/1000000000000000000),1,(5339003778472158829616193196826338961/3299945124352925540200000000000000000),false,MergedCutProfiles.Batch615.profile24606,(fun _ => MergedCutProfiles.Batch615.profile24606)⟩
theorem profilesValid4090 : retention4090.ProfilesValid := by
  exact MergedCutProfiles.Batch615.valid24606
theorem numericValid4090 : retention4090.NumericValid := by decide +kernel
def certificate4090 : RatCutBinCertificate := ⟨⟨retention4090,(1982008282598564961/1000000000000000000),(17460968802135489/125000000000000000),(876051008877953263/62500000000000000),(4590923125678254077949/1000000000000000000),(199769331115882637/125000000000000000)⟩,(499813638359035487/500000000000000000),(336596077624550163/1000000000000000000),(296885524667448769/1000000000000000000),(216201638258006681/500000000000000000)⟩
theorem valid4090 : certificate4090.Valid := by decide +kernel
theorem sound4090 : certificate4090.Sound := rat_cut_bin_certificate_sound certificate4090 profilesValid4090 numericValid4090 valid4090

def retention4091 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(1/2),64,1,(63849579314623294310930918929863576759/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch502.profile20104,(fun _ => MergedCutProfiles.Batch502.profile20104)⟩
theorem profilesValid4091 : retention4091.ProfilesValid := by
  exact MergedCutProfiles.Batch502.valid20104
theorem numericValid4091 : retention4091.NumericValid := by decide +kernel
def certificate4091 : RatCutBinCertificate := ⟨⟨retention4091,(1982008282598564961/1000000000000000000),(17460968802135489/125000000000000000),(876051008877953263/62500000000000000),(4590923125678254077949/1000000000000000000),(977897515734967931/1000000000000000000)⟩,(499813638359035487/500000000000000000),(262611279936641401/500000000000000000),(136569185349130983/1000000000000000000),(821820246791039/6250000000000000)⟩
theorem valid4091 : certificate4091.Valid := by decide +kernel
theorem sound4091 : certificate4091.Sound := rat_cut_bin_certificate_sound certificate4091 profilesValid4091 numericValid4091 valid4091

def certificates : List RatCutBinCertificate := [certificate4080,certificate4081,certificate4082,certificate4083,certificate4084,certificate4085,certificate4086,certificate4087,certificate4088,certificate4089,certificate4090,certificate4091]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4080,List.forall_mem_cons.mpr ⟨sound4081,List.forall_mem_cons.mpr ⟨sound4082,List.forall_mem_cons.mpr ⟨sound4083,List.forall_mem_cons.mpr ⟨sound4084,List.forall_mem_cons.mpr ⟨sound4085,List.forall_mem_cons.mpr ⟨sound4086,List.forall_mem_cons.mpr ⟨sound4087,List.forall_mem_cons.mpr ⟨sound4088,List.forall_mem_cons.mpr ⟨sound4089,List.forall_mem_cons.mpr ⟨sound4090,List.forall_mem_cons.mpr ⟨sound4091,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch340
