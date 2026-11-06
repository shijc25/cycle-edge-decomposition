import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch709
import Cycle12.MergedCutProfiles.Batch710

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch425

def retention5100 : RatCutRetentionCertificate := ⟨(59/1000),(3/50),(521595349538127502/249739220709829794675),(436438046520174739/500000000000000000),(73/20),(846863840296371988078431008560867056071/349150437216139791200000000000000000000),false,MergedCutProfiles.Batch709.profile28365,(fun _ => MergedCutProfiles.Batch709.profile28365)⟩
theorem profilesValid5100 : retention5100.ProfilesValid := by
  exact MergedCutProfiles.Batch709.valid28365
theorem numericValid5100 : retention5100.NumericValid := by decide +kernel
def certificate5100 : RatCutBinCertificate := ⟨⟨retention5100,(1978102063365112229/1000000000000000000),(182428996879551849/1000000000000000000),(15581512187564472011/1000000000000000000),(19575556805189512953233/1000000000000000000),(2340965279910653669/1000000000000000000)⟩,(999916666859785693/1000000000000000000),(766186290942439063/1000000000000000000),(14877680408125463/500000000000000000),(7942196951305521/500000000000000000)⟩
theorem valid5100 : certificate5100.Valid := by decide +kernel
theorem sound5100 : certificate5100.Sound := rat_cut_bin_certificate_sound certificate5100 profilesValid5100 numericValid5100 valid5100

def retention5101 : RatCutRetentionCertificate := ⟨(59/1000),(3/50),(9099691582736018567/416232034516382991125),(260797674769063751/100000000000000000),(9/5),(1465344855829917509107692534682953869/651994186922659377500000000000000000),false,MergedCutProfiles.Batch709.profile28366,(fun _ => MergedCutProfiles.Batch709.profile28366)⟩
theorem profilesValid5101 : retention5101.ProfilesValid := by
  exact MergedCutProfiles.Batch709.valid28366
theorem numericValid5101 : retention5101.NumericValid := by decide +kernel
def certificate5101 : RatCutBinCertificate := ⟨⟨retention5101,(1978102063365112229/1000000000000000000),(182428996879551849/1000000000000000000),(15581512187564472011/1000000000000000000),(19575556805189512953233/1000000000000000000),(2205793927418095221/1000000000000000000)⟩,(999916666859785693/1000000000000000000),(356080714065886693/500000000000000000),(46094899102538981/1000000000000000000),(22394631653746607/500000000000000000)⟩
theorem valid5101 : certificate5101.Valid := by decide +kernel
theorem sound5101 : certificate5101.Sound := rat_cut_bin_certificate_sound certificate5101 profilesValid5101 numericValid5101 valid5101

def retention5102 : RatCutRetentionCertificate := ⟨(59/1000),(3/50),(1/40),(27299074748208055701/1000000000000000000),(21/20),(32389089071561930824634404114058249831013/14559506532377629707200000000000000000000),false,MergedCutProfiles.Batch709.profile28367,(fun _ => MergedCutProfiles.Batch709.profile28367)⟩
theorem profilesValid5102 : retention5102.ProfilesValid := by
  exact MergedCutProfiles.Batch709.valid28367
theorem numericValid5102 : retention5102.NumericValid := by decide +kernel
def certificate5102 : RatCutBinCertificate := ⟨⟨retention5102,(1978102063365112229/1000000000000000000),(182428996879551849/1000000000000000000),(15581512187564472011/1000000000000000000),(19575556805189512953233/1000000000000000000),(1100141524878734557/500000000000000000)⟩,(999916666859785693/1000000000000000000),(333942311097289447/500000000000000000),(3126526731913639/50000000000000000),(122096100895822149/1000000000000000000)⟩
theorem valid5102 : certificate5102.Valid := by decide +kernel
theorem sound5102 : certificate5102.Sound := rat_cut_bin_certificate_sound certificate5102 profilesValid5102 numericValid5102 valid5102

def retention5103 : RatCutRetentionCertificate := ⟨(3/50),(61/1000),(93790351585804959/171528320771418379961),(5047318325061113/8000000000000000),4,(599696818184729857717/256000000000000000000),true,MergedCutProfiles.Batch709.profile28368,![MergedCutProfiles.Batch709.profile28368,MergedCutProfiles.Batch709.profile28369,MergedCutProfiles.Batch709.profile28370,MergedCutProfiles.Batch709.profile28371,MergedCutProfiles.Batch709.profile28372,MergedCutProfiles.Batch709.profile28373,MergedCutProfiles.Batch709.profile28374,MergedCutProfiles.Batch709.profile28375,MergedCutProfiles.Batch709.profile28376,MergedCutProfiles.Batch709.profile28377,MergedCutProfiles.Batch709.profile28378,MergedCutProfiles.Batch709.profile28379,MergedCutProfiles.Batch709.profile28380,MergedCutProfiles.Batch709.profile28381,MergedCutProfiles.Batch709.profile28382,MergedCutProfiles.Batch709.profile28383]⟩
theorem profilesValid5103 : retention5103.ProfilesValid := by
  change ∀ j : Fin 16, (retention5103.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch709.valid28368
  · exact MergedCutProfiles.Batch709.valid28369
  · exact MergedCutProfiles.Batch709.valid28370
  · exact MergedCutProfiles.Batch709.valid28371
  · exact MergedCutProfiles.Batch709.valid28372
  · exact MergedCutProfiles.Batch709.valid28373
  · exact MergedCutProfiles.Batch709.valid28374
  · exact MergedCutProfiles.Batch709.valid28375
  · exact MergedCutProfiles.Batch709.valid28376
  · exact MergedCutProfiles.Batch709.valid28377
  · exact MergedCutProfiles.Batch709.valid28378
  · exact MergedCutProfiles.Batch709.valid28379
  · exact MergedCutProfiles.Batch709.valid28380
  · exact MergedCutProfiles.Batch709.valid28381
  · exact MergedCutProfiles.Batch709.valid28382
  · exact MergedCutProfiles.Batch709.valid28383
theorem numericValid5103 : retention5103.NumericValid := by decide +kernel
def certificate5103 : RatCutBinCertificate := ⟨⟨retention5103,(1970997404722675463/1000000000000000000),(9485872639178457/50000000000000000),(991749776211874147/62500000000000000),(19169980940630702698633/1000000000000000000),(2248304501723302343/1000000000000000000)⟩,(62494746145771967/62500000000000000),(333828639517333731/500000000000000000),(15655584523066233/250000000000000000),(7196000994987751/250000000000000000)⟩
theorem valid5103 : certificate5103.Valid := by decide +kernel
theorem sound5103 : certificate5103.Sound := rat_cut_bin_certificate_sound certificate5103 profilesValid5103 numericValid5103 valid5103

def retention5104 : RatCutRetentionCertificate := ⟨(3/50),(61/1000),(1056984338000000000/1200698245399928659727),(656532461100634713/1000000000000000000),4,(151859560383461618473/64000000000000000000),true,MergedCutProfiles.Batch709.profile28384,![MergedCutProfiles.Batch709.profile28384,MergedCutProfiles.Batch709.profile28385,MergedCutProfiles.Batch709.profile28372,MergedCutProfiles.Batch709.profile28386,MergedCutProfiles.Batch709.profile28375,MergedCutProfiles.Batch709.profile28377,MergedCutProfiles.Batch709.profile28387,MergedCutProfiles.Batch709.profile28388,MergedCutProfiles.Batch709.profile28389,MergedCutProfiles.Batch709.profile28390,MergedCutProfiles.Batch709.profile28391,MergedCutProfiles.Batch709.profile28392,MergedCutProfiles.Batch709.profile28393,MergedCutProfiles.Batch709.profile28394,MergedCutProfiles.Batch709.profile28395,MergedCutProfiles.Batch709.profile28396]⟩
theorem profilesValid5104 : retention5104.ProfilesValid := by
  change ∀ j : Fin 16, (retention5104.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch709.valid28384
  · exact MergedCutProfiles.Batch709.valid28385
  · exact MergedCutProfiles.Batch709.valid28372
  · exact MergedCutProfiles.Batch709.valid28386
  · exact MergedCutProfiles.Batch709.valid28375
  · exact MergedCutProfiles.Batch709.valid28377
  · exact MergedCutProfiles.Batch709.valid28387
  · exact MergedCutProfiles.Batch709.valid28388
  · exact MergedCutProfiles.Batch709.valid28389
  · exact MergedCutProfiles.Batch709.valid28390
  · exact MergedCutProfiles.Batch709.valid28391
  · exact MergedCutProfiles.Batch709.valid28392
  · exact MergedCutProfiles.Batch709.valid28393
  · exact MergedCutProfiles.Batch709.valid28394
  · exact MergedCutProfiles.Batch709.valid28395
  · exact MergedCutProfiles.Batch709.valid28396
theorem numericValid5104 : retention5104.NumericValid := by decide +kernel
def certificate5104 : RatCutBinCertificate := ⟨⟨retention5104,(1970997404722675463/1000000000000000000),(9485872639178457/50000000000000000),(991749776211874147/62500000000000000),(19169980940630702698633/1000000000000000000),(2278544451104252953/1000000000000000000)⟩,(62494746145771967/62500000000000000),(642295785432740861/1000000000000000000),(18338946878887279/250000000000000000),(34334298894757109/1000000000000000000)⟩
theorem valid5104 : certificate5104.Valid := by decide +kernel
theorem sound5104 : certificate5104.Sound := rat_cut_bin_certificate_sound certificate5104 profilesValid5104 numericValid5104 valid5104

def retention5105 : RatCutRetentionCertificate := ⟨(3/50),(61/1000),(1169219051643642914/1200698245399928659727),(528492169/500000000),(59/20),(19376113752058468843/8000000000000000000),true,MergedCutProfiles.Batch709.profile28384,![MergedCutProfiles.Batch709.profile28384,MergedCutProfiles.Batch709.profile28397,MergedCutProfiles.Batch709.profile28398,MergedCutProfiles.Batch709.profile28374,MergedCutProfiles.Batch709.profile28376,MergedCutProfiles.Batch709.profile28378,MergedCutProfiles.Batch709.profile28388,MergedCutProfiles.Batch709.profile28389,MergedCutProfiles.Batch709.profile28383,MergedCutProfiles.Batch709.profile28391,MergedCutProfiles.Batch709.profile28392,MergedCutProfiles.Batch709.profile28399,MergedCutProfiles.Batch710.profile28400,MergedCutProfiles.Batch710.profile28401,MergedCutProfiles.Batch710.profile28402,MergedCutProfiles.Batch710.profile28403]⟩
theorem profilesValid5105 : retention5105.ProfilesValid := by
  change ∀ j : Fin 16, (retention5105.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch709.valid28384
  · exact MergedCutProfiles.Batch709.valid28397
  · exact MergedCutProfiles.Batch709.valid28398
  · exact MergedCutProfiles.Batch709.valid28374
  · exact MergedCutProfiles.Batch709.valid28376
  · exact MergedCutProfiles.Batch709.valid28378
  · exact MergedCutProfiles.Batch709.valid28388
  · exact MergedCutProfiles.Batch709.valid28389
  · exact MergedCutProfiles.Batch709.valid28383
  · exact MergedCutProfiles.Batch709.valid28391
  · exact MergedCutProfiles.Batch709.valid28392
  · exact MergedCutProfiles.Batch709.valid28399
  · exact MergedCutProfiles.Batch710.valid28400
  · exact MergedCutProfiles.Batch710.valid28401
  · exact MergedCutProfiles.Batch710.valid28402
  · exact MergedCutProfiles.Batch710.valid28403
theorem numericValid5105 : retention5105.NumericValid := by decide +kernel
def certificate5105 : RatCutBinCertificate := ⟨⟨retention5105,(1970997404722675463/1000000000000000000),(9485872639178457/50000000000000000),(991749776211874147/62500000000000000),(19169980940630702698633/1000000000000000000),(2352496640175043977/1000000000000000000)⟩,(62494746145771967/62500000000000000),(47298296746701067/100000000000000000),(17289649396152027/100000000000000000),(109785868704878763/1000000000000000000)⟩
theorem valid5105 : certificate5105.Valid := by decide +kernel
theorem sound5105 : certificate5105.Sound := rat_cut_bin_certificate_sound certificate5105 profilesValid5105 numericValid5105 valid5105

def retention5106 : RatCutRetentionCertificate := ⟨(3/50),(61/1000),(18404177834188316083/1200698245399928659727),(584609525821821457/500000000000000000),(11/4),(292327845807043812653/128000000000000000000),true,MergedCutProfiles.Batch710.profile28403,![MergedCutProfiles.Batch710.profile28403,MergedCutProfiles.Batch710.profile28404,MergedCutProfiles.Batch710.profile28405,MergedCutProfiles.Batch710.profile28406,MergedCutProfiles.Batch710.profile28407,MergedCutProfiles.Batch710.profile28408,MergedCutProfiles.Batch710.profile28409,MergedCutProfiles.Batch710.profile28410,MergedCutProfiles.Batch710.profile28411,MergedCutProfiles.Batch710.profile28412,MergedCutProfiles.Batch710.profile28413,MergedCutProfiles.Batch710.profile28414,MergedCutProfiles.Batch710.profile28415,MergedCutProfiles.Batch710.profile28416,MergedCutProfiles.Batch710.profile28417,MergedCutProfiles.Batch710.profile28418]⟩
theorem profilesValid5106 : retention5106.ProfilesValid := by
  change ∀ j : Fin 16, (retention5106.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch710.valid28403
  · exact MergedCutProfiles.Batch710.valid28404
  · exact MergedCutProfiles.Batch710.valid28405
  · exact MergedCutProfiles.Batch710.valid28406
  · exact MergedCutProfiles.Batch710.valid28407
  · exact MergedCutProfiles.Batch710.valid28408
  · exact MergedCutProfiles.Batch710.valid28409
  · exact MergedCutProfiles.Batch710.valid28410
  · exact MergedCutProfiles.Batch710.valid28411
  · exact MergedCutProfiles.Batch710.valid28412
  · exact MergedCutProfiles.Batch710.valid28413
  · exact MergedCutProfiles.Batch710.valid28414
  · exact MergedCutProfiles.Batch710.valid28415
  · exact MergedCutProfiles.Batch710.valid28416
  · exact MergedCutProfiles.Batch710.valid28417
  · exact MergedCutProfiles.Batch710.valid28418
theorem numericValid5106 : retention5106.NumericValid := by decide +kernel
def certificate5106 : RatCutBinCertificate := ⟨⟨retention5106,(1970997404722675463/1000000000000000000),(9485872639178457/50000000000000000),(991749776211874147/62500000000000000),(19169980940630702698633/1000000000000000000),(1109503389474095211/500000000000000000)⟩,(62494746145771967/62500000000000000),(238278259375414513/500000000000000000),(85117235737749701/500000000000000000),(109796435770902403/1000000000000000000)⟩
theorem valid5106 : certificate5106.Valid := by decide +kernel
theorem sound5106 : certificate5106.Sound := rat_cut_bin_certificate_sound certificate5106 profilesValid5106 numericValid5106 valid5106

def retention5107 : RatCutRetentionCertificate := ⟨(3/50),(61/1000),(64000000000000000000/1200698245399928659727),(18404177834188316083/1000000000000000000),1,(7501959483333373315442272892532350913/3680835566837663216600000000000000000),false,MergedCutProfiles.Batch710.profile28419,(fun _ => MergedCutProfiles.Batch710.profile28419)⟩
theorem profilesValid5107 : retention5107.ProfilesValid := by
  exact MergedCutProfiles.Batch710.valid28419
theorem numericValid5107 : retention5107.NumericValid := by decide +kernel
def certificate5107 : RatCutBinCertificate := ⟨⟨retention5107,(1970997404722675463/1000000000000000000),(9485872639178457/50000000000000000),(991749776211874147/62500000000000000),(19169980940630702698633/1000000000000000000),(125909247592128639/62500000000000000)⟩,(62494746145771967/62500000000000000),(28322924670529441/100000000000000000),(35944153997664937/100000000000000000),(130522633619027449/200000000000000000)⟩
theorem valid5107 : certificate5107.Valid := by decide +kernel
theorem sound5107 : certificate5107.Sound := rat_cut_bin_certificate_sound certificate5107 profilesValid5107 numericValid5107 valid5107

def retention5108 : RatCutRetentionCertificate := ⟨(3/50),(61/1000),(1/2),64,1,(10216326792794747474245594982314111119/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch710.profile28420,(fun _ => MergedCutProfiles.Batch710.profile28420)⟩
theorem profilesValid5108 : retention5108.ProfilesValid := by
  exact MergedCutProfiles.Batch710.valid28420
theorem numericValid5108 : retention5108.NumericValid := by decide +kernel
def certificate5108 : RatCutBinCertificate := ⟨⟨retention5108,(1970997404722675463/1000000000000000000),(9485872639178457/50000000000000000),(991749776211874147/62500000000000000),(19169980940630702698633/1000000000000000000),(487061476774351067/500000000000000000)⟩,(62494746145771967/62500000000000000),(140394524055640671/250000000000000000),(22877769964442707/200000000000000000),(109748879317480147/1000000000000000000)⟩
theorem valid5108 : certificate5108.Valid := by decide +kernel
theorem sound5108 : certificate5108.Sound := rat_cut_bin_certificate_sound certificate5108 profilesValid5108 numericValid5108 valid5108

def retention5109 : RatCutRetentionCertificate := ⟨(3/50),(61/1000),(64000000000000000000/1200698245399928659727),(285782926977396341/6250000000000000),1,(3793066563504315757899068030288715343/1829010732655336582400000000000000000),false,MergedCutProfiles.Batch710.profile28419,(fun _ => MergedCutProfiles.Batch710.profile28419)⟩
theorem profilesValid5109 : retention5109.ProfilesValid := by
  exact MergedCutProfiles.Batch710.valid28419
theorem numericValid5109 : retention5109.NumericValid := by decide +kernel
def certificate5109 : RatCutBinCertificate := ⟨⟨retention5109,(1726038416722675463/1000000000000000000),(9485872639178457/50000000000000000),(991749776211874147/62500000000000000),(19169980940630702698633/1000000000000000000),(2053198563821077183/1000000000000000000)⟩,(124990798229290507/125000000000000000),(313207029943737/20000000000000000),(27728428860627531/31250000000000000),(1743402681493886113/1000000000000000000)⟩
theorem valid5109 : certificate5109.Valid := by decide +kernel
theorem sound5109 : certificate5109.Sound := rat_cut_bin_certificate_sound certificate5109 profilesValid5109 numericValid5109 valid5109

def retention5110 : RatCutRetentionCertificate := ⟨(3/50),(61/1000),(1/2),64,1,(10216326792794747474245594982314111119/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch710.profile28420,(fun _ => MergedCutProfiles.Batch710.profile28420)⟩
theorem profilesValid5110 : retention5110.ProfilesValid := by
  exact MergedCutProfiles.Batch710.valid28420
theorem numericValid5110 : retention5110.NumericValid := by decide +kernel
def certificate5110 : RatCutBinCertificate := ⟨⟨retention5110,(1726038416722675463/1000000000000000000),(9485872639178457/50000000000000000),(991749776211874147/62500000000000000),(19169980940630702698633/1000000000000000000),(244262919709849149/250000000000000000)⟩,(124990798229290507/125000000000000000),(8227254478788577/250000000000000000),(417920559344353637/500000000000000000),(804319973933790167/1000000000000000000)⟩
theorem valid5110 : certificate5110.Valid := by decide +kernel
theorem sound5110 : certificate5110.Sound := rat_cut_bin_certificate_sound certificate5110 profilesValid5110 numericValid5110 valid5110

def retention5111 : RatCutRetentionCertificate := ⟨(3/50),(61/1000),(763591415237891503/1200698245399928659727),(756031104195932181/1000000000000000000),4,(1483914942618660721538128781555639083/604824883356745744800000000000000000),false,MergedCutProfiles.Batch710.profile28421,(fun _ => MergedCutProfiles.Batch710.profile28421)⟩
theorem profilesValid5111 : retention5111.ProfilesValid := by
  exact MergedCutProfiles.Batch710.valid28421
theorem numericValid5111 : retention5111.NumericValid := by decide +kernel
def certificate5111 : RatCutBinCertificate := ⟨⟨retention5111,(1986327842722675463/1000000000000000000),(9485872639178457/50000000000000000),(991749776211874147/62500000000000000),(19169980940630702698633/1000000000000000000),(14740423913906013/6250000000000000)⟩,(124989410560935021/125000000000000000),(48647578353073147/62500000000000000),(6652256891886689/250000000000000000),(102562201241871/7812500000000000)⟩
theorem valid5111 : certificate5111.Valid := by decide +kernel
theorem sound5111 : certificate5111.Sound := rat_cut_bin_certificate_sound certificate5111 profilesValid5111 numericValid5111 valid5111

def certificates : List RatCutBinCertificate := [certificate5100,certificate5101,certificate5102,certificate5103,certificate5104,certificate5105,certificate5106,certificate5107,certificate5108,certificate5109,certificate5110,certificate5111]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound5100,List.forall_mem_cons.mpr ⟨sound5101,List.forall_mem_cons.mpr ⟨sound5102,List.forall_mem_cons.mpr ⟨sound5103,List.forall_mem_cons.mpr ⟨sound5104,List.forall_mem_cons.mpr ⟨sound5105,List.forall_mem_cons.mpr ⟨sound5106,List.forall_mem_cons.mpr ⟨sound5107,List.forall_mem_cons.mpr ⟨sound5108,List.forall_mem_cons.mpr ⟨sound5109,List.forall_mem_cons.mpr ⟨sound5110,List.forall_mem_cons.mpr ⟨sound5111,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch425
