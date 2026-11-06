import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch710
import Cycle12.MergedCutProfiles.Batch711

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch426

def retention5112 : RatCutRetentionCertificate := ⟨(3/50),(61/1000),(877728641265577911/1200698245399928659727),(763591415237891503/1000000000000000000),4,(1873577390827111604622519777874625227/763591415237891503000000000000000000),false,MergedCutProfiles.Batch710.profile28422,(fun _ => MergedCutProfiles.Batch710.profile28422)⟩
theorem profilesValid5112 : retention5112.ProfilesValid := by
  exact MergedCutProfiles.Batch710.valid28422
theorem numericValid5112 : retention5112.NumericValid := by decide +kernel
def certificate5112 : RatCutBinCertificate := ⟨⟨retention5112,(1986327842722675463/1000000000000000000),(9485872639178457/50000000000000000),(991749776211874147/62500000000000000),(19169980940630702698633/1000000000000000000),(47172886635463151/20000000000000000)⟩,(124989410560935021/125000000000000000),(776702423599386447/1000000000000000000),(27026440425141537/1000000000000000000),(13356313317437727/1000000000000000000)⟩
theorem valid5112 : certificate5112.Valid := by decide +kernel
theorem sound5112 : certificate5112.Sound := rat_cut_bin_certificate_sound certificate5112 profilesValid5112 numericValid5112 valid5112

def retention5113 : RatCutRetentionCertificate := ⟨(3/50),(61/1000),(2622475177696164323/1200698245399928659727),(877728641265577911/1000000000000000000),(18/5),(70909578527116143052791518524235463597/29257621375519263700000000000000000000),false,MergedCutProfiles.Batch710.profile28423,(fun _ => MergedCutProfiles.Batch710.profile28423)⟩
theorem profilesValid5113 : retention5113.ProfilesValid := by
  exact MergedCutProfiles.Batch710.valid28423
theorem numericValid5113 : retention5113.NumericValid := by decide +kernel
def certificate5113 : RatCutBinCertificate := ⟨⟨retention5113,(1986327842722675463/1000000000000000000),(9485872639178457/50000000000000000),(991749776211874147/62500000000000000),(19169980940630702698633/1000000000000000000),(2338132739447689527/1000000000000000000)⟩,(124989410560935021/125000000000000000),(7625200630762559/10000000000000000),(3842571574805009/125000000000000000),(8279838007807679/500000000000000000)⟩
theorem valid5113 : certificate5113.Valid := by decide +kernel
theorem sound5113 : certificate5113.Sound := rat_cut_bin_certificate_sound certificate5113 profilesValid5113 numericValid5113 valid5113

def retention5114 : RatCutRetentionCertificate := ⟨(3/50),(61/1000),(26909947552888464989/1200698245399928659727),(2622475177696164323/1000000000000000000),(9/5),(589123459884740848529422032601556661131/262247517769616432300000000000000000000),false,MergedCutProfiles.Batch710.profile28424,(fun _ => MergedCutProfiles.Batch710.profile28424)⟩
theorem profilesValid5114 : retention5114.ProfilesValid := by
  exact MergedCutProfiles.Batch710.valid28424
theorem numericValid5114 : retention5114.NumericValid := by decide +kernel
def certificate5114 : RatCutBinCertificate := ⟨⟨retention5114,(1986327842722675463/1000000000000000000),(9485872639178457/50000000000000000),(991749776211874147/62500000000000000),(19169980940630702698633/1000000000000000000),(440738634702392043/200000000000000000)⟩,(124989410560935021/125000000000000000),(709884523025466843/1000000000000000000),(23435719890078429/500000000000000000),(22780717587362959/500000000000000000)⟩
theorem valid5114 : certificate5114.Valid := by decide +kernel
theorem sound5114 : certificate5114.Sound := rat_cut_bin_certificate_sound certificate5114 profilesValid5114 numericValid5114 valid5114

def retention5115 : RatCutRetentionCertificate := ⟨(3/50),(61/1000),(1/40),(26909947552888464989/1000000000000000000),(21/20),(2337632962021272984907770217832495702439/1050144294746866926400000000000000000000),false,MergedCutProfiles.Batch710.profile28425,(fun _ => MergedCutProfiles.Batch710.profile28425)⟩
theorem profilesValid5115 : retention5115.ProfilesValid := by
  exact MergedCutProfiles.Batch710.valid28425
theorem numericValid5115 : retention5115.NumericValid := by decide +kernel
def certificate5115 : RatCutBinCertificate := ⟨⟨retention5115,(1986327842722675463/1000000000000000000),(9485872639178457/50000000000000000),(991749776211874147/62500000000000000),(19169980940630702698633/1000000000000000000),(440215054028068287/200000000000000000)⟩,(124989410560935021/125000000000000000),(665654980238915453/1000000000000000000),(63434232785993309/1000000000000000000),(61890022144405123/500000000000000000)⟩
theorem valid5115 : certificate5115.Valid := by decide +kernel
theorem sound5115 : certificate5115.Sound := rat_cut_bin_certificate_sound certificate5115 profilesValid5115 numericValid5115 valid5115

def retention5116 : RatCutRetentionCertificate := ⟨(61/1000),(31/500),(631885542140188102/1155117845288214377213),(595264764199185457/1000000000000000000),4,(583510605116699497249/256000000000000000000),true,MergedCutProfiles.Batch710.profile28426,![MergedCutProfiles.Batch710.profile28426,MergedCutProfiles.Batch710.profile28427,MergedCutProfiles.Batch710.profile28428,MergedCutProfiles.Batch710.profile28429,MergedCutProfiles.Batch710.profile28430,MergedCutProfiles.Batch710.profile28431,MergedCutProfiles.Batch710.profile28432,MergedCutProfiles.Batch710.profile28433,MergedCutProfiles.Batch710.profile28434,MergedCutProfiles.Batch710.profile28435,MergedCutProfiles.Batch710.profile28436,MergedCutProfiles.Batch710.profile28437,MergedCutProfiles.Batch710.profile28438,MergedCutProfiles.Batch710.profile28439,MergedCutProfiles.Batch711.profile28440,MergedCutProfiles.Batch711.profile28441]⟩
theorem profilesValid5116 : retention5116.ProfilesValid := by
  change ∀ j : Fin 16, (retention5116.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch710.valid28426
  · exact MergedCutProfiles.Batch710.valid28427
  · exact MergedCutProfiles.Batch710.valid28428
  · exact MergedCutProfiles.Batch710.valid28429
  · exact MergedCutProfiles.Batch710.valid28430
  · exact MergedCutProfiles.Batch710.valid28431
  · exact MergedCutProfiles.Batch710.valid28432
  · exact MergedCutProfiles.Batch710.valid28433
  · exact MergedCutProfiles.Batch710.valid28434
  · exact MergedCutProfiles.Batch710.valid28435
  · exact MergedCutProfiles.Batch710.valid28436
  · exact MergedCutProfiles.Batch710.valid28437
  · exact MergedCutProfiles.Batch710.valid28438
  · exact MergedCutProfiles.Batch710.valid28439
  · exact MergedCutProfiles.Batch711.valid28440
  · exact MergedCutProfiles.Batch711.valid28441
theorem numericValid5116 : retention5116.NumericValid := by decide +kernel
def certificate5116 : RatCutBinCertificate := ⟨⟨retention5116,(971172334768336193/500000000000000000),(24651154762240763/125000000000000000),(8081272758122984273/500000000000000000),(18785377548995781000869/1000000000000000000),(218453887725616347/100000000000000000)⟩,(499958108936788439/500000000000000000),(763138881967049177/1000000000000000000),(30573045455665507/1000000000000000000),(13580361766429159/1000000000000000000)⟩
theorem valid5116 : certificate5116.Valid := by decide +kernel
theorem sound5116 : certificate5116.Sound := rat_cut_bin_certificate_sound certificate5116 profilesValid5116 numericValid5116 valid5116

def retention5117 : RatCutRetentionCertificate := ⟨(61/1000),(31/500),(1048636430000000000/1155117845288214377213),(315942771070094051/500000000000000000),4,(299550282581578731827/128000000000000000000),true,MergedCutProfiles.Batch711.profile28442,![MergedCutProfiles.Batch711.profile28442,MergedCutProfiles.Batch711.profile28443,MergedCutProfiles.Batch710.profile28430,MergedCutProfiles.Batch711.profile28444,MergedCutProfiles.Batch711.profile28445,MergedCutProfiles.Batch710.profile28435,MergedCutProfiles.Batch711.profile28446,MergedCutProfiles.Batch710.profile28438,MergedCutProfiles.Batch711.profile28440,MergedCutProfiles.Batch711.profile28447,MergedCutProfiles.Batch711.profile28448,MergedCutProfiles.Batch711.profile28449,MergedCutProfiles.Batch711.profile28450,MergedCutProfiles.Batch711.profile28451,MergedCutProfiles.Batch711.profile28452,MergedCutProfiles.Batch711.profile28453]⟩
theorem profilesValid5117 : retention5117.ProfilesValid := by
  change ∀ j : Fin 16, (retention5117.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch711.valid28442
  · exact MergedCutProfiles.Batch711.valid28443
  · exact MergedCutProfiles.Batch710.valid28430
  · exact MergedCutProfiles.Batch711.valid28444
  · exact MergedCutProfiles.Batch711.valid28445
  · exact MergedCutProfiles.Batch710.valid28435
  · exact MergedCutProfiles.Batch711.valid28446
  · exact MergedCutProfiles.Batch710.valid28438
  · exact MergedCutProfiles.Batch711.valid28440
  · exact MergedCutProfiles.Batch711.valid28447
  · exact MergedCutProfiles.Batch711.valid28448
  · exact MergedCutProfiles.Batch711.valid28449
  · exact MergedCutProfiles.Batch711.valid28450
  · exact MergedCutProfiles.Batch711.valid28451
  · exact MergedCutProfiles.Batch711.valid28452
  · exact MergedCutProfiles.Batch711.valid28453
theorem numericValid5117 : retention5117.NumericValid := by decide +kernel
def certificate5117 : RatCutBinCertificate := ⟨⟨retention5117,(971172334768336193/500000000000000000),(24651154762240763/125000000000000000),(8081272758122984273/500000000000000000),(18785377548995781000869/1000000000000000000),(2245437182910760479/1000000000000000000)⟩,(499958108936788439/500000000000000000),(142826464345455907/200000000000000000),(4542860264807671/100000000000000000),(20865043948806219/1000000000000000000)⟩
theorem valid5117 : certificate5117.Valid := by decide +kernel
theorem sound5117 : certificate5117.Sound := rat_cut_bin_certificate_sound certificate5117 profilesValid5117 numericValid5117 valid5117

def retention5118 : RatCutRetentionCertificate := ⟨(61/1000),(31/500),(2326689254553419802/1155117845288214377213),(104863643/100000000),3,(19292575082482436057/8000000000000000000),true,MergedCutProfiles.Batch711.profile28454,![MergedCutProfiles.Batch711.profile28454,MergedCutProfiles.Batch711.profile28455,MergedCutProfiles.Batch710.profile28436,MergedCutProfiles.Batch711.profile28456,MergedCutProfiles.Batch711.profile28448,MergedCutProfiles.Batch711.profile28457,MergedCutProfiles.Batch711.profile28458,MergedCutProfiles.Batch711.profile28459,MergedCutProfiles.Batch711.profile28460,MergedCutProfiles.Batch711.profile28461,MergedCutProfiles.Batch711.profile28462,MergedCutProfiles.Batch711.profile28463,MergedCutProfiles.Batch711.profile28464,MergedCutProfiles.Batch711.profile28465,MergedCutProfiles.Batch711.profile28466,MergedCutProfiles.Batch711.profile28467]⟩
theorem profilesValid5118 : retention5118.ProfilesValid := by
  change ∀ j : Fin 16, (retention5118.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch711.valid28454
  · exact MergedCutProfiles.Batch711.valid28455
  · exact MergedCutProfiles.Batch710.valid28436
  · exact MergedCutProfiles.Batch711.valid28456
  · exact MergedCutProfiles.Batch711.valid28448
  · exact MergedCutProfiles.Batch711.valid28457
  · exact MergedCutProfiles.Batch711.valid28458
  · exact MergedCutProfiles.Batch711.valid28459
  · exact MergedCutProfiles.Batch711.valid28460
  · exact MergedCutProfiles.Batch711.valid28461
  · exact MergedCutProfiles.Batch711.valid28462
  · exact MergedCutProfiles.Batch711.valid28463
  · exact MergedCutProfiles.Batch711.valid28464
  · exact MergedCutProfiles.Batch711.valid28465
  · exact MergedCutProfiles.Batch711.valid28466
  · exact MergedCutProfiles.Batch711.valid28467
theorem numericValid5118 : retention5118.NumericValid := by decide +kernel
def certificate5118 : RatCutBinCertificate := ⟨⟨retention5118,(971172334768336193/500000000000000000),(24651154762240763/125000000000000000),(8081272758122984273/500000000000000000),(18785377548995781000869/1000000000000000000),(2340472393538185739/1000000000000000000)⟩,(499958108936788439/500000000000000000),(509680439188084199/1000000000000000000),(1146949349321871/7812500000000000),(18353189604045313/200000000000000000)⟩
theorem valid5118 : certificate5118.Valid := by decide +kernel
theorem sound5118 : certificate5118.Sound := rat_cut_bin_certificate_sound certificate5118 profilesValid5118 numericValid5118 valid5118

def retention5119 : RatCutRetentionCertificate := ⟨(61/1000),(31/500),(64000000000000000000/1155117845288214377213),(1163344627276709901/500000000000000000),(7/4),(77357191913206094245294849436647683383/37227028072854716832000000000000000000),false,MergedCutProfiles.Batch711.profile28468,(fun _ => MergedCutProfiles.Batch711.profile28468)⟩
theorem profilesValid5119 : retention5119.ProfilesValid := by
  exact MergedCutProfiles.Batch711.valid28468
theorem numericValid5119 : retention5119.NumericValid := by decide +kernel
def certificate5119 : RatCutBinCertificate := ⟨⟨retention5119,(971172334768336193/500000000000000000),(24651154762240763/125000000000000000),(8081272758122984273/500000000000000000),(18785377548995781000869/1000000000000000000),(2036509951414024807/1000000000000000000)⟩,(499958108936788439/500000000000000000),(104453443331211429/250000000000000000),(108775618108685967/500000000000000000),(19687599326335647/100000000000000000)⟩
theorem valid5119 : certificate5119.Valid := by decide +kernel
theorem sound5119 : certificate5119.Sound := rat_cut_bin_certificate_sound certificate5119 profilesValid5119 numericValid5119 valid5119

def retention5120 : RatCutRetentionCertificate := ⟨(61/1000),(31/500),(1/2),64,1,(255409723632512018918146253640534376911/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch711.profile28469,(fun _ => MergedCutProfiles.Batch711.profile28469)⟩
theorem profilesValid5120 : retention5120.ProfilesValid := by
  exact MergedCutProfiles.Batch711.valid28469
theorem numericValid5120 : retention5120.NumericValid := by decide +kernel
def certificate5120 : RatCutBinCertificate := ⟨⟨retention5120,(971172334768336193/500000000000000000),(24651154762240763/125000000000000000),(8081272758122984273/500000000000000000),(18785377548995781000869/1000000000000000000),(973994477548254739/1000000000000000000)⟩,(499958108936788439/500000000000000000),(59596348302170201/100000000000000000),(47790094657417877/500000000000000000),(91691267023809273/1000000000000000000)⟩
theorem valid5120 : certificate5120.Valid := by decide +kernel
theorem sound5120 : certificate5120.Sound := rat_cut_bin_certificate_sound certificate5120 profilesValid5120 numericValid5120 valid5120

def retention5121 : RatCutRetentionCertificate := ⟨(61/1000),(31/500),(64000000000000000000/1155117845288214377213),(3071824663619598033/62500000000000000),1,(20333985906831202317757271197154021827/9829838923582713705600000000000000000),false,MergedCutProfiles.Batch711.profile28468,(fun _ => MergedCutProfiles.Batch711.profile28468)⟩
theorem profilesValid5121 : retention5121.ProfilesValid := by
  exact MergedCutProfiles.Batch711.valid28468
theorem numericValid5121 : retention5121.NumericValid := by decide +kernel
def certificate5121 : RatCutBinCertificate := ⟨⟨retention5121,(858666725768336193/500000000000000000),(24651154762240763/125000000000000000),(8081272758122984273/500000000000000000),(18785377548995781000869/1000000000000000000),(2047643823641114781/1000000000000000000)⟩,(499962961897639471/500000000000000000),(3845425257325913/250000000000000000),(222043211778052909/250000000000000000),(872895917166676799/500000000000000000)⟩
theorem valid5121 : certificate5121.Valid := by decide +kernel
theorem sound5121 : certificate5121.Sound := rat_cut_bin_certificate_sound certificate5121 profilesValid5121 numericValid5121 valid5121

def retention5122 : RatCutRetentionCertificate := ⟨(61/1000),(31/500),(1/2),64,1,(255409723632512018918146253640534376911/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch711.profile28469,(fun _ => MergedCutProfiles.Batch711.profile28469)⟩
theorem profilesValid5122 : retention5122.ProfilesValid := by
  exact MergedCutProfiles.Batch711.valid28469
theorem numericValid5122 : retention5122.NumericValid := by decide +kernel
def certificate5122 : RatCutBinCertificate := ⟨⟨retention5122,(858666725768336193/500000000000000000),(24651154762240763/125000000000000000),(8081272758122984273/500000000000000000),(18785377548995781000869/1000000000000000000),(976739979369081547/1000000000000000000)⟩,(499962961897639471/500000000000000000),(8061573646778691/250000000000000000),(418875014640422283/500000000000000000),(402951594123796347/500000000000000000)⟩
theorem valid5122 : certificate5122.Valid := by decide +kernel
theorem sound5122 : certificate5122.Sound := rat_cut_bin_certificate_sound certificate5122 profilesValid5122 numericValid5122 valid5122

def retention5123 : RatCutRetentionCertificate := ⟨(61/1000),(31/500),(767799224368385911/1155117845288214377213),(2375616412030897/3125000000000000),4,(1867292031464027696165249405923443039/760197251849887040000000000000000000),false,MergedCutProfiles.Batch711.profile28470,(fun _ => MergedCutProfiles.Batch711.profile28470)⟩
theorem profilesValid5123 : retention5123.ProfilesValid := by
  exact MergedCutProfiles.Batch711.valid28470
theorem numericValid5123 : retention5123.NumericValid := by decide +kernel
def certificate5123 : RatCutBinCertificate := ⟨⟨retention5123,(997797158768336193/500000000000000000),(24651154762240763/125000000000000000),(8081272758122984273/500000000000000000),(18785377548995781000869/1000000000000000000),(2358927409697038459/1000000000000000000)⟩,(249978480232172581/250000000000000000),(386609835560851443/500000000000000000),(27914345022602261/1000000000000000000),(1378651089047723/100000000000000000)⟩
theorem valid5123 : certificate5123.Valid := by decide +kernel
theorem sound5123 : certificate5123.Sound := rat_cut_bin_certificate_sound certificate5123 profilesValid5123 numericValid5123 valid5123

def certificates : List RatCutBinCertificate := [certificate5112,certificate5113,certificate5114,certificate5115,certificate5116,certificate5117,certificate5118,certificate5119,certificate5120,certificate5121,certificate5122,certificate5123]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound5112,List.forall_mem_cons.mpr ⟨sound5113,List.forall_mem_cons.mpr ⟨sound5114,List.forall_mem_cons.mpr ⟨sound5115,List.forall_mem_cons.mpr ⟨sound5116,List.forall_mem_cons.mpr ⟨sound5117,List.forall_mem_cons.mpr ⟨sound5118,List.forall_mem_cons.mpr ⟨sound5119,List.forall_mem_cons.mpr ⟨sound5120,List.forall_mem_cons.mpr ⟨sound5121,List.forall_mem_cons.mpr ⟨sound5122,List.forall_mem_cons.mpr ⟨sound5123,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch426
