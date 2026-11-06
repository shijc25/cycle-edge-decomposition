import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch000
import Cycle12.MergedCutProfiles.Batch001

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch000

def retention0 : RatCutRetentionCertificate := ⟨0,(3/1000),(318188191847170663/3348560240451390669848),(526754133773041959/1000000000000000000),4,(97633641832135167520402649405687251/46822589668714840800000000000000000),true,MergedCutProfiles.Batch000.profile0,![MergedCutProfiles.Batch000.profile0,MergedCutProfiles.Batch000.profile1,MergedCutProfiles.Batch000.profile2,MergedCutProfiles.Batch000.profile3,MergedCutProfiles.Batch000.profile4,MergedCutProfiles.Batch000.profile5,MergedCutProfiles.Batch000.profile6,MergedCutProfiles.Batch000.profile7,MergedCutProfiles.Batch000.profile7,MergedCutProfiles.Batch000.profile8,MergedCutProfiles.Batch000.profile9,MergedCutProfiles.Batch000.profile10,MergedCutProfiles.Batch000.profile10,MergedCutProfiles.Batch000.profile11,MergedCutProfiles.Batch000.profile12,MergedCutProfiles.Batch000.profile12]⟩
theorem profilesValid0 : retention0.ProfilesValid := by
  change ∀ j : Fin 16, (retention0.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch000.valid0
  · exact MergedCutProfiles.Batch000.valid1
  · exact MergedCutProfiles.Batch000.valid2
  · exact MergedCutProfiles.Batch000.valid3
  · exact MergedCutProfiles.Batch000.valid4
  · exact MergedCutProfiles.Batch000.valid5
  · exact MergedCutProfiles.Batch000.valid6
  · exact MergedCutProfiles.Batch000.valid7
  · exact MergedCutProfiles.Batch000.valid7
  · exact MergedCutProfiles.Batch000.valid8
  · exact MergedCutProfiles.Batch000.valid9
  · exact MergedCutProfiles.Batch000.valid10
  · exact MergedCutProfiles.Batch000.valid10
  · exact MergedCutProfiles.Batch000.valid11
  · exact MergedCutProfiles.Batch000.valid12
  · exact MergedCutProfiles.Batch000.valid12
theorem numericValid0 : retention0.NumericValid := by decide +kernel
def certificate0 : RatCutBinCertificate := ⟨⟨retention0,(891234023952519337/500000000000000000),(357448886238193/1000000000000000000),(6680438901231477649/1000000000000000000),(22659999926297011/500000000000),(2084800944649637809/1000000000000000000)⟩,(999960669283898883/1000000000000000000),(172463974460757337/250000000000000000),(1350488648852557/25000000000000000),(22570520050706067/1000000000000000000)⟩
theorem valid0 : certificate0.Valid := by decide +kernel
theorem sound0 : certificate0.Sound := rat_cut_bin_certificate_sound certificate0 profilesValid0 numericValid0 valid0

def retention1 : RatCutRetentionCertificate := ⟨0,(3/1000),(81850652937500000/418570030056423833731),(318188191847170663/500000000000000000),4,(73937659345396981263/32000000000000000000),true,MergedCutProfiles.Batch000.profile1,![MergedCutProfiles.Batch000.profile1,MergedCutProfiles.Batch000.profile13,MergedCutProfiles.Batch000.profile5,MergedCutProfiles.Batch000.profile7,MergedCutProfiles.Batch000.profile9,MergedCutProfiles.Batch000.profile10,MergedCutProfiles.Batch000.profile11,MergedCutProfiles.Batch000.profile14,MergedCutProfiles.Batch000.profile15,MergedCutProfiles.Batch000.profile16,MergedCutProfiles.Batch000.profile17,MergedCutProfiles.Batch000.profile18,MergedCutProfiles.Batch000.profile19,MergedCutProfiles.Batch000.profile20,MergedCutProfiles.Batch000.profile21,MergedCutProfiles.Batch000.profile22]⟩
theorem profilesValid1 : retention1.ProfilesValid := by
  change ∀ j : Fin 16, (retention1.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch000.valid1
  · exact MergedCutProfiles.Batch000.valid13
  · exact MergedCutProfiles.Batch000.valid5
  · exact MergedCutProfiles.Batch000.valid7
  · exact MergedCutProfiles.Batch000.valid9
  · exact MergedCutProfiles.Batch000.valid10
  · exact MergedCutProfiles.Batch000.valid11
  · exact MergedCutProfiles.Batch000.valid14
  · exact MergedCutProfiles.Batch000.valid15
  · exact MergedCutProfiles.Batch000.valid16
  · exact MergedCutProfiles.Batch000.valid17
  · exact MergedCutProfiles.Batch000.valid18
  · exact MergedCutProfiles.Batch000.valid19
  · exact MergedCutProfiles.Batch000.valid20
  · exact MergedCutProfiles.Batch000.valid21
  · exact MergedCutProfiles.Batch000.valid22
theorem numericValid1 : retention1.NumericValid := by decide +kernel
def certificate1 : RatCutBinCertificate := ⟨⟨retention1,(891234023952519337/500000000000000000),(357448886238193/1000000000000000000),(6680438901231477649/1000000000000000000),(22659999926297011/500000000000),(2310170357920530769/1000000000000000000)⟩,(999960669283898883/1000000000000000000),(21862180860760887/40000000000000000),(123260289876328331/1000000000000000000),(14505156779662409/250000000000000000)⟩
theorem valid1 : certificate1.Valid := by decide +kernel
theorem sound1 : certificate1.Sound := rat_cut_bin_certificate_sound certificate1 profilesValid1 numericValid1 valid1

def retention2 : RatCutRetentionCertificate := ⟨0,(3/1000),(4893230564416370337/6697120480902781339696),(1309610447/1000000000),(49/20),(12262057404453086215518064472150051911/5238441788000000000000000000000000000),true,MergedCutProfiles.Batch000.profile6,![MergedCutProfiles.Batch000.profile6,MergedCutProfiles.Batch000.profile12,MergedCutProfiles.Batch000.profile17,MergedCutProfiles.Batch000.profile21,MergedCutProfiles.Batch000.profile23,MergedCutProfiles.Batch000.profile24,MergedCutProfiles.Batch000.profile25,MergedCutProfiles.Batch000.profile26,MergedCutProfiles.Batch000.profile27,MergedCutProfiles.Batch000.profile28,MergedCutProfiles.Batch000.profile29,MergedCutProfiles.Batch000.profile30,MergedCutProfiles.Batch000.profile31,MergedCutProfiles.Batch000.profile32,MergedCutProfiles.Batch000.profile33,MergedCutProfiles.Batch000.profile34]⟩
theorem profilesValid2 : retention2.ProfilesValid := by
  change ∀ j : Fin 16, (retention2.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch000.valid6
  · exact MergedCutProfiles.Batch000.valid12
  · exact MergedCutProfiles.Batch000.valid17
  · exact MergedCutProfiles.Batch000.valid21
  · exact MergedCutProfiles.Batch000.valid23
  · exact MergedCutProfiles.Batch000.valid24
  · exact MergedCutProfiles.Batch000.valid25
  · exact MergedCutProfiles.Batch000.valid26
  · exact MergedCutProfiles.Batch000.valid27
  · exact MergedCutProfiles.Batch000.valid28
  · exact MergedCutProfiles.Batch000.valid29
  · exact MergedCutProfiles.Batch000.valid30
  · exact MergedCutProfiles.Batch000.valid31
  · exact MergedCutProfiles.Batch000.valid32
  · exact MergedCutProfiles.Batch000.valid33
  · exact MergedCutProfiles.Batch000.valid34
theorem numericValid2 : retention2.NumericValid := by decide +kernel
def certificate2 : RatCutBinCertificate := ⟨⟨retention2,(891234023952519337/500000000000000000),(357448886238193/1000000000000000000),(6680438901231477649/1000000000000000000),(22659999926297011/500000000000),(2340549699956726519/1000000000000000000)⟩,(999960669283898883/1000000000000000000),(14166241014357259/40000000000000000),(6955464559407417/25000000000000000),(102399864370716119/500000000000000000)⟩
theorem valid2 : certificate2.Valid := by decide +kernel
theorem sound2 : certificate2.Sound := rat_cut_bin_certificate_sound certificate2 profilesValid2 numericValid2 valid2

def retention3 : RatCutRetentionCertificate := ⟨0,(3/1000),(4000000000000000000/418570030056423833731),(4893230564416370337/1000000000000000000),(6/5),(700117791749486973261/320000000000000000000),true,MergedCutProfiles.Batch000.profile35,![MergedCutProfiles.Batch000.profile35,MergedCutProfiles.Batch000.profile36,MergedCutProfiles.Batch000.profile37,MergedCutProfiles.Batch000.profile38,MergedCutProfiles.Batch000.profile39,MergedCutProfiles.Batch001.profile40,MergedCutProfiles.Batch001.profile41,MergedCutProfiles.Batch001.profile42,MergedCutProfiles.Batch001.profile43,MergedCutProfiles.Batch001.profile44,MergedCutProfiles.Batch001.profile45,MergedCutProfiles.Batch001.profile46,MergedCutProfiles.Batch001.profile47,MergedCutProfiles.Batch001.profile48,MergedCutProfiles.Batch001.profile49,MergedCutProfiles.Batch001.profile50]⟩
theorem profilesValid3 : retention3.ProfilesValid := by
  change ∀ j : Fin 16, (retention3.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch000.valid35
  · exact MergedCutProfiles.Batch000.valid36
  · exact MergedCutProfiles.Batch000.valid37
  · exact MergedCutProfiles.Batch000.valid38
  · exact MergedCutProfiles.Batch000.valid39
  · exact MergedCutProfiles.Batch001.valid40
  · exact MergedCutProfiles.Batch001.valid41
  · exact MergedCutProfiles.Batch001.valid42
  · exact MergedCutProfiles.Batch001.valid43
  · exact MergedCutProfiles.Batch001.valid44
  · exact MergedCutProfiles.Batch001.valid45
  · exact MergedCutProfiles.Batch001.valid46
  · exact MergedCutProfiles.Batch001.valid47
  · exact MergedCutProfiles.Batch001.valid48
  · exact MergedCutProfiles.Batch001.valid49
  · exact MergedCutProfiles.Batch001.valid50
theorem numericValid3 : retention3.NumericValid := by decide +kernel
def certificate3 : RatCutBinCertificate := ⟨⟨retention3,(891234023952519337/500000000000000000),(357448886238193/1000000000000000000),(6680438901231477649/1000000000000000000),(22659999926297011/500000000000),(2187753650230410211/1000000000000000000)⟩,(999960669283898883/1000000000000000000),(241651185570638789/1000000000000000000),(415036341483384853/1000000000000000000),(288684196338090843/500000000000000000)⟩
theorem valid3 : certificate3.Valid := by decide +kernel
theorem sound3 : certificate3.Sound := rat_cut_bin_certificate_sound certificate3 profilesValid3 numericValid3 valid3

def retention4 : RatCutRetentionCertificate := ⟨0,(3/1000),(1/2),64,1,(2553689015764907893961280798454983519/2560000000000000000000000000000000000),false,MergedCutProfiles.Batch001.profile51,(fun _ => MergedCutProfiles.Batch001.profile51)⟩
theorem profilesValid4 : retention4.ProfilesValid := by
  exact MergedCutProfiles.Batch001.valid51
theorem numericValid4 : retention4.NumericValid := by decide +kernel
def certificate4 : RatCutBinCertificate := ⟨⟨retention4,(891234023952519337/500000000000000000),(357448886238193/1000000000000000000),(6680438901231477649/1000000000000000000),(22659999926297011/500000000000),(249359849406917421/250000000000000000)⟩,(999960669283898883/1000000000000000000),(1673579182292773/3906250000000000),(52103724881267771/250000000000000000),(204683002457726703/1000000000000000000)⟩
theorem valid4 : certificate4.Valid := by decide +kernel
theorem sound4 : certificate4.Sound := rat_cut_bin_certificate_sound certificate4 profilesValid4 numericValid4 valid4

def retention5 : RatCutRetentionCertificate := ⟨0,(3/1000),(4000000000000000000/418570030056423833731),(3396530379125543999/1000000000000000000),(27/20),(11860664480153354488559335842548250680031/5434448606600870398400000000000000000000),false,MergedCutProfiles.Batch001.profile52,(fun _ => MergedCutProfiles.Batch001.profile52)⟩
theorem profilesValid5 : retention5.ProfilesValid := by
  exact MergedCutProfiles.Batch001.valid52
theorem numericValid5 : retention5.NumericValid := by decide +kernel
def certificate5 : RatCutBinCertificate := ⟨⟨retention5,(1050420927952519337/500000000000000000),(357448886238193/1000000000000000000),(6680438901231477649/1000000000000000000),(22659999926297011/500000000000),(1091172320054019613/500000000000000000)⟩,(49997682213302363/50000000000000000),(179300808368956533/1000000000000000000),(256021833127978333/500000000000000000),(305979037303551487/500000000000000000)⟩
theorem valid5 : certificate5.Valid := by decide +kernel
theorem sound5 : certificate5.Sound := rat_cut_bin_certificate_sound certificate5 profilesValid5 numericValid5 valid5

def retention6 : RatCutRetentionCertificate := ⟨0,(3/1000),(1/2),64,1,(2553689015764907893961280798454983519/2560000000000000000000000000000000000),false,MergedCutProfiles.Batch001.profile51,(fun _ => MergedCutProfiles.Batch001.profile51)⟩
theorem profilesValid6 : retention6.ProfilesValid := by
  exact MergedCutProfiles.Batch001.valid51
theorem numericValid6 : retention6.NumericValid := by decide +kernel
def certificate6 : RatCutBinCertificate := ⟨⟨retention6,(1050420927952519337/500000000000000000),(357448886238193/1000000000000000000),(6680438901231477649/1000000000000000000),(22659999926297011/500000000000),(997422362465044357/1000000000000000000)⟩,(49997682213302363/50000000000000000),(392307384350172227/1000000000000000000),(60151283531647803/250000000000000000),(236291201862173697/1000000000000000000)⟩
theorem valid6 : certificate6.Valid := by decide +kernel
theorem sound6 : certificate6.Sound := rat_cut_bin_certificate_sound certificate6 profilesValid6 numericValid6 valid6

def retention7 : RatCutRetentionCertificate := ⟨0,(3/1000),(608818170029686007/13394240961805562679393),(127245632834735863/250000000000000000),4,(32457190027206752483/16000000000000000000),true,MergedCutProfiles.Batch001.profile53,![MergedCutProfiles.Batch001.profile53,MergedCutProfiles.Batch000.profile0,MergedCutProfiles.Batch001.profile54,MergedCutProfiles.Batch001.profile55,MergedCutProfiles.Batch000.profile1,MergedCutProfiles.Batch000.profile2,MergedCutProfiles.Batch000.profile3,MergedCutProfiles.Batch000.profile3,MergedCutProfiles.Batch000.profile13,MergedCutProfiles.Batch000.profile13,MergedCutProfiles.Batch000.profile4,MergedCutProfiles.Batch000.profile4,MergedCutProfiles.Batch000.profile5,MergedCutProfiles.Batch000.profile5,MergedCutProfiles.Batch000.profile6,MergedCutProfiles.Batch000.profile6]⟩
theorem profilesValid7 : retention7.ProfilesValid := by
  change ∀ j : Fin 16, (retention7.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch001.valid53
  · exact MergedCutProfiles.Batch000.valid0
  · exact MergedCutProfiles.Batch001.valid54
  · exact MergedCutProfiles.Batch001.valid55
  · exact MergedCutProfiles.Batch000.valid1
  · exact MergedCutProfiles.Batch000.valid2
  · exact MergedCutProfiles.Batch000.valid3
  · exact MergedCutProfiles.Batch000.valid3
  · exact MergedCutProfiles.Batch000.valid13
  · exact MergedCutProfiles.Batch000.valid13
  · exact MergedCutProfiles.Batch000.valid4
  · exact MergedCutProfiles.Batch000.valid4
  · exact MergedCutProfiles.Batch000.valid5
  · exact MergedCutProfiles.Batch000.valid5
  · exact MergedCutProfiles.Batch000.valid6
  · exact MergedCutProfiles.Batch000.valid6
theorem numericValid7 : retention7.NumericValid := by decide +kernel
def certificate7 : RatCutBinCertificate := ⟨⟨retention7,(1752033943952519337/1000000000000000000),(357448886238193/1000000000000000000),(1336087783505573881/200000000000000000),(22659999981574252727111/250000000000000000),(126762462112770053/62500000000000000)⟩,(499990335205508731/500000000000000000),(755555412698648113/1000000000000000000),(2041298592623691/62500000000000000),(6629134478780309/500000000000000000)⟩
theorem valid7 : certificate7.Valid := by decide +kernel
theorem sound7 : certificate7.Sound := rat_cut_bin_certificate_sound certificate7 profilesValid7 numericValid7 valid7

def retention8 : RatCutRetentionCertificate := ⟨0,(3/1000),(433134822000000000/4464746987268520893131),(608818170029686007/1000000000000000000),4,(1383555473909020898789804037039231171/608818170029686007000000000000000000),true,MergedCutProfiles.Batch001.profile54,![MergedCutProfiles.Batch001.profile54,MergedCutProfiles.Batch000.profile1,MergedCutProfiles.Batch000.profile2,MergedCutProfiles.Batch000.profile13,MergedCutProfiles.Batch000.profile4,MergedCutProfiles.Batch000.profile5,MergedCutProfiles.Batch000.profile6,MergedCutProfiles.Batch000.profile7,MergedCutProfiles.Batch000.profile8,MergedCutProfiles.Batch000.profile8,MergedCutProfiles.Batch000.profile9,MergedCutProfiles.Batch000.profile10,MergedCutProfiles.Batch000.profile11,MergedCutProfiles.Batch000.profile11,MergedCutProfiles.Batch000.profile12,MergedCutProfiles.Batch000.profile14]⟩
theorem profilesValid8 : retention8.ProfilesValid := by
  change ∀ j : Fin 16, (retention8.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch001.valid54
  · exact MergedCutProfiles.Batch000.valid1
  · exact MergedCutProfiles.Batch000.valid2
  · exact MergedCutProfiles.Batch000.valid13
  · exact MergedCutProfiles.Batch000.valid4
  · exact MergedCutProfiles.Batch000.valid5
  · exact MergedCutProfiles.Batch000.valid6
  · exact MergedCutProfiles.Batch000.valid7
  · exact MergedCutProfiles.Batch000.valid8
  · exact MergedCutProfiles.Batch000.valid8
  · exact MergedCutProfiles.Batch000.valid9
  · exact MergedCutProfiles.Batch000.valid10
  · exact MergedCutProfiles.Batch000.valid11
  · exact MergedCutProfiles.Batch000.valid11
  · exact MergedCutProfiles.Batch000.valid12
  · exact MergedCutProfiles.Batch000.valid14
theorem numericValid8 : retention8.NumericValid := by decide +kernel
def certificate8 : RatCutBinCertificate := ⟨⟨retention8,(1752033943952519337/1000000000000000000),(357448886238193/1000000000000000000),(1336087783505573881/200000000000000000),(22659999981574252727111/250000000000000000),(2272151597316889461/1000000000000000000)⟩,(499990335205508731/500000000000000000),(595033304354434317/1000000000000000000),(1500974275014723/15625000000000000),(1106134414033799/25000000000000000)⟩
theorem valid8 : certificate8.Valid := by decide +kernel
theorem sound8 : certificate8.Sound := rat_cut_bin_certificate_sound certificate8 profilesValid8 numericValid8 valid8

def retention9 : RatCutRetentionCertificate := ⟨0,(3/1000),(7699063825194549412/13394240961805562679393),(649702233/500000000),(5/2),(84941004954428892686580606416956991/36094568500000000000000000000000000),true,MergedCutProfiles.Batch000.profile5,![MergedCutProfiles.Batch000.profile5,MergedCutProfiles.Batch000.profile10,MergedCutProfiles.Batch000.profile15,MergedCutProfiles.Batch000.profile18,MergedCutProfiles.Batch000.profile21,MergedCutProfiles.Batch000.profile23,MergedCutProfiles.Batch001.profile56,MergedCutProfiles.Batch001.profile57,MergedCutProfiles.Batch000.profile25,MergedCutProfiles.Batch001.profile58,MergedCutProfiles.Batch001.profile59,MergedCutProfiles.Batch001.profile60,MergedCutProfiles.Batch001.profile61,MergedCutProfiles.Batch000.profile29,MergedCutProfiles.Batch000.profile30,MergedCutProfiles.Batch000.profile31]⟩
theorem profilesValid9 : retention9.ProfilesValid := by
  change ∀ j : Fin 16, (retention9.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch000.valid5
  · exact MergedCutProfiles.Batch000.valid10
  · exact MergedCutProfiles.Batch000.valid15
  · exact MergedCutProfiles.Batch000.valid18
  · exact MergedCutProfiles.Batch000.valid21
  · exact MergedCutProfiles.Batch000.valid23
  · exact MergedCutProfiles.Batch001.valid56
  · exact MergedCutProfiles.Batch001.valid57
  · exact MergedCutProfiles.Batch000.valid25
  · exact MergedCutProfiles.Batch001.valid58
  · exact MergedCutProfiles.Batch001.valid59
  · exact MergedCutProfiles.Batch001.valid60
  · exact MergedCutProfiles.Batch001.valid61
  · exact MergedCutProfiles.Batch000.valid29
  · exact MergedCutProfiles.Batch000.valid30
  · exact MergedCutProfiles.Batch000.valid31
theorem numericValid9 : retention9.NumericValid := by decide +kernel
def certificate9 : RatCutBinCertificate := ⟨⟨retention9,(1752033943952519337/1000000000000000000),(357448886238193/1000000000000000000),(1336087783505573881/200000000000000000),(22659999981574252727111/250000000000000000),(1176528065099205663/500000000000000000)⟩,(499990335205508731/500000000000000000),(36683353762676981/100000000000000000),(10611396830805947/40000000000000000),(774378430816281/4000000000000000)⟩
theorem valid9 : certificate9.Valid := by decide +kernel
theorem sound9 : certificate9.Sound := rat_cut_bin_certificate_sound certificate9 profilesValid9 numericValid9 valid9

def retention10 : RatCutRetentionCertificate := ⟨0,(3/1000),(64000000000000000000/13394240961805562679393),(1924765956298637353/250000000000000000),(11/10),(431166113320429061421170765630711283871/192476595629863735300000000000000000000),true,MergedCutProfiles.Batch001.profile62,![MergedCutProfiles.Batch001.profile62,MergedCutProfiles.Batch000.profile35,MergedCutProfiles.Batch001.profile63,MergedCutProfiles.Batch000.profile36,MergedCutProfiles.Batch001.profile64,MergedCutProfiles.Batch000.profile37,MergedCutProfiles.Batch001.profile65,MergedCutProfiles.Batch000.profile38,MergedCutProfiles.Batch001.profile66,MergedCutProfiles.Batch000.profile39,MergedCutProfiles.Batch001.profile67,MergedCutProfiles.Batch001.profile40,MergedCutProfiles.Batch001.profile68,MergedCutProfiles.Batch001.profile41,MergedCutProfiles.Batch001.profile69,MergedCutProfiles.Batch001.profile42]⟩
theorem profilesValid10 : retention10.ProfilesValid := by
  change ∀ j : Fin 16, (retention10.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch001.valid62
  · exact MergedCutProfiles.Batch000.valid35
  · exact MergedCutProfiles.Batch001.valid63
  · exact MergedCutProfiles.Batch000.valid36
  · exact MergedCutProfiles.Batch001.valid64
  · exact MergedCutProfiles.Batch000.valid37
  · exact MergedCutProfiles.Batch001.valid65
  · exact MergedCutProfiles.Batch000.valid38
  · exact MergedCutProfiles.Batch001.valid66
  · exact MergedCutProfiles.Batch000.valid39
  · exact MergedCutProfiles.Batch001.valid67
  · exact MergedCutProfiles.Batch001.valid40
  · exact MergedCutProfiles.Batch001.valid68
  · exact MergedCutProfiles.Batch001.valid41
  · exact MergedCutProfiles.Batch001.valid69
  · exact MergedCutProfiles.Batch001.valid42
theorem numericValid10 : retention10.NumericValid := by decide +kernel
def certificate10 : RatCutBinCertificate := ⟨⟨retention10,(1752033943952519337/1000000000000000000),(357448886238193/1000000000000000000),(1336087783505573881/200000000000000000),(22659999981574252727111/250000000000000000),(2239993198476786291/1000000000000000000)⟩,(499990335205508731/500000000000000000),(56357945201903151/250000000000000000),(438576073209066511/1000000000000000000),(359982264859994701/500000000000000000)⟩
theorem valid10 : certificate10.Valid := by decide +kernel
theorem sound10 : certificate10.Sound := rat_cut_bin_certificate_sound certificate10 profilesValid10 numericValid10 valid10

def retention11 : RatCutRetentionCertificate := ⟨0,(3/1000),(1/2),64,1,(2553689015764907893961280798454983519/2560000000000000000000000000000000000),false,MergedCutProfiles.Batch001.profile51,(fun _ => MergedCutProfiles.Batch001.profile51)⟩
theorem profilesValid11 : retention11.ProfilesValid := by
  exact MergedCutProfiles.Batch001.valid51
theorem numericValid11 : retention11.NumericValid := by decide +kernel
def certificate11 : RatCutBinCertificate := ⟨⟨retention11,(1752033943952519337/1000000000000000000),(357448886238193/1000000000000000000),(1336087783505573881/200000000000000000),(22659999981574252727111/250000000000000000),(49872051302965883/50000000000000000)⟩,(499990335205508731/500000000000000000),(221056903801531463/500000000000000000),(19703787113581079/100000000000000000),(38702781346610031/200000000000000000)⟩
theorem valid11 : certificate11.Valid := by decide +kernel
theorem sound11 : certificate11.Sound := rat_cut_bin_certificate_sound certificate11 profilesValid11 numericValid11 valid11

def certificates : List RatCutBinCertificate := [certificate0,certificate1,certificate2,certificate3,certificate4,certificate5,certificate6,certificate7,certificate8,certificate9,certificate10,certificate11]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_cons.mpr ⟨sound6,List.forall_mem_cons.mpr ⟨sound7,List.forall_mem_cons.mpr ⟨sound8,List.forall_mem_cons.mpr ⟨sound9,List.forall_mem_cons.mpr ⟨sound10,List.forall_mem_cons.mpr ⟨sound11,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch000
