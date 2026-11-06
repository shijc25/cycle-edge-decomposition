import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch001
import Cycle12.MergedCutProfiles.Batch002
import Cycle12.MergedCutProfiles.Batch003
import Cycle12.MergedCutProfiles.Batch307
import Cycle12.MergedCutProfiles.Batch441
import Cycle12.MergedCutProfiles.Batch561
import Cycle12.MergedCutProfiles.Batch644

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch359

def retention4308 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(255957219200000000/75016018916683844152359),(812971579528030041/1000000000000000000),(18/5),(21643527450201664011168968442688554279/9033017550311444900000000000000000000),false,MergedCutProfiles.Batch644.profile25774,(fun _ => MergedCutProfiles.Batch644.profile25774)⟩
theorem profilesValid4308 : retention4308.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25774
theorem numericValid4308 : retention4308.NumericValid := by decide +kernel
def certificate4308 : RatCutBinCertificate := ⟨⟨retention4308,(1842540530097226809/1000000000000000000),(637434242080419/1000000000000000000),(864707979900376041/125000000000000000),(2605974084985895537591801/1000000000000000000),(2395434991133056993/1000000000000000000)⟩,(3124997791274663/3125000000000000),(424945882897232873/1000000000000000000),(211387590224976347/1000000000000000000),(28650415547329119/250000000000000000)⟩
theorem valid4308 : certificate4308.Valid := by decide +kernel
theorem sound4308 : certificate4308.Sound := rat_cut_bin_certificate_sound certificate4308 profilesValid4308 numericValid4308 valid4308

def retention4309 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(2301703997688245553/125026698194473073587265),(79986631/62500000),(5/2),(12146588311167197608165488792708845031/5119144384000000000000000000000000000),false,MergedCutProfiles.Batch644.profile25775,(fun _ => MergedCutProfiles.Batch644.profile25775)⟩
theorem profilesValid4309 : retention4309.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25775
theorem numericValid4309 : retention4309.NumericValid := by decide +kernel
def certificate4309 : RatCutBinCertificate := ⟨⟨retention4309,(1842540530097226809/1000000000000000000),(637434242080419/1000000000000000000),(864707979900376041/125000000000000000),(2605974084985895537591801/1000000000000000000),(1186176296959898733/500000000000000000)⟩,(3124997791274663/3125000000000000),(83624282641332043/250000000000000000),(149588528352190959/500000000000000000),(54739810374050431/250000000000000000)⟩
theorem valid4309 : certificate4309.Valid := by decide +kernel
theorem sound4309 : certificate4309.Sound := rat_cut_bin_certificate_sound certificate4309 profilesValid4309 numericValid4309 valid4309

def retention4310 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(12800000000000000000/75016018916683844152359),(6905111993064736659/1000000000000000000),(11/10),(6357167108953756898566222430981444549039/2762044797225894663600000000000000000000),true,MergedCutProfiles.Batch001.profile71,![MergedCutProfiles.Batch001.profile71,MergedCutProfiles.Batch001.profile72,MergedCutProfiles.Batch001.profile73,MergedCutProfiles.Batch002.profile86,MergedCutProfiles.Batch001.profile75,MergedCutProfiles.Batch001.profile77,MergedCutProfiles.Batch307.profile12301,MergedCutProfiles.Batch001.profile78,MergedCutProfiles.Batch002.profile80,MergedCutProfiles.Batch002.profile81,MergedCutProfiles.Batch002.profile82,MergedCutProfiles.Batch002.profile83,MergedCutProfiles.Batch002.profile84,MergedCutProfiles.Batch002.profile85,MergedCutProfiles.Batch002.profile85,MergedCutProfiles.Batch307.profile12302]⟩
theorem profilesValid4310 : retention4310.ProfilesValid := by
  change ∀ j : Fin 16, (retention4310.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch001.valid71
  · exact MergedCutProfiles.Batch001.valid72
  · exact MergedCutProfiles.Batch001.valid73
  · exact MergedCutProfiles.Batch002.valid86
  · exact MergedCutProfiles.Batch001.valid75
  · exact MergedCutProfiles.Batch001.valid77
  · exact MergedCutProfiles.Batch307.valid12301
  · exact MergedCutProfiles.Batch001.valid78
  · exact MergedCutProfiles.Batch002.valid80
  · exact MergedCutProfiles.Batch002.valid81
  · exact MergedCutProfiles.Batch002.valid82
  · exact MergedCutProfiles.Batch002.valid83
  · exact MergedCutProfiles.Batch002.valid84
  · exact MergedCutProfiles.Batch002.valid85
  · exact MergedCutProfiles.Batch002.valid85
  · exact MergedCutProfiles.Batch307.valid12302
theorem numericValid4310 : retention4310.NumericValid := by decide +kernel
def certificate4310 : RatCutBinCertificate := ⟨⟨retention4310,(1842540530097226809/1000000000000000000),(637434242080419/1000000000000000000),(864707979900376041/125000000000000000),(2605974084985895537591801/1000000000000000000),(2301429460415553527/1000000000000000000)⟩,(3124997791274663/3125000000000000),(51619791403727923/250000000000000000),(233767701727634109/500000000000000000),(766930454646551259/1000000000000000000)⟩
theorem valid4310 : certificate4310.Valid := by decide +kernel
theorem sound4310 : certificate4310.Sound := rat_cut_bin_certificate_sound certificate4310 profilesValid4310 numericValid4310 valid4310

def retention4311 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(1/2),64,1,(15960555614684130987744105293091422311/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch003.profile124,(fun _ => MergedCutProfiles.Batch003.profile124)⟩
theorem profilesValid4311 : retention4311.ProfilesValid := by
  exact MergedCutProfiles.Batch003.valid124
theorem numericValid4311 : retention4311.NumericValid := by decide +kernel
def certificate4311 : RatCutBinCertificate := ⟨⟨retention4311,(1842540530097226809/1000000000000000000),(637434242080419/1000000000000000000),(864707979900376041/125000000000000000),(2605974084985895537591801/1000000000000000000),(99736494339382959/100000000000000000)⟩,(3124997791274663/3125000000000000),(82334128281785297/200000000000000000),(111478844199923193/500000000000000000),(218957822901902989/1000000000000000000)⟩
theorem valid4311 : certificate4311.Valid := by decide +kernel
theorem sound4311 : certificate4311.Sound := rat_cut_bin_certificate_sound certificate4311 profilesValid4311 numericValid4311 valid4311

def retention4312 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(12800000000000000000/75016018916683844152359),(1862186741982826351/125000000000000000),1,(2151366103913908370513264259237250323/931093370991413175500000000000000000),false,MergedCutProfiles.Batch644.profile25776,(fun _ => MergedCutProfiles.Batch644.profile25776)⟩
theorem profilesValid4312 : retention4312.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25776
theorem numericValid4312 : retention4312.NumericValid := by decide +kernel
def certificate4312 : RatCutBinCertificate := ⟨⟨retention4312,(1620555575097226809/1000000000000000000),(637434242080419/1000000000000000000),(864707979900376041/125000000000000000),(2605974084985895537591801/1000000000000000000),(2310431083571533267/1000000000000000000)⟩,(9999993783605451/10000000000000000),(17965572633189621/500000000000000000),(827202600550567447/1000000000000000000),(330917197834394399/200000000000000000)⟩
theorem valid4312 : certificate4312.Valid := by decide +kernel
theorem sound4312 : certificate4312.Sound := rat_cut_bin_certificate_sound certificate4312 profilesValid4312 numericValid4312 valid4312

def retention4313 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(1/2),64,1,(15960555614684130987744105293091422311/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch003.profile124,(fun _ => MergedCutProfiles.Batch003.profile124)⟩
theorem profilesValid4313 : retention4313.ProfilesValid := by
  exact MergedCutProfiles.Batch003.valid124
theorem numericValid4313 : retention4313.NumericValid := by decide +kernel
def certificate4313 : RatCutBinCertificate := ⟨⟨retention4313,(1620555575097226809/1000000000000000000),(637434242080419/1000000000000000000),(864707979900376041/125000000000000000),(2605974084985895537591801/1000000000000000000),(498692699196749517/500000000000000000)⟩,(9999993783605451/10000000000000000),(20808514698902339/250000000000000000),(704755911200906693/1000000000000000000),(692126611401348407/1000000000000000000)⟩
theorem valid4313 : certificate4313.Valid := by decide +kernel
theorem sound4313 : certificate4313.Sound := rat_cut_bin_certificate_sound certificate4313 profilesValid4313 numericValid4313 valid4313

def retention4314 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(233489596485260492/125026698194473073587265),(173383363726678583/250000000000000000),4,(264498185387633256208345692828956943/110965352785074293120000000000000000),false,MergedCutProfiles.Batch644.profile25777,(fun _ => MergedCutProfiles.Batch644.profile25777)⟩
theorem profilesValid4314 : retention4314.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25777
theorem numericValid4314 : retention4314.NumericValid := by decide +kernel
def certificate4314 : RatCutBinCertificate := ⟨⟨retention4314,(1763692728097226809/1000000000000000000),(637434242080419/1000000000000000000),(864707979900376041/125000000000000000),(2605974084985895537591801/1000000000000000000),(1191480240072583381/500000000000000000)⟩,(999999323453633449/1000000000000000000),(167634556021358499/250000000000000000),(61464699799959299/1000000000000000000),(30143662729394369/1000000000000000000)⟩
theorem valid4314 : certificate4314.Valid := by decide +kernel
theorem sound4314 : certificate4314.Sound := rat_cut_bin_certificate_sound certificate4314 profilesValid4314 numericValid4314 valid4314

def retention4315 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(3626669767205179363/75016018916683844152359),(175117197363945369/250000000000000000),4,(20856903191710286239564963348058863/8755859868197268450000000000000000),false,MergedCutProfiles.Batch644.profile25778,(fun _ => MergedCutProfiles.Batch644.profile25778)⟩
theorem profilesValid4315 : retention4315.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25778
theorem numericValid4315 : retention4315.NumericValid := by decide +kernel
def certificate4315 : RatCutBinCertificate := ⟨⟨retention4315,(1763692728097226809/1000000000000000000),(637434242080419/1000000000000000000),(864707979900376041/125000000000000000),(2605974084985895537591801/1000000000000000000),(1190700376687477767/500000000000000000)⟩,(999999323453633449/1000000000000000000),(334369231749918811/500000000000000000),(31093217912444639/500000000000000000),(1526730030077473/50000000000000000)⟩
theorem valid4315 : certificate4315.Valid := by decide +kernel
theorem sound4315 : certificate4315.Sound := rat_cut_bin_certificate_sound certificate4315 profilesValid4315 numericValid4315 valid4315

def retention4316 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(1/40),(3626669767205179363/200000000000000000),(21/20),(2492522987685258485174873348341428638759/1160534325505657396160000000000000000000),false,MergedCutProfiles.Batch644.profile25779,(fun _ => MergedCutProfiles.Batch644.profile25779)⟩
theorem profilesValid4316 : retention4316.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25779
theorem numericValid4316 : retention4316.NumericValid := by decide +kernel
def certificate4316 : RatCutBinCertificate := ⟨⟨retention4316,(1763692728097226809/1000000000000000000),(637434242080419/1000000000000000000),(864707979900376041/125000000000000000),(2605974084985895537591801/1000000000000000000),(2147566768165810561/1000000000000000000)⟩,(999999323453633449/1000000000000000000),(15714727207693729/31250000000000000),(37861094819519849/250000000000000000),(13985158697634601/50000000000000000)⟩
theorem valid4316 : certificate4316.Valid := by decide +kernel
theorem sound4316 : certificate4316.Sound := rat_cut_bin_certificate_sound certificate4316 profilesValid4316 numericValid4316 valid4316

def retention4317 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(120413366453115391/47800972580928223399921),(138999654602583193/250000000000000000),4,(54183486461232318769661981349704967/24988701951026192000000000000000000),true,MergedCutProfiles.Batch644.profile25780,![MergedCutProfiles.Batch644.profile25780,MergedCutProfiles.Batch561.profile22453,MergedCutProfiles.Batch561.profile22453,MergedCutProfiles.Batch561.profile22453,MergedCutProfiles.Batch561.profile22453,MergedCutProfiles.Batch561.profile22453,MergedCutProfiles.Batch561.profile22454,MergedCutProfiles.Batch561.profile22454,MergedCutProfiles.Batch561.profile22454,MergedCutProfiles.Batch561.profile22454,MergedCutProfiles.Batch561.profile22454,MergedCutProfiles.Batch561.profile22454,MergedCutProfiles.Batch561.profile22454,MergedCutProfiles.Batch441.profile17645,MergedCutProfiles.Batch441.profile17645,MergedCutProfiles.Batch441.profile17645]⟩
theorem profilesValid4317 : retention4317.ProfilesValid := by
  change ∀ j : Fin 16, (retention4317.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch644.valid25780
  · exact MergedCutProfiles.Batch561.valid22453
  · exact MergedCutProfiles.Batch561.valid22453
  · exact MergedCutProfiles.Batch561.valid22453
  · exact MergedCutProfiles.Batch561.valid22453
  · exact MergedCutProfiles.Batch561.valid22453
  · exact MergedCutProfiles.Batch561.valid22454
  · exact MergedCutProfiles.Batch561.valid22454
  · exact MergedCutProfiles.Batch561.valid22454
  · exact MergedCutProfiles.Batch561.valid22454
  · exact MergedCutProfiles.Batch561.valid22454
  · exact MergedCutProfiles.Batch561.valid22454
  · exact MergedCutProfiles.Batch561.valid22454
  · exact MergedCutProfiles.Batch441.valid17645
  · exact MergedCutProfiles.Batch441.valid17645
  · exact MergedCutProfiles.Batch441.valid17645
theorem numericValid4317 : retention4317.NumericValid := by decide +kernel
def certificate4317 : RatCutBinCertificate := ⟨⟨retention4317,(446171425503821687/250000000000000000),(249776479000013/250000000000000000),(6999655494241419451/1000000000000000000),(210034515586513729646543/125000000000000000),(1083650205420972479/500000000000000000)⟩,(249999734634674439/250000000000000000),(153430151248634759/250000000000000000),(86651485438566877/1000000000000000000),(37752388804067201/1000000000000000000)⟩
theorem valid4317 : certificate4317.Valid := by decide +kernel
theorem sound4317 : certificate4317.Sound := rat_cut_bin_certificate_sound certificate4317 profilesValid4317 numericValid4317 valid4317

def retention4318 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(256566617000000000/47800972580928223399921),(120413366453115391/200000000000000000),4,(5458923019435625434562083010431977951/2408267329062307820000000000000000000),true,MergedCutProfiles.Batch561.profile22453,![MergedCutProfiles.Batch561.profile22453,MergedCutProfiles.Batch561.profile22453,MergedCutProfiles.Batch561.profile22454,MergedCutProfiles.Batch561.profile22454,MergedCutProfiles.Batch561.profile22454,MergedCutProfiles.Batch561.profile22454,MergedCutProfiles.Batch441.profile17645,MergedCutProfiles.Batch441.profile17645,MergedCutProfiles.Batch441.profile17645,MergedCutProfiles.Batch441.profile17645,MergedCutProfiles.Batch441.profile17645,MergedCutProfiles.Batch561.profile22455,MergedCutProfiles.Batch561.profile22455,MergedCutProfiles.Batch561.profile22455,MergedCutProfiles.Batch561.profile22455,MergedCutProfiles.Batch561.profile22455]⟩
theorem profilesValid4318 : retention4318.ProfilesValid := by
  change ∀ j : Fin 16, (retention4318.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch561.valid22453
  · exact MergedCutProfiles.Batch561.valid22453
  · exact MergedCutProfiles.Batch561.valid22454
  · exact MergedCutProfiles.Batch561.valid22454
  · exact MergedCutProfiles.Batch561.valid22454
  · exact MergedCutProfiles.Batch561.valid22454
  · exact MergedCutProfiles.Batch441.valid17645
  · exact MergedCutProfiles.Batch441.valid17645
  · exact MergedCutProfiles.Batch441.valid17645
  · exact MergedCutProfiles.Batch441.valid17645
  · exact MergedCutProfiles.Batch441.valid17645
  · exact MergedCutProfiles.Batch561.valid22455
  · exact MergedCutProfiles.Batch561.valid22455
  · exact MergedCutProfiles.Batch561.valid22455
  · exact MergedCutProfiles.Batch561.valid22455
  · exact MergedCutProfiles.Batch561.valid22455
theorem numericValid4318 : retention4318.NumericValid := by decide +kernel
def certificate4318 : RatCutBinCertificate := ⟨⟨retention4318,(446171425503821687/250000000000000000),(249776479000013/250000000000000000),(6999655494241419451/1000000000000000000),(210034515586513729646543/125000000000000000),(453144800706674073/200000000000000000)⟩,(249999734634674439/250000000000000000),(111187806676387649/200000000000000000),(117671020260848469/1000000000000000000),(421568138509187/7812500000000000)⟩
theorem valid4318 : certificate4318.Valid := by decide +kernel
theorem sound4318 : certificate4318.Sound := rat_cut_bin_certificate_sound certificate4318 profilesValid4318 numericValid4318 valid4318

def retention4319 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(14537318753194304388/239004862904641116999605),(256566617/200000000),(5/2),(3040764850124120168042200423640781471/1282833085000000000000000000000000000),true,MergedCutProfiles.Batch441.profile17645,![MergedCutProfiles.Batch441.profile17645,MergedCutProfiles.Batch307.profile12314,MergedCutProfiles.Batch441.profile17646,MergedCutProfiles.Batch441.profile17647,MergedCutProfiles.Batch003.profile126,MergedCutProfiles.Batch307.profile12315,MergedCutProfiles.Batch441.profile17648,MergedCutProfiles.Batch003.profile127,MergedCutProfiles.Batch003.profile127,MergedCutProfiles.Batch003.profile142,MergedCutProfiles.Batch307.profile12316,MergedCutProfiles.Batch307.profile12316,MergedCutProfiles.Batch003.profile128,MergedCutProfiles.Batch003.profile128,MergedCutProfiles.Batch441.profile17649,MergedCutProfiles.Batch441.profile17649]⟩
theorem profilesValid4319 : retention4319.ProfilesValid := by
  change ∀ j : Fin 16, (retention4319.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch441.valid17645
  · exact MergedCutProfiles.Batch307.valid12314
  · exact MergedCutProfiles.Batch441.valid17646
  · exact MergedCutProfiles.Batch441.valid17647
  · exact MergedCutProfiles.Batch003.valid126
  · exact MergedCutProfiles.Batch307.valid12315
  · exact MergedCutProfiles.Batch441.valid17648
  · exact MergedCutProfiles.Batch003.valid127
  · exact MergedCutProfiles.Batch003.valid127
  · exact MergedCutProfiles.Batch003.valid142
  · exact MergedCutProfiles.Batch307.valid12316
  · exact MergedCutProfiles.Batch307.valid12316
  · exact MergedCutProfiles.Batch003.valid128
  · exact MergedCutProfiles.Batch003.valid128
  · exact MergedCutProfiles.Batch441.valid17649
  · exact MergedCutProfiles.Batch441.valid17649
theorem numericValid4319 : retention4319.NumericValid := by decide +kernel
def certificate4319 : RatCutBinCertificate := ⟨⟨retention4319,(446171425503821687/250000000000000000),(249776479000013/250000000000000000),(6999655494241419451/1000000000000000000),(210034515586513729646543/125000000000000000),(592428569707617017/250000000000000000)⟩,(249999734634674439/250000000000000000),(42620723181698561/125000000000000000),(58431337935462939/200000000000000000),(213753739710814429/1000000000000000000)⟩
theorem valid4319 : certificate4319.Valid := by decide +kernel
theorem sound4319 : certificate4319.Sound := rat_cut_bin_certificate_sound certificate4319 profilesValid4319 numericValid4319 valid4319

def certificates : List RatCutBinCertificate := [certificate4308,certificate4309,certificate4310,certificate4311,certificate4312,certificate4313,certificate4314,certificate4315,certificate4316,certificate4317,certificate4318,certificate4319]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4308,List.forall_mem_cons.mpr ⟨sound4309,List.forall_mem_cons.mpr ⟨sound4310,List.forall_mem_cons.mpr ⟨sound4311,List.forall_mem_cons.mpr ⟨sound4312,List.forall_mem_cons.mpr ⟨sound4313,List.forall_mem_cons.mpr ⟨sound4314,List.forall_mem_cons.mpr ⟨sound4315,List.forall_mem_cons.mpr ⟨sound4316,List.forall_mem_cons.mpr ⟨sound4317,List.forall_mem_cons.mpr ⟨sound4318,List.forall_mem_cons.mpr ⟨sound4319,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch359
