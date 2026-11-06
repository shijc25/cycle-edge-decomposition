import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch032

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs032

def inputs640 : RatMajorityInputs := ⟨(98520971827795947609583131/50000000000000000000000),(61431783366681/12500000000000),(1001524323377492271/1000000000000000000),(66018296289630141/500000000000000000),(61431783366681/25000000000000),(17133678540715039/200000000000000000),27⟩
theorem inputs_valid640 : inputs640.Valid := by decide +kernel
def envelope640 : RatMajorityEnvelope := ⟨320,0,inputs640,(178431137/156195000),(332954377810346047/500000000000000000)⟩
theorem envelope_sound640 : envelope640.Sound := by
  apply rat_majority_inputs_envelopes inputs640 inputs_valid640
  · norm_num [envelope640]
  · intro rho hr0 hr1
    have hh := Batch032.bound1280 rho hr0 hr1
    norm_num [Batch032.certificate1280,envelope640,inputs640,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch032.bound1281 rho hr0 hr1
    norm_num [Batch032.certificate1281,envelope640,inputs640,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs641 : RatMajorityInputs := ⟨(98520971827795947609583131/50000000000000000000000),(503356431677463/100000000000000),(1001524323377492271/1000000000000000000),(30463350979200769/250000000000000000),(503356431677463/200000000000000),(80718930027124603/1000000000000000000),26⟩
theorem inputs_valid641 : inputs641.Valid := by decide +kernel
def envelope641 : RatMajorityEnvelope := ⟨320,1,inputs641,1,(33756807810488003/62500000000000000)⟩
theorem envelope_sound641 : envelope641.Sound := by
  apply rat_majority_inputs_envelopes inputs641 inputs_valid641
  · norm_num [envelope641]
  · intro rho hr0 hr1
    have hh := Batch032.bound1282 rho hr0 hr1
    norm_num [Batch032.certificate1282,envelope641,inputs641,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch032.bound1283 rho hr0 hr1
    norm_num [Batch032.certificate1283,envelope641,inputs641,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs642 : RatMajorityInputs := ⟨(48802994951765073891531033/25000000000000000000000),(61619662108829/12500000000000),(1001538629846823003/1000000000000000000),(65355195394021841/500000000000000000),(61619662108829/25000000000000),(85026995027534723/1000000000000000000),26⟩
theorem inputs_valid642 : inputs642.Valid := by decide +kernel
def envelope642 : RatMajorityEnvelope := ⟨321,0,inputs642,(1246864667/1093070000),(664309187908522527/1000000000000000000)⟩
theorem envelope_sound642 : envelope642.Sound := by
  apply rat_majority_inputs_envelopes inputs642 inputs_valid642
  · norm_num [envelope642]
  · intro rho hr0 hr1
    have hh := Batch032.bound1284 rho hr0 hr1
    norm_num [Batch032.certificate1284,envelope642,inputs642,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch032.bound1285 rho hr0 hr1
    norm_num [Batch032.certificate1285,envelope642,inputs642,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs643 : RatMajorityInputs := ⟨(48802994951765073891531033/25000000000000000000000),(63063262605937/12500000000000),(1001538629846823003/1000000000000000000),(120907731985031791/1000000000000000000),(63063262605937/25000000000000),(80256260766152747/1000000000000000000),26⟩
theorem inputs_valid643 : inputs643.Valid := by decide +kernel
def envelope643 : RatMajorityEnvelope := ⟨321,1,inputs643,1,(540015549326937759/1000000000000000000)⟩
theorem envelope_sound643 : envelope643.Sound := by
  apply rat_majority_inputs_envelopes inputs643 inputs_valid643
  · norm_num [envelope643]
  · intro rho hr0 hr1
    have hh := Batch032.bound1286 rho hr0 hr1
    norm_num [Batch032.certificate1286,envelope643,inputs643,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch032.bound1287 rho hr0 hr1
    norm_num [Batch032.certificate1287,envelope643,inputs643,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs644 : RatMajorityInputs := ⟨(193430506828361315781077327/100000000000000000000000),(494259795214327/100000000000000),(500776408781975263/500000000000000000),(129570669445581597/1000000000000000000),(494259795214327/200000000000000),(16895011324893753/200000000000000000),27⟩
theorem inputs_valid644 : inputs644.Valid := by decide +kernel
def envelope644 : RatMajorityEnvelope := ⟨322,0,inputs644,(1244753077/1092785000),(662750328479416491/1000000000000000000)⟩
theorem envelope_sound644 : envelope644.Sound := by
  apply rat_majority_inputs_envelopes inputs644 inputs_valid644
  · norm_num [envelope644]
  · intro rho hr0 hr1
    have hh := Batch032.bound1288 rho hr0 hr1
    norm_num [Batch032.certificate1288,envelope644,inputs644,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch032.bound1289 rho hr0 hr1
    norm_num [Batch032.certificate1289,envelope644,inputs644,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs645 : RatMajorityInputs := ⟨(193430506828361315781077327/100000000000000000000000),(101001403931181/20000000000000),(500776408781975263/500000000000000000),(120497743622936743/1000000000000000000),(101001403931181/40000000000000),(20013875731747741/250000000000000000),26⟩
theorem inputs_valid645 : inputs645.Valid := by decide +kernel
def envelope645 : RatMajorityEnvelope := ⟨322,1,inputs645,1,(53997884207366611/100000000000000000)⟩
theorem envelope_sound645 : envelope645.Sound := by
  apply rat_majority_inputs_envelopes inputs645 inputs_valid645
  · norm_num [envelope645]
  · intro rho hr0 hr1
    have hh := Batch032.bound1290 rho hr0 hr1
    norm_num [Batch032.certificate1290,envelope645,inputs645,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch032.bound1291 rho hr0 hr1
    norm_num [Batch032.certificate1291,envelope645,inputs645,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs646 : RatMajorityInputs := ⟨(2396202680448009801953217/1250000000000000000000),(123975051482943/25000000000000),(100156688315736157/100000000000000000),(128147785179964959/1000000000000000000),(123975051482943/50000000000000),(16757004280921217/200000000000000000),26⟩
theorem inputs_valid646 : inputs646.Valid := by decide +kernel
def envelope646 : RatMajorityEnvelope := ⟨323,0,inputs646,(165683791/145668000),(661146613584402163/1000000000000000000)⟩
theorem envelope_sound646 : envelope646.Sound := by
  apply rat_majority_inputs_envelopes inputs646 inputs_valid646
  · norm_num [envelope646]
  · intro rho hr0 hr1
    have hh := Batch032.bound1292 rho hr0 hr1
    norm_num [Batch032.certificate1292,envelope646,inputs646,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch032.bound1293 rho hr0 hr1
    norm_num [Batch032.certificate1293,envelope646,inputs646,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs647 : RatMajorityInputs := ⟨(2396202680448009801953217/1250000000000000000000),(126532060649847/25000000000000),(100156688315736157/100000000000000000),(59792268733651001/500000000000000000),(126532060649847/50000000000000),(79607958259334273/1000000000000000000),26⟩
theorem inputs_valid647 : inputs647.Valid := by decide +kernel
def envelope647 : RatMajorityEnvelope := ⟨323,1,inputs647,1,(539889133830467151/1000000000000000000)⟩
theorem envelope_sound647 : envelope647.Sound := by
  apply rat_majority_inputs_envelopes inputs647 inputs_valid647
  · norm_num [envelope647]
  · intro rho hr0 hr1
    have hh := Batch032.bound1294 rho hr0 hr1
    norm_num [Batch032.certificate1294,envelope647,inputs647,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch032.bound1295 rho hr0 hr1
    norm_num [Batch032.certificate1295,envelope647,inputs647,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs648 : RatMajorityInputs := ⟨(2968858951123503559502529/1562500000000000000000),(1942429526433/390625000000),(125197603816143359/125000000000000000),(15872142486989677/125000000000000000),(1942429526433/781250000000),(832164866583423/10000000000000000),28⟩
theorem inputs_valid648 : inputs648.Valid := by decide +kernel
def envelope648 : RatMajorityEnvelope := ⟨324,0,inputs648,(165292411/145632000),(65889368507565313/100000000000000000)⟩
theorem envelope_sound648 : envelope648.Sound := by
  apply rat_majority_inputs_envelopes inputs648 inputs_valid648
  · norm_num [envelope648]
  · intro rho hr0 hr1
    have hh := Batch032.bound1296 rho hr0 hr1
    norm_num [Batch032.certificate1296,envelope648,inputs648,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch032.bound1297 rho hr0 hr1
    norm_num [Batch032.certificate1297,envelope648,inputs648,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs649 : RatMajorityInputs := ⟨(2968858951123503559502529/1562500000000000000000),(31721629490127/6250000000000),(125197603816143359/125000000000000000),(118438586407984561/1000000000000000000),(31721629490127/12500000000000),(39522800736692849/500000000000000000),26⟩
theorem inputs_valid649 : inputs649.Valid := by decide +kernel
def envelope649 : RatMajorityEnvelope := ⟨324,1,inputs649,1,(134943793017943021/250000000000000000)⟩
theorem envelope_sound649 : envelope649.Sound := by
  apply rat_majority_inputs_envelopes inputs649 inputs_valid649
  · norm_num [envelope649]
  · intro rho hr0 hr1
    have hh := Batch032.bound1298 rho hr0 hr1
    norm_num [Batch032.certificate1298,envelope649,inputs649,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch032.bound1299 rho hr0 hr1
    norm_num [Batch032.certificate1299,envelope649,inputs649,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs650 : RatMajorityInputs := ⟨(18836159229264843758847983/10000000000000000000000),(9935331436291/2000000000000),(125199332070059441/125000000000000000),(31850475770657919/250000000000000000),(9935331436291/4000000000000),(5213928997056809/62500000000000000),26⟩
theorem inputs_valid650 : inputs650.Valid := by decide +kernel
def envelope650 : RatMajorityEnvelope := ⟨325,0,inputs650,(1237813681/1091975000),(328820741716693039/500000000000000000)⟩
theorem envelope_sound650 : envelope650.Sound := by
  apply rat_majority_inputs_envelopes inputs650 inputs_valid650
  · norm_num [envelope650]
  · intro rho hr0 hr1
    have hh := Batch032.bound1300 rho hr0 hr1
    norm_num [Batch032.certificate1300,envelope650,inputs650,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch032.bound1301 rho hr0 hr1
    norm_num [Batch032.certificate1301,envelope650,inputs650,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs651 : RatMajorityInputs := ⟨(18836159229264843758847983/10000000000000000000000),(6350882091099/1250000000000),(125199332070059441/125000000000000000),(118017153947944041/1000000000000000000),(6350882091099/2500000000000),(19709644439892643/250000000000000000),26⟩
theorem inputs_valid651 : inputs651.Valid := by decide +kernel
def envelope651 : RatMajorityEnvelope := ⟨325,1,inputs651,1,(539737391076274947/1000000000000000000)⟩
theorem envelope_sound651 : envelope651.Sound := by
  apply rat_majority_inputs_envelopes inputs651 inputs_valid651
  · norm_num [envelope651]
  · intro rho hr0 hr1
    have hh := Batch032.bound1302 rho hr0 hr1
    norm_num [Batch032.certificate1302,envelope651,inputs651,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch032.bound1303 rho hr0 hr1
    norm_num [Batch032.certificate1303,envelope651,inputs651,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs652 : RatMajorityInputs := ⟨(5836243223012095412417703/3125000000000000000000),(62510261929143/12500000000000),(40064334031345821/40000000000000000),(124582892175534907/1000000000000000000),(62510261929143/25000000000000),(20512827880170463/250000000000000000),26⟩
theorem inputs_valid652 : inputs652.Valid := by decide +kernel
def envelope652 : RatMajorityEnvelope := ⟨326,0,inputs652,(123555083/109172000),(65578401154486843/100000000000000000)⟩
theorem envelope_sound652 : envelope652.Sound := by
  apply rat_majority_inputs_envelopes inputs652 inputs_valid652
  · norm_num [envelope652]
  · intro rho hr0 hr1
    have hh := Batch032.bound1304 rho hr0 hr1
    norm_num [Batch032.certificate1304,envelope652,inputs652,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch032.bound1305 rho hr0 hr1
    norm_num [Batch032.certificate1305,envelope652,inputs652,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs653 : RatMajorityInputs := ⟨(5836243223012095412417703/3125000000000000000000),(31827944098489/6250000000000),(40064334031345821/40000000000000000),(117076667100104083/1000000000000000000),(31827944098489/12500000000000),(78376156208279201/1000000000000000000),27⟩
theorem inputs_valid653 : inputs653.Valid := by decide +kernel
def envelope653 : RatMajorityEnvelope := ⟨326,1,inputs653,1,(21585811572310111/40000000000000000)⟩
theorem envelope_sound653 : envelope653.Sound := by
  apply rat_majority_inputs_envelopes inputs653 inputs_valid653
  · norm_num [envelope653]
  · intro rho hr0 hr1
    have hh := Batch032.bound1306 rho hr0 hr1
    norm_num [Batch032.certificate1306,envelope653,inputs653,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch032.bound1307 rho hr0 hr1
    norm_num [Batch032.certificate1307,envelope653,inputs653,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs654 : RatMajorityInputs := ⟨(37040084530976201858166753/20000000000000000000000),(6278431524057/1250000000000),(250405477485432323/250000000000000000),(122749344160771869/1000000000000000000),(6278431524057/2500000000000),(40578383097835353/500000000000000000),26⟩
theorem inputs_valid654 : inputs654.Valid := by decide +kernel
def envelope654 : RatMajorityEnvelope := ⟨327,0,inputs654,(273911797/242550000),(163360028236576653/250000000000000000)⟩
theorem envelope_sound654 : envelope654.Sound := by
  apply rat_majority_inputs_envelopes inputs654 inputs_valid654
  · norm_num [envelope654]
  · intro rho hr0 hr1
    have hh := Batch032.bound1308 rho hr0 hr1
    norm_num [Batch032.certificate1308,envelope654,inputs654,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch032.bound1309 rho hr0 hr1
    norm_num [Batch032.certificate1309,envelope654,inputs654,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs655 : RatMajorityInputs := ⟨(37040084530976201858166753/20000000000000000000000),(51069997065087/10000000000000),(250405477485432323/250000000000000000),(7245283026784683/62500000000000000),(51069997065087/20000000000000),(15561773856198987/200000000000000000),27⟩
theorem inputs_valid655 : inputs655.Valid := by decide +kernel
def envelope655 : RatMajorityEnvelope := ⟨327,1,inputs655,1,(539531295427428091/1000000000000000000)⟩
theorem envelope_sound655 : envelope655.Sound := by
  apply rat_majority_inputs_envelopes inputs655 inputs_valid655
  · norm_num [envelope655]
  · intro rho hr0 hr1
    have hh := Batch032.bound1310 rho hr0 hr1
    norm_num [Batch032.certificate1310,envelope655,inputs655,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch032.bound1311 rho hr0 hr1
    norm_num [Batch032.certificate1311,envelope655,inputs655,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs656 : RatMajorityInputs := ⟨(31417232671709142909524892161/25000000000000000000000),(211794859764619/50000000000000),(500001193614664263/500000000000000000),(205534660685740379/1000000000000000000),(211794859764619/100000000000000),(24055622882230929/200000000000000000),25⟩
theorem inputs_valid656 : inputs656.Valid := by decide +kernel
def envelope656 : RatMajorityEnvelope := ⟨328,0,inputs656,(694811003/602792500),(681389053121324357/1000000000000000000)⟩
theorem envelope_sound656 : envelope656.Sound := by
  apply rat_majority_inputs_envelopes inputs656 inputs_valid656
  · norm_num [envelope656]
  · intro rho hr0 hr1
    have hh := Batch032.bound1312 rho hr0 hr1
    norm_num [Batch032.certificate1312,envelope656,inputs656,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch032.bound1313 rho hr0 hr1
    norm_num [Batch032.certificate1313,envelope656,inputs656,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs657 : RatMajorityInputs := ⟨(31417232671709142909524892161/25000000000000000000000),(42227706797209/10000000000000),(500001193614664263/500000000000000000),(25905529158215633/125000000000000000),(42227706797209/20000000000000),(30267531732525323/250000000000000000),25⟩
theorem inputs_valid657 : inputs657.Valid := by decide +kernel
def envelope657 : RatMajorityEnvelope := ⟨328,1,inputs657,1,(549566758183060013/1000000000000000000)⟩
theorem envelope_sound657 : envelope657.Sound := by
  apply rat_majority_inputs_envelopes inputs657 inputs_valid657
  · norm_num [envelope657]
  · intro rho hr0 hr1
    have hh := Batch032.bound1314 rho hr0 hr1
    norm_num [Batch032.certificate1314,envelope657,inputs657,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch032.bound1315 rho hr0 hr1
    norm_num [Batch032.certificate1315,envelope657,inputs657,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs658 : RatMajorityInputs := ⟨(40458024583154253247157620573/50000000000000000000000),(222635302403323/50000000000000),(200000741511401477/200000000000000000),(178967927355920517/1000000000000000000),(222635302403323/100000000000000),(26980324923429521/250000000000000000),25⟩
theorem inputs_valid658 : inputs658.Valid := by decide +kernel
def envelope658 : RatMajorityEnvelope := ⟨329,0,inputs658,(2769602081/2407820000),(676496766482074299/1000000000000000000)⟩
theorem envelope_sound658 : envelope658.Sound := by
  apply rat_majority_inputs_envelopes inputs658 inputs_valid658
  · norm_num [envelope658]
  · intro rho hr0 hr1
    have hh := Batch032.bound1316 rho hr0 hr1
    norm_num [Batch032.certificate1316,envelope658,inputs658,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch032.bound1317 rho hr0 hr1
    norm_num [Batch032.certificate1317,envelope658,inputs658,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs659 : RatMajorityInputs := ⟨(40458024583154253247157620573/50000000000000000000000),(105682659250479/25000000000000),(200000741511401477/200000000000000000),(51663043941052671/250000000000000000),(105682659250479/50000000000000),(120795869734009027/1000000000000000000),25⟩
theorem inputs_valid659 : inputs659.Valid := by decide +kernel
def envelope659 : RatMajorityEnvelope := ⟨329,1,inputs659,1,(549488971839446569/1000000000000000000)⟩
theorem envelope_sound659 : envelope659.Sound := by
  apply rat_majority_inputs_envelopes inputs659 inputs_valid659
  · norm_num [envelope659]
  · intro rho hr0 hr1
    have hh := Batch032.bound1318 rho hr0 hr1
    norm_num [Batch032.certificate1318,envelope659,inputs659,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch032.bound1319 rho hr0 hr1
    norm_num [Batch032.certificate1319,envelope659,inputs659,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope640,envelope641,envelope642,envelope643,envelope644,envelope645,envelope646,envelope647,envelope648,envelope649,envelope650,envelope651,envelope652,envelope653,envelope654,envelope655,envelope656,envelope657,envelope658,envelope659]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound640
  · exact envelope_sound641
  · exact envelope_sound642
  · exact envelope_sound643
  · exact envelope_sound644
  · exact envelope_sound645
  · exact envelope_sound646
  · exact envelope_sound647
  · exact envelope_sound648
  · exact envelope_sound649
  · exact envelope_sound650
  · exact envelope_sound651
  · exact envelope_sound652
  · exact envelope_sound653
  · exact envelope_sound654
  · exact envelope_sound655
  · exact envelope_sound656
  · exact envelope_sound657
  · exact envelope_sound658
  · exact envelope_sound659

end Cycle12.MajorityCertificates.Inputs032
