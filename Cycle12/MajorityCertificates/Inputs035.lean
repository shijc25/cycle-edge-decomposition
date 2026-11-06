import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch035

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs035

def inputs700 : RatMajorityInputs := ⟨(1538830656983076387465164019/25000000000000000000000),(53595288802689/12500000000000),(1000048740153977629/1000000000000000000),(49728102824385037/250000000000000000),(53595288802689/25000000000000),(117207249012723551/1000000000000000000),26⟩
theorem inputs_valid700 : inputs700.Valid := by decide +kernel
def envelope700 : RatMajorityEnvelope := ⟨350,0,inputs700,(116614913/98727500),(706192089653867151/1000000000000000000)⟩
theorem envelope_sound700 : envelope700.Sound := by
  apply rat_majority_inputs_envelopes inputs700 inputs_valid700
  · norm_num [envelope700]
  · intro rho hr0 hr1
    have hh := Batch035.bound1400 rho hr0 hr1
    norm_num [Batch035.certificate1400,envelope700,inputs700,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch035.bound1401 rho hr0 hr1
    norm_num [Batch035.certificate1401,envelope700,inputs700,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs701 : RatMajorityInputs := ⟨(1538830656983076387465164019/25000000000000000000000),(211190707057479/50000000000000),(1000048740153977629/1000000000000000000),(5177697544855913/25000000000000000),(211190707057479/100000000000000),(15125872175156209/125000000000000000),25⟩
theorem inputs_valid701 : inputs701.Valid := by decide +kernel
def envelope701 : RatMajorityEnvelope := ⟨350,1,inputs701,1,(549567899888167037/1000000000000000000)⟩
theorem envelope_sound701 : envelope701.Sound := by
  apply rat_majority_inputs_envelopes inputs701 inputs_valid701
  · norm_num [envelope701]
  · intro rho hr0 hr1
    have hh := Batch035.bound1402 rho hr0 hr1
    norm_num [Batch035.certificate1402,envelope701,inputs701,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch035.bound1403 rho hr0 hr1
    norm_num [Batch035.certificate1403,envelope701,inputs701,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs702 : RatMajorityInputs := ⟨(2945220575196385876596165757/50000000000000000000000),(8584439421397/2000000000000),(1000050931989036567/1000000000000000000),(99166346589744923/500000000000000000),(8584439421397/4000000000000),(58469090265644501/500000000000000000),25⟩
theorem inputs_valid702 : inputs702.Valid := by decide +kernel
def envelope702 : RatMajorityEnvelope := ⟨351,0,inputs702,(1400676597/1184330000),(44217280540842007/62500000000000000)⟩
theorem envelope_sound702 : envelope702.Sound := by
  apply rat_majority_inputs_envelopes inputs702 inputs_valid702
  · norm_num [envelope702]
  · intro rho hr0 hr1
    have hh := Batch035.bound1404 rho hr0 hr1
    norm_num [Batch035.certificate1404,envelope702,inputs702,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch035.bound1405 rho hr0 hr1
    norm_num [Batch035.certificate1405,envelope702,inputs702,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs703 : RatMajorityInputs := ⟨(2945220575196385876596165757/50000000000000000000000),(10567014236779/2500000000000),(1000050931989036567/1000000000000000000),(206717461015223321/1000000000000000000),(10567014236779/5000000000000),(120826113274015033/1000000000000000000),25⟩
theorem inputs_valid703 : inputs703.Valid := by decide +kernel
def envelope703 : RatMajorityEnvelope := ⟨351,1,inputs703,1,(549517165000835517/1000000000000000000)⟩
theorem envelope_sound703 : envelope703.Sound := by
  apply rat_majority_inputs_envelopes inputs703 inputs_valid703
  · norm_num [envelope703]
  · intro rho hr0 hr1
    have hh := Batch035.bound1406 rho hr0 hr1
    norm_num [Batch035.certificate1406,envelope703,inputs703,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch035.bound1407 rho hr0 hr1
    norm_num [Batch035.certificate1407,envelope703,inputs703,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs704 : RatMajorityInputs := ⟨(351270206404267350068619837/6250000000000000000000),(13416841031873/3125000000000),(1000053379928365091/1000000000000000000),(99092717186916717/500000000000000000),(13416841031873/6250000000000),(58434912811386513/500000000000000000),25⟩
theorem inputs_valid704 : inputs704.Valid := by decide +kernel
def envelope704 : RatMajorityEnvelope := ⟨352,0,inputs704,(1400989831/1183760000),(708212041135595529/1000000000000000000)⟩
theorem envelope_sound704 : envelope704.Sound := by
  apply rat_majority_inputs_envelopes inputs704 inputs_valid704
  · norm_num [envelope704]
  · intro rho hr0 hr1
    have hh := Batch035.bound1408 rho hr0 hr1
    norm_num [Batch035.certificate1408,envelope704,inputs704,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch035.bound1409 rho hr0 hr1
    norm_num [Batch035.certificate1409,envelope704,inputs704,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs705 : RatMajorityInputs := ⟨(351270206404267350068619837/6250000000000000000000),(26410207682551/6250000000000),(1000053379928365091/1000000000000000000),(206870411332335471/1000000000000000000),(26410207682551/12500000000000),(12089696626502207/100000000000000000),25⟩
theorem inputs_valid705 : inputs705.Valid := by decide +kernel
def envelope705 : RatMajorityEnvelope := ⟨352,1,inputs705,1,(549538402784489019/1000000000000000000)⟩
theorem envelope_sound705 : envelope705.Sound := by
  apply rat_majority_inputs_envelopes inputs705 inputs_valid705
  · norm_num [envelope705]
  · intro rho hr0 hr1
    have hh := Batch035.bound1410 rho hr0 hr1
    norm_num [Batch035.certificate1410,envelope705,inputs705,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch035.bound1411 rho hr0 hr1
    norm_num [Batch035.certificate1411,envelope705,inputs705,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs706 : RatMajorityInputs := ⟨(5113567989850641552236332007/100000000000000000000000),(428789472414737/100000000000000),(250014667532055947/250000000000000000),(39775623077647967/200000000000000000),(428789472414737/200000000000000),(58595666090531089/500000000000000000),25⟩
theorem inputs_valid706 : inputs706.Valid := by decide +kernel
def envelope706 : RatMajorityEnvelope := ⟨353,0,inputs706,(2803302577/2364910000),(354980076301320479/500000000000000000)⟩
theorem envelope_sound706 : envelope706.Sound := by
  apply rat_majority_inputs_envelopes inputs706 inputs_valid706
  · norm_num [envelope706]
  · intro rho hr0 hr1
    have hh := Batch035.bound1412 rho hr0 hr1
    norm_num [Batch035.certificate1412,envelope706,inputs706,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch035.bound1413 rho hr0 hr1
    norm_num [Batch035.certificate1413,envelope706,inputs706,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs707 : RatMajorityInputs := ⟨(5113567989850641552236332007/100000000000000000000000),(42253856193149/10000000000000),(250014667532055947/250000000000000000),(41380544917656653/200000000000000000),(42253856193149/20000000000000),(60455967417025283/500000000000000000),25⟩
theorem inputs_valid707 : inputs707.Valid := by decide +kernel
def envelope707 : RatMajorityEnvelope := ⟨353,1,inputs707,1,(137386216792274459/250000000000000000)⟩
theorem envelope_sound707 : envelope707.Sound := by
  apply rat_majority_inputs_envelopes inputs707 inputs_valid707
  · norm_num [envelope707]
  · intro rho hr0 hr1
    have hh := Batch035.bound1414 rho hr0 hr1
    norm_num [Batch035.certificate1414,envelope707,inputs707,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch035.bound1415 rho hr0 hr1
    norm_num [Batch035.certificate1415,envelope707,inputs707,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs708 : RatMajorityInputs := ⟨(4694347251518821769157831903/100000000000000000000000),(429011383942071/100000000000000),(200012781965038269/200000000000000000),(99299053207294977/500000000000000000),(429011383942071/200000000000000),(117061373755004039/1000000000000000000),25⟩
theorem inputs_valid708 : inputs708.Valid := by decide +kernel
def envelope708 : RatMajorityEnvelope := ⟨354,0,inputs708,(2804659981/2362710000),(88930419705759817/125000000000000000)⟩
theorem envelope_sound708 : envelope708.Sound := by
  apply rat_majority_inputs_envelopes inputs708 inputs_valid708
  · norm_num [envelope708]
  · intro rho hr0 hr1
    have hh := Batch035.bound1416 rho hr0 hr1
    norm_num [Batch035.certificate1416,envelope708,inputs708,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch035.bound1417 rho hr0 hr1
    norm_num [Batch035.certificate1417,envelope708,inputs708,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs709 : RatMajorityInputs := ⟨(4694347251518821769157831903/100000000000000000000000),(422284833629631/100000000000000),(200012781965038269/200000000000000000),(51808521153476331/250000000000000000),(422284833629631/200000000000000),(4842617043025761/40000000000000000),25⟩
theorem inputs_valid709 : inputs709.Valid := by decide +kernel
def envelope709 : RatMajorityEnvelope := ⟨354,1,inputs709,1,(34349430005092089/62500000000000000)⟩
theorem envelope_sound709 : envelope709.Sound := by
  apply rat_majority_inputs_envelopes inputs709 inputs_valid709
  · norm_num [envelope709]
  · intro rho hr0 hr1
    have hh := Batch035.bound1418 rho hr0 hr1
    norm_num [Batch035.certificate1418,envelope709,inputs709,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch035.bound1419 rho hr0 hr1
    norm_num [Batch035.certificate1419,envelope709,inputs709,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs710 : RatMajorityInputs := ⟨(904990947991640968608337011/20000000000000000000000),(429492287964093/100000000000000),(62504143901537999/62500000000000000),(24749054602287243/125000000000000000),(429492287964093/200000000000000),(58390117732242411/500000000000000000),25⟩
theorem inputs_valid710 : inputs710.Valid := by decide +kernel
def envelope710 : RatMajorityEnvelope := ⟨355,0,inputs710,(93578567/78733000),(356368283909780103/500000000000000000)⟩
theorem envelope_sound710 : envelope710.Sound := by
  apply rat_majority_inputs_envelopes inputs710 inputs_valid710
  · norm_num [envelope710]
  · intro rho hr0 hr1
    have hh := Batch035.bound1420 rho hr0 hr1
    norm_num [Batch035.certificate1420,envelope710,inputs710,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch035.bound1421 rho hr0 hr1
    norm_num [Batch035.certificate1421,envelope710,inputs710,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs711 : RatMajorityInputs := ⟨(904990947991640968608337011/20000000000000000000000),(84520595355819/20000000000000),(62504143901537999/62500000000000000),(41363734312187773/200000000000000000),(84520595355819/40000000000000),(24174599697060953/200000000000000000),26⟩
theorem inputs_valid711 : inputs711.Valid := by decide +kernel
def envelope711 : RatMajorityEnvelope := ⟨355,1,inputs711,1,(34346057040685269/62500000000000000)⟩
theorem envelope_sound711 : envelope711.Sound := by
  apply rat_majority_inputs_envelopes inputs711 inputs_valid711
  · norm_num [envelope711]
  · intro rho hr0 hr1
    have hh := Batch035.bound1422 rho hr0 hr1
    norm_num [Batch035.certificate1422,envelope711,inputs711,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch035.bound1423 rho hr0 hr1
    norm_num [Batch035.certificate1423,envelope711,inputs711,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs712 : RatMajorityInputs := ⟨(271683561647443947090114893/6250000000000000000000),(53701896588873/12500000000000),(500034508908805021/500000000000000000),(197837920329561153/1000000000000000000),(53701896588873/25000000000000),(116708504954820631/1000000000000000000),25⟩
theorem inputs_valid712 : inputs712.Valid := by decide +kernel
def envelope712 : RatMajorityEnvelope := ⟨356,0,inputs712,(2808068343/2360920000),(356739194600082707/500000000000000000)⟩
theorem envelope_sound712 : envelope712.Sound := by
  apply rat_majority_inputs_envelopes inputs712 inputs_valid712
  · norm_num [envelope712]
  · intro rho hr0 hr1
    have hh := Batch035.bound1424 rho hr0 hr1
    norm_num [Batch035.certificate1424,envelope712,inputs712,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch035.bound1425 rho hr0 hr1
    norm_num [Batch035.certificate1425,envelope712,inputs712,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs713 : RatMajorityInputs := ⟨(271683561647443947090114893/6250000000000000000000),(105722692477779/25000000000000),(500034508908805021/500000000000000000),(206443487033479963/1000000000000000000),(105722692477779/50000000000000),(60349595736201367/500000000000000000),25⟩
theorem inputs_valid713 : inputs713.Valid := by decide +kernel
def envelope713 : RatMajorityEnvelope := ⟨356,1,inputs713,1,(549488452952751323/1000000000000000000)⟩
theorem envelope_sound713 : envelope713.Sound := by
  apply rat_majority_inputs_envelopes inputs713 inputs_valid713
  · norm_num [envelope713]
  · intro rho hr0 hr1
    have hh := Batch035.bound1426 rho hr0 hr1
    norm_num [Batch035.certificate1426,envelope713,inputs713,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch035.bound1427 rho hr0 hr1
    norm_num [Batch035.certificate1427,envelope713,inputs713,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs714 : RatMajorityInputs := ⟨(1044990158623029078574969197/25000000000000000000000),(53717301205389/12500000000000),(200014355003487453/200000000000000000),(49420765721485931/250000000000000000),(53717301205389/25000000000000),(58318306557950053/500000000000000000),25⟩
theorem inputs_valid714 : inputs714.Valid := by decide +kernel
def envelope714 : RatMajorityEnvelope := ⟨357,0,inputs714,(561758423/471972000),(714221334600863469/1000000000000000000)⟩
theorem envelope_sound714 : envelope714.Sound := by
  apply rat_majority_inputs_envelopes inputs714 inputs_valid714
  · norm_num [envelope714]
  · intro rho hr0 hr1
    have hh := Batch035.bound1428 rho hr0 hr1
    norm_num [Batch035.certificate1428,envelope714,inputs714,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch035.bound1429 rho hr0 hr1
    norm_num [Batch035.certificate1429,envelope714,inputs714,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs715 : RatMajorityInputs := ⟨(1044990158623029078574969197/25000000000000000000000),(21138816330027/5000000000000),(200014355003487453/200000000000000000),(206592614118278133/1000000000000000000),(21138816330027/10000000000000),(24153655462365569/200000000000000000),25⟩
theorem inputs_valid715 : inputs715.Valid := by decide +kernel
def envelope715 : RatMajorityEnvelope := ⟨357,1,inputs715,1,(54950929808688849/100000000000000000)⟩
theorem envelope_sound715 : envelope715.Sound := by
  apply rat_majority_inputs_envelopes inputs715 inputs_valid715
  · norm_num [envelope715]
  · intro rho hr0 hr1
    have hh := Batch035.bound1430 rho hr0 hr1
    norm_num [Batch035.certificate1430,envelope715,inputs715,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch035.bound1431 rho hr0 hr1
    norm_num [Batch035.certificate1431,envelope715,inputs715,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs716 : RatMajorityInputs := ⟨(251446394843224820063477787/6250000000000000000000),(214932114105039/50000000000000),(40002982916104729/40000000000000000),(197525066620987261/1000000000000000000),(214932114105039/100000000000000),(29140815233348853/250000000000000000),26⟩
theorem inputs_valid716 : inputs716.Valid := by decide +kernel
def envelope716 : RatMajorityEnvelope := ⟨358,0,inputs716,(87798034/73713125),(714963917830904553/1000000000000000000)⟩
theorem envelope_sound716 : envelope716.Sound := by
  apply rat_majority_inputs_envelopes inputs716 inputs_valid716
  · norm_num [envelope716]
  · intro rho hr0 hr1
    have hh := Batch035.bound1432 rho hr0 hr1
    norm_num [Batch035.certificate1432,envelope716,inputs716,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch035.bound1433 rho hr0 hr1
    norm_num [Batch035.certificate1433,envelope716,inputs716,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs717 : RatMajorityInputs := ⟨(251446394843224820063477787/6250000000000000000000),(105758495165567/25000000000000),(40002982916104729/40000000000000000),(206257000769101897/1000000000000000000),(105758495165567/50000000000000),(120612795298875507/1000000000000000000),26⟩
theorem inputs_valid717 : inputs717.Valid := by decide +kernel
def envelope717 : RatMajorityEnvelope := ⟨358,1,inputs717,1,(549466127395823857/1000000000000000000)⟩
theorem envelope_sound717 : envelope717.Sound := by
  apply rat_majority_inputs_envelopes inputs717 inputs_valid717
  · norm_num [envelope717]
  · intro rho hr0 hr1
    have hh := Batch035.bound1434 rho hr0 hr1
    norm_num [Batch035.certificate1434,envelope717,inputs717,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch035.bound1435 rho hr0 hr1
    norm_num [Batch035.certificate1435,envelope717,inputs717,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs718 : RatMajorityInputs := ⟨(3719936063267706176322150221/100000000000000000000000),(107322464320483/25000000000000),(250020162901559941/250000000000000000),(198247196468338333/1000000000000000000),(107322464320483/50000000000000),(116898494816332033/1000000000000000000),25⟩
theorem inputs_valid718 : inputs718.Valid := by decide +kernel
def envelope718 : RatMajorityEnvelope := ⟨359,0,inputs718,(56221647/47127400),(358372084070335879/500000000000000000)⟩
theorem envelope_sound718 : envelope718.Sound := by
  apply rat_majority_inputs_envelopes inputs718 inputs_valid718
  · norm_num [envelope718]
  · intro rho hr0 hr1
    have hh := Batch035.bound1436 rho hr0 hr1
    norm_num [Batch035.certificate1436,envelope718,inputs718,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch035.bound1437 rho hr0 hr1
    norm_num [Batch035.certificate1437,envelope718,inputs718,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs719 : RatMajorityInputs := ⟨(3719936063267706176322150221/100000000000000000000000),(422603441799077/100000000000000),(250020162901559941/250000000000000000),(206818064873808089/1000000000000000000),(422603441799077/200000000000000),(120872717443833591/1000000000000000000),25⟩
theorem inputs_valid719 : inputs719.Valid := by decide +kernel
def envelope719 : RatMajorityEnvelope := ⟨359,1,inputs719,1,(549542775352657273/1000000000000000000)⟩
theorem envelope_sound719 : envelope719.Sound := by
  apply rat_majority_inputs_envelopes inputs719 inputs_valid719
  · norm_num [envelope719]
  · intro rho hr0 hr1
    have hh := Batch035.bound1438 rho hr0 hr1
    norm_num [Batch035.certificate1438,envelope719,inputs719,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch035.bound1439 rho hr0 hr1
    norm_num [Batch035.certificate1439,envelope719,inputs719,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope700,envelope701,envelope702,envelope703,envelope704,envelope705,envelope706,envelope707,envelope708,envelope709,envelope710,envelope711,envelope712,envelope713,envelope714,envelope715,envelope716,envelope717,envelope718,envelope719]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound700
  · exact envelope_sound701
  · exact envelope_sound702
  · exact envelope_sound703
  · exact envelope_sound704
  · exact envelope_sound705
  · exact envelope_sound706
  · exact envelope_sound707
  · exact envelope_sound708
  · exact envelope_sound709
  · exact envelope_sound710
  · exact envelope_sound711
  · exact envelope_sound712
  · exact envelope_sound713
  · exact envelope_sound714
  · exact envelope_sound715
  · exact envelope_sound716
  · exact envelope_sound717
  · exact envelope_sound718
  · exact envelope_sound719

end Cycle12.MajorityCertificates.Inputs035
