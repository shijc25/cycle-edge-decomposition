import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch039

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs039

def inputs780 : RatMajorityInputs := ⟨(8086743269383303206935803/781250000000000000000),(14384711884741/3125000000000),(1000289891537334381/1000000000000000000),(162308482554846989/1000000000000000000),(14384711884741/6250000000000),(50051586164808751/500000000000000000),25⟩
theorem inputs_valid780 : inputs780.Valid := by decide +kernel
def envelope780 : RatMajorityEnvelope := ⟨390,0,inputs780,(1393586781/1156640000),(72432055364461153/100000000000000000)⟩
theorem envelope_sound780 : envelope780.Sound := by
  apply rat_majority_inputs_envelopes inputs780 inputs_valid780
  · norm_num [envelope780]
  · intro rho hr0 hr1
    have hh := Batch039.bound1560 rho hr0 hr1
    norm_num [Batch039.certificate1560,envelope780,inputs780,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch039.bound1561 rho hr0 hr1
    norm_num [Batch039.certificate1561,envelope780,inputs780,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs781 : RatMajorityInputs := ⟨(8086743269383303206935803/781250000000000000000),(13590958634033/3125000000000),(1000289891537334381/1000000000000000000),(19127513142806679/100000000000000000),(13590958634033/6250000000000),(11365890451245077/100000000000000000),25⟩
theorem inputs_valid781 : inputs781.Valid := by decide +kernel
def envelope781 : RatMajorityEnvelope := ⟨390,1,inputs781,1,(547616940719799529/1000000000000000000)⟩
theorem envelope_sound781 : envelope781.Sound := by
  apply rat_majority_inputs_envelopes inputs781 inputs_valid781
  · norm_num [envelope781]
  · intro rho hr0 hr1
    have hh := Batch039.bound1562 rho hr0 hr1
    norm_num [Batch039.certificate1562,envelope781,inputs781,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch039.bound1563 rho hr0 hr1
    norm_num [Batch039.certificate1563,envelope781,inputs781,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs782 : RatMajorityInputs := ⟨(511002187345508614161679271/50000000000000000000000),(461456391014749/100000000000000),(1000293607850076141/1000000000000000000),(503425675156583/3125000000000000),(461456391014749/200000000000000),(49765707546402957/500000000000000000),26⟩
theorem inputs_valid782 : inputs782.Valid := by decide +kernel
def envelope782 : RatMajorityEnvelope := ⟨391,0,inputs782,(1392215693/1156405000),(361681552317927791/500000000000000000)⟩
theorem envelope_sound782 : envelope782.Sound := by
  apply rat_majority_inputs_envelopes inputs782 inputs_valid782
  · norm_num [envelope782]
  · intro rho hr0 hr1
    have hh := Batch039.bound1564 rho hr0 hr1
    norm_num [Batch039.certificate1564,envelope782,inputs782,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch039.bound1565 rho hr0 hr1
    norm_num [Batch039.certificate1565,envelope782,inputs782,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs783 : RatMajorityInputs := ⟨(511002187345508614161679271/50000000000000000000000),(217656989572217/50000000000000),(1000293607850076141/1000000000000000000),(95391469287800709/500000000000000000),(217656989572217/100000000000000),(113429940640850603/1000000000000000000),25⟩
theorem inputs_valid783 : inputs783.Valid := by decide +kernel
def envelope783 : RatMajorityEnvelope := ⟨391,1,inputs783,1,(547556091256836551/1000000000000000000)⟩
theorem envelope_sound783 : envelope783.Sound := by
  apply rat_majority_inputs_envelopes inputs783 inputs_valid783
  · norm_num [envelope783]
  · intro rho hr0 hr1
    have hh := Batch039.bound1566 rho hr0 hr1
    norm_num [Batch039.certificate1566,envelope783,inputs783,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch039.bound1567 rho hr0 hr1
    norm_num [Batch039.certificate1567,envelope783,inputs783,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs784 : RatMajorityInputs := ⟨(495448750105223977245852779/50000000000000000000000),(231327101709269/50000000000000),(250075706785576827/250000000000000000),(159837097418851773/1000000000000000000),(231327101709269/100000000000000),(98937096756129647/1000000000000000000),25⟩
theorem inputs_valid784 : inputs784.Valid := by decide +kernel
def envelope784 : RatMajorityEnvelope := ⟨392,0,inputs784,(555769689/462268000),(721760171526555343/1000000000000000000)⟩
theorem envelope_sound784 : envelope784.Sound := by
  apply rat_majority_inputs_envelopes inputs784 inputs_valid784
  · norm_num [envelope784]
  · intro rho hr0 hr1
    have hh := Batch039.bound1568 rho hr0 hr1
    norm_num [Batch039.certificate1568,envelope784,inputs784,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch039.bound1569 rho hr0 hr1
    norm_num [Batch039.certificate1569,envelope784,inputs784,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs785 : RatMajorityInputs := ⟨(495448750105223977245852779/50000000000000000000000),(54454860333739/12500000000000),(250075706785576827/250000000000000000),(95193602151424949/500000000000000000),(54454860333739/25000000000000),(4529832851834331/40000000000000000),25⟩
theorem inputs_valid785 : inputs785.Valid := by decide +kernel
def envelope785 : RatMajorityEnvelope := ⟨392,1,inputs785,1,(17109683290821257/31250000000000000)⟩
theorem envelope_sound785 : envelope785.Sound := by
  apply rat_majority_inputs_envelopes inputs785 inputs_valid785
  · norm_num [envelope785]
  · intro rho hr0 hr1
    have hh := Batch039.bound1570 rho hr0 hr1
    norm_num [Batch039.certificate1570,envelope785,inputs785,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch039.bound1571 rho hr0 hr1
    norm_num [Batch039.certificate1571,envelope785,inputs785,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs786 : RatMajorityInputs := ⟨(96724128671767668786186813/10000000000000000000000),(29088869420943/6250000000000),(15629847426498737/15625000000000000),(156960302584814787/1000000000000000000),(29088869420943/12500000000000),(48788691026697653/500000000000000000),26⟩
theorem inputs_valid786 : inputs786.Valid := by decide +kernel
def envelope786 : RatMajorityEnvelope := ⟨393,0,inputs786,(692862157/577615000),(719023152695157489/1000000000000000000)⟩
theorem envelope_sound786 : envelope786.Sound := by
  apply rat_majority_inputs_envelopes inputs786 inputs_valid786
  · norm_num [envelope786]
  · intro rho hr0 hr1
    have hh := Batch039.bound1572 rho hr0 hr1
    norm_num [Batch039.certificate1572,envelope786,inputs786,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch039.bound1573 rho hr0 hr1
    norm_num [Batch039.certificate1573,envelope786,inputs786,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs787 : RatMajorityInputs := ⟨(96724128671767668786186813/10000000000000000000000),(27290215819809/6250000000000),(15629847426498737/15625000000000000),(94584012074778623/500000000000000000),(27290215819809/12500000000000),(56339215211195989/500000000000000000),25⟩
theorem inputs_valid787 : inputs787.Valid := by decide +kernel
def envelope787 : RatMajorityEnvelope := ⟨393,1,inputs787,1,(547358889319958347/1000000000000000000)⟩
theorem envelope_sound787 : envelope787.Sound := by
  apply rat_majority_inputs_envelopes inputs787 inputs_valid787
  · norm_num [envelope787]
  · intro rho hr0 hr1
    have hh := Batch039.bound1574 rho hr0 hr1
    norm_num [Batch039.certificate1574,envelope787,inputs787,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch039.bound1575 rho hr0 hr1
    norm_num [Batch039.certificate1575,envelope787,inputs787,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs788 : RatMajorityInputs := ⟨(961771567610971590602650917/100000000000000000000000),(234004404500367/50000000000000),(20006240001444841/20000000000000000),(154312184600461709/1000000000000000000),(234004404500367/100000000000000),(4816169778637413/50000000000000000),26⟩
theorem inputs_valid788 : inputs788.Valid := by decide +kernel
def envelope788 : RatMajorityEnvelope := ⟨394,0,inputs788,(2766988429/2310590000),(179245771373603359/250000000000000000)⟩
theorem envelope_sound788 : envelope788.Sound := by
  apply rat_majority_inputs_envelopes inputs788 inputs_valid788
  · norm_num [envelope788]
  · intro rho hr0 hr1
    have hh := Batch039.bound1576 rho hr0 hr1
    norm_num [Batch039.certificate1576,envelope788,inputs788,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch039.bound1577 rho hr0 hr1
    norm_num [Batch039.certificate1577,envelope788,inputs788,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs789 : RatMajorityInputs := ⟨(961771567610971590602650917/100000000000000000000000),(17510386018679/4000000000000),(20006240001444841/20000000000000000),(37564226540887831/200000000000000000),(17510386018679/8000000000000),(112051325155992431/1000000000000000000),26⟩
theorem inputs_valid789 : inputs789.Valid := by decide +kernel
def envelope789 : RatMajorityEnvelope := ⟨394,1,inputs789,1,(273594970261446157/500000000000000000)⟩
theorem envelope_sound789 : envelope789.Sound := by
  apply rat_majority_inputs_envelopes inputs789 inputs_valid789
  · norm_num [envelope789]
  · intro rho hr0 hr1
    have hh := Batch039.bound1578 rho hr0 hr1
    norm_num [Batch039.certificate1578,envelope789,inputs789,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch039.bound1579 rho hr0 hr1
    norm_num [Batch039.certificate1579,envelope789,inputs789,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs790 : RatMajorityInputs := ⟨(1485471292108358877260913/156250000000000000000),(117407749763499/25000000000000),(1000315633883359749/1000000000000000000),(38167874169849531/250000000000000000),(117407749763499/50000000000000),(47772640595573581/500000000000000000),26⟩
theorem inputs_valid790 : inputs790.Valid := by decide +kernel
def envelope790 : RatMajorityEnvelope := ⟨395,0,inputs790,(172647529/144386250),(7152184657567021/10000000000000000)⟩
theorem envelope_sound790 : envelope790.Sound := by
  apply rat_majority_inputs_envelopes inputs790 inputs_valid790
  · norm_num [envelope790]
  · intro rho hr0 hr1
    have hh := Batch039.bound1580 rho hr0 hr1
    norm_num [Batch039.certificate1580,envelope790,inputs790,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch039.bound1581 rho hr0 hr1
    norm_num [Batch039.certificate1581,envelope790,inputs790,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs791 : RatMajorityInputs := ⟨(1485471292108358877260913/156250000000000000000),(219173188389081/50000000000000),(1000315633883359749/1000000000000000000),(18711640885950249/100000000000000000),(219173188389081/100000000000000),(111723089549202321/1000000000000000000),25⟩
theorem inputs_valid791 : inputs791.Valid := by decide +kernel
def envelope791 : RatMajorityEnvelope := ⟨395,1,inputs791,1,(10942058602990651/20000000000000000)⟩
theorem envelope_sound791 : envelope791.Sound := by
  apply rat_majority_inputs_envelopes inputs791 inputs_valid791
  · norm_num [envelope791]
  · intro rho hr0 hr1
    have hh := Batch039.bound1582 rho hr0 hr1
    norm_num [Batch039.certificate1582,envelope791,inputs791,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch039.bound1583 rho hr0 hr1
    norm_num [Batch039.certificate1583,envelope791,inputs791,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs792 : RatMajorityInputs := ⟨(939928462367019570345640939/100000000000000000000000),(470773690210583/100000000000000),(1000319252477980607/1000000000000000000),(151524911876004203/1000000000000000000),(470773690210583/200000000000000),(95000943955914437/1000000000000000000),26⟩
theorem inputs_valid792 : inputs792.Valid := by decide +kernel
def envelope792 : RatMajorityEnvelope := ⟨396,0,inputs792,(2759746911/2309770000),(357144143772767507/500000000000000000)⟩
theorem envelope_sound792 : envelope792.Sound := by
  apply rat_majority_inputs_envelopes inputs792 inputs_valid792
  · norm_num [envelope792]
  · intro rho hr0 hr1
    have hh := Batch039.bound1584 rho hr0 hr1
    norm_num [Batch039.certificate1584,envelope792,inputs792,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch039.bound1585 rho hr0 hr1
    norm_num [Batch039.certificate1585,envelope792,inputs792,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs793 : RatMajorityInputs := ⟨(939928462367019570345640939/100000000000000000000000),(439072265111839/100000000000000),(1000319252477980607/1000000000000000000),(186247641781453117/1000000000000000000),(439072265111839/200000000000000),(55659166039401657/500000000000000000),26⟩
theorem inputs_valid793 : inputs793.Valid := by decide +kernel
def envelope793 : RatMajorityEnvelope := ⟨396,1,inputs793,1,(546995522680627001/1000000000000000000)⟩
theorem envelope_sound793 : envelope793.Sound := by
  apply rat_majority_inputs_envelopes inputs793 inputs_valid793
  · norm_num [envelope793]
  · intro rho hr0 hr1
    have hh := Batch039.bound1586 rho hr0 hr1
    norm_num [Batch039.certificate1586,envelope793,inputs793,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch039.bound1587 rho hr0 hr1
    norm_num [Batch039.certificate1587,envelope793,inputs793,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs794 : RatMajorityInputs := ⟨(116180343351063510535760029/12500000000000000000000),(29515617155119/6250000000000),(50016142755018703/50000000000000000),(150054811537466601/1000000000000000000),(29515617155119/12500000000000),(9430233083560669/100000000000000000),26⟩
theorem inputs_valid794 : inputs794.Valid := by decide +kernel
def envelope794 : RatMajorityEnvelope := ⟨397,0,inputs794,(2755197411/2309360000),(142513769619841583/200000000000000000)⟩
theorem envelope_sound794 : envelope794.Sound := by
  apply rat_majority_inputs_envelopes inputs794 inputs_valid794
  · norm_num [envelope794]
  · intro rho hr0 hr1
    have hh := Batch039.bound1588 rho hr0 hr1
    norm_num [Batch039.certificate1588,envelope794,inputs794,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch039.bound1589 rho hr0 hr1
    norm_num [Batch039.certificate1589,envelope794,inputs794,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs795 : RatMajorityInputs := ⟨(116180343351063510535760029/12500000000000000000000),(13738974731037/3125000000000),(50016142755018703/50000000000000000),(185561983509087269/1000000000000000000),(13738974731037/6250000000000),(11099879240469991/100000000000000000),25⟩
theorem inputs_valid795 : inputs795.Valid := by decide +kernel
def envelope795 : RatMajorityEnvelope := ⟨397,1,inputs795,1,(273455622563319901/500000000000000000)⟩
theorem envelope_sound795 : envelope795.Sound := by
  apply rat_majority_inputs_envelopes inputs795 inputs_valid795
  · norm_num [envelope795]
  · intro rho hr0 hr1
    have hh := Batch039.bound1590 rho hr0 hr1
    norm_num [Batch039.certificate1590,envelope795,inputs795,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch039.bound1591 rho hr0 hr1
    norm_num [Batch039.certificate1591,envelope795,inputs795,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs796 : RatMajorityInputs := ⟨(229810876182170765513089041/25000000000000000000000),(473870964374041/100000000000000),(500163219084923781/500000000000000000),(148454751829947767/1000000000000000000),(473870964374041/200000000000000),(23385264364574171/250000000000000000),26⟩
theorem inputs_valid796 : inputs796.Valid := by decide +kernel
def envelope796 : RatMajorityEnvelope := ⟨398,0,inputs796,(687660353/577242500),(5553332548850539/7812500000000000)⟩
theorem envelope_sound796 : envelope796.Sound := by
  apply rat_majority_inputs_envelopes inputs796 inputs_valid796
  · norm_num [envelope796]
  · intro rho hr0 hr1
    have hh := Batch039.bound1592 rho hr0 hr1
    norm_num [Batch039.certificate1592,envelope796,inputs796,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch039.bound1593 rho hr0 hr1
    norm_num [Batch039.certificate1593,envelope796,inputs796,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs797 : RatMajorityInputs := ⟨(229810876182170765513089041/25000000000000000000000),(27513829445243/6250000000000),(500163219084923781/500000000000000000),(36975895099249127/200000000000000000),(27513829445243/12500000000000),(110680638453220249/1000000000000000000),25⟩
theorem inputs_valid797 : inputs797.Valid := by decide +kernel
def envelope797 : RatMajorityEnvelope := ⟨398,1,inputs797,1,(546827505659451001/1000000000000000000)⟩
theorem envelope_sound797 : envelope797.Sound := by
  apply rat_majority_inputs_envelopes inputs797 inputs_valid797
  · norm_num [envelope797]
  · intro rho hr0 hr1
    have hh := Batch039.bound1594 rho hr0 hr1
    norm_num [Batch039.certificate1594,envelope797,inputs797,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch039.bound1595 rho hr0 hr1
    norm_num [Batch039.certificate1595,envelope797,inputs797,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs798 : RatMajorityInputs := ⟨(454658987716515165398260473/50000000000000000000000),(475337575877967/100000000000000),(200066000454631823/200000000000000000),(2940400502920477/20000000000000000),(475337575877967/200000000000000),(92857624393056587/1000000000000000000),27⟩
theorem inputs_valid798 : inputs798.Valid := by decide +kernel
def envelope798 : RatMajorityEnvelope := ⟨399,0,inputs798,(2746161679/2308590000),(177280878945322679/250000000000000000)⟩
theorem envelope_sound798 : envelope798.Sound := by
  apply rat_majority_inputs_envelopes inputs798 inputs_valid798
  · norm_num [envelope798]
  · intro rho hr0 hr1
    have hh := Batch039.bound1596 rho hr0 hr1
    norm_num [Batch039.certificate1596,envelope798,inputs798,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch039.bound1597 rho hr0 hr1
    norm_num [Batch039.certificate1597,envelope798,inputs798,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs799 : RatMajorityInputs := ⟨(454658987716515165398260473/50000000000000000000000),(220398485288211/50000000000000),(200066000454631823/200000000000000000),(1151232409964423/6250000000000000),(220398485288211/100000000000000),(3448828207331551/31250000000000000),25⟩
theorem inputs_valid799 : inputs799.Valid := by decide +kernel
def envelope799 : RatMajorityEnvelope := ⟨399,1,inputs799,1,(546743936747947763/1000000000000000000)⟩
theorem envelope_sound799 : envelope799.Sound := by
  apply rat_majority_inputs_envelopes inputs799 inputs_valid799
  · norm_num [envelope799]
  · intro rho hr0 hr1
    have hh := Batch039.bound1598 rho hr0 hr1
    norm_num [Batch039.certificate1598,envelope799,inputs799,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch039.bound1599 rho hr0 hr1
    norm_num [Batch039.certificate1599,envelope799,inputs799,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope780,envelope781,envelope782,envelope783,envelope784,envelope785,envelope786,envelope787,envelope788,envelope789,envelope790,envelope791,envelope792,envelope793,envelope794,envelope795,envelope796,envelope797,envelope798,envelope799]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound780
  · exact envelope_sound781
  · exact envelope_sound782
  · exact envelope_sound783
  · exact envelope_sound784
  · exact envelope_sound785
  · exact envelope_sound786
  · exact envelope_sound787
  · exact envelope_sound788
  · exact envelope_sound789
  · exact envelope_sound790
  · exact envelope_sound791
  · exact envelope_sound792
  · exact envelope_sound793
  · exact envelope_sound794
  · exact envelope_sound795
  · exact envelope_sound796
  · exact envelope_sound797
  · exact envelope_sound798
  · exact envelope_sound799

end Cycle12.MajorityCertificates.Inputs039
