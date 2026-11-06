import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch048

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs048

def inputs960 : RatMajorityInputs := ⟨(1672939453204846809210573/20000000000000000000),(10303664629/2500000000),(250008966504081883/250000000000000000),(22084033551283977/100000000000000000),(10303664629/5000000000),(127360589816486877/1000000000000000000),25⟩
theorem inputs_valid960 : inputs960.Valid := by decide +kernel
def envelope960 : RatMajorityEnvelope := ⟨458,1,inputs960,1,(275706373726602279/500000000000000000)⟩
theorem envelope_sound960 : envelope960.Sound := by
  apply rat_majority_inputs_envelopes inputs960 inputs_valid960
  · norm_num [envelope960]
  · intro rho hr0 hr1
    have hh := Batch048.bound1920 rho hr0 hr1
    norm_num [Batch048.certificate1920,envelope960,inputs960,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch048.bound1921 rho hr0 hr1
    norm_num [Batch048.certificate1921,envelope960,inputs960,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs961 : RatMajorityInputs := ⟨(1672939453204846809210573/20000000000000000000),(86089173521/20000000000),(250008966504081883/250000000000000000),(19679605518992233/100000000000000000),(86089173521/40000000000),(116224764456385969/1000000000000000000),25⟩
theorem inputs_valid961 : inputs961.Valid := by decide +kernel
def envelope961 : RatMajorityEnvelope := ⟨458,2,inputs961,1,(68526987098199371/125000000000000000)⟩
theorem envelope_sound961 : envelope961.Sound := by
  apply rat_majority_inputs_envelopes inputs961 inputs_valid961
  · norm_num [envelope961]
  · intro rho hr0 hr1
    have hh := Batch048.bound1922 rho hr0 hr1
    norm_num [Batch048.certificate1922,envelope961,inputs961,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch048.bound1923 rho hr0 hr1
    norm_num [Batch048.certificate1923,envelope961,inputs961,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs962 : RatMajorityInputs := ⟨(1660451740466551077376071/20000000000000000000),(44352639037/10000000000),(1000036135760449599/1000000000000000000),(180991496273674857/1000000000000000000),(44352639037/20000000000),(21773321037149063/200000000000000000),25⟩
theorem inputs_valid962 : inputs962.Valid := by decide +kernel
def envelope962 : RatMajorityEnvelope := ⟨459,0,inputs962,(707594613/587500000),(181355449307797803/250000000000000000)⟩
theorem envelope_sound962 : envelope962.Sound := by
  apply rat_majority_inputs_envelopes inputs962 inputs_valid962
  · norm_num [envelope962]
  · intro rho hr0 hr1
    have hh := Batch048.bound1924 rho hr0 hr1
    norm_num [Batch048.certificate1924,envelope962,inputs962,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch048.bound1925 rho hr0 hr1
    norm_num [Batch048.certificate1925,envelope962,inputs962,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs963 : RatMajorityInputs := ⟨(1660451740466551077376071/20000000000000000000),(658796791/160000000),(1000036135760449599/1000000000000000000),(13836876469276649/62500000000000000),(658796791/320000000),(25522933340303601/200000000000000000),25⟩
theorem inputs_valid963 : inputs963.Valid := by decide +kernel
def envelope963 : RatMajorityEnvelope := ⟨459,1,inputs963,1,(551488303274302853/1000000000000000000)⟩
theorem envelope_sound963 : envelope963.Sound := by
  apply rat_majority_inputs_envelopes inputs963 inputs_valid963
  · norm_num [envelope963]
  · intro rho hr0 hr1
    have hh := Batch048.bound1926 rho hr0 hr1
    norm_num [Batch048.certificate1926,envelope963,inputs963,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch048.bound1927 rho hr0 hr1
    norm_num [Batch048.certificate1927,envelope963,inputs963,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs964 : RatMajorityInputs := ⟨(1660451740466551077376071/20000000000000000000),(86286097317/20000000000),(1000036135760449599/1000000000000000000),(195567123511348469/1000000000000000000),(86286097317/40000000000),(57826992532309033/500000000000000000),25⟩
theorem inputs_valid964 : inputs964.Valid := by decide +kernel
def envelope964 : RatMajorityEnvelope := ⟨459,2,inputs964,1,(274028946112426879/500000000000000000)⟩
theorem envelope_sound964 : envelope964.Sound := by
  apply rat_majority_inputs_envelopes inputs964 inputs_valid964
  · norm_num [envelope964]
  · intro rho hr0 hr1
    have hh := Batch048.bound1928 rho hr0 hr1
    norm_num [Batch048.certificate1928,envelope964,inputs964,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch048.bound1929 rho hr0 hr1
    norm_num [Batch048.certificate1929,envelope964,inputs964,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs965 : RatMajorityInputs := ⟨(822054599576646358707593/10000000000000000000),(88736582189/20000000000),(15625570233784551/15625000000000000),(4520227844916997/25000000000000000),(88736582189/40000000000),(54390719598727943/500000000000000000),26⟩
theorem inputs_valid965 : inputs965.Valid := by decide +kernel
def envelope965 : RatMajorityEnvelope := ⟨460,0,inputs965,(141548083/117500000),(725630351136323813/1000000000000000000)⟩
theorem envelope_sound965 : envelope965.Sound := by
  apply rat_majority_inputs_envelopes inputs965 inputs_valid965
  · norm_num [envelope965]
  · intro rho hr0 hr1
    have hh := Batch048.bound1930 rho hr0 hr1
    norm_num [Batch048.certificate1930,envelope965,inputs965,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch048.bound1931 rho hr0 hr1
    norm_num [Batch048.certificate1931,envelope965,inputs965,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs966 : RatMajorityInputs := ⟨(822054599576646358707593/10000000000000000000),(82370087491/20000000000),(15625570233784551/15625000000000000),(221248638815192423/1000000000000000000),(82370087491/40000000000),(63774658620948101/500000000000000000),25⟩
theorem inputs_valid966 : inputs966.Valid := by decide +kernel
def envelope966 : RatMajorityEnvelope := ⟨460,1,inputs966,1,(34466814575817477/62500000000000000)⟩
theorem envelope_sound966 : envelope966.Sound := by
  apply rat_majority_inputs_envelopes inputs966 inputs_valid966
  · norm_num [envelope966]
  · intro rho hr0 hr1
    have hh := Batch048.bound1932 rho hr0 hr1
    norm_num [Batch048.certificate1932,envelope966,inputs966,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch048.bound1933 rho hr0 hr1
    norm_num [Batch048.certificate1933,envelope966,inputs966,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs967 : RatMajorityInputs := ⟨(822054599576646358707593/10000000000000000000),(17275747089/4000000000),(15625570233784551/15625000000000000),(194991242114981339/1000000000000000000),(17275747089/8000000000),(115386445771637773/1000000000000000000),25⟩
theorem inputs_valid967 : inputs967.Valid := by decide +kernel
def envelope967 : RatMajorityEnvelope := ⟨460,2,inputs967,1,(273992060323651047/500000000000000000)⟩
theorem envelope_sound967 : envelope967.Sound := by
  apply rat_majority_inputs_envelopes inputs967 inputs_valid967
  · norm_num [envelope967]
  · intro rho hr0 hr1
    have hh := Batch048.bound1934 rho hr0 hr1
    norm_num [Batch048.certificate1934,envelope967,inputs967,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch048.bound1935 rho hr0 hr1
    norm_num [Batch048.certificate1935,envelope967,inputs967,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs968 : RatMajorityInputs := ⟨(1628061046829382605907229/20000000000000000000),(44392936367/10000000000),(125004606838914253/125000000000000000),(90261128648879711/500000000000000000),(44392936367/20000000000),(108647474343817637/1000000000000000000),25⟩
theorem inputs_valid968 : inputs968.Valid := by decide +kernel
def envelope968 : RatMajorityEnvelope := ⟨461,0,inputs968,(353938191/293750000),(11340847652839561/15625000000000000)⟩
theorem envelope_sound968 : envelope968.Sound := by
  apply rat_majority_inputs_envelopes inputs968 inputs_valid968
  · norm_num [envelope968]
  · intro rho hr0 hr1
    have hh := Batch048.bound1936 rho hr0 hr1
    norm_num [Batch048.certificate1936,envelope968,inputs968,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch048.bound1937 rho hr0 hr1
    norm_num [Batch048.certificate1937,envelope968,inputs968,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs969 : RatMajorityInputs := ⟨(1628061046829382605907229/20000000000000000000),(82371694233/20000000000),(125004606838914253/125000000000000000),(221237554406734073/1000000000000000000),(82371694233/40000000000),(127544193873668931/1000000000000000000),25⟩
theorem inputs_valid969 : inputs969.Valid := by decide +kernel
def envelope969 : RatMajorityEnvelope := ⟨461,1,inputs969,1,(137866914330646251/250000000000000000)⟩
theorem envelope_sound969 : envelope969.Sound := by
  apply rat_majority_inputs_envelopes inputs969 inputs_valid969
  · norm_num [envelope969]
  · intro rho hr0 hr1
    have hh := Batch048.bound1938 rho hr0 hr1
    norm_num [Batch048.certificate1938,envelope969,inputs969,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch048.bound1939 rho hr0 hr1
    norm_num [Batch048.certificate1939,envelope969,inputs969,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs970 : RatMajorityInputs := ⟨(1628061046829382605907229/20000000000000000000),(2703178821/625000000),(125004606838914253/125000000000000000),(97114454457104459/500000000000000000),(2703178821/1250000000),(115032215300614677/1000000000000000000),26⟩
theorem inputs_valid970 : inputs970.Valid := by decide +kernel
def envelope970 : RatMajorityEnvelope := ⟨461,2,inputs970,1,(547886583911047069/1000000000000000000)⟩
theorem envelope_sound970 : envelope970.Sound := by
  apply rat_majority_inputs_envelopes inputs970 inputs_valid970
  · norm_num [envelope970]
  · intro rho hr0 hr1
    have hh := Batch048.bound1940 rho hr0 hr1
    norm_num [Batch048.certificate1940,envelope970,inputs970,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch048.bound1941 rho hr0 hr1
    norm_num [Batch048.certificate1941,envelope970,inputs970,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs971 : RatMajorityInputs := ⟨(811088285974577738768609/10000000000000000000),(44417346757/10000000000),(1000036988406292589/1000000000000000000),(45059629340338931/250000000000000000),(44417346757/20000000000),(108514948874166813/1000000000000000000),25⟩
theorem inputs_valid971 : inputs971.Valid := by decide +kernel
def envelope971 : RatMajorityEnvelope := ⟨462,0,inputs971,(2832050459/2350000000),(725998772469545357/1000000000000000000)⟩
theorem envelope_sound971 : envelope971.Sound := by
  apply rat_majority_inputs_envelopes inputs971 inputs_valid971
  · norm_num [envelope971]
  · intro rho hr0 hr1
    have hh := Batch048.bound1942 rho hr0 hr1
    norm_num [Batch048.certificate1942,envelope971,inputs971,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch048.bound1943 rho hr0 hr1
    norm_num [Batch048.certificate1943,envelope971,inputs971,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs972 : RatMajorityInputs := ⟨(811088285974577738768609/10000000000000000000),(10296139741/2500000000),(1000036988406292589/1000000000000000000),(221255327747440553/1000000000000000000),(10296139741/5000000000),(127552408956833031/1000000000000000000),25⟩
theorem inputs_valid972 : inputs972.Valid := by decide +kernel
def envelope972 : RatMajorityEnvelope := ⟨462,1,inputs972,1,(275735075923127803/500000000000000000)⟩
theorem envelope_sound972 : envelope972.Sound := by
  apply rat_majority_inputs_envelopes inputs972 inputs_valid972
  · norm_num [envelope972]
  · intro rho hr0 hr1
    have hh := Batch048.bound1944 rho hr0 hr1
    norm_num [Batch048.certificate1944,envelope972,inputs972,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch048.bound1945 rho hr0 hr1
    norm_num [Batch048.certificate1945,envelope972,inputs972,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs973 : RatMajorityInputs := ⟨(811088285974577738768609/10000000000000000000),(86579121543/20000000000),(1000036988406292589/1000000000000000000),(96875220087416901/500000000000000000),(86579121543/40000000000),(114809845270829889/1000000000000000000),25⟩
theorem inputs_valid973 : inputs973.Valid := by decide +kernel
def envelope973 : RatMajorityEnvelope := ⟨462,2,inputs973,1,(136956356296667113/250000000000000000)⟩
theorem envelope_sound973 : envelope973.Sound := by
  apply rat_majority_inputs_envelopes inputs973 inputs_valid973
  · norm_num [envelope973]
  · intro rho hr0 hr1
    have hh := Batch048.bound1946 rho hr0 hr1
    norm_num [Batch048.certificate1946,envelope973,inputs973,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch048.bound1947 rho hr0 hr1
    norm_num [Batch048.certificate1947,envelope973,inputs973,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs974 : RatMajorityInputs := ⟨(807162124973603916282671/10000000000000000000),(4442761151/1000000000),(500018584164401879/500000000000000000),(45029829060088573/250000000000000000),(4442761151/2000000000),(108459269206489889/1000000000000000000),26⟩
theorem inputs_valid974 : inputs974.Valid := by decide +kernel
def envelope974 : RatMajorityEnvelope := ⟨463,0,inputs974,(566466363/470000000),(72609661420493597/100000000000000000)⟩
theorem envelope_sound974 : envelope974.Sound := by
  apply rat_majority_inputs_envelopes inputs974 inputs_valid974
  · norm_num [envelope974]
  · intro rho hr0 hr1
    have hh := Batch048.bound1948 rho hr0 hr1
    norm_num [Batch048.certificate1948,envelope974,inputs974,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch048.bound1949 rho hr0 hr1
    norm_num [Batch048.certificate1949,envelope974,inputs974,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs975 : RatMajorityInputs := ⟨(807162124973603916282671/10000000000000000000),(82362677001/20000000000),(500018584164401879/500000000000000000),(221299767386825137/1000000000000000000),(82362677001/40000000000),(12757294950440987/100000000000000000),25⟩
theorem inputs_valid975 : inputs975.Valid := by decide +kernel
def envelope975 : RatMajorityEnvelope := ⟨463,1,inputs975,1,(275738163444214007/500000000000000000)⟩
theorem envelope_sound975 : envelope975.Sound := by
  apply rat_majority_inputs_envelopes inputs975 inputs_valid975
  · norm_num [envelope975]
  · intro rho hr0 hr1
    have hh := Batch048.bound1950 rho hr0 hr1
    norm_num [Batch048.certificate1950,envelope975,inputs975,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch048.bound1951 rho hr0 hr1
    norm_num [Batch048.certificate1951,envelope975,inputs975,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs976 : RatMajorityInputs := ⟨(807162124973603916282671/10000000000000000000),(43313428147/10000000000),(500018584164401879/500000000000000000),(193455848513532059/1000000000000000000),(43313428147/20000000000),(28668229126481917/250000000000000000),26⟩
theorem inputs_valid976 : inputs976.Valid := by decide +kernel
def envelope976 : RatMajorityEnvelope := ⟨463,2,inputs976,1,(54778784856576261/100000000000000000)⟩
theorem envelope_sound976 : envelope976.Sound := by
  apply rat_majority_inputs_envelopes inputs976 inputs_valid976
  · norm_num [envelope976]
  · intro rho hr0 hr1
    have hh := Batch048.bound1952 rho hr0 hr1
    norm_num [Batch048.certificate1952,envelope976,inputs976,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch048.bound1953 rho hr0 hr1
    norm_num [Batch048.certificate1953,envelope976,inputs976,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs977 : RatMajorityInputs := ⟨(1540300193017108690266427/20000000000000000000),(21949222639/5000000000),(31251217332061107/31250000000000000),(46588139022860411/250000000000000000),(21949222639/10000000000),(111367218421658717/1000000000000000000),26⟩
theorem inputs_valid977 : inputs977.Valid := by decide +kernel
def envelope977 : RatMajorityEnvelope := ⟨464,0,inputs977,(713884051/587500000),(735627526956331133/1000000000000000000)⟩
theorem envelope_sound977 : envelope977.Sound := by
  apply rat_majority_inputs_envelopes inputs977 inputs_valid977
  · norm_num [envelope977]
  · intro rho hr0 hr1
    have hh := Batch048.bound1954 rho hr0 hr1
    norm_num [Batch048.certificate1954,envelope977,inputs977,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch048.bound1955 rho hr0 hr1
    norm_num [Batch048.certificate1955,envelope977,inputs977,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs978 : RatMajorityInputs := ⟨(1540300193017108690266427/20000000000000000000),(81981073191/20000000000),(31251217332061107/31250000000000000),(223945832169627173/1000000000000000000),(81981073191/40000000000),(128795831524606233/1000000000000000000),25⟩
theorem inputs_valid978 : inputs978.Valid := by decide +kernel
def envelope978 : RatMajorityEnvelope := ⟨464,1,inputs978,1,(27592083139139829/50000000000000000)⟩
theorem envelope_sound978 : envelope978.Sound := by
  apply rat_majority_inputs_envelopes inputs978 inputs_valid978
  · norm_num [envelope978]
  · intro rho hr0 hr1
    have hh := Batch048.bound1956 rho hr0 hr1
    norm_num [Batch048.certificate1956,envelope978,inputs978,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch048.bound1957 rho hr0 hr1
    norm_num [Batch048.certificate1957,envelope978,inputs978,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs979 : RatMajorityInputs := ⟨(1540300193017108690266427/20000000000000000000),(17313041589/4000000000),(31251217332061107/31250000000000000),(7753455127869167/40000000000000000),(17313041589/8000000000),(71781117292529/625000000000000),25⟩
theorem inputs_valid979 : inputs979.Valid := by decide +kernel
def envelope979 : RatMajorityEnvelope := ⟨464,2,inputs979,1,(273918621781848867/500000000000000000)⟩
theorem envelope_sound979 : envelope979.Sound := by
  apply rat_majority_inputs_envelopes inputs979 inputs_valid979
  · norm_num [envelope979]
  · intro rho hr0 hr1
    have hh := Batch048.bound1958 rho hr0 hr1
    norm_num [Batch048.certificate1958,envelope979,inputs979,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch048.bound1959 rho hr0 hr1
    norm_num [Batch048.certificate1959,envelope979,inputs979,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope960,envelope961,envelope962,envelope963,envelope964,envelope965,envelope966,envelope967,envelope968,envelope969,envelope970,envelope971,envelope972,envelope973,envelope974,envelope975,envelope976,envelope977,envelope978,envelope979]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound960
  · exact envelope_sound961
  · exact envelope_sound962
  · exact envelope_sound963
  · exact envelope_sound964
  · exact envelope_sound965
  · exact envelope_sound966
  · exact envelope_sound967
  · exact envelope_sound968
  · exact envelope_sound969
  · exact envelope_sound970
  · exact envelope_sound971
  · exact envelope_sound972
  · exact envelope_sound973
  · exact envelope_sound974
  · exact envelope_sound975
  · exact envelope_sound976
  · exact envelope_sound977
  · exact envelope_sound978
  · exact envelope_sound979

end Cycle12.MajorityCertificates.Inputs048
