import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch049

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs049

def inputs980 : RatMajorityInputs := ⟨(1484410279971919735598199/20000000000000000000),(87956694081/20000000000),(200008084272540413/200000000000000000),(92699885790958313/500000000000000000),(87956694081/40000000000),(13865398017308303/125000000000000000),25⟩
theorem inputs_valid980 : inputs980.Valid := by decide +kernel
def envelope980 : RatMajorityEnvelope := ⟨465,0,inputs980,(1428907787/1175000000),(92052884623558309/125000000000000000)⟩
theorem envelope_sound980 : envelope980.Sound := by
  apply rat_majority_inputs_envelopes inputs980 inputs_valid980
  · norm_num [envelope980]
  · intro rho hr0 hr1
    have hh := Batch049.bound1960 rho hr0 hr1
    norm_num [Batch049.certificate1960,envelope980,inputs980,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch049.bound1961 rho hr0 hr1
    norm_num [Batch049.certificate1961,envelope980,inputs980,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs981 : RatMajorityInputs := ⟨(1484410279971919735598199/20000000000000000000),(81933253981/20000000000),(200008084272540413/200000000000000000),(224279242516777259/1000000000000000000),(81933253981/40000000000),(64474948234963557/500000000000000000),24⟩
theorem inputs_valid981 : inputs981.Valid := by decide +kernel
def envelope981 : RatMajorityEnvelope := ⟨465,1,inputs981,1,(275944188289964891/500000000000000000)⟩
theorem envelope_sound981 : envelope981.Sound := by
  apply rat_majority_inputs_envelopes inputs981 inputs_valid981
  · norm_num [envelope981]
  · intro rho hr0 hr1
    have hh := Batch049.bound1962 rho hr0 hr1
    norm_num [Batch049.certificate1962,envelope981,inputs981,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch049.bound1963 rho hr0 hr1
    norm_num [Batch049.certificate1963,envelope981,inputs981,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs982 : RatMajorityInputs := ⟨(1484410279971919735598199/20000000000000000000),(43467915079/10000000000),(200008084272540413/200000000000000000),(191558171185869497/1000000000000000000),(43467915079/20000000000),(113790555372023071/1000000000000000000),26⟩
theorem inputs_valid982 : inputs982.Valid := by decide +kernel
def envelope982 : RatMajorityEnvelope := ⟨465,2,inputs982,1,(109509471756457437/200000000000000000)⟩
theorem envelope_sound982 : envelope982.Sound := by
  apply rat_majority_inputs_envelopes inputs982 inputs_valid982
  · norm_num [envelope982]
  · intro rho hr0 hr1
    have hh := Batch049.bound1964 rho hr0 hr1
    norm_num [Batch049.certificate1964,envelope982,inputs982,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch049.bound1965 rho hr0 hr1
    norm_num [Batch049.certificate1965,envelope982,inputs982,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs983 : RatMajorityInputs := ⟨(179029326341325990782277/2500000000000000000),(88115265689/20000000000),(250010473485732701/250000000000000000),(46114606515432109/250000000000000000),(88115265689/40000000000),(110484322908018047/1000000000000000000),26⟩
theorem inputs_valid983 : inputs983.Valid := by decide +kernel
def envelope983 : RatMajorityEnvelope := ⟨466,0,inputs983,(357512993/293750000),(184305996459546329/250000000000000000)⟩
theorem envelope_sound983 : envelope983.Sound := by
  apply rat_majority_inputs_envelopes inputs983 inputs_valid983
  · norm_num [envelope983]
  · intro rho hr0 hr1
    have hh := Batch049.bound1966 rho hr0 hr1
    norm_num [Batch049.certificate1966,envelope983,inputs983,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch049.bound1967 rho hr0 hr1
    norm_num [Batch049.certificate1967,envelope983,inputs983,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs984 : RatMajorityInputs := ⟨(179029326341325990782277/2500000000000000000),(8188385919/2000000000),(250010473485732701/250000000000000000),(1754875522999837/7812500000000000),(8188385919/4000000000),(64554615579057491/500000000000000000),25⟩
theorem inputs_valid984 : inputs984.Valid := by decide +kernel
def envelope984 : RatMajorityEnvelope := ⟨466,1,inputs984,1,(34496044590964577/62500000000000000)⟩
theorem envelope_sound984 : envelope984.Sound := by
  apply rat_majority_inputs_envelopes inputs984 inputs_valid984
  · norm_num [envelope984]
  · intro rho hr0 hr1
    have hh := Batch049.bound1968 rho hr0 hr1
    norm_num [Batch049.certificate1968,envelope984,inputs984,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch049.bound1969 rho hr0 hr1
    norm_num [Batch049.certificate1969,envelope984,inputs984,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs985 : RatMajorityInputs := ⟨(179029326341325990782277/2500000000000000000),(43782403077/10000000000),(250010473485732701/250000000000000000),(37548738997426513/200000000000000000),(43782403077/20000000000),(28003815367360509/250000000000000000),25⟩
theorem inputs_valid985 : inputs985.Valid := by decide +kernel
def envelope985 : RatMajorityEnvelope := ⟨466,2,inputs985,1,(547065368703272793/1000000000000000000)⟩
theorem envelope_sound985 : envelope985.Sound := by
  apply rat_majority_inputs_envelopes inputs985 inputs_valid985
  · norm_num [envelope985]
  · intro rho hr0 hr1
    have hh := Batch049.bound1970 rho hr0 hr1
    norm_num [Batch049.certificate1970,envelope985,inputs985,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch049.bound1971 rho hr0 hr1
    norm_num [Batch049.certificate1971,envelope985,inputs985,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs986 : RatMajorityInputs := ⟨(1414720511717648624221293/20000000000000000000),(8933821899/2000000000),(1000042412602879859/1000000000000000000),(177334231630529057/1000000000000000000),(8933821899/4000000000),(107157509582931239/1000000000000000000),25⟩
theorem inputs_valid986 : inputs986.Valid := by decide +kernel
def envelope986 : RatMajorityEnvelope := ⟨467,0,inputs986,(177466451/146875000),(728602436606159057/1000000000000000000)⟩
theorem envelope_sound986 : envelope986.Sound := by
  apply rat_majority_inputs_envelopes inputs986 inputs_valid986
  · norm_num [envelope986]
  · intro rho hr0 hr1
    have hh := Batch049.bound1972 rho hr0 hr1
    norm_num [Batch049.certificate1972,envelope986,inputs986,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch049.bound1973 rho hr0 hr1
    norm_num [Batch049.certificate1973,envelope986,inputs986,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs987 : RatMajorityInputs := ⟨(1414720511717648624221293/20000000000000000000),(80634751/19531250),(1000042412602879859/1000000000000000000),(13742070104770063/62500000000000000),(80634751/39062500),(3966046483715147/31250000000000000),25⟩
theorem inputs_valid987 : inputs987.Valid := by decide +kernel
def envelope987 : RatMajorityEnvelope := ⟨467,1,inputs987,1,(551282918865700831/1000000000000000000)⟩
theorem envelope_sound987 : envelope987.Sound := by
  apply rat_majority_inputs_envelopes inputs987 inputs_valid987
  · norm_num [envelope987]
  · intro rho hr0 hr1
    have hh := Batch049.bound1974 rho hr0 hr1
    norm_num [Batch049.certificate1974,envelope987,inputs987,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch049.bound1975 rho hr0 hr1
    norm_num [Batch049.certificate1975,envelope987,inputs987,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs988 : RatMajorityInputs := ⟨(1414720511717648624221293/20000000000000000000),(87099793089/20000000000),(1000042412602879859/1000000000000000000),(95278769508511933/500000000000000000),(87099793089/40000000000),(2266501484399839/20000000000000000),26⟩
theorem inputs_valid988 : inputs988.Valid := by decide +kernel
def envelope988 : RatMajorityEnvelope := ⟨467,2,inputs988,1,(547421143168435177/1000000000000000000)⟩
theorem envelope_sound988 : envelope988.Sound := by
  apply rat_majority_inputs_envelopes inputs988 inputs_valid988
  · norm_num [envelope988]
  · intro rho hr0 hr1
    have hh := Batch049.bound1976 rho hr0 hr1
    norm_num [Batch049.certificate1976,envelope988,inputs988,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch049.bound1977 rho hr0 hr1
    norm_num [Batch049.certificate1977,envelope988,inputs988,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs989 : RatMajorityInputs := ⟨(695324298427434223942361/10000000000000000000),(89420359057/20000000000),(500021573391598257/500000000000000000),(176864270085250679/1000000000000000000),(89420359057/40000000000),(13367210904692241/125000000000000000),25⟩
theorem inputs_valid989 : inputs989.Valid := by decide +kernel
def envelope989 : RatMajorityEnvelope := ⟨468,0,inputs989,(2840598817/2350000000),(364499872835456939/500000000000000000)⟩
theorem envelope_sound989 : envelope989.Sound := by
  apply rat_majority_inputs_envelopes inputs989 inputs_valid989
  · norm_num [envelope989]
  · intro rho hr0 hr1
    have hh := Batch049.bound1978 rho hr0 hr1
    norm_num [Batch049.certificate1978,envelope989,inputs989,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch049.bound1979 rho hr0 hr1
    norm_num [Batch049.certificate1979,envelope989,inputs989,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs990 : RatMajorityInputs := ⟨(695324298427434223942361/10000000000000000000),(82149770479/20000000000),(500021573391598257/500000000000000000),(8910915154609467/40000000000000000),(82149770479/40000000000),(64126893828785097/500000000000000000),25⟩
theorem inputs_valid990 : inputs990.Valid := by decide +kernel
def envelope990 : RatMajorityEnvelope := ⟨468,1,inputs990,1,(551681423122404941/1000000000000000000)⟩
theorem envelope_sound990 : envelope990.Sound := by
  apply rat_majority_inputs_envelopes inputs990 inputs_valid990
  · norm_num [envelope990]
  · intro rho hr0 hr1
    have hh := Batch049.bound1980 rho hr0 hr1
    norm_num [Batch049.certificate1980,envelope990,inputs990,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch049.bound1981 rho hr0 hr1
    norm_num [Batch049.certificate1981,envelope990,inputs990,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs991 : RatMajorityInputs := ⟨(695324298427434223942361/10000000000000000000),(10911561877/2500000000),(500021573391598257/500000000000000000),(189387175594095489/1000000000000000000),(10911561877/5000000000),(112780438174056927/1000000000000000000),26⟩
theorem inputs_valid991 : inputs991.Valid := by decide +kernel
def envelope991 : RatMajorityEnvelope := ⟨468,2,inputs991,1,(109454651518957211/200000000000000000)⟩
theorem envelope_sound991 : envelope991.Sound := by
  apply rat_majority_inputs_envelopes inputs991 inputs_valid991
  · norm_num [envelope991]
  · intro rho hr0 hr1
    have hh := Batch049.bound1982 rho hr0 hr1
    norm_num [Batch049.certificate1982,envelope991,inputs991,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch049.bound1983 rho hr0 hr1
    norm_num [Batch049.certificate1983,envelope991,inputs991,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs992 : RatMajorityInputs := ⟨(683679117574155313118141/10000000000000000000),(89502818959/20000000000),(500021940866067901/500000000000000000),(44098387592554993/250000000000000000),(89502818959/40000000000),(6669841408227061/62500000000000000),26⟩
theorem inputs_valid992 : inputs992.Valid := by decide +kernel
def envelope992 : RatMajorityEnvelope := ⟨469,0,inputs992,(568347051/470000000),(22793672389997981/31250000000000000)⟩
theorem envelope_sound992 : envelope992.Sound := by
  apply rat_majority_inputs_envelopes inputs992 inputs_valid992
  · norm_num [envelope992]
  · intro rho hr0 hr1
    have hh := Batch049.bound1984 rho hr0 hr1
    norm_num [Batch049.certificate1984,envelope992,inputs992,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch049.bound1985 rho hr0 hr1
    norm_num [Batch049.certificate1985,envelope992,inputs992,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs993 : RatMajorityInputs := ⟨(683679117574155313118141/10000000000000000000),(16423526451/4000000000),(500021940866067901/500000000000000000),(44599189039142999/200000000000000000),(16423526451/8000000000),(128356875289106697/1000000000000000000),25⟩
theorem inputs_valid993 : inputs993.Valid := by decide +kernel
def envelope993 : RatMajorityEnvelope := ⟨469,1,inputs993,1,(551712478165127119/1000000000000000000)⟩
theorem envelope_sound993 : envelope993.Sound := by
  apply rat_majority_inputs_envelopes inputs993 inputs_valid993
  · norm_num [envelope993]
  · intro rho hr0 hr1
    have hh := Batch049.bound1986 rho hr0 hr1
    norm_num [Batch049.certificate1986,envelope993,inputs993,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch049.bound1987 rho hr0 hr1
    norm_num [Batch049.certificate1987,envelope993,inputs993,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs994 : RatMajorityInputs := ⟨(683679117574155313118141/10000000000000000000),(87485276561/20000000000),(500021940866067901/500000000000000000),(94111212886432661/500000000000000000),(87485276561/40000000000),(56119098111870787/500000000000000000),25⟩
theorem inputs_valid994 : inputs994.Valid := by decide +kernel
def envelope994 : RatMajorityEnvelope := ⟨469,2,inputs994,1,(136781631135324609/250000000000000000)⟩
theorem envelope_sound994 : envelope994.Sound := by
  apply rat_majority_inputs_envelopes inputs994 inputs_valid994
  · norm_num [envelope994]
  · intro rho hr0 hr1
    have hh := Batch049.bound1988 rho hr0 hr1
    norm_num [Batch049.certificate1988,envelope994,inputs994,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch049.bound1989 rho hr0 hr1
    norm_num [Batch049.certificate1989,envelope994,inputs994,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs995 : RatMajorityInputs := ⟨(42025525510335018123437/625000000000000000),(89585630703/20000000000),(1000044617290180847/1000000000000000000),(175921901239722091/1000000000000000000),(89585630703/40000000000),(106496754595890553/1000000000000000000),25⟩
theorem inputs_valid995 : inputs995.Valid := by decide +kernel
def envelope995 : RatMajorityEnvelope := ⟨470,0,inputs995,(2842872459/2350000000),(729795706853336877/1000000000000000000)⟩
theorem envelope_sound995 : envelope995.Sound := by
  apply rat_majority_inputs_envelopes inputs995 inputs_valid995
  · norm_num [envelope995]
  · intro rho hr0 hr1
    have hh := Batch049.bound1990 rho hr0 hr1
    norm_num [Batch049.certificate1990,envelope995,inputs995,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch049.bound1991 rho hr0 hr1
    norm_num [Batch049.certificate1991,envelope995,inputs995,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs996 : RatMajorityInputs := ⟨(42025525510335018123437/625000000000000000),(41058289751/10000000000),(1000044617290180847/1000000000000000000),(27875406912298727/125000000000000000),(41058289751/20000000000),(128360253535700523/1000000000000000000),25⟩
theorem inputs_valid996 : inputs996.Valid := by decide +kernel
def envelope996 : RatMajorityEnvelope := ⟨470,1,inputs996,1,(275856892073849061/500000000000000000)⟩
theorem envelope_sound996 : envelope996.Sound := by
  apply rat_majority_inputs_envelopes inputs996 inputs_valid996
  · norm_num [envelope996]
  · intro rho hr0 hr1
    have hh := Batch049.bound1992 rho hr0 hr1
    norm_num [Batch049.certificate1992,envelope996,inputs996,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch049.bound1993 rho hr0 hr1
    norm_num [Batch049.certificate1993,envelope996,inputs996,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs997 : RatMajorityInputs := ⟨(42025525510335018123437/625000000000000000),(4383910947/1000000000),(1000044617290180847/1000000000000000000),(187062789757825723/1000000000000000000),(4383910947/2000000000),(111698112219712241/1000000000000000000),25⟩
theorem inputs_valid997 : inputs997.Valid := by decide +kernel
def envelope997 : RatMajorityEnvelope := ⟨470,2,inputs997,1,(273490436582587689/500000000000000000)⟩
theorem envelope_sound997 : envelope997.Sound := by
  apply rat_majority_inputs_envelopes inputs997 inputs_valid997
  · norm_num [envelope997]
  · intro rho hr0 hr1
    have hh := Batch049.bound1994 rho hr0 hr1
    norm_num [Batch049.certificate1994,envelope997,inputs997,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch049.bound1995 rho hr0 hr1
    norm_num [Batch049.certificate1995,envelope997,inputs997,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs998 : RatMajorityInputs := ⟨(165374181681685886025689/2500000000000000000),(89668818541/20000000000),(1000045353298101759/1000000000000000000),(21931149643415913/125000000000000000),(89668818541/40000000000),(21255100774705977/200000000000000000),26⟩
theorem inputs_valid998 : inputs998.Valid := by decide +kernel
def envelope998 : RatMajorityEnvelope := ⟨471,0,inputs998,(711002597/587500000),(146038858078990693/200000000000000000)⟩
theorem envelope_sound998 : envelope998.Sound := by
  apply rat_majority_inputs_envelopes inputs998 inputs_valid998
  · norm_num [envelope998]
  · intro rho hr0 hr1
    have hh := Batch049.bound1996 rho hr0 hr1
    norm_num [Batch049.certificate1996,envelope998,inputs998,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch049.bound1997 rho hr0 hr1
    norm_num [Batch049.certificate1997,envelope998,inputs998,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs999 : RatMajorityInputs := ⟨(165374181681685886025689/2500000000000000000),(82064732063/20000000000),(1000045353298101759/1000000000000000000),(27920439703516119/125000000000000000),(82064732063/40000000000),(8032921260724543/62500000000000000),24⟩
theorem inputs_valid999 : inputs999.Valid := by decide +kernel
def envelope999 : RatMajorityEnvelope := ⟨471,1,inputs999,1,(551763795336112229/1000000000000000000)⟩
theorem envelope_sound999 : envelope999.Sound := by
  apply rat_majority_inputs_envelopes inputs999 inputs_valid999
  · norm_num [envelope999]
  · intro rho hr0 hr1
    have hh := Batch049.bound1998 rho hr0 hr1
    norm_num [Batch049.certificate1998,envelope999,inputs999,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch049.bound1999 rho hr0 hr1
    norm_num [Batch049.certificate1999,envelope999,inputs999,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope980,envelope981,envelope982,envelope983,envelope984,envelope985,envelope986,envelope987,envelope988,envelope989,envelope990,envelope991,envelope992,envelope993,envelope994,envelope995,envelope996,envelope997,envelope998,envelope999]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound980
  · exact envelope_sound981
  · exact envelope_sound982
  · exact envelope_sound983
  · exact envelope_sound984
  · exact envelope_sound985
  · exact envelope_sound986
  · exact envelope_sound987
  · exact envelope_sound988
  · exact envelope_sound989
  · exact envelope_sound990
  · exact envelope_sound991
  · exact envelope_sound992
  · exact envelope_sound993
  · exact envelope_sound994
  · exact envelope_sound995
  · exact envelope_sound996
  · exact envelope_sound997
  · exact envelope_sound998
  · exact envelope_sound999

end Cycle12.MajorityCertificates.Inputs049
