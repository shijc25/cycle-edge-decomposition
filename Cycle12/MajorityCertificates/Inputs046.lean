import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch046

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs046

def inputs920 : RatMajorityInputs := ⟨(2175035626776589890175923/20000000000000000000),(2189116321/500000000),(1000027586346918613/1000000000000000000),(7509784674848169/40000000000000000),(2189116321/1000000000),(56007845403979877/500000000000000000),25⟩
theorem inputs_valid920 : inputs920.Valid := by decide +kernel
def envelope920 : RatMajorityEnvelope := ⟨445,0,inputs920,(2814786207/2350000000),(720039081481378339/1000000000000000000)⟩
theorem envelope_sound920 : envelope920.Sound := by
  apply rat_majority_inputs_envelopes inputs920 inputs_valid920
  · norm_num [envelope920]
  · intro rho hr0 hr1
    have hh := Batch046.bound1840 rho hr0 hr1
    norm_num [Batch046.certificate1840,envelope920,inputs920,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch046.bound1841 rho hr0 hr1
    norm_num [Batch046.certificate1841,envelope920,inputs920,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs921 : RatMajorityInputs := ⟨(2175035626776589890175923/20000000000000000000),(82613476521/20000000000),(1000027586346918613/1000000000000000000),(219574788965266537/1000000000000000000),(82613476521/40000000000),(126775571030882823/1000000000000000000),25⟩
theorem inputs_valid921 : inputs921.Valid := by decide +kernel
def envelope921 : RatMajorityEnvelope := ⟨445,1,inputs921,1,(551236090696366019/1000000000000000000)⟩
theorem envelope_sound921 : envelope921.Sound := by
  apply rat_majority_inputs_envelopes inputs921 inputs_valid921
  · norm_num [envelope921]
  · intro rho hr0 hr1
    have hh := Batch046.bound1842 rho hr0 hr1
    norm_num [Batch046.certificate1842,envelope921,inputs921,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch046.bound1843 rho hr0 hr1
    norm_num [Batch046.certificate1843,envelope921,inputs921,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs922 : RatMajorityInputs := ⟨(2175035626776589890175923/20000000000000000000),(16988553871/4000000000),(1000027586346918613/1000000000000000000),(51020000865528837/250000000000000000),(16988553871/8000000000),(119603971215365381/1000000000000000000),25⟩
theorem inputs_valid922 : inputs922.Valid := by decide +kernel
def envelope922 : RatMajorityEnvelope := ⟨445,2,inputs922,1,(109831994942805579/200000000000000000)⟩
theorem envelope_sound922 : envelope922.Sound := by
  apply rat_majority_inputs_envelopes inputs922 inputs_valid922
  · norm_num [envelope922]
  · intro rho hr0 hr1
    have hh := Batch046.bound1844 rho hr0 hr1
    norm_num [Batch046.certificate1844,envelope922,inputs922,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch046.bound1845 rho hr0 hr1
    norm_num [Batch046.certificate1845,envelope922,inputs922,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs923 : RatMajorityInputs := ⟨(258986399395826479014429/2500000000000000000),(17543907093/4000000000),(1000028959701933309/1000000000000000000),(186815255698513669/1000000000000000000),(17543907093/8000000000),(446331189355769/4000000000000000),25⟩
theorem inputs_valid923 : inputs923.Valid := by decide +kernel
def envelope923 : RatMajorityEnvelope := ⟨446,0,inputs923,(1408507273/1175000000),(180202319904564067/250000000000000000)⟩
theorem envelope_sound923 : envelope923.Sound := by
  apply rat_majority_inputs_envelopes inputs923 inputs_valid923
  · norm_num [envelope923]
  · intro rho hr0 hr1
    have hh := Batch046.bound1846 rho hr0 hr1
    norm_num [Batch046.certificate1846,envelope923,inputs923,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch046.bound1847 rho hr0 hr1
    norm_num [Batch046.certificate1847,envelope923,inputs923,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs924 : RatMajorityInputs := ⟨(258986399395826479014429/2500000000000000000),(82566104281/20000000000),(1000028959701933309/1000000000000000000),(219899758141533137/1000000000000000000),(82566104281/40000000000),(25385160208380139/200000000000000000),25⟩
theorem inputs_valid924 : inputs924.Valid := by decide +kernel
def envelope924 : RatMajorityEnvelope := ⟨446,1,inputs924,1,(137820273353862757/250000000000000000)⟩
theorem envelope_sound924 : envelope924.Sound := by
  apply rat_majority_inputs_envelopes inputs924 inputs_valid924
  · norm_num [envelope924]
  · intro rho hr0 hr1
    have hh := Batch046.bound1848 rho hr0 hr1
    norm_num [Batch046.certificate1848,envelope924,inputs924,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch046.bound1849 rho hr0 hr1
    norm_num [Batch046.certificate1849,envelope924,inputs924,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs925 : RatMajorityInputs := ⟨(258986399395826479014429/2500000000000000000),(8528719969/2000000000),(1000028959701933309/1000000000000000000),(201868202868327383/1000000000000000000),(8528719969/4000000000),(118578511646887297/1000000000000000000),25⟩
theorem inputs_valid925 : inputs925.Valid := by decide +kernel
def envelope925 : RatMajorityEnvelope := ⟨446,2,inputs925,1,(137217733536665771/250000000000000000)⟩
theorem envelope_sound925 : envelope925.Sound := by
  apply rat_majority_inputs_envelopes inputs925 inputs_valid925
  · norm_num [envelope925]
  · intro rho hr0 hr1
    have hh := Batch046.bound1850 rho hr0 hr1
    norm_num [Batch046.certificate1850,envelope925,inputs925,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch046.bound1851 rho hr0 hr1
    norm_num [Batch046.certificate1851,envelope925,inputs925,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs926 : RatMajorityInputs := ⟨(20331118945775398207233/200000000000000000),(87904108883/20000000000),(250007378022010031/250000000000000000),(46428209639704173/250000000000000000),(87904108883/40000000000),(55534551486051663/500000000000000000),26⟩
theorem inputs_valid926 : inputs926.Valid := by decide +kernel
def envelope926 : RatMajorityEnvelope := ⟨447,0,inputs926,(1409589719/1175000000),(721539197102998961/1000000000000000000)⟩
theorem envelope_sound926 : envelope926.Sound := by
  apply rat_majority_inputs_envelopes inputs926 inputs_valid926
  · norm_num [envelope926]
  · intro rho hr0 hr1
    have hh := Batch046.bound1852 rho hr0 hr1
    norm_num [Batch046.certificate1852,envelope926,inputs926,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch046.bound1853 rho hr0 hr1
    norm_num [Batch046.certificate1853,envelope926,inputs926,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs927 : RatMajorityInputs := ⟨(20331118945775398207233/200000000000000000),(20643260899/5000000000),(250007378022010031/250000000000000000),(219852130268161869/1000000000000000000),(20643260899/10000000000),(63451891749456409/500000000000000000),25⟩
theorem inputs_valid927 : inputs927.Valid := by decide +kernel
def envelope927 : RatMajorityEnvelope := ⟨447,1,inputs927,1,(275637400938662273/500000000000000000)⟩
theorem envelope_sound927 : envelope927.Sound := by
  apply rat_majority_inputs_envelopes inputs927 inputs_valid927
  · norm_num [envelope927]
  · intro rho hr0 hr1
    have hh := Batch046.bound1854 rho hr0 hr1
    norm_num [Batch046.certificate1854,envelope927,inputs927,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch046.bound1855 rho hr0 hr1
    norm_num [Batch046.certificate1855,envelope927,inputs927,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs928 : RatMajorityInputs := ⟨(20331118945775398207233/200000000000000000),(21420621817/5000000000),(250007378022010031/250000000000000000),(49838655499212419/250000000000000000),(21420621817/10000000000),(58706233677404771/500000000000000000),25⟩
theorem inputs_valid928 : inputs928.Valid := by decide +kernel
def envelope928 : RatMajorityEnvelope := ⟨447,2,inputs928,1,(109708807877825233/200000000000000000)⟩
theorem envelope_sound928 : envelope928.Sound := by
  apply rat_majority_inputs_envelopes inputs928 inputs_valid928
  · norm_num [envelope928]
  · intro rho hr0 hr1
    have hh := Batch046.bound1856 rho hr0 hr1
    norm_num [Batch046.certificate1856,envelope928,inputs928,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch046.bound1857 rho hr0 hr1
    norm_num [Batch046.certificate1857,envelope928,inputs928,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs929 : RatMajorityInputs := ⟨(993240040108102637257263/10000000000000000000),(10997616997/2500000000),(12500377561107687/12500000000000000),(185255598054308743/1000000000000000000),(10997616997/5000000000),(110855979800455961/1000000000000000000),25⟩
theorem inputs_valid929 : inputs929.Valid := by decide +kernel
def envelope929 : RatMajorityEnvelope := ⟨448,0,inputs929,(1410150117/1175000000),(360964142323120277/500000000000000000)⟩
theorem envelope_sound929 : envelope929.Sound := by
  apply rat_majority_inputs_envelopes inputs929 inputs_valid929
  · norm_num [envelope929]
  · intro rho hr0 hr1
    have hh := Batch046.bound1858 rho hr0 hr1
    norm_num [Batch046.certificate1858,envelope929,inputs929,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch046.bound1859 rho hr0 hr1
    norm_num [Batch046.certificate1859,envelope929,inputs929,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs930 : RatMajorityInputs := ⟨(993240040108102637257263/10000000000000000000),(82556057937/20000000000),(12500377561107687/12500000000000000),(27496090769201523/125000000000000000),(82556057937/40000000000),(63478841776004981/500000000000000000),25⟩
theorem inputs_valid930 : inputs930.Valid := by decide +kernel
def envelope930 : RatMajorityEnvelope := ⟨448,1,inputs930,1,(110258207363515651/200000000000000000)⟩
theorem envelope_sound930 : envelope930.Sound := by
  apply rat_majority_inputs_envelopes inputs930 inputs_valid930
  · norm_num [envelope930]
  · intro rho hr0 hr1
    have hh := Batch046.bound1860 rho hr0 hr1
    norm_num [Batch046.certificate1860,envelope930,inputs930,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch046.bound1861 rho hr0 hr1
    norm_num [Batch046.certificate1861,envelope930,inputs930,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs931 : RatMajorityInputs := ⟨(993240040108102637257263/10000000000000000000),(42928503223/10000000000),(12500377561107687/12500000000000000),(99126636086720153/500000000000000000),(42928503223/20000000000),(116901315056892721/1000000000000000000),26⟩
theorem inputs_valid931 : inputs931.Valid := by decide +kernel
def envelope931 : RatMajorityEnvelope := ⟨448,2,inputs931,1,(34275103943959219/62500000000000000)⟩
theorem envelope_sound931 : envelope931.Sound := by
  apply rat_majority_inputs_envelopes inputs931 inputs_valid931
  · norm_num [envelope931]
  · intro rho hr0 hr1
    have hh := Batch046.bound1862 rho hr0 hr1
    norm_num [Batch046.certificate1862,envelope931,inputs931,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch046.bound1863 rho hr0 hr1
    norm_num [Batch046.certificate1863,envelope931,inputs931,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs932 : RatMajorityInputs := ⟨(377916862337942942460269/4000000000000000000),(88024811557/20000000000),(1000031753799748341/1000000000000000000),(5781090611676391/31250000000000000),(88024811557/40000000000),(22146889940432041/200000000000000000),25⟩
theorem inputs_valid932 : inputs932.Valid := by decide +kernel
def envelope932 : RatMajorityEnvelope := ⟨449,0,inputs932,(2821498731/2350000000),(22573946640848489/31250000000000000)⟩
theorem envelope_sound932 : envelope932.Sound := by
  apply rat_majority_inputs_envelopes inputs932 inputs_valid932
  · norm_num [envelope932]
  · intro rho hr0 hr1
    have hh := Batch046.bound1864 rho hr0 hr1
    norm_num [Batch046.certificate1864,envelope932,inputs932,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch046.bound1865 rho hr0 hr1
    norm_num [Batch046.certificate1865,envelope932,inputs932,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs933 : RatMajorityInputs := ⟨(377916862337942942460269/4000000000000000000),(2062874321/500000000),(1000031753799748341/1000000000000000000),(22025096067663877/100000000000000000),(2062874321/1000000000),(5083526090525043/40000000000000000),25⟩
theorem inputs_valid933 : inputs933.Valid := by decide +kernel
def envelope933 : RatMajorityEnvelope := ⟨449,1,inputs933,1,(551330303135748461/1000000000000000000)⟩
theorem envelope_sound933 : envelope933.Sound := by
  apply rat_majority_inputs_envelopes inputs933 inputs_valid933
  · norm_num [envelope933]
  · intro rho hr0 hr1
    have hh := Batch046.bound1866 rho hr0 hr1
    norm_num [Batch046.certificate1866,envelope933,inputs933,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch046.bound1867 rho hr0 hr1
    norm_num [Batch046.certificate1867,envelope933,inputs933,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs934 : RatMajorityInputs := ⟨(377916862337942942460269/4000000000000000000),(42692916851/10000000000),(1000031753799748341/1000000000000000000),(201238526057309973/1000000000000000000),(42692916851/20000000000),(118286474995676653/1000000000000000000),25⟩
theorem inputs_valid934 : inputs934.Valid := by decide +kernel
def envelope934 : RatMajorityEnvelope := ⟨449,2,inputs934,1,(548789952904577891/1000000000000000000)⟩
theorem envelope_sound934 : envelope934.Sound := by
  apply rat_majority_inputs_envelopes inputs934 inputs_valid934
  · norm_num [envelope934]
  · intro rho hr0 hr1
    have hh := Batch046.bound1868 rho hr0 hr1
    norm_num [Batch046.certificate1868,envelope934,inputs934,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch046.bound1869 rho hr0 hr1
    norm_num [Batch046.certificate1869,envelope934,inputs934,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs935 : RatMajorityInputs := ⟨(1857361210910240130551901/20000000000000000000),(44106684841/10000000000),(200006460941167221/200000000000000000),(183878077844368027/1000000000000000000),(44106684841/20000000000),(110213681100677997/1000000000000000000),25⟩
theorem inputs_valid935 : inputs935.Valid := by decide +kernel
def envelope935 : RatMajorityEnvelope := ⟨450,0,inputs935,(705916709/587500000),(2892391364982577/4000000000000000)⟩
theorem envelope_sound935 : envelope935.Sound := by
  apply rat_majority_inputs_envelopes inputs935 inputs_valid935
  · norm_num [envelope935]
  · intro rho hr0 hr1
    have hh := Batch046.bound1870 rho hr0 hr1
    norm_num [Batch046.certificate1870,envelope935,inputs935,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch046.bound1871 rho hr0 hr1
    norm_num [Batch046.certificate1871,envelope935,inputs935,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs936 : RatMajorityInputs := ⟨(1857361210910240130551901/20000000000000000000),(82552440441/20000000000),(200006460941167221/200000000000000000),(21999356458679331/100000000000000000),(82552440441/40000000000),(6348458289701233/50000000000000000),25⟩
theorem inputs_valid936 : inputs936.Valid := by decide +kernel
def envelope936 : RatMajorityEnvelope := ⟨450,1,inputs936,1,(137823822394712631/250000000000000000)⟩
theorem envelope_sound936 : envelope936.Sound := by
  apply rat_majority_inputs_envelopes inputs936 inputs_valid936
  · norm_num [envelope936]
  · intro rho hr0 hr1
    have hh := Batch046.bound1872 rho hr0 hr1
    norm_num [Batch046.certificate1872,envelope936,inputs936,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch046.bound1873 rho hr0 hr1
    norm_num [Batch046.certificate1873,envelope936,inputs936,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs937 : RatMajorityInputs := ⟨(1857361210910240130551901/20000000000000000000),(3431288439/800000000),(200006460941167221/200000000000000000),(198724661015455407/1000000000000000000),(3431288439/1600000000),(23424022355738901/200000000000000000),25⟩
theorem inputs_valid937 : inputs937.Valid := by decide +kernel
def envelope937 : RatMajorityEnvelope := ⟨450,2,inputs937,1,(274231777807833171/500000000000000000)⟩
theorem envelope_sound937 : envelope937.Sound := by
  apply rat_majority_inputs_envelopes inputs937 inputs_valid937
  · norm_num [envelope937]
  · intro rho hr0 hr1
    have hh := Batch046.bound1874 rho hr0 hr1
    norm_num [Batch046.certificate1874,envelope937,inputs937,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch046.bound1875 rho hr0 hr1
    norm_num [Batch046.certificate1875,envelope937,inputs937,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs938 : RatMajorityInputs := ⟨(908804702382556272052011/10000000000000000000),(11036421607/2500000000),(200006602248025787/200000000000000000),(183417747906984939/1000000000000000000),(11036421607/5000000000),(109998965101737569/1000000000000000000),25⟩
theorem inputs_valid938 : inputs938.Valid := by decide +kernel
def envelope938 : RatMajorityEnvelope := ⟨451,0,inputs938,(11299163/9400000),(180872162713286889/250000000000000000)⟩
theorem envelope_sound938 : envelope938.Sound := by
  apply rat_majority_inputs_envelopes inputs938 inputs_valid938
  · norm_num [envelope938]
  · intro rho hr0 hr1
    have hh := Batch046.bound1876 rho hr0 hr1
    norm_num [Batch046.certificate1876,envelope938,inputs938,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch046.bound1877 rho hr0 hr1
    norm_num [Batch046.certificate1877,envelope938,inputs938,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs939 : RatMajorityInputs := ⟨(908804702382556272052011/10000000000000000000),(2061977937/500000000),(200006602248025787/200000000000000000),(220497513696284199/1000000000000000000),(2061977937/1000000000),(3975066347581263/31250000000000000),25⟩
theorem inputs_valid939 : inputs939.Valid := by decide +kernel
def envelope939 : RatMajorityEnvelope := ⟨451,1,inputs939,1,(110272917850142537/200000000000000000)⟩
theorem envelope_sound939 : envelope939.Sound := by
  apply rat_majority_inputs_envelopes inputs939 inputs_valid939
  · norm_num [envelope939]
  · intro rho hr0 hr1
    have hh := Batch046.bound1878 rho hr0 hr1
    norm_num [Batch046.certificate1878,envelope939,inputs939,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch046.bound1879 rho hr0 hr1
    norm_num [Batch046.certificate1879,envelope939,inputs939,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope920,envelope921,envelope922,envelope923,envelope924,envelope925,envelope926,envelope927,envelope928,envelope929,envelope930,envelope931,envelope932,envelope933,envelope934,envelope935,envelope936,envelope937,envelope938,envelope939]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound920
  · exact envelope_sound921
  · exact envelope_sound922
  · exact envelope_sound923
  · exact envelope_sound924
  · exact envelope_sound925
  · exact envelope_sound926
  · exact envelope_sound927
  · exact envelope_sound928
  · exact envelope_sound929
  · exact envelope_sound930
  · exact envelope_sound931
  · exact envelope_sound932
  · exact envelope_sound933
  · exact envelope_sound934
  · exact envelope_sound935
  · exact envelope_sound936
  · exact envelope_sound937
  · exact envelope_sound938
  · exact envelope_sound939

end Cycle12.MajorityCertificates.Inputs046
