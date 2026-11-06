import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch047

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs047

def inputs940 : RatMajorityInputs := ⟨(908804702382556272052011/10000000000000000000),(1719493731/400000000),(200006602248025787/200000000000000000),(197513512221165777/1000000000000000000),(1719493731/800000000),(29139474125223923/250000000000000000),25⟩
theorem inputs_valid940 : inputs940.Valid := by decide +kernel
def envelope940 : RatMajorityEnvelope := ⟨451,2,inputs940,1,(137076810162324883/250000000000000000)⟩
theorem envelope_sound940 : envelope940.Sound := by
  apply rat_majority_inputs_envelopes inputs940 inputs_valid940
  · norm_num [envelope940]
  · intro rho hr0 hr1
    have hh := Batch047.bound1880 rho hr0 hr1
    norm_num [Batch047.certificate1880,envelope940,inputs940,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch047.bound1881 rho hr0 hr1
    norm_num [Batch047.certificate1881,envelope940,inputs940,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs941 : RatMajorityInputs := ⟨(450674878308412961975453/5000000000000000000),(2757717903/625000000),(250008321069709981/250000000000000000),(11479978163579597/62500000000000000),(2757717903/1250000000),(4404845265312871/40000000000000000),26⟩
theorem inputs_valid941 : inputs941.Valid := by decide +kernel
def envelope941 : RatMajorityEnvelope := ⟨452,0,inputs941,(707270729/587500000),(725167249388208271/1000000000000000000)⟩
theorem envelope_sound941 : envelope941.Sound := by
  apply rat_majority_inputs_envelopes inputs941 inputs_valid941
  · norm_num [envelope941]
  · intro rho hr0 hr1
    have hh := Batch047.bound1882 rho hr0 hr1
    norm_num [Batch047.certificate1882,envelope941,inputs941,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch047.bound1883 rho hr0 hr1
    norm_num [Batch047.certificate1883,envelope941,inputs941,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs942 : RatMajorityInputs := ⟨(450674878308412961975453/5000000000000000000),(41201882741/10000000000),(250008321069709981/250000000000000000),(44203280147654911/200000000000000000),(41201882741/20000000000),(1019535778550409/8000000000000000),25⟩
theorem inputs_valid942 : inputs942.Valid := by decide +kernel
def envelope942 : RatMajorityEnvelope := ⟨452,1,inputs942,1,(110287170634922051/200000000000000000)⟩
theorem envelope_sound942 : envelope942.Sound := by
  apply rat_majority_inputs_envelopes inputs942 inputs_valid942
  · norm_num [envelope942]
  · intro rho hr0 hr1
    have hh := Batch047.bound1884 rho hr0 hr1
    norm_num [Batch047.certificate1884,envelope942,inputs942,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch047.bound1885 rho hr0 hr1
    norm_num [Batch047.certificate1885,envelope942,inputs942,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs943 : RatMajorityInputs := ⟨(450674878308412961975453/5000000000000000000),(43090387297/10000000000),(250008321069709981/250000000000000000),(24527949834065761/125000000000000000),(43090387297/20000000000),(115958911149836117/1000000000000000000),26⟩
theorem inputs_valid943 : inputs943.Valid := by decide +kernel
def envelope943 : RatMajorityEnvelope := ⟨452,2,inputs943,1,(274070547800983569/500000000000000000)⟩
theorem envelope_sound943 : envelope943.Sound := by
  apply rat_majority_inputs_envelopes inputs943 inputs_valid943
  · norm_num [envelope943]
  · intro rho hr0 hr1
    have hh := Batch047.bound1886 rho hr0 hr1
    norm_num [Batch047.certificate1886,envelope943,inputs943,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch047.bound1887 rho hr0 hr1
    norm_num [Batch047.certificate1887,envelope943,inputs943,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs944 : RatMajorityInputs := ⟨(1783723888197323555406987/20000000000000000000),(88286266353/20000000000),(500016819186586113/500000000000000000),(183447853533635167/1000000000000000000),(88286266353/40000000000),(55006504374637411/500000000000000000),25⟩
theorem inputs_valid944 : inputs944.Valid := by decide +kernel
def envelope944 : RatMajorityEnvelope := ⟨453,0,inputs944,(2829646141/2350000000),(5666900201355091/7812500000000000)⟩
theorem envelope_sound944 : envelope944.Sound := by
  apply rat_majority_inputs_envelopes inputs944 inputs_valid944
  · norm_num [envelope944]
  · intro rho hr0 hr1
    have hh := Batch047.bound1888 rho hr0 hr1
    norm_num [Batch047.certificate1888,envelope944,inputs944,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch047.bound1889 rho hr0 hr1
    norm_num [Batch047.certificate1889,envelope944,inputs944,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs945 : RatMajorityInputs := ⟨(1783723888197323555406987/20000000000000000000),(82421573171/20000000000),(500016819186586113/500000000000000000),(110446841524712433/500000000000000000),(82421573171/40000000000),(127385248770964231/1000000000000000000),25⟩
theorem inputs_valid945 : inputs945.Valid := by decide +kernel
def envelope945 : RatMajorityEnvelope := ⟨453,1,inputs945,1,(275709580207006183/500000000000000000)⟩
theorem envelope_sound945 : envelope945.Sound := by
  apply rat_majority_inputs_envelopes inputs945 inputs_valid945
  · norm_num [envelope945]
  · intro rho hr0 hr1
    have hh := Batch047.bound1890 rho hr0 hr1
    norm_num [Batch047.certificate1890,envelope945,inputs945,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch047.bound1891 rho hr0 hr1
    norm_num [Batch047.certificate1891,envelope945,inputs945,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs946 : RatMajorityInputs := ⟨(1783723888197323555406987/20000000000000000000),(17251543029/4000000000),(500016819186586113/500000000000000000),(195743846805738653/1000000000000000000),(17251543029/8000000000),(115736076967920077/1000000000000000000),25⟩
theorem inputs_valid946 : inputs946.Valid := by decide +kernel
def envelope946 : RatMajorityEnvelope := ⟨453,2,inputs946,1,(548079548920046001/1000000000000000000)⟩
theorem envelope_sound946 : envelope946.Sound := by
  apply rat_majority_inputs_envelopes inputs946 inputs_valid946
  · norm_num [envelope946]
  · intro rho hr0 hr1
    have hh := Batch047.bound1892 rho hr0 hr1
    norm_num [Batch047.certificate1892,envelope946,inputs946,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch047.bound1893 rho hr0 hr1
    norm_num [Batch047.certificate1893,envelope946,inputs946,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs947 : RatMajorityInputs := ⟨(1765106760957069316201143/20000000000000000000),(17665107403/4000000000),(250008498294221067/250000000000000000),(183216439644423531/1000000000000000000),(17665107403/8000000000),(13738131832343567/125000000000000000),26⟩
theorem inputs_valid947 : inputs947.Valid := by decide +kernel
def envelope947 : RatMajorityEnvelope := ⟨454,0,inputs947,(283020971/235000000),(145111884221134729/200000000000000000)⟩
theorem envelope_sound947 : envelope947.Sound := by
  apply rat_majority_inputs_envelopes inputs947 inputs_valid947
  · norm_num [envelope947]
  · intro rho hr0 hr1
    have hh := Batch047.bound1894 rho hr0 hr1
    norm_num [Batch047.certificate1894,envelope947,inputs947,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch047.bound1895 rho hr0 hr1
    norm_num [Batch047.certificate1895,envelope947,inputs947,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs948 : RatMajorityInputs := ⟨(1765106760957069316201143/20000000000000000000),(82408638771/20000000000),(250008498294221067/250000000000000000),(110491405986478617/500000000000000000),(82408638771/40000000000),(127426446725533127/1000000000000000000),25⟩
theorem inputs_valid948 : inputs948.Valid := by decide +kernel
def envelope948 : RatMajorityEnvelope := ⟨454,1,inputs948,1,(551431532124885863/1000000000000000000)⟩
theorem envelope_sound948 : envelope948.Sound := by
  apply rat_majority_inputs_envelopes inputs948 inputs_valid948
  · norm_num [envelope948]
  · intro rho hr0 hr1
    have hh := Batch047.bound1896 rho hr0 hr1
    norm_num [Batch047.certificate1896,envelope948,inputs948,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch047.bound1897 rho hr0 hr1
    norm_num [Batch047.certificate1897,envelope948,inputs948,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs949 : RatMajorityInputs := ⟨(1765106760957069316201143/20000000000000000000),(86360769789/20000000000),(250008498294221067/250000000000000000),(2438785163221709/12500000000000000),(86360769789/40000000000),(11543828224151359/100000000000000000),25⟩
theorem inputs_valid949 : inputs949.Valid := by decide +kernel
def envelope949 : RatMajorityEnvelope := ⟨454,2,inputs949,1,(109599476158882003/200000000000000000)⟩
theorem envelope_sound949 : envelope949.Sound := by
  apply rat_majority_inputs_envelopes inputs949 inputs_valid949
  · norm_num [envelope949]
  · intro rho hr0 hr1
    have hh := Batch047.bound1898 rho hr0 hr1
    norm_num [Batch047.certificate1898,envelope949,inputs949,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch047.bound1899 rho hr0 hr1
    norm_num [Batch047.certificate1899,envelope949,inputs949,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs950 : RatMajorityInputs := ⟨(879045480576851624018781/10000000000000000000),(88375606679/20000000000),(1000034128832922299/1000000000000000000),(182921749809820613/1000000000000000000),(88375606679/40000000000),(2195351359932419/20000000000000000),26⟩
theorem inputs_valid950 : inputs950.Valid := by decide +kernel
def envelope950 : RatMajorityEnvelope := ⟨455,0,inputs950,(2830748999/2350000000),(725740362323868799/1000000000000000000)⟩
theorem envelope_sound950 : envelope950.Sound := by
  apply rat_majority_inputs_envelopes inputs950 inputs_valid950
  · norm_num [envelope950]
  · intro rho hr0 hr1
    have hh := Batch047.bound1900 rho hr0 hr1
    norm_num [Batch047.certificate1900,envelope950,inputs950,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch047.bound1901 rho hr0 hr1
    norm_num [Batch047.certificate1901,envelope950,inputs950,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs951 : RatMajorityInputs := ⟨(879045480576851624018781/10000000000000000000),(82407308671/20000000000),(1000034128832922299/1000000000000000000),(110495989582923437/500000000000000000),(82407308671/40000000000),(15928835505487899/125000000000000000),25⟩
theorem inputs_valid951 : inputs951.Valid := by decide +kernel
def envelope951 : RatMajorityEnvelope := ⟨455,1,inputs951,1,(275716422503994007/500000000000000000)⟩
theorem envelope_sound951 : envelope951.Sound := by
  apply rat_majority_inputs_envelopes inputs951 inputs_valid951
  · norm_num [envelope951]
  · intro rho hr0 hr1
    have hh := Batch047.bound1902 rho hr0 hr1
    norm_num [Batch047.certificate1902,envelope951,inputs951,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch047.bound1903 rho hr0 hr1
    norm_num [Batch047.certificate1903,envelope951,inputs951,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs952 : RatMajorityInputs := ⟨(879045480576851624018781/10000000000000000000),(86464335699/20000000000),(1000034128832922299/1000000000000000000),(24307547873651211/125000000000000000),(86464335699/40000000000),(115139782070062023/1000000000000000000),25⟩
theorem inputs_valid952 : inputs952.Valid := by decide +kernel
def envelope952 : RatMajorityEnvelope := ⟨455,2,inputs952,1,(109583015449672957/200000000000000000)⟩
theorem envelope_sound952 : envelope952.Sound := by
  apply rat_majority_inputs_envelopes inputs952 inputs_valid952
  · norm_num [envelope952]
  · intro rho hr0 hr1
    have hh := Batch047.bound1904 rho hr0 hr1
    norm_num [Batch047.certificate1904,envelope952,inputs952,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch047.bound1905 rho hr0 hr1
    norm_num [Batch047.certificate1905,envelope952,inputs952,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs953 : RatMajorityInputs := ⟨(218623952813459885048013/2500000000000000000),(88393475421/20000000000),(25000857659925147/25000000000000000),(182816679334356509/1000000000000000000),(88393475421/40000000000),(21943708747729291/200000000000000000),25⟩
theorem inputs_valid953 : inputs953.Valid := by decide +kernel
def envelope953 : RatMajorityEnvelope := ⟨456,0,inputs953,(22648281/18800000),(725841158355515233/1000000000000000000)⟩
theorem envelope_sound953 : envelope953.Sound := by
  apply rat_majority_inputs_envelopes inputs953 inputs_valid953
  · norm_num [envelope953]
  · intro rho hr0 hr1
    have hh := Batch047.bound1906 rho hr0 hr1
    norm_num [Batch047.certificate1906,envelope953,inputs953,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch047.bound1907 rho hr0 hr1
    norm_num [Batch047.certificate1907,envelope953,inputs953,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs954 : RatMajorityInputs := ⟨(218623952813459885048013/2500000000000000000),(41202231669/10000000000),(25000857659925147/25000000000000000),(44202318112341571/200000000000000000),(41202231669/20000000000),(15929968616821293/125000000000000000),25⟩
theorem inputs_valid954 : inputs954.Valid := by decide +kernel
def envelope954 : RatMajorityEnvelope := ⟨456,1,inputs954,1,(68929451004076749/125000000000000000)⟩
theorem envelope_sound954 : envelope954.Sound := by
  apply rat_majority_inputs_envelopes inputs954 inputs_valid954
  · norm_num [envelope954]
  · intro rho hr0 hr1
    have hh := Batch047.bound1908 rho hr0 hr1
    norm_num [Batch047.certificate1908,envelope954,inputs954,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch047.bound1909 rho hr0 hr1
    norm_num [Batch047.certificate1909,envelope954,inputs954,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs955 : RatMajorityInputs := ⟨(218623952813459885048013/2500000000000000000),(43250656169/10000000000),(25000857659925147/25000000000000000),(194231445706015537/1000000000000000000),(43250656169/20000000000),(23006678839411843/200000000000000000),25⟩
theorem inputs_valid955 : inputs955.Valid := by decide +kernel
def envelope955 : RatMajorityEnvelope := ⟨456,2,inputs955,1,(68485729345020663/125000000000000000)⟩
theorem envelope_sound955 : envelope955.Sound := by
  apply rat_majority_inputs_envelopes inputs955 inputs_valid955
  · norm_num [envelope955]
  · intro rho hr0 hr1
    have hh := Batch047.bound1910 rho hr0 hr1
    norm_num [Batch047.certificate1910,envelope955,inputs955,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch047.bound1911 rho hr0 hr1
    norm_num [Batch047.certificate1911,envelope955,inputs955,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs956 : RatMajorityInputs := ⟨(1707096871094615169326297/20000000000000000000),(88459918099/20000000000),(500017574175569267/500000000000000000),(3648528770809519/20000000000000000),(88459918099/40000000000),(109536445172664527/1000000000000000000),25⟩
theorem inputs_valid956 : inputs956.Valid := by decide +kernel
def envelope956 : RatMajorityEnvelope := ⟨457,0,inputs956,(2828316527/2350000000),(724757477311169027/1000000000000000000)⟩
theorem envelope_sound956 : envelope956.Sound := by
  apply rat_majority_inputs_envelopes inputs956 inputs_valid956
  · norm_num [envelope956]
  · intro rho hr0 hr1
    have hh := Batch047.bound1912 rho hr0 hr1
    norm_num [Batch047.certificate1912,envelope956,inputs956,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch047.bound1913 rho hr0 hr1
    norm_num [Batch047.certificate1913,envelope956,inputs956,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs957 : RatMajorityInputs := ⟨(1707096871094615169326297/20000000000000000000),(2060533157/500000000),(500017574175569267/500000000000000000),(110447692029452501/500000000000000000),(2060533157/1000000000),(12738603503017709/100000000000000000),25⟩
theorem inputs_valid957 : inputs957.Valid := by decide +kernel
def envelope957 : RatMajorityEnvelope := ⟨457,1,inputs957,1,(275710003394525639/500000000000000000)⟩
theorem envelope_sound957 : envelope957.Sound := by
  apply rat_majority_inputs_envelopes inputs957 inputs_valid957
  · norm_num [envelope957]
  · intro rho hr0 hr1
    have hh := Batch047.bound1914 rho hr0 hr1
    norm_num [Batch047.certificate1914,envelope957,inputs957,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch047.bound1915 rho hr0 hr1
    norm_num [Batch047.certificate1915,envelope957,inputs957,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs958 : RatMajorityInputs := ⟨(1707096871094615169326297/20000000000000000000),(2147151337/500000000),(500017574175569267/500000000000000000),(24758807577563663/125000000000000000),(2147151337/1000000000),(58408227480235303/500000000000000000),25⟩
theorem inputs_valid958 : inputs958.Valid := by decide +kernel
def envelope958 : RatMajorityEnvelope := ⟨457,2,inputs958,1,(17136877925796831/31250000000000000)⟩
theorem envelope_sound958 : envelope958.Sound := by
  apply rat_majority_inputs_envelopes inputs958 inputs_valid958
  · norm_num [envelope958]
  · intro rho hr0 hr1
    have hh := Batch047.bound1916 rho hr0 hr1
    norm_num [Batch047.certificate1916,envelope958,inputs958,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch047.bound1917 rho hr0 hr1
    norm_num [Batch047.certificate1917,envelope958,inputs958,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs959 : RatMajorityInputs := ⟨(1672939453204846809210573/20000000000000000000),(276891711/62500000),(250008966504081883/250000000000000000),(45393689096929489/250000000000000000),(276891711/125000000),(109138922708829803/1000000000000000000),26⟩
theorem inputs_valid959 : inputs959.Valid := by decide +kernel
def envelope959 : RatMajorityEnvelope := ⟨458,0,inputs959,(565859309/470000000),(725057669527114933/1000000000000000000)⟩
theorem envelope_sound959 : envelope959.Sound := by
  apply rat_majority_inputs_envelopes inputs959 inputs_valid959
  · norm_num [envelope959]
  · intro rho hr0 hr1
    have hh := Batch047.bound1918 rho hr0 hr1
    norm_num [Batch047.certificate1918,envelope959,inputs959,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch047.bound1919 rho hr0 hr1
    norm_num [Batch047.certificate1919,envelope959,inputs959,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope940,envelope941,envelope942,envelope943,envelope944,envelope945,envelope946,envelope947,envelope948,envelope949,envelope950,envelope951,envelope952,envelope953,envelope954,envelope955,envelope956,envelope957,envelope958,envelope959]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound940
  · exact envelope_sound941
  · exact envelope_sound942
  · exact envelope_sound943
  · exact envelope_sound944
  · exact envelope_sound945
  · exact envelope_sound946
  · exact envelope_sound947
  · exact envelope_sound948
  · exact envelope_sound949
  · exact envelope_sound950
  · exact envelope_sound951
  · exact envelope_sound952
  · exact envelope_sound953
  · exact envelope_sound954
  · exact envelope_sound955
  · exact envelope_sound956
  · exact envelope_sound957
  · exact envelope_sound958
  · exact envelope_sound959

end Cycle12.MajorityCertificates.Inputs047
