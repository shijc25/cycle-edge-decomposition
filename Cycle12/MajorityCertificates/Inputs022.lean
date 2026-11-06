import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch022

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs022

def inputs440 : RatMajorityInputs := ⟨(1403103043436268142643949/1562500000000000000000),(113694379101687/25000000000000),(1003349511063246311/1000000000000000000),(168275271425760267/1000000000000000000),(113694379101687/50000000000000),(51455662595467059/500000000000000000),26⟩
theorem inputs_valid440 : inputs440.Valid := by decide +kernel
def envelope440 : RatMajorityEnvelope := ⟨220,0,inputs440,(1213821843/1041340000),(4319391409990637/6250000000000000)⟩
theorem envelope_sound440 : envelope440.Sound := by
  apply rat_majority_inputs_envelopes inputs440 inputs_valid440
  · norm_num [envelope440]
  · intro rho hr0 hr1
    have hh := Batch022.bound880 rho hr0 hr1
    norm_num [Batch022.certificate880,envelope440,inputs440,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch022.bound881 rho hr0 hr1
    norm_num [Batch022.certificate881,envelope440,inputs440,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs441 : RatMajorityInputs := ⟨(1403103043436268142643949/1562500000000000000000),(25463639649683/5000000000000),(1003349511063246311/1000000000000000000),(3658006507192747/31250000000000000),(25463639649683/10000000000000),(1959152261233423/25000000000000000),26⟩
theorem inputs_valid441 : inputs441.Valid := by decide +kernel
def envelope441 : RatMajorityEnvelope := ⟨220,1,inputs441,1,(67556581733346349/125000000000000000)⟩
theorem envelope_sound441 : envelope441.Sound := by
  apply rat_majority_inputs_envelopes inputs441 inputs_valid441
  · norm_num [envelope441]
  · intro rho hr0 hr1
    have hh := Batch022.bound882 rho hr0 hr1
    norm_num [Batch022.certificate882,envelope441,inputs441,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch022.bound883 rho hr0 hr1
    norm_num [Batch022.certificate883,envelope441,inputs441,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs442 : RatMajorityInputs := ⟨(17405843363478569910954431/20000000000000000000000),(91268854259931/20000000000000),(50172819154152491/50000000000000000),(83283436656681003/500000000000000000),(91268854259931/40000000000000),(4084331623290559/40000000000000000),25⟩
theorem inputs_valid442 : inputs442.Valid := by decide +kernel
def envelope442 : RatMajorityEnvelope := ⟨221,0,inputs442,(605030463/519762500),(689580742084930241/1000000000000000000)⟩
theorem envelope_sound442 : envelope442.Sound := by
  apply rat_majority_inputs_envelopes inputs442 inputs_valid442
  · norm_num [envelope442]
  · intro rho hr0 hr1
    have hh := Batch022.bound884 rho hr0 hr1
    norm_num [Batch022.certificate884,envelope442,inputs442,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch022.bound885 rho hr0 hr1
    norm_num [Batch022.certificate885,envelope442,inputs442,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs443 : RatMajorityInputs := ⟨(17405843363478569910954431/20000000000000000000000),(2040124736889/400000000000),(50172819154152491/50000000000000000),(116453620072321409/1000000000000000000),(2040124736889/800000000000),(15613898474021941/200000000000000000),27⟩
theorem inputs_valid443 : inputs443.Valid := by decide +kernel
def envelope443 : RatMajorityEnvelope := ⟨221,1,inputs443,1,(270219997706550467/500000000000000000)⟩
theorem envelope_sound443 : envelope443.Sound := by
  apply rat_majority_inputs_envelopes inputs443 inputs_valid443
  · norm_num [envelope443]
  · intro rho hr0 hr1
    have hh := Batch022.bound886 rho hr0 hr1
    norm_num [Batch022.certificate886,envelope443,inputs443,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch022.bound887 rho hr0 hr1
    norm_num [Batch022.certificate887,envelope443,inputs443,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs444 : RatMajorityInputs := ⟨(42475253004635966883193811/50000000000000000000000),(91643674080903/20000000000000),(1003541192477395193/1000000000000000000),(164542999917904463/1000000000000000000),(91643674080903/40000000000000),(101155954202668863/1000000000000000000),26⟩
theorem inputs_valid444 : inputs444.Valid := by decide +kernel
def envelope444 : RatMajorityEnvelope := ⟨222,0,inputs444,(2412021201/2076710000),(687112301972079277/1000000000000000000)⟩
theorem envelope_sound444 : envelope444.Sound := by
  apply rat_majority_inputs_envelopes inputs444 inputs_valid444
  · norm_num [envelope444]
  · intro rho hr0 hr1
    have hh := Batch022.bound888 rho hr0 hr1
    norm_num [Batch022.certificate888,envelope444,inputs444,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch022.bound889 rho hr0 hr1
    norm_num [Batch022.certificate889,envelope444,inputs444,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs445 : RatMajorityInputs := ⟨(42475253004635966883193811/50000000000000000000000),(510765986132173/100000000000000),(1003541192477395193/1000000000000000000),(115872418741966103/1000000000000000000),(510765986132173/200000000000000),(77783190569433201/1000000000000000000),26⟩
theorem inputs_valid445 : inputs445.Valid := by decide +kernel
def envelope445 : RatMajorityEnvelope := ⟨222,1,inputs445,1,(270209718432302693/500000000000000000)⟩
theorem envelope_sound445 : envelope445.Sound := by
  apply rat_majority_inputs_envelopes inputs445 inputs_valid445
  · norm_num [envelope445]
  · intro rho hr0 hr1
    have hh := Batch022.bound890 rho hr0 hr1
    norm_num [Batch022.certificate890,envelope445,inputs445,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch022.bound891 rho hr0 hr1
    norm_num [Batch022.certificate891,envelope445,inputs445,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs446 : RatMajorityInputs := ⟨(82985040175926169118941149/100000000000000000000000),(230030411255781/50000000000000),(1003625300518014481/1000000000000000000),(162574029684375041/1000000000000000000),(230030411255781/100000000000000),(100228358385118081/1000000000000000000),25⟩
theorem inputs_valid446 : inputs446.Valid := by decide +kernel
def envelope446 : RatMajorityEnvelope := ⟨223,0,inputs446,(1202015249/1037235000),(684641862048884403/1000000000000000000)⟩
theorem envelope_sound446 : envelope446.Sound := by
  apply rat_majority_inputs_envelopes inputs446 inputs_valid446
  · norm_num [envelope446]
  · intro rho hr0 hr1
    have hh := Batch022.bound892 rho hr0 hr1
    norm_num [Batch022.certificate892,envelope446,inputs446,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch022.bound893 rho hr0 hr1
    norm_num [Batch022.certificate893,envelope446,inputs446,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs447 : RatMajorityInputs := ⟨(82985040175926169118941149/100000000000000000000000),(102469471890309/20000000000000),(1003625300518014481/1000000000000000000),(114630392275135481/1000000000000000000),(102469471890309/40000000000000),(77170594308129119/1000000000000000000),26⟩
theorem inputs_valid447 : inputs447.Valid := by decide +kernel
def envelope447 : RatMajorityEnvelope := ⟨223,1,inputs447,1,(540330690158854977/1000000000000000000)⟩
theorem envelope_sound447 : envelope447.Sound := by
  apply rat_majority_inputs_envelopes inputs447 inputs_valid447
  · norm_num [envelope447]
  · intro rho hr0 hr1
    have hh := Batch022.bound894 rho hr0 hr1
    norm_num [Batch022.certificate894,envelope447,inputs447,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch022.bound895 rho hr0 hr1
    norm_num [Batch022.certificate895,envelope447,inputs447,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs448 : RatMajorityInputs := ⟨(82586804792816642393579949/100000000000000000000000),(92556372936143/20000000000000),(40145713252148057/40000000000000000),(9981462883154767/62500000000000000),(92556372936143/40000000000000),(772452849482947/7812500000000000),25⟩
theorem inputs_valid448 : inputs448.Valid := by decide +kernel
def envelope448 : RatMajorityEnvelope := ⟨224,0,inputs448,(299984213/259328750),(136501593886747567/200000000000000000)⟩
theorem envelope_sound448 : envelope448.Sound := by
  apply rat_majority_inputs_envelopes inputs448 inputs_valid448
  · norm_num [envelope448]
  · intro rho hr0 hr1
    have hh := Batch022.bound896 rho hr0 hr1
    norm_num [Batch022.certificate896,envelope448,inputs448,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch022.bound897 rho hr0 hr1
    norm_num [Batch022.certificate897,envelope448,inputs448,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs449 : RatMajorityInputs := ⟨(82586804792816642393579949/100000000000000000000000),(514131570799589/100000000000000),(40145713252148057/40000000000000000),(7077709829431819/62500000000000000),(514131570799589/200000000000000),(76485212766954497/1000000000000000000),27⟩
theorem inputs_valid449 : inputs449.Valid := by decide +kernel
def envelope449 : RatMajorityEnvelope := ⟨224,1,inputs449,1,(270098254027137529/500000000000000000)⟩
theorem envelope_sound449 : envelope449.Sound := by
  apply rat_majority_inputs_envelopes inputs449 inputs_valid449
  · norm_num [envelope449]
  · intro rho hr0 hr1
    have hh := Batch022.bound898 rho hr0 hr1
    norm_num [Batch022.certificate898,envelope449,inputs449,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch022.bound899 rho hr0 hr1
    norm_num [Batch022.certificate899,envelope449,inputs449,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs450 : RatMajorityInputs := ⟨(40833460707369826170247767/50000000000000000000000),(46402246962187/10000000000000),(125460497637424747/125000000000000000),(158409239399218783/1000000000000000000),(46402246962187/20000000000000),(98262545373006009/1000000000000000000),26⟩
theorem inputs_valid450 : inputs450.Valid := by decide +kernel
def envelope450 : RatMajorityEnvelope := ⟨225,0,inputs450,(2395013701/2073580000),(42552020310731221/62500000000000000)⟩
theorem envelope_sound450 : envelope450.Sound := by
  apply rat_majority_inputs_envelopes inputs450 inputs_valid450
  · norm_num [envelope450]
  · intro rho hr0 hr1
    have hh := Batch022.bound900 rho hr0 hr1
    norm_num [Batch022.certificate900,envelope450,inputs450,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch022.bound901 rho hr0 hr1
    norm_num [Batch022.certificate901,envelope450,inputs450,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs451 : RatMajorityInputs := ⟨(40833460707369826170247767/50000000000000000000000),(257377025010923/50000000000000),(125460497637424747/125000000000000000),(112762990963032909/1000000000000000000),(257377025010923/100000000000000),(76247530560624293/1000000000000000000),27⟩
theorem inputs_valid451 : inputs451.Valid := by decide +kernel
def envelope451 : RatMajorityEnvelope := ⟨225,1,inputs451,1,(33760409422890077/62500000000000000)⟩
theorem envelope_sound451 : envelope451.Sound := by
  apply rat_majority_inputs_envelopes inputs451 inputs_valid451
  · norm_num [envelope451]
  · intro rho hr0 hr1
    have hh := Batch022.bound902 rho hr0 hr1
    norm_num [Batch022.certificate902,envelope451,inputs451,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch022.bound903 rho hr0 hr1
    norm_num [Batch022.certificate903,envelope451,inputs451,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs452 : RatMajorityInputs := ⟨(504824338056854324669037/625000000000000000000),(18505195962303/4000000000000),(1003724921230936827/1000000000000000000),(159862560767786823/1000000000000000000),(18505195962303/8000000000000),(19789824100249883/200000000000000000),26⟩
theorem inputs_valid452 : inputs452.Valid := by decide +kernel
def envelope452 : RatMajorityEnvelope := ⟨226,0,inputs452,(3987939/3454250),(680526454747379423/1000000000000000000)⟩
theorem envelope_sound452 : envelope452.Sound := by
  apply rat_majority_inputs_envelopes inputs452 inputs_valid452
  · norm_num [envelope452]
  · intro rho hr0 hr1
    have hh := Batch022.bound904 rho hr0 hr1
    norm_num [Batch022.certificate904,envelope452,inputs452,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch022.bound905 rho hr0 hr1
    norm_num [Batch022.certificate905,envelope452,inputs452,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs453 : RatMajorityInputs := ⟨(504824338056854324669037/625000000000000000000),(103135913647893/20000000000000),(1003724921230936827/1000000000000000000),(4482085681275073/40000000000000000),(103135913647893/40000000000000),(75895503314994993/1000000000000000000),27⟩
theorem inputs_valid453 : inputs453.Valid := by decide +kernel
def envelope453 : RatMajorityEnvelope := ⟨226,1,inputs453,1,(270056518064326981/500000000000000000)⟩
theorem envelope_sound453 : envelope453.Sound := by
  apply rat_majority_inputs_envelopes inputs453 inputs_valid453
  · norm_num [envelope453]
  · intro rho hr0 hr1
    have hh := Batch022.bound906 rho hr0 hr1
    norm_num [Batch022.certificate906,envelope453,inputs453,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch022.bound907 rho hr0 hr1
    norm_num [Batch022.certificate907,envelope453,inputs453,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs454 : RatMajorityInputs := ⟨(7990135415467242959536927/10000000000000000000000),(46286186239111/10000000000000),(125470702967251849/125000000000000000),(39904919784891673/250000000000000000),(46286186239111/20000000000000),(9883442418824527/100000000000000000),26⟩
theorem inputs_valid454 : inputs454.Valid := by decide +kernel
def envelope454 : RatMajorityEnvelope := ⟨227,0,inputs454,(1194132047/1035775000),(169768855876873601/250000000000000000)⟩
theorem envelope_sound454 : envelope454.Sound := by
  apply rat_majority_inputs_envelopes inputs454 inputs_valid454
  · norm_num [envelope454]
  · intro rho hr0 hr1
    have hh := Batch022.bound908 rho hr0 hr1
    norm_num [Batch022.certificate908,envelope454,inputs454,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch022.bound909 rho hr0 hr1
    norm_num [Batch022.certificate909,envelope454,inputs454,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs455 : RatMajorityInputs := ⟨(7990135415467242959536927/10000000000000000000000),(25814917343839/5000000000000),(125470702967251849/125000000000000000),(111579127188652589/1000000000000000000),(25814917343839/10000000000000),(18915263400649263/250000000000000000),27⟩
theorem inputs_valid455 : inputs455.Valid := by decide +kernel
def envelope455 : RatMajorityEnvelope := ⟨227,1,inputs455,1,(270041907150661391/500000000000000000)⟩
theorem envelope_sound455 : envelope455.Sound := by
  apply rat_majority_inputs_envelopes inputs455 inputs_valid455
  · norm_num [envelope455]
  · intro rho hr0 hr1
    have hh := Batch022.bound910 rho hr0 hr1
    norm_num [Batch022.certificate910,envelope455,inputs455,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch022.bound911 rho hr0 hr1
    norm_num [Batch022.certificate911,envelope455,inputs455,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs456 : RatMajorityInputs := ⟨(39527092269869298685977753/50000000000000000000000),(464460406693857/100000000000000),(1003806096752928541/1000000000000000000),(7897728556192793/50000000000000000),(464460406693857/200000000000000),(19609523342983547/200000000000000000),27⟩
theorem inputs_valid456 : inputs456.Valid := by decide +kernel
def envelope456 : RatMajorityEnvelope := ⟨228,0,inputs456,(596281133/517642500),(135614873992521279/200000000000000000)⟩
theorem envelope_sound456 : envelope456.Sound := by
  apply rat_majority_inputs_envelopes inputs456 inputs_valid456
  · norm_num [envelope456]
  · intro rho hr0 hr1
    have hh := Batch022.bound912 rho hr0 hr1
    norm_num [Batch022.certificate912,envelope456,inputs456,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch022.bound913 rho hr0 hr1
    norm_num [Batch022.certificate913,envelope456,inputs456,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs457 : RatMajorityInputs := ⟨(39527092269869298685977753/50000000000000000000000),(129162579203337/25000000000000),(1003806096752928541/1000000000000000000),(111310868620056253/1000000000000000000),(129162579203337/50000000000000),(18882004654133773/250000000000000000),27⟩
theorem inputs_valid457 : inputs457.Valid := by decide +kernel
def envelope457 : RatMajorityEnvelope := ⟨228,1,inputs457,1,(540075416770798237/1000000000000000000)⟩
theorem envelope_sound457 : envelope457.Sound := by
  apply rat_majority_inputs_envelopes inputs457 inputs_valid457
  · norm_num [envelope457]
  · intro rho hr0 hr1
    have hh := Batch022.bound914 rho hr0 hr1
    norm_num [Batch022.certificate914,envelope457,inputs457,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch022.bound915 rho hr0 hr1
    norm_num [Batch022.certificate915,envelope457,inputs457,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs458 : RatMajorityInputs := ⟨(19557422841654091042252221/25000000000000000000000),(14563027867089/3125000000000),(50192316531731491/50000000000000000),(39086942830378247/250000000000000000),(14563027867089/6250000000000),(97287529960895679/1000000000000000000),26⟩
theorem inputs_valid458 : inputs458.Valid := by decide +kernel
def envelope458 : RatMajorityEnvelope := ⟨229,0,inputs458,(238030463/206961000),(676338450161962633/1000000000000000000)⟩
theorem envelope_sound458 : envelope458.Sound := by
  apply rat_majority_inputs_envelopes inputs458 inputs_valid458
  · norm_num [envelope458]
  · intro rho hr0 hr1
    have hh := Batch022.bound916 rho hr0 hr1
    norm_num [Batch022.certificate916,envelope458,inputs458,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch022.bound917 rho hr0 hr1
    norm_num [Batch022.certificate917,envelope458,inputs458,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs459 : RatMajorityInputs := ⟨(19557422841654091042252221/25000000000000000000000),(517951743242889/100000000000000),(50192316531731491/50000000000000000),(110323981664402653/1000000000000000000),(517951743242889/200000000000000),(75038143388520171/1000000000000000000),27⟩
theorem inputs_valid459 : inputs459.Valid := by decide +kernel
def envelope459 : RatMajorityEnvelope := ⟨229,1,inputs459,1,(539993860959519651/1000000000000000000)⟩
theorem envelope_sound459 : envelope459.Sound := by
  apply rat_majority_inputs_envelopes inputs459 inputs_valid459
  · norm_num [envelope459]
  · intro rho hr0 hr1
    have hh := Batch022.bound918 rho hr0 hr1
    norm_num [Batch022.certificate918,envelope459,inputs459,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch022.bound919 rho hr0 hr1
    norm_num [Batch022.certificate919,envelope459,inputs459,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope440,envelope441,envelope442,envelope443,envelope444,envelope445,envelope446,envelope447,envelope448,envelope449,envelope450,envelope451,envelope452,envelope453,envelope454,envelope455,envelope456,envelope457,envelope458,envelope459]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound440
  · exact envelope_sound441
  · exact envelope_sound442
  · exact envelope_sound443
  · exact envelope_sound444
  · exact envelope_sound445
  · exact envelope_sound446
  · exact envelope_sound447
  · exact envelope_sound448
  · exact envelope_sound449
  · exact envelope_sound450
  · exact envelope_sound451
  · exact envelope_sound452
  · exact envelope_sound453
  · exact envelope_sound454
  · exact envelope_sound455
  · exact envelope_sound456
  · exact envelope_sound457
  · exact envelope_sound458
  · exact envelope_sound459

end Cycle12.MajorityCertificates.Inputs022
