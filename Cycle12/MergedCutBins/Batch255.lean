import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch348
import Cycle12.MergedCutProfiles.Batch349
import Cycle12.MergedCutProfiles.Batch350
import Cycle12.MergedCutProfiles.Batch471
import Cycle12.MergedCutProfiles.Batch472

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch255

def retention3060 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(32000000000000000000/88221878646497850223),(4908142808574272397/500000000000000000),1,(5410031408851323312012398090361775607/4362793607621575464000000000000000000),false,MergedCutProfiles.Batch471.profile18864,(fun _ => MergedCutProfiles.Batch471.profile18864)⟩
theorem profilesValid3060 : retention3060.ProfilesValid := by
  exact MergedCutProfiles.Batch471.valid18864
theorem numericValid3060 : retention3060.NumericValid := by decide +kernel
def certificate3060 : RatCutBinCertificate := ⟨⟨retention3060,(2114609507369050987/1000000000000000000),(65254397982896969/1000000000000000000),(10848174231108216483/1000000000000000000),(1924254854081980321927/1000000000000000000),(38353700697434587/31250000000000000)⟩,(249742172540852081/250000000000000000),(840481789046831/8000000000000000),(81905042901057109/125000000000000000),(714042936631528481/1000000000000000000)⟩
theorem valid3060 : certificate3060.Valid := by decide +kernel
theorem sound3060 : certificate3060.Sound := rat_cut_bin_certificate_sound certificate3060 profilesValid3060 numericValid3060 valid3060

def retention3061 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(1/2),64,1,(255381539274569722621815190999861472551/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch348.profile13941,(fun _ => MergedCutProfiles.Batch348.profile13941)⟩
theorem profilesValid3061 : retention3061.ProfilesValid := by
  exact MergedCutProfiles.Batch348.valid13941
theorem numericValid3061 : retention3061.NumericValid := by decide +kernel
def certificate3061 : RatCutBinCertificate := ⟨⟨retention3061,(2114609507369050987/1000000000000000000),(65254397982896969/1000000000000000000),(10848174231108216483/1000000000000000000),(1924254854081980321927/1000000000000000000),(196972848441629779/200000000000000000)⟩,(249742172540852081/250000000000000000),(65461990794734511/500000000000000000),(300649480354194679/500000000000000000),(582616465674106629/1000000000000000000)⟩
theorem valid3061 : certificate3061.Valid := by decide +kernel
theorem sound3061 : certificate3061.Sound := rat_cut_bin_certificate_sound certificate3061 profilesValid3061 numericValid3061 valid3061

def retention3062 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(347910122393387419/83310645544398190007),(344465467716225167/500000000000000000),(79/20),(1489771450900740782671/640000000000000000000),true,MergedCutProfiles.Batch471.profile18865,![MergedCutProfiles.Batch471.profile18865,MergedCutProfiles.Batch471.profile18866,MergedCutProfiles.Batch471.profile18867,MergedCutProfiles.Batch471.profile18868,MergedCutProfiles.Batch471.profile18869,MergedCutProfiles.Batch471.profile18870,MergedCutProfiles.Batch471.profile18871,MergedCutProfiles.Batch471.profile18872,MergedCutProfiles.Batch471.profile18873,MergedCutProfiles.Batch349.profile13963,MergedCutProfiles.Batch348.profile13948,MergedCutProfiles.Batch471.profile18874,MergedCutProfiles.Batch471.profile18875,MergedCutProfiles.Batch471.profile18876,MergedCutProfiles.Batch471.profile18877,MergedCutProfiles.Batch471.profile18878]⟩
theorem profilesValid3062 : retention3062.ProfilesValid := by
  change ∀ j : Fin 16, (retention3062.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch471.valid18865
  · exact MergedCutProfiles.Batch471.valid18866
  · exact MergedCutProfiles.Batch471.valid18867
  · exact MergedCutProfiles.Batch471.valid18868
  · exact MergedCutProfiles.Batch471.valid18869
  · exact MergedCutProfiles.Batch471.valid18870
  · exact MergedCutProfiles.Batch471.valid18871
  · exact MergedCutProfiles.Batch471.valid18872
  · exact MergedCutProfiles.Batch471.valid18873
  · exact MergedCutProfiles.Batch349.valid13963
  · exact MergedCutProfiles.Batch348.valid13948
  · exact MergedCutProfiles.Batch471.valid18874
  · exact MergedCutProfiles.Batch471.valid18875
  · exact MergedCutProfiles.Batch471.valid18876
  · exact MergedCutProfiles.Batch471.valid18877
  · exact MergedCutProfiles.Batch471.valid18878
theorem numericValid3062 : retention3062.NumericValid := by decide +kernel
def certificate3062 : RatCutBinCertificate := ⟨⟨retention3062,(986718527482828073/500000000000000000),(69043717129131353/1000000000000000000),(11012437943120596923/1000000000000000000),(1844708507240218827801/1000000000000000000),(2278895112653650071/1000000000000000000)⟩,(499499977693425231/500000000000000000),(494638789227024993/1000000000000000000),(78585651207861119/500000000000000000),(18682015347473523/250000000000000000)⟩
theorem valid3062 : certificate3062.Valid := by decide +kernel
theorem sound3062 : certificate3062.Sound := rat_cut_bin_certificate_sound certificate3062 profilesValid3062 numericValid3062 valid3062

def retention3063 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(966278675097830285/166621291088796380014),(347910122393387419/500000000000000000),(39/10),(1478825847700709434719/640000000000000000000),true,MergedCutProfiles.Batch471.profile18879,![MergedCutProfiles.Batch471.profile18879,MergedCutProfiles.Batch472.profile18880,MergedCutProfiles.Batch472.profile18881,MergedCutProfiles.Batch348.profile13946,MergedCutProfiles.Batch471.profile18871,MergedCutProfiles.Batch472.profile18882,MergedCutProfiles.Batch472.profile18883,MergedCutProfiles.Batch472.profile18884,MergedCutProfiles.Batch350.profile14005,MergedCutProfiles.Batch471.profile18876,MergedCutProfiles.Batch349.profile13979,MergedCutProfiles.Batch472.profile18885,MergedCutProfiles.Batch472.profile18886,MergedCutProfiles.Batch472.profile18887,MergedCutProfiles.Batch472.profile18888,MergedCutProfiles.Batch472.profile18889]⟩
theorem profilesValid3063 : retention3063.ProfilesValid := by
  change ∀ j : Fin 16, (retention3063.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch471.valid18879
  · exact MergedCutProfiles.Batch472.valid18880
  · exact MergedCutProfiles.Batch472.valid18881
  · exact MergedCutProfiles.Batch348.valid13946
  · exact MergedCutProfiles.Batch471.valid18871
  · exact MergedCutProfiles.Batch472.valid18882
  · exact MergedCutProfiles.Batch472.valid18883
  · exact MergedCutProfiles.Batch472.valid18884
  · exact MergedCutProfiles.Batch350.valid14005
  · exact MergedCutProfiles.Batch471.valid18876
  · exact MergedCutProfiles.Batch349.valid13979
  · exact MergedCutProfiles.Batch472.valid18885
  · exact MergedCutProfiles.Batch472.valid18886
  · exact MergedCutProfiles.Batch472.valid18887
  · exact MergedCutProfiles.Batch472.valid18888
  · exact MergedCutProfiles.Batch472.valid18889
theorem numericValid3063 : retention3063.NumericValid := by decide +kernel
def certificate3063 : RatCutBinCertificate := ⟨⟨retention3063,(986718527482828073/500000000000000000),(69043717129131353/1000000000000000000),(11012437943120596923/1000000000000000000),(1844708507240218827801/1000000000000000000),(2262411248577191113/1000000000000000000)⟩,(499499977693425231/500000000000000000),(495343125428956777/1000000000000000000),(156676003526974491/1000000000000000000),(9349153651384941/125000000000000000)⟩
theorem valid3063 : certificate3063.Valid := by decide +kernel
theorem sound3063 : certificate3063.Sound := rat_cut_bin_certificate_sound certificate3063 profilesValid3063 numericValid3063 valid3063

def retention3064 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(563714492500000000/83310645544398190007),(193255735019566057/200000000000000000),(59/20),(585500660418182657593/256000000000000000000),true,MergedCutProfiles.Batch472.profile18890,![MergedCutProfiles.Batch472.profile18890,MergedCutProfiles.Batch472.profile18891,MergedCutProfiles.Batch472.profile18892,MergedCutProfiles.Batch349.profile13962,MergedCutProfiles.Batch348.profile13947,MergedCutProfiles.Batch472.profile18883,MergedCutProfiles.Batch349.profile13978,MergedCutProfiles.Batch471.profile18875,MergedCutProfiles.Batch472.profile18893,MergedCutProfiles.Batch348.profile13950,MergedCutProfiles.Batch472.profile18894,MergedCutProfiles.Batch472.profile18887,MergedCutProfiles.Batch472.profile18888,MergedCutProfiles.Batch472.profile18895,MergedCutProfiles.Batch348.profile13953,MergedCutProfiles.Batch472.profile18896]⟩
theorem profilesValid3064 : retention3064.ProfilesValid := by
  change ∀ j : Fin 16, (retention3064.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch472.valid18890
  · exact MergedCutProfiles.Batch472.valid18891
  · exact MergedCutProfiles.Batch472.valid18892
  · exact MergedCutProfiles.Batch349.valid13962
  · exact MergedCutProfiles.Batch348.valid13947
  · exact MergedCutProfiles.Batch472.valid18883
  · exact MergedCutProfiles.Batch349.valid13978
  · exact MergedCutProfiles.Batch471.valid18875
  · exact MergedCutProfiles.Batch472.valid18893
  · exact MergedCutProfiles.Batch348.valid13950
  · exact MergedCutProfiles.Batch472.valid18894
  · exact MergedCutProfiles.Batch472.valid18887
  · exact MergedCutProfiles.Batch472.valid18888
  · exact MergedCutProfiles.Batch472.valid18895
  · exact MergedCutProfiles.Batch348.valid13953
  · exact MergedCutProfiles.Batch472.valid18896
theorem numericValid3064 : retention3064.NumericValid := by decide +kernel
def certificate3064 : RatCutBinCertificate := ⟨⟨retention3064,(986718527482828073/500000000000000000),(69043717129131353/1000000000000000000),(11012437943120596923/1000000000000000000),(1844708507240218827801/1000000000000000000),(450122410736015113/200000000000000000)⟩,(499499977693425231/500000000000000000),(4163559788212019/10000000000000000),(109412995987756393/500000000000000000),(65772853476802747/500000000000000000)⟩
theorem valid3064 : certificate3064.Valid := by decide +kernel
theorem sound3064 : certificate3064.Sound := rat_cut_bin_certificate_sound certificate3064 profilesValid3064 numericValid3064 valid3064

def retention3065 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(1144368116859529399/166621291088796380014),(225485797/200000000),(13/5),(36432681101901611579/16000000000000000000),true,MergedCutProfiles.Batch472.profile18890,![MergedCutProfiles.Batch472.profile18890,MergedCutProfiles.Batch349.profile13961,MergedCutProfiles.Batch471.profile18869,MergedCutProfiles.Batch349.profile13962,MergedCutProfiles.Batch348.profile13947,MergedCutProfiles.Batch472.profile18883,MergedCutProfiles.Batch472.profile18897,MergedCutProfiles.Batch349.profile13964,MergedCutProfiles.Batch472.profile18898,MergedCutProfiles.Batch349.profile13965,MergedCutProfiles.Batch472.profile18886,MergedCutProfiles.Batch349.profile13992,MergedCutProfiles.Batch472.profile18899,MergedCutProfiles.Batch349.profile13967,MergedCutProfiles.Batch472.profile18900,MergedCutProfiles.Batch349.profile13968]⟩
theorem profilesValid3065 : retention3065.ProfilesValid := by
  change ∀ j : Fin 16, (retention3065.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch472.valid18890
  · exact MergedCutProfiles.Batch349.valid13961
  · exact MergedCutProfiles.Batch471.valid18869
  · exact MergedCutProfiles.Batch349.valid13962
  · exact MergedCutProfiles.Batch348.valid13947
  · exact MergedCutProfiles.Batch472.valid18883
  · exact MergedCutProfiles.Batch472.valid18897
  · exact MergedCutProfiles.Batch349.valid13964
  · exact MergedCutProfiles.Batch472.valid18898
  · exact MergedCutProfiles.Batch349.valid13965
  · exact MergedCutProfiles.Batch472.valid18886
  · exact MergedCutProfiles.Batch349.valid13992
  · exact MergedCutProfiles.Batch472.valid18899
  · exact MergedCutProfiles.Batch349.valid13967
  · exact MergedCutProfiles.Batch472.valid18900
  · exact MergedCutProfiles.Batch349.valid13968
theorem numericValid3065 : retention3065.NumericValid := by decide +kernel
def certificate3065 : RatCutBinCertificate := ⟨⟨retention3065,(986718527482828073/500000000000000000),(69043717129131353/1000000000000000000),(11012437943120596923/1000000000000000000),(1844708507240218827801/1000000000000000000),(448974635234074089/200000000000000000)⟩,(499499977693425231/500000000000000000),(387342111335291003/1000000000000000000),(245282472001030831/1000000000000000000),(163405226375859363/1000000000000000000)⟩
theorem valid3065 : certificate3065.Valid := by decide +kernel
theorem sound3065 : certificate3065.Sound := rat_cut_bin_certificate_sound certificate3065 profilesValid3065 numericValid3065 valid3065

def retention3066 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(1589172657835037085/166621291088796380014),(1144368116859529399/1000000000000000000),(51/20),(2883287299835830730823/1280000000000000000000),true,MergedCutProfiles.Batch472.profile18901,![MergedCutProfiles.Batch472.profile18901,MergedCutProfiles.Batch472.profile18902,MergedCutProfiles.Batch472.profile18903,MergedCutProfiles.Batch472.profile18904,MergedCutProfiles.Batch349.profile13978,MergedCutProfiles.Batch348.profile13949,MergedCutProfiles.Batch471.profile18878,MergedCutProfiles.Batch472.profile18905,MergedCutProfiles.Batch472.profile18906,MergedCutProfiles.Batch349.profile13967,MergedCutProfiles.Batch350.profile14007,MergedCutProfiles.Batch349.profile13994,MergedCutProfiles.Batch349.profile13969,MergedCutProfiles.Batch472.profile18907,MergedCutProfiles.Batch349.profile13982,MergedCutProfiles.Batch472.profile18908]⟩
theorem profilesValid3066 : retention3066.ProfilesValid := by
  change ∀ j : Fin 16, (retention3066.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch472.valid18901
  · exact MergedCutProfiles.Batch472.valid18902
  · exact MergedCutProfiles.Batch472.valid18903
  · exact MergedCutProfiles.Batch472.valid18904
  · exact MergedCutProfiles.Batch349.valid13978
  · exact MergedCutProfiles.Batch348.valid13949
  · exact MergedCutProfiles.Batch471.valid18878
  · exact MergedCutProfiles.Batch472.valid18905
  · exact MergedCutProfiles.Batch472.valid18906
  · exact MergedCutProfiles.Batch349.valid13967
  · exact MergedCutProfiles.Batch350.valid14007
  · exact MergedCutProfiles.Batch349.valid13994
  · exact MergedCutProfiles.Batch349.valid13969
  · exact MergedCutProfiles.Batch472.valid18907
  · exact MergedCutProfiles.Batch349.valid13982
  · exact MergedCutProfiles.Batch472.valid18908
theorem numericValid3066 : retention3066.NumericValid := by decide +kernel
def certificate3066 : RatCutBinCertificate := ⟨⟨retention3066,(986718527482828073/500000000000000000),(69043717129131353/1000000000000000000),(11012437943120596923/1000000000000000000),(1844708507240218827801/1000000000000000000),(1110508725323260359/500000000000000000)⟩,(499499977693425231/500000000000000000),(12150131903676809/31250000000000000),(121949289222584921/500000000000000000),(163413126571112413/1000000000000000000)⟩
theorem valid3066 : certificate3066.Valid := by decide +kernel
theorem sound3066 : certificate3066.Sound := rat_cut_bin_certificate_sound certificate3066 profilesValid3066 numericValid3066 valid3066

def retention3067 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(16969070131101906431/166621291088796380014),(317834531567007417/200000000000000000),(21/10),(48331270057403906400886546252495747079/25426762525360593360000000000000000000),false,MergedCutProfiles.Batch472.profile18909,(fun _ => MergedCutProfiles.Batch472.profile18909)⟩
theorem profilesValid3067 : retention3067.ProfilesValid := by
  exact MergedCutProfiles.Batch472.valid18909
theorem numericValid3067 : retention3067.NumericValid := by decide +kernel
def certificate3067 : RatCutBinCertificate := ⟨⟨retention3067,(986718527482828073/500000000000000000),(69043717129131353/1000000000000000000),(11012437943120596923/1000000000000000000),(1844708507240218827801/1000000000000000000),(234352526211202897/125000000000000000)⟩,(499499977693425231/500000000000000000),(401049908525516803/1000000000000000000),(46504352084283109/200000000000000000),(40897463233060071/250000000000000000)⟩
theorem valid3067 : certificate3067.Valid := by decide +kernel
theorem sound3067 : certificate3067.Sound := rat_cut_bin_certificate_sound certificate3067 profilesValid3067 numericValid3067 valid3067

def retention3068 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(32000000000000000000/83310645544398190007),(16969070131101906431/1000000000000000000),1,(659649313528479901872217995999011343/543010244195261005792000000000000000),false,MergedCutProfiles.Batch472.profile18910,(fun _ => MergedCutProfiles.Batch472.profile18910)⟩
theorem profilesValid3068 : retention3068.ProfilesValid := by
  exact MergedCutProfiles.Batch472.valid18910
theorem numericValid3068 : retention3068.NumericValid := by decide +kernel
def certificate3068 : RatCutBinCertificate := ⟨⟨retention3068,(986718527482828073/500000000000000000),(69043717129131353/1000000000000000000),(11012437943120596923/1000000000000000000),(1844708507240218827801/1000000000000000000),(1202428150825882827/1000000000000000000)⟩,(499499977693425231/500000000000000000),(204404512770281491/500000000000000000),(45101469108310049/200000000000000000),(252952363142793793/1000000000000000000)⟩
theorem valid3068 : certificate3068.Valid := by decide +kernel
theorem sound3068 : certificate3068.Sound := rat_cut_bin_certificate_sound certificate3068 profilesValid3068 numericValid3068 valid3068

def retention3069 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(1/2),64,1,(63845591220989223006162834149049868551/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch350.profile14023,(fun _ => MergedCutProfiles.Batch350.profile14023)⟩
theorem profilesValid3069 : retention3069.ProfilesValid := by
  exact MergedCutProfiles.Batch350.valid14023
theorem numericValid3069 : retention3069.NumericValid := by decide +kernel
def certificate3069 : RatCutBinCertificate := ⟨⟨retention3069,(986718527482828073/500000000000000000),(69043717129131353/1000000000000000000),(11012437943120596923/1000000000000000000),(1844708507240218827801/1000000000000000000),(123151833778142039/125000000000000000)⟩,(499499977693425231/500000000000000000),(478876385099349417/1000000000000000000),(84260352363330673/500000000000000000),(163346993344587703/1000000000000000000)⟩
theorem valid3069 : certificate3069.Valid := by decide +kernel
theorem sound3069 : certificate3069.Sound := rat_cut_bin_certificate_sound certificate3069 profilesValid3069 numericValid3069 valid3069

def retention3070 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(32000000000000000000/83310645544398190007),(9821535649951716947/1000000000000000000),1,(47079945666289397590611745580573066211/39286142599806867788000000000000000000),false,MergedCutProfiles.Batch472.profile18910,(fun _ => MergedCutProfiles.Batch472.profile18910)⟩
theorem profilesValid3070 : retention3070.ProfilesValid := by
  exact MergedCutProfiles.Batch472.valid18910
theorem numericValid3070 : retention3070.NumericValid := by decide +kernel
def certificate3070 : RatCutBinCertificate := ⟨⟨retention3070,(1061052254982828073/500000000000000000),(69043717129131353/1000000000000000000),(11012437943120596923/1000000000000000000),(1844708507240218827801/1000000000000000000),(296270182032352949/250000000000000000)⟩,(199784922418507913/200000000000000000),(108987403487755051/1000000000000000000),(80841870303606873/125000000000000000),(341569962255728379/500000000000000000)⟩
theorem valid3070 : certificate3070.Valid := by decide +kernel
theorem sound3070 : certificate3070.Sound := rat_cut_bin_certificate_sound certificate3070 profilesValid3070 numericValid3070 valid3070

def retention3071 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(1/2),64,1,(63845591220989223006162834149049868551/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch350.profile14023,(fun _ => MergedCutProfiles.Batch350.profile14023)⟩
theorem profilesValid3071 : retention3071.ProfilesValid := by
  exact MergedCutProfiles.Batch350.valid14023
theorem numericValid3071 : retention3071.NumericValid := by decide +kernel
def certificate3071 : RatCutBinCertificate := ⟨⟨retention3071,(1061052254982828073/500000000000000000),(69043717129131353/1000000000000000000),(11012437943120596923/1000000000000000000),(1844708507240218827801/1000000000000000000),(984282582365465191/1000000000000000000)⟩,(199784922418507913/200000000000000000),(1049770655673319/8000000000000000),(600706123635778129/1000000000000000000),(58167760201439107/100000000000000000)⟩
theorem valid3071 : certificate3071.Valid := by decide +kernel
theorem sound3071 : certificate3071.Sound := rat_cut_bin_certificate_sound certificate3071 profilesValid3071 numericValid3071 valid3071

def certificates : List RatCutBinCertificate := [certificate3060,certificate3061,certificate3062,certificate3063,certificate3064,certificate3065,certificate3066,certificate3067,certificate3068,certificate3069,certificate3070,certificate3071]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3060,List.forall_mem_cons.mpr ⟨sound3061,List.forall_mem_cons.mpr ⟨sound3062,List.forall_mem_cons.mpr ⟨sound3063,List.forall_mem_cons.mpr ⟨sound3064,List.forall_mem_cons.mpr ⟨sound3065,List.forall_mem_cons.mpr ⟨sound3066,List.forall_mem_cons.mpr ⟨sound3067,List.forall_mem_cons.mpr ⟨sound3068,List.forall_mem_cons.mpr ⟨sound3069,List.forall_mem_cons.mpr ⟨sound3070,List.forall_mem_cons.mpr ⟨sound3071,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch255
