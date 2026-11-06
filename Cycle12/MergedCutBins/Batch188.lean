import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch347
import Cycle12.MergedCutProfiles.Batch348
import Cycle12.MergedCutProfiles.Batch349
import Cycle12.MergedCutProfiles.Batch350

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch188

def retention2256 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(2751812526555582181/35288751458599140089),(1313321379683531931/1000000000000000000),(9/4),(502711563556073547111/256000000000000000000),true,MergedCutProfiles.Batch347.profile13887,![MergedCutProfiles.Batch347.profile13887,MergedCutProfiles.Batch348.profile13924,MergedCutProfiles.Batch348.profile13925,MergedCutProfiles.Batch348.profile13926,MergedCutProfiles.Batch348.profile13927,MergedCutProfiles.Batch348.profile13928,MergedCutProfiles.Batch348.profile13929,MergedCutProfiles.Batch348.profile13930,MergedCutProfiles.Batch348.profile13931,MergedCutProfiles.Batch348.profile13932,MergedCutProfiles.Batch348.profile13933,MergedCutProfiles.Batch348.profile13934,MergedCutProfiles.Batch348.profile13935,MergedCutProfiles.Batch348.profile13936,MergedCutProfiles.Batch348.profile13937,MergedCutProfiles.Batch348.profile13938]⟩
theorem profilesValid2256 : retention2256.ProfilesValid := by
  change ∀ j : Fin 16, (retention2256.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch347.valid13887
  · exact MergedCutProfiles.Batch348.valid13924
  · exact MergedCutProfiles.Batch348.valid13925
  · exact MergedCutProfiles.Batch348.valid13926
  · exact MergedCutProfiles.Batch348.valid13927
  · exact MergedCutProfiles.Batch348.valid13928
  · exact MergedCutProfiles.Batch348.valid13929
  · exact MergedCutProfiles.Batch348.valid13930
  · exact MergedCutProfiles.Batch348.valid13931
  · exact MergedCutProfiles.Batch348.valid13932
  · exact MergedCutProfiles.Batch348.valid13933
  · exact MergedCutProfiles.Batch348.valid13934
  · exact MergedCutProfiles.Batch348.valid13935
  · exact MergedCutProfiles.Batch348.valid13936
  · exact MergedCutProfiles.Batch348.valid13937
  · exact MergedCutProfiles.Batch348.valid13938
theorem numericValid2256 : retention2256.NumericValid := by decide +kernel
def certificate2256 : RatCutBinCertificate := ⟨⟨retention2256,(1014237732961313733/500000000000000000),(65254397982896969/1000000000000000000),(433920294918310661/40000000000000000),(153938020535635409411/200000000000000000),(77450473953771363/40000000000000000)⟩,(997526471210469939/1000000000000000000),(378853191433530941/1000000000000000000),(126713454498519331/500000000000000000),(21052762105076679/125000000000000000)⟩
theorem valid2256 : certificate2256.Valid := by decide +kernel
theorem sound2256 : certificate2256.Sound := rat_cut_bin_certificate_sound certificate2256 profilesValid2256 numericValid2256 valid2256

def retention2257 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(14497338018066728969/35288751458599140089),(2751812526555582181/500000000000000000),(11/10),(640645911216227047696726411328207645359/550362505311116436200000000000000000000),false,MergedCutProfiles.Batch348.profile13939,(fun _ => MergedCutProfiles.Batch348.profile13939)⟩
theorem profilesValid2257 : retention2257.ProfilesValid := by
  exact MergedCutProfiles.Batch348.valid13939
theorem numericValid2257 : retention2257.NumericValid := by decide +kernel
def certificate2257 : RatCutBinCertificate := ⟨⟨retention2257,(1014237732961313733/500000000000000000),(65254397982896969/1000000000000000000),(433920294918310661/40000000000000000),(153938020535635409411/200000000000000000),(35956911957316983/31250000000000000)⟩,(997526471210469939/1000000000000000000),(112361660192358127/250000000000000000),(95556727317773341/500000000000000000),(170001708064520801/1000000000000000000)⟩
theorem valid2257 : certificate2257.Valid := by decide +kernel
theorem sound2257 : certificate2257.Sound := rat_cut_bin_certificate_sound certificate2257 profilesValid2257 numericValid2257 valid2257

def retention2258 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(17514363817231703183/35288751458599140089),(14497338018066728969/500000000000000000),1,(4639651172776912421783962703976804063/4639148165781353270080000000000000000),false,MergedCutProfiles.Batch348.profile13940,(fun _ => MergedCutProfiles.Batch348.profile13940)⟩
theorem profilesValid2258 : retention2258.ProfilesValid := by
  exact MergedCutProfiles.Batch348.valid13940
theorem numericValid2258 : retention2258.NumericValid := by decide +kernel
def certificate2258 : RatCutBinCertificate := ⟨⟨retention2258,(1014237732961313733/500000000000000000),(65254397982896969/1000000000000000000),(433920294918310661/40000000000000000),(153938020535635409411/200000000000000000),(123488303940516487/125000000000000000)⟩,(997526471210469939/1000000000000000000),(467846752981619009/1000000000000000000),(88384960581927141/500000000000000000),(168452608622254893/1000000000000000000)⟩
theorem valid2258 : certificate2258.Valid := by decide +kernel
theorem sound2258 : certificate2258.Sound := rat_cut_bin_certificate_sound certificate2258 profilesValid2258 numericValid2258 valid2258

def retention2259 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(1/2),(17514363817231703183/500000000000000000),1,(139322375109864222592065768094375413199/140114910537853625464000000000000000000),false,MergedCutProfiles.Batch348.profile13941,(fun _ => MergedCutProfiles.Batch348.profile13941)⟩
theorem profilesValid2259 : retention2259.ProfilesValid := by
  exact MergedCutProfiles.Batch348.valid13941
theorem numericValid2259 : retention2259.NumericValid := by decide +kernel
def certificate2259 : RatCutBinCertificate := ⟨⟨retention2259,(1014237732961313733/500000000000000000),(65254397982896969/1000000000000000000),(433920294918310661/40000000000000000),(153938020535635409411/200000000000000000),(98214168639397627/100000000000000000)⟩,(997526471210469939/1000000000000000000),(468334642035417119/1000000000000000000),(176399570392024817/1000000000000000000),(84050466597953521/500000000000000000)⟩
theorem valid2259 : certificate2259.Valid := by decide +kernel
theorem sound2259 : certificate2259.Sound := rat_cut_bin_certificate_sound certificate2259 profilesValid2259 numericValid2259 valid2259

def retention2260 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(2185883233359184241/5041250208371305727),(1116426337608269407/200000000000000000),(21/20),(393957426304878387939172858234143205599/357256428034646210240000000000000000000),false,MergedCutProfiles.Batch348.profile13942,(fun _ => MergedCutProfiles.Batch348.profile13942)⟩
theorem profilesValid2260 : retention2260.ProfilesValid := by
  exact MergedCutProfiles.Batch348.valid13942
theorem numericValid2260 : retention2260.NumericValid := by decide +kernel
def certificate2260 : RatCutBinCertificate := ⟨⟨retention2260,(1162918830461313733/500000000000000000),(65254397982896969/1000000000000000000),(433920294918310661/40000000000000000),(153938020535635409411/200000000000000000),(136004960927971223/125000000000000000)⟩,(997163799401202289/1000000000000000000),(220448392815147077/1000000000000000000),(223017281149783779/500000000000000000),(195782047363995747/500000000000000000)⟩
theorem valid2260 : certificate2260.Valid := by decide +kernel
theorem sound2260 : certificate2260.Sound := rat_cut_bin_certificate_sound certificate2260 profilesValid2260 numericValid2260 valid2260

def retention2261 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(17414173137885156396/35288751458599140089),(15301182633514289687/500000000000000000),1,(123164548731909347164081449650825095623/122409461068114317496000000000000000000),false,MergedCutProfiles.Batch348.profile13943,(fun _ => MergedCutProfiles.Batch348.profile13943)⟩
theorem profilesValid2261 : retention2261.ProfilesValid := by
  exact MergedCutProfiles.Batch348.valid13943
theorem numericValid2261 : retention2261.NumericValid := by decide +kernel
def certificate2261 : RatCutBinCertificate := ⟨⟨retention2261,(1162918830461313733/500000000000000000),(65254397982896969/1000000000000000000),(433920294918310661/40000000000000000),(153938020535635409411/200000000000000000),(992177808706170899/1000000000000000000)⟩,(997163799401202289/1000000000000000000),(30218449544397329/125000000000000000),(25931230531249309/62500000000000000),(397578565697010489/1000000000000000000)⟩
theorem valid2261 : certificate2261.Valid := by decide +kernel
theorem sound2261 : certificate2261.Sound := rat_cut_bin_certificate_sound certificate2261 profilesValid2261 numericValid2261 valid2261

def retention2262 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(2512616409894858280/5041250208371305727),(4353543284471289099/125000000000000000),1,(7538880035551395900442023773058871/7558234868873765796875000000000000),false,MergedCutProfiles.Batch348.profile13944,(fun _ => MergedCutProfiles.Batch348.profile13944)⟩
theorem profilesValid2262 : retention2262.ProfilesValid := by
  exact MergedCutProfiles.Batch348.valid13944
theorem numericValid2262 : retention2262.NumericValid := by decide +kernel
def certificate2262 : RatCutBinCertificate := ⟨⟨retention2262,(1162918830461313733/500000000000000000),(65254397982896969/1000000000000000000),(433920294918310661/40000000000000000),(153938020535635409411/200000000000000000),(98344851232152173/100000000000000000)⟩,(997163799401202289/1000000000000000000),(243893399000077001/1000000000000000000),(82373597865952217/200000000000000000),(392795143006137847/1000000000000000000)⟩
theorem valid2262 : certificate2262.Valid := by decide +kernel
theorem sound2262 : certificate2262.Sound := rat_cut_bin_certificate_sound certificate2262 profilesValid2262 numericValid2262 valid2262

def retention2263 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(1/2),(439707871731600199/12500000000000000),1,(139914872200063110260501871322526206311/140706518954112063680000000000000000000),false,MergedCutProfiles.Batch348.profile13941,(fun _ => MergedCutProfiles.Batch348.profile13941)⟩
theorem profilesValid2263 : retention2263.ProfilesValid := by
  exact MergedCutProfiles.Batch348.valid13941
theorem numericValid2263 : retention2263.NumericValid := by decide +kernel
def certificate2263 : RatCutBinCertificate := ⟨⟨retention2263,(1162918830461313733/500000000000000000),(65254397982896969/1000000000000000000),(433920294918310661/40000000000000000),(153938020535635409411/200000000000000000),(980383047131039463/1000000000000000000)⟩,(997163799401202289/1000000000000000000),(244656005745482307/1000000000000000000),(16431801038979801/40000000000000000),(97672543731137143/250000000000000000)⟩
theorem valid2263 : certificate2263.Valid := by decide +kernel
theorem sound2263 : certificate2263.Sound := rat_cut_bin_certificate_sound certificate2263 profilesValid2263 numericValid2263 valid2263

def retention2264 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(151787347956364037/13329703287103710401),(751422514635465529/1000000000000000000),(7/2),(7187764360167080599/3200000000000000000),true,MergedCutProfiles.Batch348.profile13945,![MergedCutProfiles.Batch348.profile13945,MergedCutProfiles.Batch348.profile13946,MergedCutProfiles.Batch348.profile13947,MergedCutProfiles.Batch348.profile13948,MergedCutProfiles.Batch348.profile13949,MergedCutProfiles.Batch348.profile13950,MergedCutProfiles.Batch348.profile13951,MergedCutProfiles.Batch348.profile13952,MergedCutProfiles.Batch348.profile13953,MergedCutProfiles.Batch348.profile13954,MergedCutProfiles.Batch348.profile13955,MergedCutProfiles.Batch348.profile13956,MergedCutProfiles.Batch348.profile13957,MergedCutProfiles.Batch348.profile13958,MergedCutProfiles.Batch348.profile13959,MergedCutProfiles.Batch349.profile13960]⟩
theorem profilesValid2264 : retention2264.ProfilesValid := by
  change ∀ j : Fin 16, (retention2264.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch348.valid13945
  · exact MergedCutProfiles.Batch348.valid13946
  · exact MergedCutProfiles.Batch348.valid13947
  · exact MergedCutProfiles.Batch348.valid13948
  · exact MergedCutProfiles.Batch348.valid13949
  · exact MergedCutProfiles.Batch348.valid13950
  · exact MergedCutProfiles.Batch348.valid13951
  · exact MergedCutProfiles.Batch348.valid13952
  · exact MergedCutProfiles.Batch348.valid13953
  · exact MergedCutProfiles.Batch348.valid13954
  · exact MergedCutProfiles.Batch348.valid13955
  · exact MergedCutProfiles.Batch348.valid13956
  · exact MergedCutProfiles.Batch348.valid13957
  · exact MergedCutProfiles.Batch348.valid13958
  · exact MergedCutProfiles.Batch348.valid13959
  · exact MergedCutProfiles.Batch349.valid13960
theorem numericValid2264 : retention2264.NumericValid := by decide +kernel
def certificate2264 : RatCutBinCertificate := ⟨⟨retention2264,(509833898978535091/250000000000000000),(69043717129131353/1000000000000000000),(5506125422214505869/500000000000000000),(737870866433231862963/1000000000000000000),(1100711778591847159/500000000000000000)⟩,(498708035098880483/500000000000000000),(425222444184127079/1000000000000000000),(3299234472675807/15625000000000000),(13356578480018813/125000000000000000)⟩
theorem valid2264 : certificate2264.Valid := by decide +kernel
theorem sound2264 : certificate2264.Sound := rat_cut_bin_certificate_sound certificate2264 profilesValid2264 numericValid2264 valid2264

def retention2265 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(916878268150850379/66648516435518552005),(151787347956364037/200000000000000000),(7/2),(572734612017040066073/256000000000000000000),true,MergedCutProfiles.Batch349.profile13961,![MergedCutProfiles.Batch349.profile13961,MergedCutProfiles.Batch349.profile13962,MergedCutProfiles.Batch349.profile13963,MergedCutProfiles.Batch349.profile13964,MergedCutProfiles.Batch349.profile13965,MergedCutProfiles.Batch349.profile13966,MergedCutProfiles.Batch349.profile13967,MergedCutProfiles.Batch349.profile13968,MergedCutProfiles.Batch349.profile13969,MergedCutProfiles.Batch348.profile13956,MergedCutProfiles.Batch349.profile13970,MergedCutProfiles.Batch349.profile13971,MergedCutProfiles.Batch349.profile13972,MergedCutProfiles.Batch349.profile13973,MergedCutProfiles.Batch349.profile13974,MergedCutProfiles.Batch349.profile13975]⟩
theorem profilesValid2265 : retention2265.ProfilesValid := by
  change ∀ j : Fin 16, (retention2265.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch349.valid13961
  · exact MergedCutProfiles.Batch349.valid13962
  · exact MergedCutProfiles.Batch349.valid13963
  · exact MergedCutProfiles.Batch349.valid13964
  · exact MergedCutProfiles.Batch349.valid13965
  · exact MergedCutProfiles.Batch349.valid13966
  · exact MergedCutProfiles.Batch349.valid13967
  · exact MergedCutProfiles.Batch349.valid13968
  · exact MergedCutProfiles.Batch349.valid13969
  · exact MergedCutProfiles.Batch348.valid13956
  · exact MergedCutProfiles.Batch349.valid13970
  · exact MergedCutProfiles.Batch349.valid13971
  · exact MergedCutProfiles.Batch349.valid13972
  · exact MergedCutProfiles.Batch349.valid13973
  · exact MergedCutProfiles.Batch349.valid13974
  · exact MergedCutProfiles.Batch349.valid13975
theorem numericValid2265 : retention2265.NumericValid := by decide +kernel
def certificate2265 : RatCutBinCertificate := ⟨⟨retention2265,(509833898978535091/250000000000000000),(69043717129131353/1000000000000000000),(5506125422214505869/500000000000000000),(737870866433231862963/1000000000000000000),(2192491788587355343/1000000000000000000)⟩,(498708035098880483/500000000000000000),(212373910092611529/500000000000000000),(52889283318679379/250000000000000000),(53455655787276497/500000000000000000)⟩
theorem valid2265 : certificate2265.Valid := by decide +kernel
theorem sound2265 : certificate2265.Sound := rat_cut_bin_certificate_sound certificate2265 profilesValid2265 numericValid2265 valid2265

def retention2266 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(211942886200000000/13329703287103710401),(916878268150850379/1000000000000000000),(59/20),(2829765537771113084827/1280000000000000000000),true,MergedCutProfiles.Batch349.profile13976,![MergedCutProfiles.Batch349.profile13976,MergedCutProfiles.Batch349.profile13977,MergedCutProfiles.Batch349.profile13978,MergedCutProfiles.Batch349.profile13979,MergedCutProfiles.Batch348.profile13951,MergedCutProfiles.Batch349.profile13967,MergedCutProfiles.Batch349.profile13980,MergedCutProfiles.Batch349.profile13981,MergedCutProfiles.Batch349.profile13982,MergedCutProfiles.Batch348.profile13958,MergedCutProfiles.Batch349.profile13983,MergedCutProfiles.Batch349.profile13984,MergedCutProfiles.Batch349.profile13974,MergedCutProfiles.Batch349.profile13985,MergedCutProfiles.Batch349.profile13986,MergedCutProfiles.Batch349.profile13987]⟩
theorem profilesValid2266 : retention2266.ProfilesValid := by
  change ∀ j : Fin 16, (retention2266.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch349.valid13976
  · exact MergedCutProfiles.Batch349.valid13977
  · exact MergedCutProfiles.Batch349.valid13978
  · exact MergedCutProfiles.Batch349.valid13979
  · exact MergedCutProfiles.Batch348.valid13951
  · exact MergedCutProfiles.Batch349.valid13967
  · exact MergedCutProfiles.Batch349.valid13980
  · exact MergedCutProfiles.Batch349.valid13981
  · exact MergedCutProfiles.Batch349.valid13982
  · exact MergedCutProfiles.Batch348.valid13958
  · exact MergedCutProfiles.Batch349.valid13983
  · exact MergedCutProfiles.Batch349.valid13984
  · exact MergedCutProfiles.Batch349.valid13974
  · exact MergedCutProfiles.Batch349.valid13985
  · exact MergedCutProfiles.Batch349.valid13986
  · exact MergedCutProfiles.Batch349.valid13987
theorem numericValid2266 : retention2266.NumericValid := by decide +kernel
def certificate2266 : RatCutBinCertificate := ⟨⟨retention2266,(509833898978535091/250000000000000000),(69043717129131353/1000000000000000000),(5506125422214505869/500000000000000000),(737870866433231862963/1000000000000000000),(2173034141834260997/1000000000000000000)⟩,(498708035098880483/500000000000000000),(7803893796909479/20000000000000000),(242587591057032139/1000000000000000000),(70012113298364291/500000000000000000)⟩
theorem valid2266 : certificate2266.Valid := by decide +kernel
theorem sound2266 : certificate2266.Sound := rat_cut_bin_certificate_sound certificate2266 profilesValid2266 numericValid2266 valid2266

def retention2267 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(219344325192120139/13329703287103710401),(1059714431/1000000000),(53/20),(4411347079137966399/2000000000000000000),true,MergedCutProfiles.Batch349.profile13988,![MergedCutProfiles.Batch349.profile13988,MergedCutProfiles.Batch349.profile13989,MergedCutProfiles.Batch349.profile13990,MergedCutProfiles.Batch349.profile13991,MergedCutProfiles.Batch349.profile13992,MergedCutProfiles.Batch349.profile13993,MergedCutProfiles.Batch349.profile13994,MergedCutProfiles.Batch349.profile13995,MergedCutProfiles.Batch349.profile13996,MergedCutProfiles.Batch349.profile13997,MergedCutProfiles.Batch349.profile13998,MergedCutProfiles.Batch349.profile13999,MergedCutProfiles.Batch350.profile14000,MergedCutProfiles.Batch350.profile14001,MergedCutProfiles.Batch350.profile14002,MergedCutProfiles.Batch350.profile14003]⟩
theorem profilesValid2267 : retention2267.ProfilesValid := by
  change ∀ j : Fin 16, (retention2267.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch349.valid13988
  · exact MergedCutProfiles.Batch349.valid13989
  · exact MergedCutProfiles.Batch349.valid13990
  · exact MergedCutProfiles.Batch349.valid13991
  · exact MergedCutProfiles.Batch349.valid13992
  · exact MergedCutProfiles.Batch349.valid13993
  · exact MergedCutProfiles.Batch349.valid13994
  · exact MergedCutProfiles.Batch349.valid13995
  · exact MergedCutProfiles.Batch349.valid13996
  · exact MergedCutProfiles.Batch349.valid13997
  · exact MergedCutProfiles.Batch349.valid13998
  · exact MergedCutProfiles.Batch349.valid13999
  · exact MergedCutProfiles.Batch350.valid14000
  · exact MergedCutProfiles.Batch350.valid14001
  · exact MergedCutProfiles.Batch350.valid14002
  · exact MergedCutProfiles.Batch350.valid14003
theorem numericValid2267 : retention2267.NumericValid := by decide +kernel
def certificate2267 : RatCutBinCertificate := ⟨⟨retention2267,(509833898978535091/250000000000000000),(69043717129131353/1000000000000000000),(5506125422214505869/500000000000000000),(737870866433231862963/1000000000000000000),(1085894674586128001/500000000000000000)⟩,(498708035098880483/500000000000000000),(365561545819741007/1000000000000000000),(53312521485885001/200000000000000000),(168603505577885871/1000000000000000000)⟩
theorem valid2267 : certificate2267.Valid := by decide +kernel
theorem sound2267 : certificate2267.Sound := rat_cut_bin_certificate_sound certificate2267 profilesValid2267 numericValid2267 valid2267

def certificates : List RatCutBinCertificate := [certificate2256,certificate2257,certificate2258,certificate2259,certificate2260,certificate2261,certificate2262,certificate2263,certificate2264,certificate2265,certificate2266,certificate2267]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2256,List.forall_mem_cons.mpr ⟨sound2257,List.forall_mem_cons.mpr ⟨sound2258,List.forall_mem_cons.mpr ⟨sound2259,List.forall_mem_cons.mpr ⟨sound2260,List.forall_mem_cons.mpr ⟨sound2261,List.forall_mem_cons.mpr ⟨sound2262,List.forall_mem_cons.mpr ⟨sound2263,List.forall_mem_cons.mpr ⟨sound2264,List.forall_mem_cons.mpr ⟨sound2265,List.forall_mem_cons.mpr ⟨sound2266,List.forall_mem_cons.mpr ⟨sound2267,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch188
