import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch068
import Cycle12.MergedCutProfiles.Batch069
import Cycle12.MergedCutProfiles.Batch070
import Cycle12.MergedCutProfiles.Batch346
import Cycle12.MergedCutProfiles.Batch347
import Cycle12.MergedCutProfiles.Batch348

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch187

def retention2244 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(3871378020337138859/37419646445651247031),(178308499624897999/125000000000000000),(21/10),(301296970167901445307/160000000000000000000),true,MergedCutProfiles.Batch068.profile2745,![MergedCutProfiles.Batch068.profile2745,MergedCutProfiles.Batch068.profile2750,MergedCutProfiles.Batch346.profile13849,MergedCutProfiles.Batch069.profile2798,MergedCutProfiles.Batch346.profile13850,MergedCutProfiles.Batch346.profile13851,MergedCutProfiles.Batch346.profile13852,MergedCutProfiles.Batch346.profile13853,MergedCutProfiles.Batch346.profile13854,MergedCutProfiles.Batch346.profile13855,MergedCutProfiles.Batch346.profile13856,MergedCutProfiles.Batch346.profile13857,MergedCutProfiles.Batch346.profile13858,MergedCutProfiles.Batch346.profile13859,MergedCutProfiles.Batch346.profile13860,MergedCutProfiles.Batch346.profile13861]⟩
theorem profilesValid2244 : retention2244.ProfilesValid := by
  change ∀ j : Fin 16, (retention2244.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch068.valid2745
  · exact MergedCutProfiles.Batch068.valid2750
  · exact MergedCutProfiles.Batch346.valid13849
  · exact MergedCutProfiles.Batch069.valid2798
  · exact MergedCutProfiles.Batch346.valid13850
  · exact MergedCutProfiles.Batch346.valid13851
  · exact MergedCutProfiles.Batch346.valid13852
  · exact MergedCutProfiles.Batch346.valid13853
  · exact MergedCutProfiles.Batch346.valid13854
  · exact MergedCutProfiles.Batch346.valid13855
  · exact MergedCutProfiles.Batch346.valid13856
  · exact MergedCutProfiles.Batch346.valid13857
  · exact MergedCutProfiles.Batch346.valid13858
  · exact MergedCutProfiles.Batch346.valid13859
  · exact MergedCutProfiles.Batch346.valid13860
  · exact MergedCutProfiles.Batch346.valid13861
theorem numericValid2244 : retention2244.NumericValid := by decide +kernel
def certificate2244 : RatCutBinCertificate := ⟨⟨retention2244,(2017155919836471829/1000000000000000000),(61591158108543061/1000000000000000000),(10687494888384588489/1000000000000000000),(50254071499741935531/62500000000000000),(1858693560010279701/1000000000000000000)⟩,(498818295444213363/500000000000000000),(384354934847684347/1000000000000000000),(24812701638180237/100000000000000000),(169067807671689363/1000000000000000000)⟩
theorem valid2244 : certificate2244.Valid := by decide +kernel
theorem sound2244 : certificate2244.Sound := rat_cut_bin_certificate_sound certificate2244 profilesValid2244 numericValid2244 valid2244

def retention2245 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(34731476576019651/78530212897484254),(3871378020337138859/500000000000000000),(21/20),(3408928799579910692665844557274077398279/3097102416269711087200000000000000000000),false,MergedCutProfiles.Batch346.profile13862,(fun _ => MergedCutProfiles.Batch346.profile13862)⟩
theorem profilesValid2245 : retention2245.ProfilesValid := by
  exact MergedCutProfiles.Batch346.valid13862
theorem numericValid2245 : retention2245.NumericValid := by decide +kernel
def certificate2245 : RatCutBinCertificate := ⟨⟨retention2245,(2017155919836471829/1000000000000000000),(61591158108543061/1000000000000000000),(10687494888384588489/1000000000000000000),(50254071499741935531/62500000000000000),(108847721034327107/100000000000000000)⟩,(498818295444213363/500000000000000000),(457951812530762539/1000000000000000000),(5762237039744129/31250000000000000),(84553252736817083/500000000000000000)⟩
theorem valid2245 : certificate2245.Valid := by decide +kernel
theorem sound2245 : certificate2245.Sound := rat_cut_bin_certificate_sound certificate2245 profilesValid2245 numericValid2245 valid2245

def retention2246 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(18463807511759401004/37419646445651247031),(33099097176946727403/1000000000000000000),1,(44436666611711951624127963302075721537/44132129569262303204000000000000000000),false,MergedCutProfiles.Batch346.profile13863,(fun _ => MergedCutProfiles.Batch346.profile13863)⟩
theorem profilesValid2246 : retention2246.ProfilesValid := by
  exact MergedCutProfiles.Batch346.valid13863
theorem numericValid2246 : retention2246.NumericValid := by decide +kernel
def certificate2246 : RatCutBinCertificate := ⟨⟨retention2246,(2017155919836471829/1000000000000000000),(61591158108543061/1000000000000000000),(10687494888384588489/1000000000000000000),(50254071499741935531/62500000000000000),(497637921520942159/500000000000000000)⟩,(498818295444213363/500000000000000000),(463301184572675733/1000000000000000000),(901224647277371/5000000000000000),(434345655974261/2500000000000000)⟩
theorem valid2246 : certificate2246.Valid := by decide +kernel
theorem sound2246 : certificate2246.Sound := rat_cut_bin_certificate_sound certificate2246 profilesValid2246 numericValid2246 valid2246

def retention2247 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(37296891173753990029/74839292891302494062),(4615951877939850251/125000000000000000),1,(147407659344343210669426741901498562231/147710460094075208032000000000000000000),false,MergedCutProfiles.Batch346.profile13864,(fun _ => MergedCutProfiles.Batch346.profile13864)⟩
theorem profilesValid2247 : retention2247.ProfilesValid := by
  exact MergedCutProfiles.Batch346.valid13864
theorem numericValid2247 : retention2247.NumericValid := by decide +kernel
def certificate2247 : RatCutBinCertificate := ⟨⟨retention2247,(2017155919836471829/1000000000000000000),(61591158108543061/1000000000000000000),(10687494888384588489/1000000000000000000),(50254071499741935531/62500000000000000),(986325310000098717/1000000000000000000)⟩,(498818295444213363/500000000000000000),(23315319549174381/50000000000000000),(88971266410234041/500000000000000000),(170533417569649273/1000000000000000000)⟩
theorem valid2247 : certificate2247.Valid := by decide +kernel
theorem sound2247 : certificate2247.Sound := rat_cut_bin_certificate_sound certificate2247 profilesValid2247 numericValid2247 valid2247

def retention2248 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(1/2),(37296891173753990029/1000000000000000000),1,(4637756103152072323051397077606521609/4662111396719248753625000000000000000),false,MergedCutProfiles.Batch070.profile2821,(fun _ => MergedCutProfiles.Batch070.profile2821)⟩
theorem profilesValid2248 : retention2248.ProfilesValid := by
  exact MergedCutProfiles.Batch070.valid2821
theorem numericValid2248 : retention2248.NumericValid := by decide +kernel
def certificate2248 : RatCutBinCertificate := ⟨⟨retention2248,(2017155919836471829/1000000000000000000),(61591158108543061/1000000000000000000),(10687494888384588489/1000000000000000000),(50254071499741935531/62500000000000000),(491575590413699863/500000000000000000)⟩,(498818295444213363/500000000000000000),(467708903099629649/1000000000000000000),(35374930704819203/200000000000000000),(169022098213614783/1000000000000000000)⟩
theorem valid2248 : certificate2248.Valid := by decide +kernel
theorem sound2248 : certificate2248.Sound := rat_cut_bin_certificate_sound certificate2248 profilesValid2248 numericValid2248 valid2248

def retention2249 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(32101331599427672229/74839292891302494062),(2758099265466254753/500000000000000000),(21/20),(2451020680530251954080643807574962260191/2206479412373003802400000000000000000000),false,MergedCutProfiles.Batch346.profile13865,(fun _ => MergedCutProfiles.Batch346.profile13865)⟩
theorem profilesValid2249 : retention2249.ProfilesValid := by
  exact MergedCutProfiles.Batch346.valid13865
theorem numericValid2249 : retention2249.NumericValid := by decide +kernel
def certificate2249 : RatCutBinCertificate := ⟨⟨retention2249,(2320905526836471829/1000000000000000000),(61591158108543061/1000000000000000000),(10687494888384588489/1000000000000000000),(50254071499741935531/62500000000000000),(1096784576853474473/1000000000000000000)⟩,(997280641756251673/1000000000000000000),(220696000772076309/1000000000000000000),(445661396897498453/1000000000000000000),(9831088364011633/25000000000000000)⟩
theorem valid2249 : certificate2249.Valid := by decide +kernel
theorem sound2249 : certificate2249.Sound := rat_cut_bin_certificate_sound certificate2249 profilesValid2249 numericValid2249 valid2249

def retention2250 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(18634324706486734452/37419646445651247031),(32101331599427672229/1000000000000000000),1,(176697552075870893915490341513291311/177110795031325088160000000000000000),false,MergedCutProfiles.Batch346.profile13866,(fun _ => MergedCutProfiles.Batch346.profile13866)⟩
theorem profilesValid2250 : retention2250.ProfilesValid := by
  exact MergedCutProfiles.Batch346.valid13866
theorem numericValid2250 : retention2250.NumericValid := by decide +kernel
def certificate2250 : RatCutBinCertificate := ⟨⟨retention2250,(2320905526836471829/1000000000000000000),(61591158108543061/1000000000000000000),(10687494888384588489/1000000000000000000),(50254071499741935531/62500000000000000),(984291534091181519/1000000000000000000)⟩,(997280641756251673/1000000000000000000),(122959489864733777/500000000000000000),(409023209192568827/1000000000000000000),(389543036456960069/1000000000000000000)⟩
theorem valid2250 : certificate2250.Valid := by decide +kernel
theorem sound2250 : certificate2250.Sound := rat_cut_bin_certificate_sound certificate2250 profilesValid2250 numericValid2250 valid2250

def retention2251 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(1/2),(4658581176621683613/125000000000000000),1,(9268441182571840705750922529632368343/9317162353243367226000000000000000000),false,MergedCutProfiles.Batch070.profile2821,(fun _ => MergedCutProfiles.Batch070.profile2821)⟩
theorem profilesValid2251 : retention2251.ProfilesValid := by
  exact MergedCutProfiles.Batch070.valid2821
theorem numericValid2251 : retention2251.NumericValid := by decide +kernel
def certificate2251 : RatCutBinCertificate := ⟨⟨retention2251,(2320905526836471829/1000000000000000000),(61591158108543061/1000000000000000000),(10687494888384588489/1000000000000000000),(50254071499741935531/62500000000000000),(245348899604345089/250000000000000000)⟩,(997280641756251673/1000000000000000000),(246644645859835169/1000000000000000000),(652812913746689/1600000000000000),(194534632379890843/500000000000000000)⟩
theorem valid2251 : certificate2251.Valid := by decide +kernel
theorem sound2251 : certificate2251.Sound := rat_cut_bin_certificate_sound certificate2251 profilesValid2251 numericValid2251 valid2251

def retention2252 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(376135294129616816/35288751458599140089),(148964472922620521/200000000000000000),(71/20),(9014564923712342653/4000000000000000000),true,MergedCutProfiles.Batch346.profile13867,![MergedCutProfiles.Batch346.profile13867,MergedCutProfiles.Batch346.profile13868,MergedCutProfiles.Batch346.profile13869,MergedCutProfiles.Batch346.profile13870,MergedCutProfiles.Batch346.profile13871,MergedCutProfiles.Batch346.profile13872,MergedCutProfiles.Batch346.profile13873,MergedCutProfiles.Batch346.profile13874,MergedCutProfiles.Batch346.profile13875,MergedCutProfiles.Batch346.profile13876,MergedCutProfiles.Batch346.profile13877,MergedCutProfiles.Batch346.profile13878,MergedCutProfiles.Batch346.profile13879,MergedCutProfiles.Batch347.profile13880,MergedCutProfiles.Batch347.profile13881,MergedCutProfiles.Batch347.profile13882]⟩
theorem profilesValid2252 : retention2252.ProfilesValid := by
  change ∀ j : Fin 16, (retention2252.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch346.valid13867
  · exact MergedCutProfiles.Batch346.valid13868
  · exact MergedCutProfiles.Batch346.valid13869
  · exact MergedCutProfiles.Batch346.valid13870
  · exact MergedCutProfiles.Batch346.valid13871
  · exact MergedCutProfiles.Batch346.valid13872
  · exact MergedCutProfiles.Batch346.valid13873
  · exact MergedCutProfiles.Batch346.valid13874
  · exact MergedCutProfiles.Batch346.valid13875
  · exact MergedCutProfiles.Batch346.valid13876
  · exact MergedCutProfiles.Batch346.valid13877
  · exact MergedCutProfiles.Batch346.valid13878
  · exact MergedCutProfiles.Batch346.valid13879
  · exact MergedCutProfiles.Batch347.valid13880
  · exact MergedCutProfiles.Batch347.valid13881
  · exact MergedCutProfiles.Batch347.valid13882
theorem numericValid2252 : retention2252.NumericValid := by decide +kernel
def certificate2252 : RatCutBinCertificate := ⟨⟨retention2252,(1014237732961313733/500000000000000000),(65254397982896969/1000000000000000000),(433920294918310661/40000000000000000),(153938020535635409411/200000000000000000),(442064577243796349/200000000000000000)⟩,(997526471210469939/1000000000000000000),(86006815430946929/200000000000000000),(20706358074706613/100000000000000000),(52024377100724441/500000000000000000)⟩
theorem valid2252 : certificate2252.Valid := by decide +kernel
theorem sound2252 : certificate2252.Sound := rat_cut_bin_certificate_sound certificate2252 profilesValid2252 numericValid2252 valid2252

def retention2253 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(129832118690200113/10082500416742611454),(23508455883101051/31250000000000000),(71/20),(179566188271525681189/80000000000000000000),true,MergedCutProfiles.Batch347.profile13883,![MergedCutProfiles.Batch347.profile13883,MergedCutProfiles.Batch347.profile13884,MergedCutProfiles.Batch347.profile13885,MergedCutProfiles.Batch347.profile13886,MergedCutProfiles.Batch346.profile13872,MergedCutProfiles.Batch347.profile13887,MergedCutProfiles.Batch347.profile13888,MergedCutProfiles.Batch347.profile13889,MergedCutProfiles.Batch347.profile13890,MergedCutProfiles.Batch346.profile13878,MergedCutProfiles.Batch347.profile13891,MergedCutProfiles.Batch347.profile13892,MergedCutProfiles.Batch347.profile13893,MergedCutProfiles.Batch347.profile13894,MergedCutProfiles.Batch347.profile13895,MergedCutProfiles.Batch347.profile13896]⟩
theorem profilesValid2253 : retention2253.ProfilesValid := by
  change ∀ j : Fin 16, (retention2253.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch347.valid13883
  · exact MergedCutProfiles.Batch347.valid13884
  · exact MergedCutProfiles.Batch347.valid13885
  · exact MergedCutProfiles.Batch347.valid13886
  · exact MergedCutProfiles.Batch346.valid13872
  · exact MergedCutProfiles.Batch347.valid13887
  · exact MergedCutProfiles.Batch347.valid13888
  · exact MergedCutProfiles.Batch347.valid13889
  · exact MergedCutProfiles.Batch347.valid13890
  · exact MergedCutProfiles.Batch346.valid13878
  · exact MergedCutProfiles.Batch347.valid13891
  · exact MergedCutProfiles.Batch347.valid13892
  · exact MergedCutProfiles.Batch347.valid13893
  · exact MergedCutProfiles.Batch347.valid13894
  · exact MergedCutProfiles.Batch347.valid13895
  · exact MergedCutProfiles.Batch347.valid13896
theorem numericValid2253 : retention2253.NumericValid := by decide +kernel
def certificate2253 : RatCutBinCertificate := ⟨⟨retention2253,(1014237732961313733/500000000000000000),(65254397982896969/1000000000000000000),(433920294918310661/40000000000000000),(153938020535635409411/200000000000000000),(2201259022436445081/1000000000000000000)⟩,(997526471210469939/1000000000000000000),(214775220388588857/500000000000000000),(103735990464027121/500000000000000000),(52051895713705083/500000000000000000)⟩
theorem valid2253 : certificate2253.Valid := by decide +kernel
theorem sound2253 : certificate2253.Sound := rat_cut_bin_certificate_sound certificate2253 profilesValid2253 numericValid2253 valid2253

def retention2254 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(76950503000000000/5041250208371305727),(908824830831400791/1000000000000000000),3,(567901295920674922943/256000000000000000000),true,MergedCutProfiles.Batch347.profile13897,![MergedCutProfiles.Batch347.profile13897,MergedCutProfiles.Batch347.profile13898,MergedCutProfiles.Batch347.profile13899,MergedCutProfiles.Batch347.profile13900,MergedCutProfiles.Batch347.profile13901,MergedCutProfiles.Batch347.profile13902,MergedCutProfiles.Batch346.profile13876,MergedCutProfiles.Batch347.profile13903,MergedCutProfiles.Batch347.profile13904,MergedCutProfiles.Batch347.profile13905,MergedCutProfiles.Batch347.profile13893,MergedCutProfiles.Batch347.profile13906,MergedCutProfiles.Batch347.profile13907,MergedCutProfiles.Batch347.profile13908,MergedCutProfiles.Batch347.profile13909,MergedCutProfiles.Batch347.profile13910]⟩
theorem profilesValid2254 : retention2254.ProfilesValid := by
  change ∀ j : Fin 16, (retention2254.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch347.valid13897
  · exact MergedCutProfiles.Batch347.valid13898
  · exact MergedCutProfiles.Batch347.valid13899
  · exact MergedCutProfiles.Batch347.valid13900
  · exact MergedCutProfiles.Batch347.valid13901
  · exact MergedCutProfiles.Batch347.valid13902
  · exact MergedCutProfiles.Batch346.valid13876
  · exact MergedCutProfiles.Batch347.valid13903
  · exact MergedCutProfiles.Batch347.valid13904
  · exact MergedCutProfiles.Batch347.valid13905
  · exact MergedCutProfiles.Batch347.valid13893
  · exact MergedCutProfiles.Batch347.valid13906
  · exact MergedCutProfiles.Batch347.valid13907
  · exact MergedCutProfiles.Batch347.valid13908
  · exact MergedCutProfiles.Batch347.valid13909
  · exact MergedCutProfiles.Batch347.valid13910
theorem numericValid2254 : retention2254.NumericValid := by decide +kernel
def certificate2254 : RatCutBinCertificate := ⟨⟨retention2254,(1014237732961313733/500000000000000000),(65254397982896969/1000000000000000000),(433920294918310661/40000000000000000),(153938020535635409411/200000000000000000),(1090878710388132287/500000000000000000)⟩,(997526471210469939/1000000000000000000),(49276204372447831/125000000000000000),(59707469606808099/250000000000000000),(34180415379264401/250000000000000000)⟩
theorem valid2254 : certificate2254.Valid := by decide +kernel
theorem sound2254 : certificate2254.Sound := rat_cut_bin_certificate_sound certificate2254 profilesValid2254 numericValid2254 valid2254

def retention2255 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(1313321379683531931/70577502917198280178),(538653521/500000000),(13/5),(4379373696515678133/2000000000000000000),true,MergedCutProfiles.Batch347.profile13911,![MergedCutProfiles.Batch347.profile13911,MergedCutProfiles.Batch347.profile13912,MergedCutProfiles.Batch347.profile13913,MergedCutProfiles.Batch346.profile13873,MergedCutProfiles.Batch347.profile13914,MergedCutProfiles.Batch347.profile13915,MergedCutProfiles.Batch347.profile13916,MergedCutProfiles.Batch347.profile13880,MergedCutProfiles.Batch347.profile13893,MergedCutProfiles.Batch347.profile13917,MergedCutProfiles.Batch347.profile13918,MergedCutProfiles.Batch347.profile13919,MergedCutProfiles.Batch348.profile13920,MergedCutProfiles.Batch348.profile13921,MergedCutProfiles.Batch348.profile13922,MergedCutProfiles.Batch348.profile13923]⟩
theorem profilesValid2255 : retention2255.ProfilesValid := by
  change ∀ j : Fin 16, (retention2255.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch347.valid13911
  · exact MergedCutProfiles.Batch347.valid13912
  · exact MergedCutProfiles.Batch347.valid13913
  · exact MergedCutProfiles.Batch346.valid13873
  · exact MergedCutProfiles.Batch347.valid13914
  · exact MergedCutProfiles.Batch347.valid13915
  · exact MergedCutProfiles.Batch347.valid13916
  · exact MergedCutProfiles.Batch347.valid13880
  · exact MergedCutProfiles.Batch347.valid13893
  · exact MergedCutProfiles.Batch347.valid13917
  · exact MergedCutProfiles.Batch347.valid13918
  · exact MergedCutProfiles.Batch347.valid13919
  · exact MergedCutProfiles.Batch348.valid13920
  · exact MergedCutProfiles.Batch348.valid13921
  · exact MergedCutProfiles.Batch348.valid13922
  · exact MergedCutProfiles.Batch348.valid13923
theorem numericValid2255 : retention2255.NumericValid := by decide +kernel
def certificate2255 : RatCutBinCertificate := ⟨⟨retention2255,(1014237732961313733/500000000000000000),(65254397982896969/1000000000000000000),(433920294918310661/40000000000000000),(153938020535635409411/200000000000000000),(86318431744507693/40000000000000000)⟩,(997526471210469939/1000000000000000000),(9219709333913641/25000000000000000),(1645811978126573/6250000000000000),(42029822269354737/250000000000000000)⟩
theorem valid2255 : certificate2255.Valid := by decide +kernel
theorem sound2255 : certificate2255.Sound := rat_cut_bin_certificate_sound certificate2255 profilesValid2255 numericValid2255 valid2255

def certificates : List RatCutBinCertificate := [certificate2244,certificate2245,certificate2246,certificate2247,certificate2248,certificate2249,certificate2250,certificate2251,certificate2252,certificate2253,certificate2254,certificate2255]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2244,List.forall_mem_cons.mpr ⟨sound2245,List.forall_mem_cons.mpr ⟨sound2246,List.forall_mem_cons.mpr ⟨sound2247,List.forall_mem_cons.mpr ⟨sound2248,List.forall_mem_cons.mpr ⟨sound2249,List.forall_mem_cons.mpr ⟨sound2250,List.forall_mem_cons.mpr ⟨sound2251,List.forall_mem_cons.mpr ⟨sound2252,List.forall_mem_cons.mpr ⟨sound2253,List.forall_mem_cons.mpr ⟨sound2254,List.forall_mem_cons.mpr ⟨sound2255,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch187
