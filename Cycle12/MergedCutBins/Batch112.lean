import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch218
import Cycle12.MergedCutProfiles.Batch219
import Cycle12.MergedCutProfiles.Batch220
import Cycle12.MergedCutProfiles.Batch221

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch112

def retention1344 : RatCutRetentionCertificate := ⟨(59/1000),(237/4000),(2919805143192072962/12863822583611712525),(645611449027728053/500000000000000000),(19/10),(1001708788055988544681/640000000000000000000),true,MergedCutProfiles.Batch219.profile8774,![MergedCutProfiles.Batch219.profile8774,MergedCutProfiles.Batch219.profile8775,MergedCutProfiles.Batch219.profile8776,MergedCutProfiles.Batch219.profile8777,MergedCutProfiles.Batch218.profile8757,MergedCutProfiles.Batch219.profile8778,MergedCutProfiles.Batch219.profile8779,MergedCutProfiles.Batch219.profile8780,MergedCutProfiles.Batch219.profile8781,MergedCutProfiles.Batch219.profile8782,MergedCutProfiles.Batch219.profile8783,MergedCutProfiles.Batch219.profile8784,MergedCutProfiles.Batch219.profile8785,MergedCutProfiles.Batch219.profile8786,MergedCutProfiles.Batch219.profile8787,MergedCutProfiles.Batch219.profile8788]⟩
theorem profilesValid1344 : retention1344.ProfilesValid := by
  change ∀ j : Fin 16, (retention1344.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch219.valid8774
  · exact MergedCutProfiles.Batch219.valid8775
  · exact MergedCutProfiles.Batch219.valid8776
  · exact MergedCutProfiles.Batch219.valid8777
  · exact MergedCutProfiles.Batch218.valid8757
  · exact MergedCutProfiles.Batch219.valid8778
  · exact MergedCutProfiles.Batch219.valid8779
  · exact MergedCutProfiles.Batch219.valid8780
  · exact MergedCutProfiles.Batch219.valid8781
  · exact MergedCutProfiles.Batch219.valid8782
  · exact MergedCutProfiles.Batch219.valid8783
  · exact MergedCutProfiles.Batch219.valid8784
  · exact MergedCutProfiles.Batch219.valid8785
  · exact MergedCutProfiles.Batch219.valid8786
  · exact MergedCutProfiles.Batch219.valid8787
  · exact MergedCutProfiles.Batch219.valid8788
theorem numericValid1344 : retention1344.NumericValid := by decide +kernel
def certificate1344 : RatCutBinCertificate := ⟨⟨retention1344,(2305019937538484471/1000000000000000000),(1770931297231219/10000000000000000),(7787744033161907579/500000000000000000),(100332580072107007567/500000000000000000),(1515356770521902853/1000000000000000000)⟩,(30953353541991321/31250000000000000),(19185244260066881/50000000000000000),(62187273712708439/250000000000000000),(37007104412136661/250000000000000000)⟩
theorem valid1344 : certificate1344.Valid := by decide +kernel
theorem sound1344 : certificate1344.Sound := rat_cut_bin_certificate_sound certificate1344 profilesValid1344 numericValid1344 valid1344

def retention1345 : RatCutRetentionCertificate := ⟨(59/1000),(237/4000),(5411018811405648374/12863822583611712525),(1459902571596036481/500000000000000000),(23/20),(721822364623876930577/640000000000000000000),true,MergedCutProfiles.Batch219.profile8789,![MergedCutProfiles.Batch219.profile8789,MergedCutProfiles.Batch219.profile8790,MergedCutProfiles.Batch219.profile8791,MergedCutProfiles.Batch219.profile8792,MergedCutProfiles.Batch219.profile8793,MergedCutProfiles.Batch219.profile8794,MergedCutProfiles.Batch219.profile8795,MergedCutProfiles.Batch219.profile8796,MergedCutProfiles.Batch219.profile8797,MergedCutProfiles.Batch219.profile8798,MergedCutProfiles.Batch219.profile8799,MergedCutProfiles.Batch220.profile8800,MergedCutProfiles.Batch220.profile8801,MergedCutProfiles.Batch220.profile8802,MergedCutProfiles.Batch220.profile8803,MergedCutProfiles.Batch220.profile8804]⟩
theorem profilesValid1345 : retention1345.ProfilesValid := by
  change ∀ j : Fin 16, (retention1345.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch219.valid8789
  · exact MergedCutProfiles.Batch219.valid8790
  · exact MergedCutProfiles.Batch219.valid8791
  · exact MergedCutProfiles.Batch219.valid8792
  · exact MergedCutProfiles.Batch219.valid8793
  · exact MergedCutProfiles.Batch219.valid8794
  · exact MergedCutProfiles.Batch219.valid8795
  · exact MergedCutProfiles.Batch219.valid8796
  · exact MergedCutProfiles.Batch219.valid8797
  · exact MergedCutProfiles.Batch219.valid8798
  · exact MergedCutProfiles.Batch219.valid8799
  · exact MergedCutProfiles.Batch220.valid8800
  · exact MergedCutProfiles.Batch220.valid8801
  · exact MergedCutProfiles.Batch220.valid8802
  · exact MergedCutProfiles.Batch220.valid8803
  · exact MergedCutProfiles.Batch220.valid8804
theorem numericValid1345 : retention1345.NumericValid := by decide +kernel
def certificate1345 : RatCutBinCertificate := ⟨⟨retention1345,(2305019937538484471/1000000000000000000),(1770931297231219/10000000000000000),(7787744033161907579/500000000000000000),(100332580072107007567/500000000000000000),(274425065959015883/250000000000000000)⟩,(30953353541991321/31250000000000000),(109257230051106499/250000000000000000),(100608692562847157/500000000000000000),(73965110416316879/500000000000000000)⟩
theorem valid1345 : certificate1345.Valid := by decide +kernel
theorem sound1345 : certificate1345.Sound := rat_cut_bin_certificate_sound certificate1345 profilesValid1345 numericValid1345 valid1345

def retention1346 : RatCutRetentionCertificate := ⟨(59/1000),(237/4000),(6219826591054481896/12863822583611712525),(2705509405702824187/500000000000000000),(11/10),(553790164602467243362249182751058847151/541101881140564837400000000000000000000),false,MergedCutProfiles.Batch220.profile8805,(fun _ => MergedCutProfiles.Batch220.profile8805)⟩
theorem profilesValid1346 : retention1346.ProfilesValid := by
  exact MergedCutProfiles.Batch220.valid8805
theorem numericValid1346 : retention1346.NumericValid := by decide +kernel
def certificate1346 : RatCutBinCertificate := ⟨⟨retention1346,(2305019937538484471/1000000000000000000),(1770931297231219/10000000000000000),(7787744033161907579/500000000000000000),(100332580072107007567/500000000000000000),(124326980232510221/125000000000000000)⟩,(30953353541991321/31250000000000000),(22249557023166293/50000000000000000),(24337350193335239/125000000000000000),(4726504682660001/31250000000000000)⟩
theorem valid1346 : certificate1346.Valid := by decide +kernel
theorem sound1346 : certificate1346.Sound := rat_cut_bin_certificate_sound certificate1346 profilesValid1346 numericValid1346 valid1346

def retention1347 : RatCutRetentionCertificate := ⟨(59/1000),(237/4000),(6344845105534676983/12863822583611712525),(777478323881810237/125000000000000000),(21/20),(619022848495711898990536850177318516999/621982659105448189600000000000000000000),false,MergedCutProfiles.Batch220.profile8806,(fun _ => MergedCutProfiles.Batch220.profile8806)⟩
theorem profilesValid1347 : retention1347.ProfilesValid := by
  exact MergedCutProfiles.Batch220.valid8806
theorem numericValid1347 : retention1347.NumericValid := by decide +kernel
def certificate1347 : RatCutBinCertificate := ⟨⟨retention1347,(2305019937538484471/1000000000000000000),(1770931297231219/10000000000000000),(7787744033161907579/500000000000000000),(100332580072107007567/500000000000000000),(241929789136203191/250000000000000000)⟩,(30953353541991321/31250000000000000),(56438903963527209/125000000000000000),(11841692237865921/62500000000000000),(37863015609521991/250000000000000000)⟩
theorem valid1347 : certificate1347.Valid := by decide +kernel
theorem sound1347 : certificate1347.Sound := rat_cut_bin_certificate_sound certificate1347 profilesValid1347 numericValid1347 valid1347

def retention1348 : RatCutRetentionCertificate := ⟨(59/1000),(237/4000),(6408293556590023753/12863822583611712525),(6344845105534676983/1000000000000000000),(21/20),(10015995106544028367576917849668566603431/10151752168855483172800000000000000000000),false,MergedCutProfiles.Batch220.profile8807,(fun _ => MergedCutProfiles.Batch220.profile8807)⟩
theorem profilesValid1348 : retention1348.ProfilesValid := by
  exact MergedCutProfiles.Batch220.valid8807
theorem numericValid1348 : retention1348.NumericValid := by decide +kernel
def certificate1348 : RatCutBinCertificate := ⟨⟨retention1348,(2305019937538484471/1000000000000000000),(1770931297231219/10000000000000000),(7787744033161907579/500000000000000000),(100332580072107007567/500000000000000000),(959105128920086233/1000000000000000000)⟩,(30953353541991321/31250000000000000),(90957717482768499/200000000000000000),(186872962924136413/1000000000000000000),(18571629867229449/125000000000000000)⟩
theorem valid1348 : certificate1348.Valid := by decide +kernel
theorem sound1348 : certificate1348.Sound := rat_cut_bin_certificate_sound certificate1348 profilesValid1348 numericValid1348 valid1348

def retention1349 : RatCutRetentionCertificate := ⟨(59/1000),(237/4000),(1/2),(6408293556590023753/1000000000000000000),(21/20),(10084081438765220107565195170435056138351/10253269690544038004800000000000000000000),false,MergedCutProfiles.Batch220.profile8808,(fun _ => MergedCutProfiles.Batch220.profile8808)⟩
theorem profilesValid1349 : retention1349.ProfilesValid := by
  exact MergedCutProfiles.Batch220.valid8808
theorem numericValid1349 : retention1349.NumericValid := by decide +kernel
def certificate1349 : RatCutBinCertificate := ⟨⟨retention1349,(2305019937538484471/1000000000000000000),(1770931297231219/10000000000000000),(7787744033161907579/500000000000000000),(100332580072107007567/500000000000000000),(477988514662185073/500000000000000000)⟩,(30953353541991321/31250000000000000),(227946165569263437/500000000000000000),(93002322541544953/500000000000000000),(73817530758124891/500000000000000000)⟩
theorem valid1349 : certificate1349.Valid := by decide +kernel
theorem sound1349 : certificate1349.Sound := rat_cut_bin_certificate_sound certificate1349 profilesValid1349 numericValid1349 valid1349

def retention1350 : RatCutRetentionCertificate := ⟨(59/1000),(237/4000),(1/2),64,1,(3990729822180473770414981848484101279/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch220.profile8808,(fun _ => MergedCutProfiles.Batch220.profile8808)⟩
theorem profilesValid1350 : retention1350.ProfilesValid := by
  exact MergedCutProfiles.Batch220.valid8808
theorem numericValid1350 : retention1350.NumericValid := by decide +kernel
def certificate1350 : RatCutBinCertificate := ⟨⟨retention1350,(2305019937538484471/1000000000000000000),(1770931297231219/10000000000000000),(7787744033161907579/500000000000000000),(100332580072107007567/500000000000000000),(971474042556150019/1000000000000000000)⟩,(30953353541991321/31250000000000000),(207290678525147731/500000000000000000),(27548085365505007/125000000000000000),(208875749239874749/1000000000000000000)⟩
theorem valid1350 : certificate1350.Valid := by decide +kernel
theorem sound1350 : certificate1350.Sound := rat_cut_bin_certificate_sound certificate1350 profilesValid1350 numericValid1350 valid1350

def retention1351 : RatCutRetentionCertificate := ⟨(59/1000),(237/4000),(5946187970415836726/12863822583611712525),(1789857992530305113/500000000000000000),(6/5),(95625759279897957165334893869298068991/89492899626515255650000000000000000000),false,MergedCutProfiles.Batch220.profile8809,(fun _ => MergedCutProfiles.Batch220.profile8809)⟩
theorem profilesValid1351 : retention1351.ProfilesValid := by
  exact MergedCutProfiles.Batch220.valid8809
theorem numericValid1351 : retention1351.NumericValid := by decide +kernel
def certificate1351 : RatCutBinCertificate := ⟨⟨retention1351,(2633685021538484471/1000000000000000000),(1770931297231219/10000000000000000),(7787744033161907579/500000000000000000),(100332580072107007567/500000000000000000),(516293830831160877/500000000000000000)⟩,(197830132413496751/200000000000000000),(76811335191198109/200000000000000000),(248412304892270443/1000000000000000000),(175949162541601483/1000000000000000000)⟩
theorem valid1351 : certificate1351.Valid := by decide +kernel
theorem sound1351 : certificate1351.Sound := rat_cut_bin_certificate_sound certificate1351 profilesValid1351 numericValid1351 valid1351

def retention1352 : RatCutRetentionCertificate := ⟨(59/1000),(237/4000),(68549659498454304/138320672942061425),(2973093985207918363/500000000000000000),(21/20),(2352474860120674593315888642947617372991/2378475188166334690400000000000000000000),false,MergedCutProfiles.Batch220.profile8810,(fun _ => MergedCutProfiles.Batch220.profile8810)⟩
theorem profilesValid1352 : retention1352.ProfilesValid := by
  exact MergedCutProfiles.Batch220.valid8810
theorem numericValid1352 : retention1352.NumericValid := by decide +kernel
def certificate1352 : RatCutBinCertificate := ⟨⟨retention1352,(2633685021538484471/1000000000000000000),(1770931297231219/10000000000000000),(7787744033161907579/500000000000000000),(100332580072107007567/500000000000000000),(59851364119317933/62500000000000000)⟩,(197830132413496751/200000000000000000),(82824383121119339/200000000000000000),(1766315656525079/8000000000000000),(43412337715391477/250000000000000000)⟩
theorem valid1352 : certificate1352.Valid := by decide +kernel
theorem sound1352 : certificate1352.Sound := rat_cut_bin_certificate_sound certificate1352 profilesValid1352 numericValid1352 valid1352

def retention1353 : RatCutRetentionCertificate := ⟨(59/1000),(237/4000),(1/2),(199222447917382821/31250000000000000),(21/20),(612183291428406440002416788161824509/622570149741821315625000000000000000),false,MergedCutProfiles.Batch220.profile8808,(fun _ => MergedCutProfiles.Batch220.profile8808)⟩
theorem profilesValid1353 : retention1353.ProfilesValid := by
  exact MergedCutProfiles.Batch220.valid8808
theorem numericValid1353 : retention1353.NumericValid := by decide +kernel
def certificate1353 : RatCutBinCertificate := ⟨⟨retention1353,(2633685021538484471/1000000000000000000),(1770931297231219/10000000000000000),(7787744033161907579/500000000000000000),(100332580072107007567/500000000000000000),(951869800032020223/1000000000000000000)⟩,(197830132413496751/200000000000000000),(41662440068784607/100000000000000000),(218590890058489793/1000000000000000000),(43124564103044501/250000000000000000)⟩
theorem valid1353 : certificate1353.Valid := by decide +kernel
theorem sound1353 : certificate1353.Sound := rat_cut_bin_certificate_sound certificate1353 profilesValid1353 numericValid1353 valid1353

def retention1354 : RatCutRetentionCertificate := ⟨(237/4000),(119/2000),(261798128497435863/2547307847567706842),(443989775251555199/500000000000000000),(53/20),(303300414540820223529/160000000000000000000),true,MergedCutProfiles.Batch220.profile8811,![MergedCutProfiles.Batch220.profile8811,MergedCutProfiles.Batch220.profile8812,MergedCutProfiles.Batch220.profile8813,MergedCutProfiles.Batch220.profile8814,MergedCutProfiles.Batch220.profile8815,MergedCutProfiles.Batch220.profile8816,MergedCutProfiles.Batch220.profile8817,MergedCutProfiles.Batch220.profile8818,MergedCutProfiles.Batch220.profile8819,MergedCutProfiles.Batch220.profile8820,MergedCutProfiles.Batch220.profile8821,MergedCutProfiles.Batch220.profile8822,MergedCutProfiles.Batch220.profile8823,MergedCutProfiles.Batch220.profile8824,MergedCutProfiles.Batch220.profile8825,MergedCutProfiles.Batch220.profile8826]⟩
theorem profilesValid1354 : retention1354.ProfilesValid := by
  change ∀ j : Fin 16, (retention1354.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch220.valid8811
  · exact MergedCutProfiles.Batch220.valid8812
  · exact MergedCutProfiles.Batch220.valid8813
  · exact MergedCutProfiles.Batch220.valid8814
  · exact MergedCutProfiles.Batch220.valid8815
  · exact MergedCutProfiles.Batch220.valid8816
  · exact MergedCutProfiles.Batch220.valid8817
  · exact MergedCutProfiles.Batch220.valid8818
  · exact MergedCutProfiles.Batch220.valid8819
  · exact MergedCutProfiles.Batch220.valid8820
  · exact MergedCutProfiles.Batch220.valid8821
  · exact MergedCutProfiles.Batch220.valid8822
  · exact MergedCutProfiles.Batch220.valid8823
  · exact MergedCutProfiles.Batch220.valid8824
  · exact MergedCutProfiles.Batch220.valid8825
  · exact MergedCutProfiles.Batch220.valid8826
theorem numericValid1354 : retention1354.NumericValid := by decide +kernel
def certificate1354 : RatCutBinCertificate := ⟨⟨retention1354,(2303314778672908521/1000000000000000000),(178859476136284067/1000000000000000000),(3911561957736737917/250000000000000000),(19958276023943220001/100000000000000000),(1825825845575007241/1000000000000000000)⟩,(99048287419965671/100000000000000000),(35376244423827013/100000000000000000),(278627287113436953/1000000000000000000),(9174553884665397/62500000000000000)⟩
theorem valid1354 : certificate1354.Valid := by decide +kernel
theorem sound1354 : certificate1354.Sound := rat_cut_bin_certificate_sound certificate1354 profilesValid1354 numericValid1354 valid1354

def retention1355 : RatCutRetentionCertificate := ⟨(237/4000),(119/2000),(3110971704388536801/12736539237838534210),(261798128497435863/200000000000000000),(37/20),(389972086856930436399/256000000000000000000),true,MergedCutProfiles.Batch220.profile8827,![MergedCutProfiles.Batch220.profile8827,MergedCutProfiles.Batch220.profile8828,MergedCutProfiles.Batch220.profile8829,MergedCutProfiles.Batch220.profile8830,MergedCutProfiles.Batch220.profile8831,MergedCutProfiles.Batch220.profile8832,MergedCutProfiles.Batch220.profile8833,MergedCutProfiles.Batch220.profile8834,MergedCutProfiles.Batch220.profile8835,MergedCutProfiles.Batch220.profile8836,MergedCutProfiles.Batch220.profile8837,MergedCutProfiles.Batch220.profile8838,MergedCutProfiles.Batch220.profile8839,MergedCutProfiles.Batch221.profile8840,MergedCutProfiles.Batch221.profile8841,MergedCutProfiles.Batch221.profile8842]⟩
theorem profilesValid1355 : retention1355.ProfilesValid := by
  change ∀ j : Fin 16, (retention1355.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch220.valid8827
  · exact MergedCutProfiles.Batch220.valid8828
  · exact MergedCutProfiles.Batch220.valid8829
  · exact MergedCutProfiles.Batch220.valid8830
  · exact MergedCutProfiles.Batch220.valid8831
  · exact MergedCutProfiles.Batch220.valid8832
  · exact MergedCutProfiles.Batch220.valid8833
  · exact MergedCutProfiles.Batch220.valid8834
  · exact MergedCutProfiles.Batch220.valid8835
  · exact MergedCutProfiles.Batch220.valid8836
  · exact MergedCutProfiles.Batch220.valid8837
  · exact MergedCutProfiles.Batch220.valid8838
  · exact MergedCutProfiles.Batch220.valid8839
  · exact MergedCutProfiles.Batch221.valid8840
  · exact MergedCutProfiles.Batch221.valid8841
  · exact MergedCutProfiles.Batch221.valid8842
theorem numericValid1355 : retention1355.NumericValid := by decide +kernel
def certificate1355 : RatCutBinCertificate := ⟨⟨retention1355,(2303314778672908521/1000000000000000000),(178859476136284067/1000000000000000000),(3911561957736737917/250000000000000000),(19958276023943220001/100000000000000000),(737299734311531401/500000000000000000)⟩,(99048287419965671/100000000000000000),(96199562892369361/250000000000000000),(49540681097736719/200000000000000000),(73430168811901673/500000000000000000)⟩
theorem valid1355 : certificate1355.Valid := by decide +kernel
theorem sound1355 : certificate1355.Sound := rat_cut_bin_certificate_sound certificate1355 profilesValid1355 numericValid1355 valid1355

def certificates : List RatCutBinCertificate := [certificate1344,certificate1345,certificate1346,certificate1347,certificate1348,certificate1349,certificate1350,certificate1351,certificate1352,certificate1353,certificate1354,certificate1355]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1344,List.forall_mem_cons.mpr ⟨sound1345,List.forall_mem_cons.mpr ⟨sound1346,List.forall_mem_cons.mpr ⟨sound1347,List.forall_mem_cons.mpr ⟨sound1348,List.forall_mem_cons.mpr ⟨sound1349,List.forall_mem_cons.mpr ⟨sound1350,List.forall_mem_cons.mpr ⟨sound1351,List.forall_mem_cons.mpr ⟨sound1352,List.forall_mem_cons.mpr ⟨sound1353,List.forall_mem_cons.mpr ⟨sound1354,List.forall_mem_cons.mpr ⟨sound1355,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch112
