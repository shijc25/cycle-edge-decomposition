import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch518
import Cycle12.MergedCutProfiles.Batch519
import Cycle12.MergedCutProfiles.Batch520

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch281

def retention3372 : RatCutRetentionCertificate := ⟨(29/500),(117/2000),(5812580625843287197/66280001659890901986),(1359716656682717717/1000000000000000000),(43/20),(2493516218866087245749/1280000000000000000000),true,MergedCutProfiles.Batch518.profile20735,![MergedCutProfiles.Batch518.profile20735,MergedCutProfiles.Batch518.profile20736,MergedCutProfiles.Batch518.profile20737,MergedCutProfiles.Batch518.profile20738,MergedCutProfiles.Batch518.profile20739,MergedCutProfiles.Batch518.profile20740,MergedCutProfiles.Batch518.profile20741,MergedCutProfiles.Batch518.profile20742,MergedCutProfiles.Batch518.profile20743,MergedCutProfiles.Batch518.profile20744,MergedCutProfiles.Batch518.profile20745,MergedCutProfiles.Batch518.profile20746,MergedCutProfiles.Batch518.profile20747,MergedCutProfiles.Batch518.profile20748,MergedCutProfiles.Batch518.profile20749,MergedCutProfiles.Batch518.profile20750]⟩
theorem profilesValid3372 : retention3372.ProfilesValid := by
  change ∀ j : Fin 16, (retention3372.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch518.valid20735
  · exact MergedCutProfiles.Batch518.valid20736
  · exact MergedCutProfiles.Batch518.valid20737
  · exact MergedCutProfiles.Batch518.valid20738
  · exact MergedCutProfiles.Batch518.valid20739
  · exact MergedCutProfiles.Batch518.valid20740
  · exact MergedCutProfiles.Batch518.valid20741
  · exact MergedCutProfiles.Batch518.valid20742
  · exact MergedCutProfiles.Batch518.valid20743
  · exact MergedCutProfiles.Batch518.valid20744
  · exact MergedCutProfiles.Batch518.valid20745
  · exact MergedCutProfiles.Batch518.valid20746
  · exact MergedCutProfiles.Batch518.valid20747
  · exact MergedCutProfiles.Batch518.valid20748
  · exact MergedCutProfiles.Batch518.valid20749
  · exact MergedCutProfiles.Batch518.valid20750
theorem numericValid3372 : retention3372.NumericValid := by decide +kernel
def certificate3372 : RatCutBinCertificate := ⟨⟨retention3372,(2184127726165908029/1000000000000000000),(42966716513336319/250000000000000000),(3825645658661106153/250000000000000000),(1017325787371704994593/1000000000000000000),(1895316037812419659/1000000000000000000)⟩,(499107026461154473/500000000000000000),(330649634600369119/1000000000000000000),(75852938592883241/250000000000000000),(205072509278790709/1000000000000000000)⟩
theorem valid3372 : certificate3372.Valid := by decide +kernel
theorem sound3372 : certificate3372.Sound := rat_cut_bin_certificate_sound certificate3372 profilesValid3372 numericValid3372 valid3372

def retention3373 : RatCutRetentionCertificate := ⟨(29/500),(117/2000),(27722007321002013823/66280001659890901986),(5812580625843287197/1000000000000000000),(11/10),(2680125140933719661022264300005072169151/2325032250337314878800000000000000000000),false,MergedCutProfiles.Batch518.profile20751,(fun _ => MergedCutProfiles.Batch518.profile20751)⟩
theorem profilesValid3373 : retention3373.ProfilesValid := by
  exact MergedCutProfiles.Batch518.valid20751
theorem numericValid3373 : retention3373.NumericValid := by decide +kernel
def certificate3373 : RatCutBinCertificate := ⟨⟨retention3373,(2184127726165908029/1000000000000000000),(42966716513336319/250000000000000000),(3825645658661106153/250000000000000000),(1017325787371704994593/1000000000000000000),(1125741802196532613/1000000000000000000)⟩,(499107026461154473/500000000000000000),(399002430763350721/1000000000000000000),(29299703785354753/125000000000000000),(103191705075415039/500000000000000000)⟩
theorem valid3373 : certificate3373.Valid := by decide +kernel
theorem sound3373 : certificate3373.Sound := rat_cut_bin_certificate_sound certificate3373 profilesValid3373 numericValid3373 valid3373

def retention3374 : RatCutRetentionCertificate := ⟨(29/500),(117/2000),(32831296116815645161/66280001659890901986),(27722007321002013823/1000000000000000000),1,(347119385556947571749555141698919417/346525091512525172787500000000000000),false,MergedCutProfiles.Batch518.profile20752,(fun _ => MergedCutProfiles.Batch518.profile20752)⟩
theorem profilesValid3374 : retention3374.ProfilesValid := by
  exact MergedCutProfiles.Batch518.valid20752
theorem numericValid3374 : retention3374.NumericValid := by decide +kernel
def certificate3374 : RatCutBinCertificate := ⟨⟨retention3374,(2184127726165908029/1000000000000000000),(42966716513336319/250000000000000000),(3825645658661106153/250000000000000000),(1017325787371704994593/1000000000000000000),(488592206983966503/500000000000000000)⟩,(499107026461154473/500000000000000000),(415821600489505167/1000000000000000000),(10964727578872729/50000000000000000),(103308393349537863/500000000000000000)⟩
theorem valid3374 : certificate3374.Valid := by decide +kernel
theorem sound3374 : certificate3374.Sound := rat_cut_bin_certificate_sound certificate3374 profilesValid3374 numericValid3374 valid3374

def retention3375 : RatCutRetentionCertificate := ⟨(29/500),(117/2000),(1/2),(32831296116815645161/1000000000000000000),1,(26106299318507171568371124462251120759/26265036893452516128800000000000000000),false,MergedCutProfiles.Batch518.profile20753,(fun _ => MergedCutProfiles.Batch518.profile20753)⟩
theorem profilesValid3375 : retention3375.ProfilesValid := by
  exact MergedCutProfiles.Batch518.valid20753
theorem numericValid3375 : retention3375.NumericValid := by decide +kernel
def certificate3375 : RatCutBinCertificate := ⟨⟨retention3375,(2184127726165908029/1000000000000000000),(42966716513336319/250000000000000000),(3825645658661106153/250000000000000000),(1017325787371704994593/1000000000000000000),(969425743411208921/1000000000000000000)⟩,(499107026461154473/500000000000000000),(41732509612689671/100000000000000000),(217977988302672763/1000000000000000000),(204879307807453477/1000000000000000000)⟩
theorem valid3375 : certificate3375.Valid := by decide +kernel
theorem sound3375 : certificate3375.Sound := rat_cut_bin_certificate_sound certificate3375 profilesValid3375 numericValid3375 valid3375

def retention3376 : RatCutRetentionCertificate := ⟨(29/500),(117/2000),(5087941482371191896/11046666943315150331),(9435637587884634693/1000000000000000000),1,(1100874671476585316586539184936648461/1048404176431626077000000000000000000),false,MergedCutProfiles.Batch518.profile20754,(fun _ => MergedCutProfiles.Batch518.profile20754)⟩
theorem profilesValid3376 : retention3376.ProfilesValid := by
  exact MergedCutProfiles.Batch518.valid20754
theorem numericValid3376 : retention3376.NumericValid := by decide +kernel
def certificate3376 : RatCutBinCertificate := ⟨⟨retention3376,(2263927312165908029/1000000000000000000),(42966716513336319/250000000000000000),(3825645658661106153/250000000000000000),(1017325787371704994593/1000000000000000000),(1024620814892911783/1000000000000000000)⟩,(998148776850135737/1000000000000000000),(119376529369264699/1000000000000000000),(624789418650441357/1000000000000000000),(144083107845232063/250000000000000000)⟩
theorem valid3376 : certificate3376.Valid := by decide +kernel
theorem sound3376 : certificate3376.Sound := rat_cut_bin_certificate_sound certificate3376 profilesValid3376 numericValid3376 valid3376

def retention3377 : RatCutRetentionCertificate := ⟨(29/500),(117/2000),(5509511552028919239/11046666943315150331),(1907978055889196961/62500000000000000),1,(24320659276625646400083002533559952931/24422119115381721100800000000000000000),false,MergedCutProfiles.Batch518.profile20755,(fun _ => MergedCutProfiles.Batch518.profile20755)⟩
theorem profilesValid3377 : retention3377.ProfilesValid := by
  exact MergedCutProfiles.Batch518.valid20755
theorem numericValid3377 : retention3377.NumericValid := by decide +kernel
def certificate3377 : RatCutBinCertificate := ⟨⟨retention3377,(2263927312165908029/1000000000000000000),(42966716513336319/250000000000000000),(3825645658661106153/250000000000000000),(1017325787371704994593/1000000000000000000),(970418740853393733/1000000000000000000)⟩,(998148776850135737/1000000000000000000),(15755527955624891/125000000000000000),(152778325016636609/250000000000000000),(35855001630705819/62500000000000000)⟩
theorem valid3377 : certificate3377.Valid := by decide +kernel
theorem sound3377 : certificate3377.Sound := rat_cut_bin_certificate_sound certificate3377 profilesValid3377 numericValid3377 valid3377

def retention3378 : RatCutRetentionCertificate := ⟨(29/500),(117/2000),(1/2),(16528534656086757717/500000000000000000),1,(131436030093269056222127607895466678783/132228277248694061736000000000000000000),false,MergedCutProfiles.Batch518.profile20753,(fun _ => MergedCutProfiles.Batch518.profile20753)⟩
theorem profilesValid3378 : retention3378.ProfilesValid := by
  exact MergedCutProfiles.Batch518.valid20753
theorem numericValid3378 : retention3378.NumericValid := by decide +kernel
def certificate3378 : RatCutBinCertificate := ⟨⟨retention3378,(2263927312165908029/1000000000000000000),(42966716513336319/250000000000000000),(3825645658661106153/250000000000000000),(1017325787371704994593/1000000000000000000),(96858166482802689/100000000000000000)⟩,(998148776850135737/1000000000000000000),(31570821863312099/250000000000000000),(610628703230063919/1000000000000000000),(143381105960393357/250000000000000000)⟩
theorem valid3378 : certificate3378.Valid := by decide +kernel
theorem sound3378 : certificate3378.Sound := rat_cut_bin_certificate_sound certificate3378 profilesValid3378 numericValid3378 valid3378

def retention3379 : RatCutRetentionCertificate := ⟨(117/2000),(59/1000),(872865926503161502/64964036552798129819),(216055922401772649/250000000000000000),(61/20),(44834144153787865989/20000000000000000000),true,MergedCutProfiles.Batch518.profile20756,![MergedCutProfiles.Batch518.profile20756,MergedCutProfiles.Batch518.profile20757,MergedCutProfiles.Batch518.profile20758,MergedCutProfiles.Batch518.profile20759,MergedCutProfiles.Batch519.profile20760,MergedCutProfiles.Batch519.profile20761,MergedCutProfiles.Batch519.profile20762,MergedCutProfiles.Batch519.profile20763,MergedCutProfiles.Batch519.profile20764,MergedCutProfiles.Batch519.profile20765,MergedCutProfiles.Batch519.profile20766,MergedCutProfiles.Batch519.profile20767,MergedCutProfiles.Batch519.profile20768,MergedCutProfiles.Batch519.profile20769,MergedCutProfiles.Batch519.profile20770,MergedCutProfiles.Batch519.profile20771]⟩
theorem profilesValid3379 : retention3379.ProfilesValid := by
  change ∀ j : Fin 16, (retention3379.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch518.valid20756
  · exact MergedCutProfiles.Batch518.valid20757
  · exact MergedCutProfiles.Batch518.valid20758
  · exact MergedCutProfiles.Batch518.valid20759
  · exact MergedCutProfiles.Batch519.valid20760
  · exact MergedCutProfiles.Batch519.valid20761
  · exact MergedCutProfiles.Batch519.valid20762
  · exact MergedCutProfiles.Batch519.valid20763
  · exact MergedCutProfiles.Batch519.valid20764
  · exact MergedCutProfiles.Batch519.valid20765
  · exact MergedCutProfiles.Batch519.valid20766
  · exact MergedCutProfiles.Batch519.valid20767
  · exact MergedCutProfiles.Batch519.valid20768
  · exact MergedCutProfiles.Batch519.valid20769
  · exact MergedCutProfiles.Batch519.valid20770
  · exact MergedCutProfiles.Batch519.valid20771
theorem numericValid3379 : retention3379.NumericValid := by decide +kernel
def certificate3379 : RatCutBinCertificate := ⟨⟨retention3379,(2189334053155315987/1000000000000000000),(175338961017292427/1000000000000000000),(7720485058765126531/500000000000000000),(1006154796753945849399/1000000000000000000),(54146915466662129/25000000000000000)⟩,(124774668856216279/125000000000000000),(174076045868853439/500000000000000000),(35562624270151059/125000000000000000),(4962855101798361/31250000000000000)⟩
theorem valid3379 : certificate3379.Valid := by decide +kernel
theorem sound3379 : certificate3379.Sound := rat_cut_bin_certificate_sound certificate3379 profilesValid3379 numericValid3379 valid3379

def retention3380 : RatCutRetentionCertificate := ⟨(117/2000),(59/1000),(1044076374599658581/64964036552798129819),(436432963251580751/500000000000000000),3,(3555505835532960573/1600000000000000000),true,MergedCutProfiles.Batch519.profile20772,![MergedCutProfiles.Batch519.profile20772,MergedCutProfiles.Batch519.profile20773,MergedCutProfiles.Batch519.profile20774,MergedCutProfiles.Batch519.profile20775,MergedCutProfiles.Batch519.profile20761,MergedCutProfiles.Batch519.profile20776,MergedCutProfiles.Batch519.profile20777,MergedCutProfiles.Batch519.profile20778,MergedCutProfiles.Batch519.profile20779,MergedCutProfiles.Batch519.profile20767,MergedCutProfiles.Batch519.profile20780,MergedCutProfiles.Batch519.profile20781,MergedCutProfiles.Batch519.profile20782,MergedCutProfiles.Batch519.profile20783,MergedCutProfiles.Batch519.profile20784,MergedCutProfiles.Batch519.profile20785]⟩
theorem profilesValid3380 : retention3380.ProfilesValid := by
  change ∀ j : Fin 16, (retention3380.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch519.valid20772
  · exact MergedCutProfiles.Batch519.valid20773
  · exact MergedCutProfiles.Batch519.valid20774
  · exact MergedCutProfiles.Batch519.valid20775
  · exact MergedCutProfiles.Batch519.valid20761
  · exact MergedCutProfiles.Batch519.valid20776
  · exact MergedCutProfiles.Batch519.valid20777
  · exact MergedCutProfiles.Batch519.valid20778
  · exact MergedCutProfiles.Batch519.valid20779
  · exact MergedCutProfiles.Batch519.valid20767
  · exact MergedCutProfiles.Batch519.valid20780
  · exact MergedCutProfiles.Batch519.valid20781
  · exact MergedCutProfiles.Batch519.valid20782
  · exact MergedCutProfiles.Batch519.valid20783
  · exact MergedCutProfiles.Batch519.valid20784
  · exact MergedCutProfiles.Batch519.valid20785
theorem numericValid3380 : retention3380.NumericValid := by decide +kernel
def certificate3380 : RatCutBinCertificate := ⟨⟨retention3380,(2189334053155315987/1000000000000000000),(175338961017292427/1000000000000000000),(7720485058765126531/500000000000000000),(1006154796753945849399/1000000000000000000),(2147603650048317111/1000000000000000000)⟩,(124774668856216279/125000000000000000),(174724846323432549/500000000000000000),(141567255407074519/500000000000000000),(158829911461791873/1000000000000000000)⟩
theorem valid3380 : certificate3380.Valid := by decide +kernel
theorem sound3380 : certificate3380.Sound := rat_cut_bin_certificate_sound certificate3380 profilesValid3380 numericValid3380 valid3380

def retention3381 : RatCutRetentionCertificate := ⟨(117/2000),(59/1000),(1105243102000000000/64964036552798129819),(1044076374599658581/1000000000000000000),(53/20),(88929912520824951059/40000000000000000000),true,MergedCutProfiles.Batch519.profile20786,![MergedCutProfiles.Batch519.profile20786,MergedCutProfiles.Batch519.profile20787,MergedCutProfiles.Batch519.profile20788,MergedCutProfiles.Batch519.profile20789,MergedCutProfiles.Batch519.profile20790,MergedCutProfiles.Batch519.profile20791,MergedCutProfiles.Batch519.profile20792,MergedCutProfiles.Batch519.profile20793,MergedCutProfiles.Batch519.profile20794,MergedCutProfiles.Batch519.profile20795,MergedCutProfiles.Batch519.profile20796,MergedCutProfiles.Batch519.profile20797,MergedCutProfiles.Batch519.profile20798,MergedCutProfiles.Batch519.profile20799,MergedCutProfiles.Batch520.profile20800,MergedCutProfiles.Batch520.profile20801]⟩
theorem profilesValid3381 : retention3381.ProfilesValid := by
  change ∀ j : Fin 16, (retention3381.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch519.valid20786
  · exact MergedCutProfiles.Batch519.valid20787
  · exact MergedCutProfiles.Batch519.valid20788
  · exact MergedCutProfiles.Batch519.valid20789
  · exact MergedCutProfiles.Batch519.valid20790
  · exact MergedCutProfiles.Batch519.valid20791
  · exact MergedCutProfiles.Batch519.valid20792
  · exact MergedCutProfiles.Batch519.valid20793
  · exact MergedCutProfiles.Batch519.valid20794
  · exact MergedCutProfiles.Batch519.valid20795
  · exact MergedCutProfiles.Batch519.valid20796
  · exact MergedCutProfiles.Batch519.valid20797
  · exact MergedCutProfiles.Batch519.valid20798
  · exact MergedCutProfiles.Batch519.valid20799
  · exact MergedCutProfiles.Batch520.valid20800
  · exact MergedCutProfiles.Batch520.valid20801
theorem numericValid3381 : retention3381.NumericValid := by decide +kernel
def certificate3381 : RatCutBinCertificate := ⟨⟨retention3381,(2189334053155315987/1000000000000000000),(175338961017292427/1000000000000000000),(7720485058765126531/500000000000000000),(1006154796753945849399/1000000000000000000),(2157362425379265067/1000000000000000000)⟩,(124774668856216279/125000000000000000),(320694828326018929/1000000000000000000),(314576928845335071/1000000000000000000),(49363328380055293/250000000000000000)⟩
theorem valid3381 : certificate3381.Valid := by decide +kernel
theorem sound3381 : certificate3381.Sound := rat_cut_bin_certificate_sound certificate3381 profilesValid3381 numericValid3381 valid3381

def retention3382 : RatCutRetentionCertificate := ⟨(117/2000),(59/1000),(1435543078930342455/64964036552798129819),(552621551/500000000),(51/20),(7040594040889911689/3200000000000000000),true,MergedCutProfiles.Batch520.profile20802,![MergedCutProfiles.Batch520.profile20802,MergedCutProfiles.Batch520.profile20803,MergedCutProfiles.Batch520.profile20804,MergedCutProfiles.Batch520.profile20805,MergedCutProfiles.Batch520.profile20806,MergedCutProfiles.Batch520.profile20807,MergedCutProfiles.Batch520.profile20808,MergedCutProfiles.Batch519.profile20780,MergedCutProfiles.Batch520.profile20809,MergedCutProfiles.Batch519.profile20798,MergedCutProfiles.Batch520.profile20810,MergedCutProfiles.Batch520.profile20811,MergedCutProfiles.Batch520.profile20812,MergedCutProfiles.Batch520.profile20813,MergedCutProfiles.Batch520.profile20814,MergedCutProfiles.Batch520.profile20815]⟩
theorem profilesValid3382 : retention3382.ProfilesValid := by
  change ∀ j : Fin 16, (retention3382.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch520.valid20802
  · exact MergedCutProfiles.Batch520.valid20803
  · exact MergedCutProfiles.Batch520.valid20804
  · exact MergedCutProfiles.Batch520.valid20805
  · exact MergedCutProfiles.Batch520.valid20806
  · exact MergedCutProfiles.Batch520.valid20807
  · exact MergedCutProfiles.Batch520.valid20808
  · exact MergedCutProfiles.Batch519.valid20780
  · exact MergedCutProfiles.Batch520.valid20809
  · exact MergedCutProfiles.Batch519.valid20798
  · exact MergedCutProfiles.Batch520.valid20810
  · exact MergedCutProfiles.Batch520.valid20811
  · exact MergedCutProfiles.Batch520.valid20812
  · exact MergedCutProfiles.Batch520.valid20813
  · exact MergedCutProfiles.Batch520.valid20814
  · exact MergedCutProfiles.Batch520.valid20815
theorem numericValid3382 : retention3382.NumericValid := by decide +kernel
def certificate3382 : RatCutBinCertificate := ⟨⟨retention3382,(2189334053155315987/1000000000000000000),(175338961017292427/1000000000000000000),(7720485058765126531/500000000000000000),(1006154796753945849399/1000000000000000000),(2136786564238144351/1000000000000000000)⟩,(124774668856216279/125000000000000000),(63208398571840391/200000000000000000),(319900574671214961/1000000000000000000),(20618952851798513/100000000000000000)⟩
theorem valid3382 : certificate3382.Valid := by decide +kernel
theorem sound3382 : certificate3382.Sound := rat_cut_bin_certificate_sound certificate3382 profilesValid3382 numericValid3382 valid3382

def retention3383 : RatCutRetentionCertificate := ⟨(117/2000),(59/1000),(6984167736388147464/64964036552798129819),(287108615786068491/200000000000000000),(41/20),(482755509339589946259/256000000000000000000),true,MergedCutProfiles.Batch519.profile20763,![MergedCutProfiles.Batch519.profile20763,MergedCutProfiles.Batch519.profile20771,MergedCutProfiles.Batch520.profile20816,MergedCutProfiles.Batch520.profile20817,MergedCutProfiles.Batch520.profile20818,MergedCutProfiles.Batch520.profile20819,MergedCutProfiles.Batch520.profile20820,MergedCutProfiles.Batch520.profile20821,MergedCutProfiles.Batch520.profile20822,MergedCutProfiles.Batch520.profile20823,MergedCutProfiles.Batch520.profile20824,MergedCutProfiles.Batch520.profile20825,MergedCutProfiles.Batch520.profile20826,MergedCutProfiles.Batch520.profile20827,MergedCutProfiles.Batch520.profile20828,MergedCutProfiles.Batch520.profile20829]⟩
theorem profilesValid3383 : retention3383.ProfilesValid := by
  change ∀ j : Fin 16, (retention3383.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch519.valid20763
  · exact MergedCutProfiles.Batch519.valid20771
  · exact MergedCutProfiles.Batch520.valid20816
  · exact MergedCutProfiles.Batch520.valid20817
  · exact MergedCutProfiles.Batch520.valid20818
  · exact MergedCutProfiles.Batch520.valid20819
  · exact MergedCutProfiles.Batch520.valid20820
  · exact MergedCutProfiles.Batch520.valid20821
  · exact MergedCutProfiles.Batch520.valid20822
  · exact MergedCutProfiles.Batch520.valid20823
  · exact MergedCutProfiles.Batch520.valid20824
  · exact MergedCutProfiles.Batch520.valid20825
  · exact MergedCutProfiles.Batch520.valid20826
  · exact MergedCutProfiles.Batch520.valid20827
  · exact MergedCutProfiles.Batch520.valid20828
  · exact MergedCutProfiles.Batch520.valid20829
theorem numericValid3383 : retention3383.NumericValid := by decide +kernel
def certificate3383 : RatCutBinCertificate := ⟨⟨retention3383,(2189334053155315987/1000000000000000000),(175338961017292427/1000000000000000000),(7720485058765126531/500000000000000000),(1006154796753945849399/1000000000000000000),(91739797950883279/50000000000000000)⟩,(124774668856216279/125000000000000000),(8316343737592061/25000000000000000),(150600204916903803/500000000000000000),(206277360524797917/1000000000000000000)⟩
theorem valid3383 : certificate3383.Valid := by decide +kernel
theorem sound3383 : certificate3383.Sound := rat_cut_bin_certificate_sound certificate3383 profilesValid3383 numericValid3383 valid3383

def certificates : List RatCutBinCertificate := [certificate3372,certificate3373,certificate3374,certificate3375,certificate3376,certificate3377,certificate3378,certificate3379,certificate3380,certificate3381,certificate3382,certificate3383]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3372,List.forall_mem_cons.mpr ⟨sound3373,List.forall_mem_cons.mpr ⟨sound3374,List.forall_mem_cons.mpr ⟨sound3375,List.forall_mem_cons.mpr ⟨sound3376,List.forall_mem_cons.mpr ⟨sound3377,List.forall_mem_cons.mpr ⟨sound3378,List.forall_mem_cons.mpr ⟨sound3379,List.forall_mem_cons.mpr ⟨sound3380,List.forall_mem_cons.mpr ⟨sound3381,List.forall_mem_cons.mpr ⟨sound3382,List.forall_mem_cons.mpr ⟨sound3383,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch281
