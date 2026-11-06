import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch225
import Cycle12.MergedCutProfiles.Batch226
import Cycle12.MergedCutProfiles.Batch227

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch115

def retention1380 : RatCutRetentionCertificate := ⟨(239/4000),(3/50),(6219826738242945107/12486961035491489733),(307912214764502233/50000000000000000),(21/20),(6069884306450579922849276110601712259/6158244295290044660000000000000000000),false,MergedCutProfiles.Batch225.profile9013,(fun _ => MergedCutProfiles.Batch225.profile9013)⟩
theorem profilesValid1380 : retention1380.ProfilesValid := by
  exact MergedCutProfiles.Batch225.valid9013
theorem numericValid1380 : retention1380.NumericValid := by decide +kernel
def certificate1380 : RatCutBinCertificate := ⟨⟨retention1380,(1164008638755611433/500000000000000000),(182428996879551849/1000000000000000000),(3947309366890257321/250000000000000000),(197461089196585477267/1000000000000000000),(239351222799225783/250000000000000000)⟩,(9903184537773961/10000000000000000),(451092595216070049/1000000000000000000),(94900073595146937/500000000000000000),(75041550054981387/500000000000000000)⟩
theorem valid1380 : certificate1380.Valid := by decide +kernel
theorem sound1380 : certificate1380.Sound := rat_cut_bin_certificate_sound certificate1380 profilesValid1380 numericValid1380 valid1380

def retention1381 : RatCutRetentionCertificate := ⟨(239/4000),(3/50),(1/2),(6219826738242945107/1000000000000000000),(21/20),(9776922909028435604239259077478042662151/9951722781188712171200000000000000000000),false,MergedCutProfiles.Batch225.profile9014,(fun _ => MergedCutProfiles.Batch225.profile9014)⟩
theorem profilesValid1381 : retention1381.ProfilesValid := by
  exact MergedCutProfiles.Batch225.valid9014
theorem numericValid1381 : retention1381.NumericValid := by decide +kernel
def certificate1381 : RatCutBinCertificate := ⟨⟨retention1381,(1164008638755611433/500000000000000000),(182428996879551849/1000000000000000000),(3947309366890257321/250000000000000000),(197461089196585477267/1000000000000000000),(238547097390614187/250000000000000000)⟩,(9903184537773961/10000000000000000),(90444015111243539/200000000000000000),(23612999660305281/125000000000000000),(7455870450713413/50000000000000000)⟩
theorem valid1381 : certificate1381.Valid := by decide +kernel
theorem sound1381 : certificate1381.Sound := rat_cut_bin_certificate_sound certificate1381 profilesValid1381 numericValid1381 valid1381

def retention1382 : RatCutRetentionCertificate := ⟨(239/4000),(3/50),(1/2),64,1,(2554078432212382798374162733929235551/2560000000000000000000000000000000000),false,MergedCutProfiles.Batch225.profile9014,(fun _ => MergedCutProfiles.Batch225.profile9014)⟩
theorem profilesValid1382 : retention1382.ProfilesValid := by
  exact MergedCutProfiles.Batch225.valid9014
theorem numericValid1382 : retention1382.NumericValid := by decide +kernel
def certificate1382 : RatCutBinCertificate := ⟨⟨retention1382,(1164008638755611433/500000000000000000),(182428996879551849/1000000000000000000),(3947309366890257321/250000000000000000),(197461089196585477267/1000000000000000000),(970788565972391613/1000000000000000000)⟩,(9903184537773961/10000000000000000),(409602595398968717/1000000000000000000),(112399143040948241/500000000000000000),(212869774202925683/1000000000000000000)⟩
theorem valid1382 : certificate1382.Valid := by decide +kernel
theorem sound1382 : certificate1382.Sound := rat_cut_bin_certificate_sound certificate1382 profilesValid1382 numericValid1382 valid1382

def retention1383 : RatCutRetentionCertificate := ⟨(239/4000),(3/50),(5831653292541842770/12486961035491489733),(3510763974248104549/1000000000000000000),(6/5),(371602986198451943635520461021725790439/351076397424810454900000000000000000000),false,MergedCutProfiles.Batch225.profile9015,(fun _ => MergedCutProfiles.Batch225.profile9015)⟩
theorem profilesValid1383 : retention1383.ProfilesValid := by
  exact MergedCutProfiles.Batch225.valid9015
theorem numericValid1383 : retention1383.NumericValid := by decide +kernel
def certificate1383 : RatCutBinCertificate := ⟨⟨retention1383,(1321743700255611433/500000000000000000),(182428996879551849/1000000000000000000),(3947309366890257321/250000000000000000),(197461089196585477267/1000000000000000000),(510904046436799639/500000000000000000)⟩,(3956013305258707/4000000000000000),(393721921375203799/1000000000000000000),(239284155782335471/1000000000000000000),(167430518172740431/1000000000000000000)⟩
theorem valid1383 : certificate1383.Valid := by decide +kernel
theorem sound1383 : certificate1383.Sound := rat_cut_bin_certificate_sound certificate1383 profilesValid1383 numericValid1383 valid1383

def retention1384 : RatCutRetentionCertificate := ⟨(239/4000),(3/50),(6190417481351834450/12486961035491489733),(583165329254184277/100000000000000000),(21/20),(92185827660648648802531596839345759759/93306452680669484320000000000000000000),false,MergedCutProfiles.Batch225.profile9016,(fun _ => MergedCutProfiles.Batch225.profile9016)⟩
theorem profilesValid1384 : retention1384.ProfilesValid := by
  exact MergedCutProfiles.Batch225.valid9016
theorem numericValid1384 : retention1384.NumericValid := by decide +kernel
def certificate1384 : RatCutBinCertificate := ⟨⟨retention1384,(1321743700255611433/500000000000000000),(182428996879551849/1000000000000000000),(3947309366890257321/250000000000000000),(197461089196585477267/1000000000000000000),(191182996731349191/200000000000000000)⟩,(3956013305258707/4000000000000000),(1643991998508873/3906250000000000),(107451097158207093/500000000000000000),(168304961059369641/1000000000000000000)⟩
theorem valid1384 : certificate1384.Valid := by decide +kernel
theorem sound1384 : certificate1384.Sound := rat_cut_bin_certificate_sound certificate1384 profilesValid1384 numericValid1384 valid1384

def retention1385 : RatCutRetentionCertificate := ⟨(239/4000),(3/50),(1/2),(123808349627036689/20000000000000000),(21/20),(3891591703743761880163606100751657239/3961867188065174048000000000000000000),false,MergedCutProfiles.Batch225.profile9014,(fun _ => MergedCutProfiles.Batch225.profile9014)⟩
theorem profilesValid1385 : retention1385.ProfilesValid := by
  exact MergedCutProfiles.Batch225.valid9014
theorem numericValid1385 : retention1385.NumericValid := by decide +kernel
def certificate1385 : RatCutBinCertificate := ⟨⟨retention1385,(1321743700255611433/500000000000000000),(182428996879551849/1000000000000000000),(3947309366890257321/250000000000000000),(197461089196585477267/1000000000000000000),(118773431122437621/125000000000000000)⟩,(3956013305258707/4000000000000000),(42339882097475007/100000000000000000),(212714344254409463/1000000000000000000),(33394999219513223/200000000000000000)⟩
theorem valid1385 : certificate1385.Valid := by decide +kernel
theorem sound1385 : certificate1385.Sound := rat_cut_bin_certificate_sound certificate1385 profilesValid1385 numericValid1385 valid1385

def retention1386 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(837722493136938411/12243847427121716584),(414714105513335847/500000000000000000),(14/5),(79656053960687614287/40000000000000000000),true,MergedCutProfiles.Batch225.profile9017,![MergedCutProfiles.Batch225.profile9017,MergedCutProfiles.Batch225.profile9018,MergedCutProfiles.Batch225.profile9019,MergedCutProfiles.Batch225.profile9020,MergedCutProfiles.Batch225.profile9021,MergedCutProfiles.Batch225.profile9022,MergedCutProfiles.Batch225.profile9023,MergedCutProfiles.Batch225.profile9024,MergedCutProfiles.Batch225.profile9025,MergedCutProfiles.Batch225.profile9026,MergedCutProfiles.Batch225.profile9027,MergedCutProfiles.Batch225.profile9028,MergedCutProfiles.Batch225.profile9029,MergedCutProfiles.Batch225.profile9030,MergedCutProfiles.Batch225.profile9031,MergedCutProfiles.Batch225.profile9032]⟩
theorem profilesValid1386 : retention1386.ProfilesValid := by
  change ∀ j : Fin 16, (retention1386.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch225.valid9017
  · exact MergedCutProfiles.Batch225.valid9018
  · exact MergedCutProfiles.Batch225.valid9019
  · exact MergedCutProfiles.Batch225.valid9020
  · exact MergedCutProfiles.Batch225.valid9021
  · exact MergedCutProfiles.Batch225.valid9022
  · exact MergedCutProfiles.Batch225.valid9023
  · exact MergedCutProfiles.Batch225.valid9024
  · exact MergedCutProfiles.Batch225.valid9025
  · exact MergedCutProfiles.Batch225.valid9026
  · exact MergedCutProfiles.Batch225.valid9027
  · exact MergedCutProfiles.Batch225.valid9028
  · exact MergedCutProfiles.Batch225.valid9029
  · exact MergedCutProfiles.Batch225.valid9030
  · exact MergedCutProfiles.Batch225.valid9031
  · exact MergedCutProfiles.Batch225.valid9032
theorem numericValid1386 : retention1386.NumericValid := by decide +kernel
def certificate1386 : RatCutBinCertificate := ⟨⟨retention1386,(142327569108315713/62500000000000000),(93024059904071007/500000000000000000),(7930683632767192701/500000000000000000),(194800079243672712331/1000000000000000000),(958289591682780121/500000000000000000)⟩,(123802645772514271/125000000000000000),(91495765889628447/250000000000000000),(8316834795637553/31250000000000000),(139068931114733083/1000000000000000000)⟩
theorem valid1386 : certificate1386.Valid := by decide +kernel
theorem sound1386 : certificate1386.Sound := rat_cut_bin_certificate_sound certificate1386 profilesValid1386 numericValid1386 valid1386

def retention1387 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(449075950073666867/6121923713560858292),(837722493136938411/1000000000000000000),(11/4),(3946513699485271863/2000000000000000000),true,MergedCutProfiles.Batch225.profile9033,![MergedCutProfiles.Batch225.profile9033,MergedCutProfiles.Batch225.profile9034,MergedCutProfiles.Batch225.profile9035,MergedCutProfiles.Batch225.profile9036,MergedCutProfiles.Batch225.profile9037,MergedCutProfiles.Batch225.profile9038,MergedCutProfiles.Batch225.profile9039,MergedCutProfiles.Batch226.profile9040,MergedCutProfiles.Batch226.profile9041,MergedCutProfiles.Batch226.profile9042,MergedCutProfiles.Batch226.profile9043,MergedCutProfiles.Batch226.profile9044,MergedCutProfiles.Batch226.profile9045,MergedCutProfiles.Batch225.profile9031,MergedCutProfiles.Batch226.profile9046,MergedCutProfiles.Batch226.profile9047]⟩
theorem profilesValid1387 : retention1387.ProfilesValid := by
  change ∀ j : Fin 16, (retention1387.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch225.valid9033
  · exact MergedCutProfiles.Batch225.valid9034
  · exact MergedCutProfiles.Batch225.valid9035
  · exact MergedCutProfiles.Batch225.valid9036
  · exact MergedCutProfiles.Batch225.valid9037
  · exact MergedCutProfiles.Batch225.valid9038
  · exact MergedCutProfiles.Batch225.valid9039
  · exact MergedCutProfiles.Batch226.valid9040
  · exact MergedCutProfiles.Batch226.valid9041
  · exact MergedCutProfiles.Batch226.valid9042
  · exact MergedCutProfiles.Batch226.valid9043
  · exact MergedCutProfiles.Batch226.valid9044
  · exact MergedCutProfiles.Batch226.valid9045
  · exact MergedCutProfiles.Batch225.valid9031
  · exact MergedCutProfiles.Batch226.valid9046
  · exact MergedCutProfiles.Batch226.valid9047
theorem numericValid1387 : retention1387.NumericValid := by decide +kernel
def certificate1387 : RatCutBinCertificate := ⟨⟨retention1387,(142327569108315713/62500000000000000),(93024059904071007/500000000000000000),(7930683632767192701/500000000000000000),(194800079243672712331/1000000000000000000),(1899770549480559609/1000000000000000000)⟩,(123802645772514271/125000000000000000),(73536887081545537/200000000000000000),(132216336932422687/500000000000000000),(69451828133784139/500000000000000000)⟩
theorem valid1387 : certificate1387.Valid := by decide +kernel
theorem sound1387 : certificate1387.Sound := rat_cut_bin_certificate_sound certificate1387 profilesValid1387 numericValid1387 valid1387

def retention1388 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(1247254638842694883/12243847427121716584),(449075950073666867/500000000000000000),(13/5),(303295956969773918843/160000000000000000000),true,MergedCutProfiles.Batch226.profile9048,![MergedCutProfiles.Batch226.profile9048,MergedCutProfiles.Batch225.profile9019,MergedCutProfiles.Batch226.profile9049,MergedCutProfiles.Batch226.profile9050,MergedCutProfiles.Batch226.profile9051,MergedCutProfiles.Batch226.profile9052,MergedCutProfiles.Batch226.profile9053,MergedCutProfiles.Batch226.profile9054,MergedCutProfiles.Batch226.profile9055,MergedCutProfiles.Batch226.profile9056,MergedCutProfiles.Batch226.profile9057,MergedCutProfiles.Batch226.profile9058,MergedCutProfiles.Batch226.profile9059,MergedCutProfiles.Batch226.profile9060,MergedCutProfiles.Batch226.profile9061,MergedCutProfiles.Batch226.profile9062]⟩
theorem profilesValid1388 : retention1388.ProfilesValid := by
  change ∀ j : Fin 16, (retention1388.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch226.valid9048
  · exact MergedCutProfiles.Batch225.valid9019
  · exact MergedCutProfiles.Batch226.valid9049
  · exact MergedCutProfiles.Batch226.valid9050
  · exact MergedCutProfiles.Batch226.valid9051
  · exact MergedCutProfiles.Batch226.valid9052
  · exact MergedCutProfiles.Batch226.valid9053
  · exact MergedCutProfiles.Batch226.valid9054
  · exact MergedCutProfiles.Batch226.valid9055
  · exact MergedCutProfiles.Batch226.valid9056
  · exact MergedCutProfiles.Batch226.valid9057
  · exact MergedCutProfiles.Batch226.valid9058
  · exact MergedCutProfiles.Batch226.valid9059
  · exact MergedCutProfiles.Batch226.valid9060
  · exact MergedCutProfiles.Batch226.valid9061
  · exact MergedCutProfiles.Batch226.valid9062
theorem numericValid1388 : retention1388.NumericValid := by decide +kernel
def certificate1388 : RatCutBinCertificate := ⟨⟨retention1388,(142327569108315713/62500000000000000),(93024059904071007/500000000000000000),(7930683632767192701/500000000000000000),(194800079243672712331/1000000000000000000),(913061081156821673/500000000000000000)⟩,(123802645772514271/125000000000000000),(92939205621806587/250000000000000000),(10415239516985441/40000000000000000),(69483022768186099/500000000000000000)⟩
theorem valid1388 : certificate1388.Valid := by decide +kernel
theorem sound1388 : certificate1388.Sound := rat_cut_bin_certificate_sound certificate1388 profilesValid1388 numericValid1388 valid1388

def retention1389 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(677582672688640501/3060961856780429146),(1247254638842694883/1000000000000000000),(39/20),(2021547821916479267523/1280000000000000000000),true,MergedCutProfiles.Batch225.profile9035,![MergedCutProfiles.Batch225.profile9035,MergedCutProfiles.Batch226.profile9063,MergedCutProfiles.Batch226.profile9064,MergedCutProfiles.Batch226.profile9065,MergedCutProfiles.Batch226.profile9066,MergedCutProfiles.Batch226.profile9067,MergedCutProfiles.Batch226.profile9068,MergedCutProfiles.Batch226.profile9069,MergedCutProfiles.Batch226.profile9070,MergedCutProfiles.Batch226.profile9071,MergedCutProfiles.Batch226.profile9072,MergedCutProfiles.Batch226.profile9073,MergedCutProfiles.Batch226.profile9074,MergedCutProfiles.Batch226.profile9075,MergedCutProfiles.Batch226.profile9076,MergedCutProfiles.Batch226.profile9077]⟩
theorem profilesValid1389 : retention1389.ProfilesValid := by
  change ∀ j : Fin 16, (retention1389.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch225.valid9035
  · exact MergedCutProfiles.Batch226.valid9063
  · exact MergedCutProfiles.Batch226.valid9064
  · exact MergedCutProfiles.Batch226.valid9065
  · exact MergedCutProfiles.Batch226.valid9066
  · exact MergedCutProfiles.Batch226.valid9067
  · exact MergedCutProfiles.Batch226.valid9068
  · exact MergedCutProfiles.Batch226.valid9069
  · exact MergedCutProfiles.Batch226.valid9070
  · exact MergedCutProfiles.Batch226.valid9071
  · exact MergedCutProfiles.Batch226.valid9072
  · exact MergedCutProfiles.Batch226.valid9073
  · exact MergedCutProfiles.Batch226.valid9074
  · exact MergedCutProfiles.Batch226.valid9075
  · exact MergedCutProfiles.Batch226.valid9076
  · exact MergedCutProfiles.Batch226.valid9077
theorem numericValid1389 : retention1389.NumericValid := by decide +kernel
def certificate1389 : RatCutBinCertificate := ⟨⟨retention1389,(142327569108315713/62500000000000000),(93024059904071007/500000000000000000),(7930683632767192701/500000000000000000),(194800079243672712331/1000000000000000000),(305445381700997941/200000000000000000)⟩,(123802645772514271/125000000000000000),(197304189831755951/500000000000000000),(238458918656233713/1000000000000000000),(139648734955466539/1000000000000000000)⟩
theorem valid1389 : certificate1389.Valid := by decide +kernel
theorem sound1389 : certificate1389.Sound := rat_cut_bin_certificate_sound certificate1389 profilesValid1389 numericValid1389 valid1389

def retention1390 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(5022818179150749059/12243847427121716584),(677582672688640501/250000000000000000),(6/5),(369370508355603677421/320000000000000000000),true,MergedCutProfiles.Batch226.profile9078,![MergedCutProfiles.Batch226.profile9078,MergedCutProfiles.Batch225.profile9028,MergedCutProfiles.Batch226.profile9079,MergedCutProfiles.Batch227.profile9080,MergedCutProfiles.Batch227.profile9081,MergedCutProfiles.Batch227.profile9082,MergedCutProfiles.Batch227.profile9083,MergedCutProfiles.Batch227.profile9084,MergedCutProfiles.Batch227.profile9085,MergedCutProfiles.Batch227.profile9086,MergedCutProfiles.Batch227.profile9087,MergedCutProfiles.Batch227.profile9088,MergedCutProfiles.Batch227.profile9089,MergedCutProfiles.Batch227.profile9090,MergedCutProfiles.Batch227.profile9091,MergedCutProfiles.Batch227.profile9092]⟩
theorem profilesValid1390 : retention1390.ProfilesValid := by
  change ∀ j : Fin 16, (retention1390.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch226.valid9078
  · exact MergedCutProfiles.Batch225.valid9028
  · exact MergedCutProfiles.Batch226.valid9079
  · exact MergedCutProfiles.Batch227.valid9080
  · exact MergedCutProfiles.Batch227.valid9081
  · exact MergedCutProfiles.Batch227.valid9082
  · exact MergedCutProfiles.Batch227.valid9083
  · exact MergedCutProfiles.Batch227.valid9084
  · exact MergedCutProfiles.Batch227.valid9085
  · exact MergedCutProfiles.Batch227.valid9086
  · exact MergedCutProfiles.Batch227.valid9087
  · exact MergedCutProfiles.Batch227.valid9088
  · exact MergedCutProfiles.Batch227.valid9089
  · exact MergedCutProfiles.Batch227.valid9090
  · exact MergedCutProfiles.Batch227.valid9091
  · exact MergedCutProfiles.Batch227.valid9092
theorem numericValid1390 : retention1390.NumericValid := by decide +kernel
def certificate1390 : RatCutBinCertificate := ⟨⟨retention1390,(142327569108315713/62500000000000000),(93024059904071007/500000000000000000),(7930683632767192701/500000000000000000),(194800079243672712331/1000000000000000000),(561109982709644319/500000000000000000)⟩,(123802645772514271/125000000000000000),(442699519845622423/1000000000000000000),(196560214419853387/1000000000000000000),(141194099244942019/1000000000000000000)⟩
theorem valid1390 : certificate1390.Valid := by decide +kernel
theorem sound1390 : certificate1390.Sound := rat_cut_bin_certificate_sound certificate1390 profilesValid1390 numericValid1390 valid1390

def retention1391 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(2974272913774385587/6121923713560858292),(5022818179150749059/1000000000000000000),(11/10),(2041612405346329998052957457496232812559/2009127271660299623600000000000000000000),false,MergedCutProfiles.Batch227.profile9093,(fun _ => MergedCutProfiles.Batch227.profile9093)⟩
theorem profilesValid1391 : retention1391.ProfilesValid := by
  exact MergedCutProfiles.Batch227.valid9093
theorem numericValid1391 : retention1391.NumericValid := by decide +kernel
def certificate1391 : RatCutBinCertificate := ⟨⟨retention1391,(142327569108315713/62500000000000000),(93024059904071007/500000000000000000),(7930683632767192701/500000000000000000),(194800079243672712331/1000000000000000000),(15418458757203547/15625000000000000)⟩,(123802645772514271/125000000000000000),(115340105321593537/250000000000000000),(90871084239838109/500000000000000000),(138786446483696849/1000000000000000000)⟩
theorem valid1391 : certificate1391.Valid := by decide +kernel
theorem sound1391 : certificate1391.Sound := rat_cut_bin_certificate_sound certificate1391 profilesValid1391 numericValid1391 valid1391

def certificates : List RatCutBinCertificate := [certificate1380,certificate1381,certificate1382,certificate1383,certificate1384,certificate1385,certificate1386,certificate1387,certificate1388,certificate1389,certificate1390,certificate1391]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1380,List.forall_mem_cons.mpr ⟨sound1381,List.forall_mem_cons.mpr ⟨sound1382,List.forall_mem_cons.mpr ⟨sound1383,List.forall_mem_cons.mpr ⟨sound1384,List.forall_mem_cons.mpr ⟨sound1385,List.forall_mem_cons.mpr ⟨sound1386,List.forall_mem_cons.mpr ⟨sound1387,List.forall_mem_cons.mpr ⟨sound1388,List.forall_mem_cons.mpr ⟨sound1389,List.forall_mem_cons.mpr ⟨sound1390,List.forall_mem_cons.mpr ⟨sound1391,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch115
