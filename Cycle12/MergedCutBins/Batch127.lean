import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch245
import Cycle12.MergedCutProfiles.Batch246
import Cycle12.MergedCutProfiles.Batch247

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch127

def retention1524 : RatCutRetentionCertificate := ⟨(1/16),(501/8000),(524414669395744529/5638939790275060547),(868157907783427697/1000000000000000000),(53/20),(2457650463129911168697/1280000000000000000000),true,MergedCutProfiles.Batch245.profile9836,![MergedCutProfiles.Batch245.profile9836,MergedCutProfiles.Batch245.profile9837,MergedCutProfiles.Batch245.profile9838,MergedCutProfiles.Batch245.profile9839,MergedCutProfiles.Batch246.profile9840,MergedCutProfiles.Batch246.profile9841,MergedCutProfiles.Batch246.profile9842,MergedCutProfiles.Batch246.profile9843,MergedCutProfiles.Batch246.profile9844,MergedCutProfiles.Batch246.profile9845,MergedCutProfiles.Batch246.profile9846,MergedCutProfiles.Batch246.profile9847,MergedCutProfiles.Batch246.profile9848,MergedCutProfiles.Batch246.profile9849,MergedCutProfiles.Batch246.profile9850,MergedCutProfiles.Batch246.profile9851]⟩
theorem profilesValid1524 : retention1524.ProfilesValid := by
  change ∀ j : Fin 16, (retention1524.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch245.valid9836
  · exact MergedCutProfiles.Batch245.valid9837
  · exact MergedCutProfiles.Batch245.valid9838
  · exact MergedCutProfiles.Batch245.valid9839
  · exact MergedCutProfiles.Batch246.valid9840
  · exact MergedCutProfiles.Batch246.valid9841
  · exact MergedCutProfiles.Batch246.valid9842
  · exact MergedCutProfiles.Batch246.valid9843
  · exact MergedCutProfiles.Batch246.valid9844
  · exact MergedCutProfiles.Batch246.valid9845
  · exact MergedCutProfiles.Batch246.valid9846
  · exact MergedCutProfiles.Batch246.valid9847
  · exact MergedCutProfiles.Batch246.valid9848
  · exact MergedCutProfiles.Batch246.valid9849
  · exact MergedCutProfiles.Batch246.valid9850
  · exact MergedCutProfiles.Batch246.valid9851
theorem numericValid1524 : retention1524.NumericValid := by decide +kernel
def certificate1524 : RatCutBinCertificate := ⟨⟨retention1524,(2349591658336079509/1000000000000000000),(100998556951347487/500000000000000000),(8306147113163076029/500000000000000000),(46874322267087648777/250000000000000000),(922146935773593383/500000000000000000)⟩,(989961407808733821/1000000000000000000),(68733056253145131/200000000000000000),(289263309985941021/1000000000000000000),(152678849946505861/1000000000000000000)⟩
theorem valid1524 : certificate1524.Valid := by decide +kernel
theorem sound1524 : certificate1524.Sound := rat_cut_bin_certificate_sound certificate1524 profilesValid1524 numericValid1524 valid1524

def retention1525 : RatCutRetentionCertificate := ⟨(1/16),(501/8000),(1905404797139655943/11277879580550121094),(524414669395744529/500000000000000000),(11/5),(1093529895664761772429/640000000000000000000),true,MergedCutProfiles.Batch246.profile9852,![MergedCutProfiles.Batch246.profile9852,MergedCutProfiles.Batch246.profile9853,MergedCutProfiles.Batch246.profile9854,MergedCutProfiles.Batch246.profile9855,MergedCutProfiles.Batch246.profile9856,MergedCutProfiles.Batch246.profile9857,MergedCutProfiles.Batch246.profile9858,MergedCutProfiles.Batch246.profile9859,MergedCutProfiles.Batch246.profile9860,MergedCutProfiles.Batch246.profile9861,MergedCutProfiles.Batch246.profile9862,MergedCutProfiles.Batch246.profile9863,MergedCutProfiles.Batch246.profile9864,MergedCutProfiles.Batch246.profile9865,MergedCutProfiles.Batch246.profile9866,MergedCutProfiles.Batch246.profile9867]⟩
theorem profilesValid1525 : retention1525.ProfilesValid := by
  change ∀ j : Fin 16, (retention1525.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch246.valid9852
  · exact MergedCutProfiles.Batch246.valid9853
  · exact MergedCutProfiles.Batch246.valid9854
  · exact MergedCutProfiles.Batch246.valid9855
  · exact MergedCutProfiles.Batch246.valid9856
  · exact MergedCutProfiles.Batch246.valid9857
  · exact MergedCutProfiles.Batch246.valid9858
  · exact MergedCutProfiles.Batch246.valid9859
  · exact MergedCutProfiles.Batch246.valid9860
  · exact MergedCutProfiles.Batch246.valid9861
  · exact MergedCutProfiles.Batch246.valid9862
  · exact MergedCutProfiles.Batch246.valid9863
  · exact MergedCutProfiles.Batch246.valid9864
  · exact MergedCutProfiles.Batch246.valid9865
  · exact MergedCutProfiles.Batch246.valid9866
  · exact MergedCutProfiles.Batch246.valid9867
theorem numericValid1525 : retention1525.NumericValid := by decide +kernel
def certificate1525 : RatCutBinCertificate := ⟨⟨retention1525,(2349591658336079509/1000000000000000000),(100998556951347487/500000000000000000),(8306147113163076029/500000000000000000),(46874322267087648777/250000000000000000),(102859840523633679/62500000000000000)⟩,(989961407808733821/1000000000000000000),(179309313725439473/500000000000000000),(5472298781008653/20000000000000000),(76348249656673043/500000000000000000)⟩
theorem valid1525 : certificate1525.Valid := by decide +kernel
theorem sound1525 : certificate1525.Sound := rat_cut_bin_certificate_sound certificate1525 profilesValid1525 numericValid1525 valid1525

def retention1526 : RatCutRetentionCertificate := ⟨(1/16),(501/8000),(3978953961771766519/11277879580550121094),(1905404797139655943/1000000000000000000),(7/5),(1635735046988446341091/1280000000000000000000),true,MergedCutProfiles.Batch246.profile9868,![MergedCutProfiles.Batch246.profile9868,MergedCutProfiles.Batch246.profile9869,MergedCutProfiles.Batch246.profile9870,MergedCutProfiles.Batch246.profile9871,MergedCutProfiles.Batch246.profile9872,MergedCutProfiles.Batch246.profile9873,MergedCutProfiles.Batch246.profile9874,MergedCutProfiles.Batch246.profile9875,MergedCutProfiles.Batch246.profile9876,MergedCutProfiles.Batch246.profile9877,MergedCutProfiles.Batch246.profile9878,MergedCutProfiles.Batch246.profile9879,MergedCutProfiles.Batch247.profile9880,MergedCutProfiles.Batch247.profile9881,MergedCutProfiles.Batch247.profile9882,MergedCutProfiles.Batch247.profile9883]⟩
theorem profilesValid1526 : retention1526.ProfilesValid := by
  change ∀ j : Fin 16, (retention1526.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch246.valid9868
  · exact MergedCutProfiles.Batch246.valid9869
  · exact MergedCutProfiles.Batch246.valid9870
  · exact MergedCutProfiles.Batch246.valid9871
  · exact MergedCutProfiles.Batch246.valid9872
  · exact MergedCutProfiles.Batch246.valid9873
  · exact MergedCutProfiles.Batch246.valid9874
  · exact MergedCutProfiles.Batch246.valid9875
  · exact MergedCutProfiles.Batch246.valid9876
  · exact MergedCutProfiles.Batch246.valid9877
  · exact MergedCutProfiles.Batch246.valid9878
  · exact MergedCutProfiles.Batch246.valid9879
  · exact MergedCutProfiles.Batch247.valid9880
  · exact MergedCutProfiles.Batch247.valid9881
  · exact MergedCutProfiles.Batch247.valid9882
  · exact MergedCutProfiles.Batch247.valid9883
theorem numericValid1526 : retention1526.NumericValid := by decide +kernel
def certificate1526 : RatCutBinCertificate := ⟨⟨retention1526,(2349591658336079509/1000000000000000000),(100998556951347487/500000000000000000),(8306147113163076029/500000000000000000),(46874322267087648777/250000000000000000),(77369003969949471/62500000000000000)⟩,(989961407808733821/1000000000000000000),(50081795122897033/125000000000000000),(116441669758170993/500000000000000000),(9551567338916869/62500000000000000)⟩
theorem valid1526 : certificate1526.Valid := by decide +kernel
theorem sound1526 : certificate1526.Sound := rat_cut_bin_certificate_sound certificate1526 profilesValid1526 numericValid1526 valid1526

def retention1527 : RatCutRetentionCertificate := ⟨(1/16),(501/8000),(2628677963696521545/5638939790275060547),(3978953961771766519/1000000000000000000),1,(260493462210809356759/256000000000000000000),true,MergedCutProfiles.Batch246.profile9840,![MergedCutProfiles.Batch246.profile9840,MergedCutProfiles.Batch247.profile9884,MergedCutProfiles.Batch247.profile9885,MergedCutProfiles.Batch247.profile9886,MergedCutProfiles.Batch247.profile9887,MergedCutProfiles.Batch247.profile9888,MergedCutProfiles.Batch247.profile9889,MergedCutProfiles.Batch247.profile9890,MergedCutProfiles.Batch247.profile9891,MergedCutProfiles.Batch247.profile9892,MergedCutProfiles.Batch247.profile9893,MergedCutProfiles.Batch247.profile9894,MergedCutProfiles.Batch247.profile9895,MergedCutProfiles.Batch247.profile9896,MergedCutProfiles.Batch247.profile9897,MergedCutProfiles.Batch247.profile9898]⟩
theorem profilesValid1527 : retention1527.ProfilesValid := by
  change ∀ j : Fin 16, (retention1527.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch246.valid9840
  · exact MergedCutProfiles.Batch247.valid9884
  · exact MergedCutProfiles.Batch247.valid9885
  · exact MergedCutProfiles.Batch247.valid9886
  · exact MergedCutProfiles.Batch247.valid9887
  · exact MergedCutProfiles.Batch247.valid9888
  · exact MergedCutProfiles.Batch247.valid9889
  · exact MergedCutProfiles.Batch247.valid9890
  · exact MergedCutProfiles.Batch247.valid9891
  · exact MergedCutProfiles.Batch247.valid9892
  · exact MergedCutProfiles.Batch247.valid9893
  · exact MergedCutProfiles.Batch247.valid9894
  · exact MergedCutProfiles.Batch247.valid9895
  · exact MergedCutProfiles.Batch247.valid9896
  · exact MergedCutProfiles.Batch247.valid9897
  · exact MergedCutProfiles.Batch247.valid9898
theorem numericValid1527 : retention1527.NumericValid := by decide +kernel
def certificate1527 : RatCutBinCertificate := ⟨⟨retention1527,(2349591658336079509/1000000000000000000),(100998556951347487/500000000000000000),(8306147113163076029/500000000000000000),(46874322267087648777/250000000000000000),(197795000494534129/200000000000000000)⟩,(989961407808733821/1000000000000000000),(44070435499007109/100000000000000000),(99095240832221741/500000000000000000),(155208364911547723/1000000000000000000)⟩
theorem valid1527 : certificate1527.Valid := by decide +kernel
theorem sound1527 : certificate1527.Sound := rat_cut_bin_certificate_sound certificate1527 profilesValid1527 numericValid1527 valid1527

def retention1528 : RatCutRetentionCertificate := ⟨(1/16),(501/8000),(2790394627904661562/5638939790275060547),(525735592739304309/100000000000000000),(11/10),(526112858021243731354720996859694131/525735592739304309000000000000000000),false,MergedCutProfiles.Batch247.profile9899,(fun _ => MergedCutProfiles.Batch247.profile9899)⟩
theorem profilesValid1528 : retention1528.ProfilesValid := by
  exact MergedCutProfiles.Batch247.valid9899
theorem numericValid1528 : retention1528.NumericValid := by decide +kernel
def certificate1528 : RatCutBinCertificate := ⟨⟨retention1528,(2349591658336079509/1000000000000000000),(100998556951347487/500000000000000000),(8306147113163076029/500000000000000000),(46874322267087648777/250000000000000000),(969284906929979889/1000000000000000000)⟩,(989961407808733821/1000000000000000000),(435796168567377889/1000000000000000000),(50559881447082139/250000000000000000),(152943185747343009/1000000000000000000)⟩
theorem valid1528 : certificate1528.Valid := by decide +kernel
theorem sound1528 : certificate1528.Sound := rat_cut_bin_certificate_sound certificate1528 profilesValid1528 numericValid1528 valid1528

def retention1529 : RatCutRetentionCertificate := ⟨(1/16),(501/8000),(2818298574183708178/5638939790275060547),(1395197313952330781/250000000000000000),(11/10),(554289293606663790605907787877472347551/558078925580932312400000000000000000000),false,MergedCutProfiles.Batch247.profile9900,(fun _ => MergedCutProfiles.Batch247.profile9900)⟩
theorem profilesValid1529 : retention1529.ProfilesValid := by
  exact MergedCutProfiles.Batch247.valid9900
theorem numericValid1529 : retention1529.NumericValid := by decide +kernel
def certificate1529 : RatCutBinCertificate := ⟨⟨retention1529,(2349591658336079509/1000000000000000000),(100998556951347487/500000000000000000),(8306147113163076029/500000000000000000),(46874322267087648777/250000000000000000),(961777156454787703/1000000000000000000)⟩,(989961407808733821/1000000000000000000),(436678328764302601/1000000000000000000),(6297116410447531/31250000000000000),(38133177440677293/250000000000000000)⟩
theorem valid1529 : certificate1529.Valid := by decide +kernel
theorem sound1529 : certificate1529.Sound := rat_cut_bin_certificate_sound certificate1529 profilesValid1529 numericValid1529 valid1529

def retention1530 : RatCutRetentionCertificate := ⟨(1/16),(501/8000),(1/2),(1409149287091854089/250000000000000000),(11/10),(17493097756089457531103482625030761733/17614366088648176112500000000000000000),false,MergedCutProfiles.Batch247.profile9901,(fun _ => MergedCutProfiles.Batch247.profile9901)⟩
theorem profilesValid1530 : retention1530.ProfilesValid := by
  exact MergedCutProfiles.Batch247.valid9901
theorem numericValid1530 : retention1530.NumericValid := by decide +kernel
def certificate1530 : RatCutBinCertificate := ⟨⟨retention1530,(2349591658336079509/1000000000000000000),(100998556951347487/500000000000000000),(8306147113163076029/500000000000000000),(46874322267087648777/250000000000000000),(480841539591124201/500000000000000000)⟩,(989961407808733821/1000000000000000000),(218157743286372027/500000000000000000),(201808506872376509/1000000000000000000),(152937292174688313/1000000000000000000)⟩
theorem valid1530 : certificate1530.Valid := by decide +kernel
theorem sound1530 : certificate1530.Sound := rat_cut_bin_certificate_sound certificate1530 profilesValid1530 numericValid1530 valid1530

def retention1531 : RatCutRetentionCertificate := ⟨(1/16),(501/8000),(1/2),64,1,(63853046903933876428655859367824142999/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch247.profile9901,(fun _ => MergedCutProfiles.Batch247.profile9901)⟩
theorem profilesValid1531 : retention1531.ProfilesValid := by
  exact MergedCutProfiles.Batch247.valid9901
theorem numericValid1531 : retention1531.NumericValid := by decide +kernel
def certificate1531 : RatCutBinCertificate := ⟨⟨retention1531,(2349591658336079509/1000000000000000000),(100998556951347487/500000000000000000),(8306147113163076029/500000000000000000),(46874322267087648777/250000000000000000),(193826705634838627/200000000000000000)⟩,(989961407808733821/1000000000000000000),(396261323083753091/1000000000000000000),(29615680521479419/125000000000000000),(27986802703506933/125000000000000000)⟩
theorem valid1531 : certificate1531.Valid := by decide +kernel
theorem sound1531 : certificate1531.Sound := rat_cut_bin_certificate_sound certificate1531 profilesValid1531 numericValid1531 valid1531

def retention1532 : RatCutRetentionCertificate := ⟨(1/16),(501/8000),(2628799504410147041/5638939790275060547),(3359894490835449699/1000000000000000000),(6/5),(355457790855225033758240772766732522439/335989449083544969900000000000000000000),false,MergedCutProfiles.Batch247.profile9902,(fun _ => MergedCutProfiles.Batch247.profile9902)⟩
theorem profilesValid1532 : retention1532.ProfilesValid := by
  exact MergedCutProfiles.Batch247.valid9902
theorem numericValid1532 : retention1532.NumericValid := by decide +kernel
def certificate1532 : RatCutBinCertificate := ⟨⟨retention1532,(2667362315336079509/1000000000000000000),(100998556951347487/500000000000000000),(8306147113163076029/500000000000000000),(46874322267087648777/250000000000000000),(15922068400590417/15625000000000000)⟩,(197719969143142513/200000000000000000),(194912245515495413/500000000000000000),(242936144258208521/1000000000000000000),(168239896114192571/1000000000000000000)⟩
theorem valid1532 : certificate1532.Valid := by decide +kernel
theorem sound1532 : certificate1532.Sound := rat_cut_bin_certificate_sound certificate1532 profilesValid1532 numericValid1532 valid1532

def retention1533 : RatCutRetentionCertificate := ⟨(1/16),(501/8000),(2790523645821293452/5638939790275060547),(2628799504410147041/500000000000000000),(11/10),(131528757393065487320047311227826760141/131439975220507352050000000000000000000),false,MergedCutProfiles.Batch247.profile9903,(fun _ => MergedCutProfiles.Batch247.profile9903)⟩
theorem profilesValid1533 : retention1533.ProfilesValid := by
  exact MergedCutProfiles.Batch247.valid9903
theorem numericValid1533 : retention1533.NumericValid := by decide +kernel
def certificate1533 : RatCutBinCertificate := ⟨⟨retention1533,(2667362315336079509/1000000000000000000),(100998556951347487/500000000000000000),(8306147113163076029/500000000000000000),(46874322267087648777/250000000000000000),(964991654373546593/1000000000000000000)⟩,(197719969143142513/200000000000000000),(25727941510334079/62500000000000000),(13936163371338107/62500000000000000),(83874132924150539/500000000000000000)⟩
theorem valid1533 : certificate1533.Valid := by decide +kernel
theorem sound1533 : certificate1533.Sound := rat_cut_bin_certificate_sound certificate1533 profilesValid1533 numericValid1533 valid1533

def retention1534 : RatCutRetentionCertificate := ⟨(1/16),(501/8000),(2818428882279506387/5638939790275060547),(697630911455323363/125000000000000000),(11/10),(554290912728836050944666842981000768791/558104729164258690400000000000000000000),false,MergedCutProfiles.Batch247.profile9904,(fun _ => MergedCutProfiles.Batch247.profile9904)⟩
theorem profilesValid1534 : retention1534.ProfilesValid := by
  exact MergedCutProfiles.Batch247.valid9904
theorem numericValid1534 : retention1534.NumericValid := by decide +kernel
def certificate1534 : RatCutBinCertificate := ⟨⟨retention1534,(2667362315336079509/1000000000000000000),(100998556951347487/500000000000000000),(8306147113163076029/500000000000000000),(46874322267087648777/250000000000000000),(478741533849446361/500000000000000000)⟩,(197719969143142513/200000000000000000),(414875202359037389/1000000000000000000),(110063034063858269/500000000000000000),(165746861564264303/1000000000000000000)⟩
theorem valid1534 : certificate1534.Valid := by decide +kernel
theorem sound1534 : certificate1534.Sound := rat_cut_bin_certificate_sound certificate1534 profilesValid1534 numericValid1534 valid1534

def retention1535 : RatCutRetentionCertificate := ⟨(1/16),(501/8000),(1/2),(2818428882279506387/500000000000000000),(21/20),(2206593782895379904123569618341876301151/2254743105823605109600000000000000000000),false,MergedCutProfiles.Batch247.profile9901,(fun _ => MergedCutProfiles.Batch247.profile9901)⟩
theorem profilesValid1535 : retention1535.ProfilesValid := by
  exact MergedCutProfiles.Batch247.valid9901
theorem numericValid1535 : retention1535.NumericValid := by decide +kernel
def certificate1535 : RatCutBinCertificate := ⟨⟨retention1535,(2667362315336079509/1000000000000000000),(100998556951347487/500000000000000000),(8306147113163076029/500000000000000000),(46874322267087648777/250000000000000000),(236145912545567861/250000000000000000)⟩,(197719969143142513/200000000000000000),(420540818582110151/1000000000000000000),(215180234450559131/1000000000000000000),(165963272414206893/1000000000000000000)⟩
theorem valid1535 : certificate1535.Valid := by decide +kernel
theorem sound1535 : certificate1535.Sound := rat_cut_bin_certificate_sound certificate1535 profilesValid1535 numericValid1535 valid1535

def certificates : List RatCutBinCertificate := [certificate1524,certificate1525,certificate1526,certificate1527,certificate1528,certificate1529,certificate1530,certificate1531,certificate1532,certificate1533,certificate1534,certificate1535]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1524,List.forall_mem_cons.mpr ⟨sound1525,List.forall_mem_cons.mpr ⟨sound1526,List.forall_mem_cons.mpr ⟨sound1527,List.forall_mem_cons.mpr ⟨sound1528,List.forall_mem_cons.mpr ⟨sound1529,List.forall_mem_cons.mpr ⟨sound1530,List.forall_mem_cons.mpr ⟨sound1531,List.forall_mem_cons.mpr ⟨sound1532,List.forall_mem_cons.mpr ⟨sound1533,List.forall_mem_cons.mpr ⟨sound1534,List.forall_mem_cons.mpr ⟨sound1535,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch127
