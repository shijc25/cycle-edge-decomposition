import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch144
import Cycle12.MergedCutProfiles.Batch145
import Cycle12.MergedCutProfiles.Batch146

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch071

def retention852 : RatCutRetentionCertificate := ⟨(39/800),(49/1000),(1191735394110842993/4994473862089329628),(15030051561647223/10000000000000000),(37/20),(19758465941092359207/12800000000000000000),true,MergedCutProfiles.Batch144.profile5779,![MergedCutProfiles.Batch144.profile5779,MergedCutProfiles.Batch144.profile5780,MergedCutProfiles.Batch144.profile5781,MergedCutProfiles.Batch144.profile5782,MergedCutProfiles.Batch144.profile5783,MergedCutProfiles.Batch144.profile5784,MergedCutProfiles.Batch144.profile5785,MergedCutProfiles.Batch144.profile5786,MergedCutProfiles.Batch144.profile5787,MergedCutProfiles.Batch144.profile5788,MergedCutProfiles.Batch144.profile5789,MergedCutProfiles.Batch144.profile5790,MergedCutProfiles.Batch144.profile5791,MergedCutProfiles.Batch144.profile5792,MergedCutProfiles.Batch144.profile5793,MergedCutProfiles.Batch144.profile5794]⟩
theorem profilesValid852 : retention852.ProfilesValid := by
  change ∀ j : Fin 16, (retention852.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch144.valid5779
  · exact MergedCutProfiles.Batch144.valid5780
  · exact MergedCutProfiles.Batch144.valid5781
  · exact MergedCutProfiles.Batch144.valid5782
  · exact MergedCutProfiles.Batch144.valid5783
  · exact MergedCutProfiles.Batch144.valid5784
  · exact MergedCutProfiles.Batch144.valid5785
  · exact MergedCutProfiles.Batch144.valid5786
  · exact MergedCutProfiles.Batch144.valid5787
  · exact MergedCutProfiles.Batch144.valid5788
  · exact MergedCutProfiles.Batch144.valid5789
  · exact MergedCutProfiles.Batch144.valid5790
  · exact MergedCutProfiles.Batch144.valid5791
  · exact MergedCutProfiles.Batch144.valid5792
  · exact MergedCutProfiles.Batch144.valid5793
  · exact MergedCutProfiles.Batch144.valid5794
theorem numericValid852 : retention852.NumericValid := by decide +kernel
def certificate852 : RatCutBinCertificate := ⟨⟨retention852,(2148772030523085131/1000000000000000000),(114392751307786871/1000000000000000000),(815404404890926431/62500000000000000),(130505885730980550373/500000000000000000),(1508769460939101139/1000000000000000000)⟩,(248172873573857223/250000000000000000),(410807388708214087/1000000000000000000),(13982795805572559/62500000000000000),(69940688368102011/500000000000000000)⟩
theorem valid852 : certificate852.Valid := by decide +kernel
theorem sound852 : certificate852.Sound := rat_cut_bin_certificate_sound certificate852 profilesValid852 numericValid852 valid852

def retention853 : RatCutRetentionCertificate := ⟨(39/800),(49/1000),(1115312040136503373/2497236931044664814),(1191735394110842993/250000000000000000),(21/20),(343369535712513028437/320000000000000000000),true,MergedCutProfiles.Batch144.profile5795,![MergedCutProfiles.Batch144.profile5795,MergedCutProfiles.Batch144.profile5796,MergedCutProfiles.Batch144.profile5797,MergedCutProfiles.Batch144.profile5798,MergedCutProfiles.Batch144.profile5799,MergedCutProfiles.Batch145.profile5800,MergedCutProfiles.Batch145.profile5801,MergedCutProfiles.Batch145.profile5802,MergedCutProfiles.Batch145.profile5803,MergedCutProfiles.Batch145.profile5804,MergedCutProfiles.Batch145.profile5805,MergedCutProfiles.Batch145.profile5806,MergedCutProfiles.Batch145.profile5807,MergedCutProfiles.Batch145.profile5808,MergedCutProfiles.Batch145.profile5809,MergedCutProfiles.Batch145.profile5810]⟩
theorem profilesValid853 : retention853.ProfilesValid := by
  change ∀ j : Fin 16, (retention853.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch144.valid5795
  · exact MergedCutProfiles.Batch144.valid5796
  · exact MergedCutProfiles.Batch144.valid5797
  · exact MergedCutProfiles.Batch144.valid5798
  · exact MergedCutProfiles.Batch144.valid5799
  · exact MergedCutProfiles.Batch145.valid5800
  · exact MergedCutProfiles.Batch145.valid5801
  · exact MergedCutProfiles.Batch145.valid5802
  · exact MergedCutProfiles.Batch145.valid5803
  · exact MergedCutProfiles.Batch145.valid5804
  · exact MergedCutProfiles.Batch145.valid5805
  · exact MergedCutProfiles.Batch145.valid5806
  · exact MergedCutProfiles.Batch145.valid5807
  · exact MergedCutProfiles.Batch145.valid5808
  · exact MergedCutProfiles.Batch145.valid5809
  · exact MergedCutProfiles.Batch145.valid5810
theorem numericValid853 : retention853.NumericValid := by decide +kernel
def certificate853 : RatCutBinCertificate := ⟨⟨retention853,(2148772030523085131/1000000000000000000),(114392751307786871/1000000000000000000),(815404404890926431/62500000000000000),(130505885730980550373/500000000000000000),(65827836724753651/62500000000000000)⟩,(248172873573857223/250000000000000000),(118940633871024659/250000000000000000),(170823605852667291/1000000000000000000),(141600142638858243/1000000000000000000)⟩
theorem valid853 : certificate853.Valid := by decide +kernel
theorem sound853 : certificate853.Sound := rat_cut_bin_certificate_sound certificate853 profilesValid853 numericValid853 valid853

def retention854 : RatCutRetentionCertificate := ⟨(39/800),(49/1000),(2463996712544581975/4994473862089329628),(1115312040136503373/125000000000000000),(21/20),(897448014855476410106917853981878700399/892249632109202698400000000000000000000),false,MergedCutProfiles.Batch145.profile5811,(fun _ => MergedCutProfiles.Batch145.profile5811)⟩
theorem profilesValid854 : retention854.ProfilesValid := by
  exact MergedCutProfiles.Batch145.valid5811
theorem numericValid854 : retention854.NumericValid := by decide +kernel
def certificate854 : RatCutBinCertificate := ⟨⟨retention854,(2148772030523085131/1000000000000000000),(114392751307786871/1000000000000000000),(815404404890926431/62500000000000000),(130505885730980550373/500000000000000000),(246510637025299983/250000000000000000)⟩,(248172873573857223/250000000000000000),(19294637782231003/40000000000000000),(165963992886684693/1000000000000000000),(8785106420564431/62500000000000000)⟩
theorem valid854 : certificate854.Valid := by decide +kernel
theorem sound854 : certificate854.Sound := rat_cut_bin_certificate_sound certificate854 profilesValid854 numericValid854 valid854

def retention855 : RatCutRetentionCertificate := ⟨(39/800),(49/1000),(9954546718680111179/19977895448357318512),(98559868501783279/10000000000000000),(21/20),(1574345221945606176150504689160932879/1576957896028532464000000000000000000),false,MergedCutProfiles.Batch145.profile5812,(fun _ => MergedCutProfiles.Batch145.profile5812)⟩
theorem profilesValid855 : retention855.ProfilesValid := by
  exact MergedCutProfiles.Batch145.valid5812
theorem numericValid855 : retention855.NumericValid := by decide +kernel
def certificate855 : RatCutBinCertificate := ⟨⟨retention855,(2148772030523085131/1000000000000000000),(114392751307786871/1000000000000000000),(815404404890926431/62500000000000000),(130505885730980550373/500000000000000000),(978559701763269253/1000000000000000000)⟩,(248172873573857223/250000000000000000),(241613785274808657/500000000000000000),(165336594373485523/1000000000000000000),(70135422821301553/500000000000000000)⟩
theorem valid855 : certificate855.Valid := by decide +kernel
theorem sound855 : certificate855.Sound := rat_cut_bin_certificate_sound certificate855 profilesValid855 numericValid855 valid855

def retention856 : RatCutRetentionCertificate := ⟨(39/800),(49/1000),(1/2),(9954546718680111179/1000000000000000000),(21/20),(15850392450891270922030362975869623869959/15927274749888177886400000000000000000000),false,MergedCutProfiles.Batch145.profile5813,(fun _ => MergedCutProfiles.Batch145.profile5813)⟩
theorem profilesValid856 : retention856.ProfilesValid := by
  exact MergedCutProfiles.Batch145.valid5813
theorem numericValid856 : retention856.NumericValid := by decide +kernel
def certificate856 : RatCutBinCertificate := ⟨⟨retention856,(2148772030523085131/1000000000000000000),(114392751307786871/1000000000000000000),(815404404890926431/62500000000000000),(130505885730980550373/500000000000000000),(975389406817231849/1000000000000000000)⟩,(248172873573857223/250000000000000000),(484529800657968023/1000000000000000000),(164391281753084921/1000000000000000000),(108725144215457/781250000000000)⟩
theorem valid856 : certificate856.Valid := by decide +kernel
theorem sound856 : certificate856.Sound := rat_cut_bin_certificate_sound certificate856 profilesValid856 numericValid856 valid856

def retention857 : RatCutRetentionCertificate := ⟨(39/800),(49/1000),(1/2),64,1,(249407353951295313243618741111/250000000000000000000000000000),false,MergedCutProfiles.Batch145.profile5813,(fun _ => MergedCutProfiles.Batch145.profile5813)⟩
theorem profilesValid857 : retention857.ProfilesValid := by
  exact MergedCutProfiles.Batch145.valid5813
theorem numericValid857 : retention857.NumericValid := by decide +kernel
def certificate857 : RatCutBinCertificate := ⟨⟨retention857,(2148772030523085131/1000000000000000000),(114392751307786871/1000000000000000000),(815404404890926431/62500000000000000),(130505885730980550373/500000000000000000),(489394319907260163/500000000000000000)⟩,(248172873573857223/250000000000000000),(460260656917836803/1000000000000000000),(91297112081341453/500000000000000000),(174730973427596789/1000000000000000000)⟩
theorem valid857 : certificate857.Valid := by decide +kernel
theorem sound857 : certificate857.Sound := rat_cut_bin_certificate_sound certificate857 profilesValid857 numericValid857 valid857

def retention858 : RatCutRetentionCertificate := ⟨(39/800),(49/1000),(8976959274760383061/19977895448357318512),(148110885905899893/40000000000000000),(6/5),(4053819913404911781632771700733119629/3702772147647497325000000000000000000),false,MergedCutProfiles.Batch145.profile5814,(fun _ => MergedCutProfiles.Batch145.profile5814)⟩
theorem profilesValid858 : retention858.ProfilesValid := by
  exact MergedCutProfiles.Batch145.valid5814
theorem numericValid858 : retention858.NumericValid := by decide +kernel
def certificate858 : RatCutBinCertificate := ⟨⟨retention858,(2528722186523085131/1000000000000000000),(114392751307786871/1000000000000000000),(815404404890926431/62500000000000000),(130505885730980550373/500000000000000000),(213639522587509817/200000000000000000)⟩,(495698886331954861/500000000000000000),(190525994464097973/500000000000000000),(251299268754656963/1000000000000000000),(92305153649635681/500000000000000000)⟩
theorem valid858 : certificate858.Valid := by decide +kernel
theorem sound858 : certificate858.Sound := rat_cut_bin_certificate_sound certificate858 profilesValid858 numericValid858 valid858

def retention859 : RatCutRetentionCertificate := ⟨(39/800),(49/1000),(2479036958453909837/4994473862089329628),(8976959274760383061/1000000000000000000),(21/20),(14364812741591685778684955601442883218599/14363134839616612897600000000000000000000),false,MergedCutProfiles.Batch145.profile5815,(fun _ => MergedCutProfiles.Batch145.profile5815)⟩
theorem profilesValid859 : retention859.ProfilesValid := by
  exact MergedCutProfiles.Batch145.valid5815
theorem numericValid859 : retention859.NumericValid := by decide +kernel
def certificate859 : RatCutBinCertificate := ⟨⟨retention859,(2528722186523085131/1000000000000000000),(114392751307786871/1000000000000000000),(815404404890926431/62500000000000000),(130505885730980550373/500000000000000000),(976835045437022673/1000000000000000000)⟩,(495698886331954861/500000000000000000),(41669146380400457/100000000000000000),(5463304466744973/25000000000000000),(45843322726152911/250000000000000000)⟩
theorem valid859 : certificate859.Valid := by decide +kernel
theorem sound859 : certificate859.Sound := rat_cut_bin_certificate_sound certificate859 profilesValid859 numericValid859 valid859

def retention860 : RatCutRetentionCertificate := ⟨(39/800),(49/1000),(1/2),(2479036958453909837/250000000000000000),(21/20),(986755238929747248911196579527695113431/991614783381563934800000000000000000000),false,MergedCutProfiles.Batch145.profile5813,(fun _ => MergedCutProfiles.Batch145.profile5813)⟩
theorem profilesValid860 : retention860.ProfilesValid := by
  exact MergedCutProfiles.Batch145.valid5813
theorem numericValid860 : retention860.NumericValid := by decide +kernel
def certificate860 : RatCutBinCertificate := ⟨⟨retention860,(2528722186523085131/1000000000000000000),(114392751307786871/1000000000000000000),(815404404890926431/62500000000000000),(130505885730980550373/500000000000000000),(485908845282094803/500000000000000000)⟩,(495698886331954861/500000000000000000),(20942139093079153/50000000000000000),(216654491060242927/1000000000000000000),(91249711477941681/500000000000000000)⟩
theorem valid860 : certificate860.Valid := by decide +kernel
theorem sound860 : certificate860.Sound := rat_cut_bin_certificate_sound certificate860 profilesValid860 numericValid860 valid860

def retention861 : RatCutRetentionCertificate := ⟨(49/1000),(197/4000),(848406691688271113/19747454135969582710),(168001325086786359/200000000000000000),(29/10),(33178783717859511693/16000000000000000000),true,MergedCutProfiles.Batch145.profile5816,![MergedCutProfiles.Batch145.profile5816,MergedCutProfiles.Batch145.profile5817,MergedCutProfiles.Batch145.profile5818,MergedCutProfiles.Batch145.profile5819,MergedCutProfiles.Batch145.profile5820,MergedCutProfiles.Batch145.profile5821,MergedCutProfiles.Batch145.profile5822,MergedCutProfiles.Batch145.profile5823,MergedCutProfiles.Batch145.profile5824,MergedCutProfiles.Batch145.profile5825,MergedCutProfiles.Batch145.profile5826,MergedCutProfiles.Batch145.profile5827,MergedCutProfiles.Batch145.profile5828,MergedCutProfiles.Batch145.profile5829,MergedCutProfiles.Batch145.profile5830,MergedCutProfiles.Batch145.profile5831]⟩
theorem profilesValid861 : retention861.ProfilesValid := by
  change ∀ j : Fin 16, (retention861.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch145.valid5816
  · exact MergedCutProfiles.Batch145.valid5817
  · exact MergedCutProfiles.Batch145.valid5818
  · exact MergedCutProfiles.Batch145.valid5819
  · exact MergedCutProfiles.Batch145.valid5820
  · exact MergedCutProfiles.Batch145.valid5821
  · exact MergedCutProfiles.Batch145.valid5822
  · exact MergedCutProfiles.Batch145.valid5823
  · exact MergedCutProfiles.Batch145.valid5824
  · exact MergedCutProfiles.Batch145.valid5825
  · exact MergedCutProfiles.Batch145.valid5826
  · exact MergedCutProfiles.Batch145.valid5827
  · exact MergedCutProfiles.Batch145.valid5828
  · exact MergedCutProfiles.Batch145.valid5829
  · exact MergedCutProfiles.Batch145.valid5830
  · exact MergedCutProfiles.Batch145.valid5831
theorem numericValid861 : retention861.NumericValid := by decide +kernel
def certificate861 : RatCutBinCertificate := ⟨⟨retention861,(2158102615044373853/1000000000000000000),(115712893678697359/1000000000000000000),(818779701756686403/62500000000000000),(259069613155146490359/1000000000000000000),(504596064839683563/250000000000000000)⟩,(992615489941763403/1000000000000000000),(187386811212610083/500000000000000000),(257408288034839381/1000000000000000000),(138122915606364329/1000000000000000000)⟩
theorem valid861 : certificate861.Valid := by decide +kernel
theorem sound861 : certificate861.Sound := rat_cut_bin_certificate_sound certificate861 profilesValid861 numericValid861 valid861

def retention862 : RatCutRetentionCertificate := ⟨(49/1000),(197/4000),(86094480400000000/1974745413596958271),(848406691688271113/1000000000000000000),(29/10),(166096143978915545939/80000000000000000000),true,MergedCutProfiles.Batch145.profile5816,![MergedCutProfiles.Batch145.profile5816,MergedCutProfiles.Batch145.profile5832,MergedCutProfiles.Batch145.profile5833,MergedCutProfiles.Batch145.profile5834,MergedCutProfiles.Batch145.profile5835,MergedCutProfiles.Batch145.profile5836,MergedCutProfiles.Batch145.profile5837,MergedCutProfiles.Batch145.profile5838,MergedCutProfiles.Batch145.profile5839,MergedCutProfiles.Batch146.profile5840,MergedCutProfiles.Batch146.profile5841,MergedCutProfiles.Batch146.profile5842,MergedCutProfiles.Batch146.profile5843,MergedCutProfiles.Batch146.profile5844,MergedCutProfiles.Batch146.profile5845,MergedCutProfiles.Batch146.profile5846]⟩
theorem profilesValid862 : retention862.ProfilesValid := by
  change ∀ j : Fin 16, (retention862.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch145.valid5816
  · exact MergedCutProfiles.Batch145.valid5832
  · exact MergedCutProfiles.Batch145.valid5833
  · exact MergedCutProfiles.Batch145.valid5834
  · exact MergedCutProfiles.Batch145.valid5835
  · exact MergedCutProfiles.Batch145.valid5836
  · exact MergedCutProfiles.Batch145.valid5837
  · exact MergedCutProfiles.Batch145.valid5838
  · exact MergedCutProfiles.Batch145.valid5839
  · exact MergedCutProfiles.Batch146.valid5840
  · exact MergedCutProfiles.Batch146.valid5841
  · exact MergedCutProfiles.Batch146.valid5842
  · exact MergedCutProfiles.Batch146.valid5843
  · exact MergedCutProfiles.Batch146.valid5844
  · exact MergedCutProfiles.Batch146.valid5845
  · exact MergedCutProfiles.Batch146.valid5846
theorem numericValid862 : retention862.NumericValid := by decide +kernel
def certificate862 : RatCutBinCertificate := ⟨⟨retention862,(2158102615044373853/1000000000000000000),(115712893678697359/1000000000000000000),(818779701756686403/62500000000000000),(259069613155146490359/1000000000000000000),(2020912177081410857/1000000000000000000)⟩,(992615489941763403/1000000000000000000),(372777279765584747/1000000000000000000),(129686360131318911/500000000000000000),(6981079148753521/50000000000000000)⟩
theorem valid862 : certificate862.Valid := by decide +kernel
theorem sound862 : certificate862.Sound := rat_cut_bin_certificate_sound certificate862 profilesValid862 numericValid862 valid862

def retention863 : RatCutRetentionCertificate := ⟨(49/1000),(197/4000),(965565954885058859/19747454135969582710),(215236201/250000000),(57/20),(32906801784047807557/16000000000000000000),true,MergedCutProfiles.Batch146.profile5847,![MergedCutProfiles.Batch146.profile5847,MergedCutProfiles.Batch146.profile5848,MergedCutProfiles.Batch146.profile5849,MergedCutProfiles.Batch146.profile5850,MergedCutProfiles.Batch146.profile5851,MergedCutProfiles.Batch146.profile5852,MergedCutProfiles.Batch146.profile5853,MergedCutProfiles.Batch145.profile5839,MergedCutProfiles.Batch146.profile5854,MergedCutProfiles.Batch146.profile5855,MergedCutProfiles.Batch146.profile5856,MergedCutProfiles.Batch146.profile5857,MergedCutProfiles.Batch146.profile5858,MergedCutProfiles.Batch146.profile5859,MergedCutProfiles.Batch146.profile5860,MergedCutProfiles.Batch146.profile5861]⟩
theorem profilesValid863 : retention863.ProfilesValid := by
  change ∀ j : Fin 16, (retention863.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch146.valid5847
  · exact MergedCutProfiles.Batch146.valid5848
  · exact MergedCutProfiles.Batch146.valid5849
  · exact MergedCutProfiles.Batch146.valid5850
  · exact MergedCutProfiles.Batch146.valid5851
  · exact MergedCutProfiles.Batch146.valid5852
  · exact MergedCutProfiles.Batch146.valid5853
  · exact MergedCutProfiles.Batch145.valid5839
  · exact MergedCutProfiles.Batch146.valid5854
  · exact MergedCutProfiles.Batch146.valid5855
  · exact MergedCutProfiles.Batch146.valid5856
  · exact MergedCutProfiles.Batch146.valid5857
  · exact MergedCutProfiles.Batch146.valid5858
  · exact MergedCutProfiles.Batch146.valid5859
  · exact MergedCutProfiles.Batch146.valid5860
  · exact MergedCutProfiles.Batch146.valid5861
theorem numericValid863 : retention863.NumericValid := by decide +kernel
def certificate863 : RatCutBinCertificate := ⟨⟨retention863,(2158102615044373853/1000000000000000000),(115712893678697359/1000000000000000000),(818779701756686403/62500000000000000),(259069613155146490359/1000000000000000000),(500584682831975187/250000000000000000)⟩,(992615489941763403/1000000000000000000),(93497471137978661/250000000000000000),(51635645672691623/200000000000000000),(139779528673114687/1000000000000000000)⟩
theorem valid863 : certificate863.Valid := by decide +kernel
theorem sound863 : certificate863.Sound := rat_cut_bin_certificate_sound certificate863 profilesValid863 numericValid863 valid863

def certificates : List RatCutBinCertificate := [certificate852,certificate853,certificate854,certificate855,certificate856,certificate857,certificate858,certificate859,certificate860,certificate861,certificate862,certificate863]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound852,List.forall_mem_cons.mpr ⟨sound853,List.forall_mem_cons.mpr ⟨sound854,List.forall_mem_cons.mpr ⟨sound855,List.forall_mem_cons.mpr ⟨sound856,List.forall_mem_cons.mpr ⟨sound857,List.forall_mem_cons.mpr ⟨sound858,List.forall_mem_cons.mpr ⟨sound859,List.forall_mem_cons.mpr ⟨sound860,List.forall_mem_cons.mpr ⟨sound861,List.forall_mem_cons.mpr ⟨sound862,List.forall_mem_cons.mpr ⟨sound863,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch071
