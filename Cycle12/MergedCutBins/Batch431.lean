import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch716
import Cycle12.MergedCutProfiles.Batch717
import Cycle12.MergedCutProfiles.Batch718

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch431

def retention5172 : RatCutRetentionCertificate := ⟨(13/200),(33/500),(157012326504254959/198806338180814466443),(777288745070569103/1000000000000000000),(79/20),(3063390466670849843743675382585806522831/1243661992112910564800000000000000000000),false,MergedCutProfiles.Batch716.profile28677,(fun _ => MergedCutProfiles.Batch716.profile28677)⟩
theorem profilesValid5172 : retention5172.ProfilesValid := by
  exact MergedCutProfiles.Batch716.valid28677
theorem numericValid5172 : retention5172.NumericValid := by decide +kernel
def certificate5172 : RatCutBinCertificate := ⟨⟨retention5172,(1014108698071840637/500000000000000000),(229314578619222081/1000000000000000000),(8713760607559645161/500000000000000000),(272404725454788921341/15625000000000000),(2357785085856615343/1000000000000000000)⟩,(499954682831775651/500000000000000000),(754205127749870389/1000000000000000000),(6453217296277/195312500000000),(16510139877970397/1000000000000000000)⟩
theorem valid5172 : certificate5172.Valid := by decide +kernel
theorem sound5172 : certificate5172.Sound := rat_cut_bin_certificate_sound certificate5172 profilesValid5172 numericValid5172 valid5172

def retention5173 : RatCutRetentionCertificate := ⟨(13/200),(33/500),(80420645247385347/90366517354915666565),(157012326504254959/200000000000000000),(79/20),(24751354171891831580633702759704053659/10048788896272317376000000000000000000),false,MergedCutProfiles.Batch716.profile28678,(fun _ => MergedCutProfiles.Batch716.profile28678)⟩
theorem profilesValid5173 : retention5173.ProfilesValid := by
  exact MergedCutProfiles.Batch716.valid28678
theorem numericValid5173 : retention5173.NumericValid := by decide +kernel
def certificate5173 : RatCutBinCertificate := ⟨⟨retention5173,(1014108698071840637/500000000000000000),(229314578619222081/1000000000000000000),(8713760607559645161/500000000000000000),(272404725454788921341/15625000000000000),(2357701418671930187/1000000000000000000)⟩,(499954682831775651/500000000000000000),(752777325111232517/1000000000000000000),(33444595037754309/1000000000000000000),(3347711695326337/200000000000000000)⟩
theorem valid5173 : certificate5173.Valid := by decide +kernel
theorem sound5173 : certificate5173.Sound := rat_cut_bin_certificate_sound certificate5173 profilesValid5173 numericValid5173 valid5173

def retention5174 : RatCutRetentionCertificate := ⟨(13/200),(33/500),(464476227393244232/198806338180814466443),(884627097721238817/1000000000000000000),(18/5),(215274743376947343475745910262637351399/88462709772123881700000000000000000000),false,MergedCutProfiles.Batch716.profile28679,(fun _ => MergedCutProfiles.Batch716.profile28679)⟩
theorem profilesValid5174 : retention5174.ProfilesValid := by
  exact MergedCutProfiles.Batch716.valid28679
theorem numericValid5174 : retention5174.NumericValid := by decide +kernel
def certificate5174 : RatCutBinCertificate := ⟨⟨retention5174,(1014108698071840637/500000000000000000),(229314578619222081/1000000000000000000),(8713760607559645161/500000000000000000),(272404725454788921341/15625000000000000),(2337432370928778897/1000000000000000000)⟩,(499954682831775651/500000000000000000),(371395903827560149/500000000000000000),(36346863570663787/1000000000000000000),(19600767639991973/1000000000000000000)⟩
theorem valid5174 : certificate5174.Valid := by decide +kernel
theorem sound5174 : certificate5174.Sound := rat_cut_bin_certificate_sound certificate5174 profilesValid5174 numericValid5174 valid5174

def retention5175 : RatCutRetentionCertificate := ⟨(13/200),(33/500),(22007158444988228229/994031690904072332215),(58059528424155529/25000000000000000),(19/10),(163813331464496756166840818672019087/72574410530194411250000000000000000),false,MergedCutProfiles.Batch717.profile28680,(fun _ => MergedCutProfiles.Batch717.profile28680)⟩
theorem profilesValid5175 : retention5175.ProfilesValid := by
  exact MergedCutProfiles.Batch717.valid28680
theorem numericValid5175 : retention5175.NumericValid := by decide +kernel
def certificate5175 : RatCutBinCertificate := ⟨⟨retention5175,(1014108698071840637/500000000000000000),(229314578619222081/1000000000000000000),(8713760607559645161/500000000000000000),(272404725454788921341/15625000000000000),(551617714183172077/250000000000000000)⟩,(499954682831775651/500000000000000000),(350743335800477227/500000000000000000),(9959771663893109/200000000000000000),(11444397368918079/250000000000000000)⟩
theorem valid5175 : certificate5175.Valid := by decide +kernel
theorem sound5175 : certificate5175.Sound := rat_cut_bin_certificate_sound certificate5175 profilesValid5175 numericValid5175 valid5175

def retention5176 : RatCutRetentionCertificate := ⟨(13/200),(33/500),(1/40),(22007158444988228229/1000000000000000000),(21/20),(78462720343977580041800507522528343527039/35211453511981165166400000000000000000000),false,MergedCutProfiles.Batch717.profile28681,(fun _ => MergedCutProfiles.Batch717.profile28681)⟩
theorem profilesValid5176 : retention5176.ProfilesValid := by
  exact MergedCutProfiles.Batch717.valid28681
theorem numericValid5176 : retention5176.NumericValid := by decide +kernel
def certificate5176 : RatCutBinCertificate := ⟨⟨retention5176,(1014108698071840637/500000000000000000),(229314578619222081/1000000000000000000),(8713760607559645161/500000000000000000),(272404725454788921341/15625000000000000),(1100153715200121771/500000000000000000)⟩,(499954682831775651/500000000000000000),(656323984888594939/1000000000000000000),(33648752106860739/500000000000000000),(129286346031398691/1000000000000000000)⟩
theorem valid5176 : certificate5176.Valid := by decide +kernel
theorem sound5176 : certificate5176.Sound := rat_cut_bin_certificate_sound certificate5176 profilesValid5176 numericValid5176 valid5176

def retention5177 : RatCutRetentionCertificate := ⟨(33/500),(67/1000),(623418701644400548/958430071261117944869),(151271012462474691/250000000000000000),4,(87108762962395076206655733273993203/37817753115618672750000000000000000),true,MergedCutProfiles.Batch717.profile28682,![MergedCutProfiles.Batch717.profile28682,MergedCutProfiles.Batch717.profile28683,MergedCutProfiles.Batch717.profile28684,MergedCutProfiles.Batch717.profile28685,MergedCutProfiles.Batch717.profile28686,MergedCutProfiles.Batch717.profile28687,MergedCutProfiles.Batch717.profile28688,MergedCutProfiles.Batch717.profile28689,MergedCutProfiles.Batch717.profile28690,MergedCutProfiles.Batch717.profile28691,MergedCutProfiles.Batch717.profile28692,MergedCutProfiles.Batch717.profile28693,MergedCutProfiles.Batch717.profile28694,MergedCutProfiles.Batch717.profile28695,MergedCutProfiles.Batch717.profile28696,MergedCutProfiles.Batch717.profile28697]⟩
theorem profilesValid5177 : retention5177.ProfilesValid := by
  change ∀ j : Fin 16, (retention5177.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch717.valid28682
  · exact MergedCutProfiles.Batch717.valid28683
  · exact MergedCutProfiles.Batch717.valid28684
  · exact MergedCutProfiles.Batch717.valid28685
  · exact MergedCutProfiles.Batch717.valid28686
  · exact MergedCutProfiles.Batch717.valid28687
  · exact MergedCutProfiles.Batch717.valid28688
  · exact MergedCutProfiles.Batch717.valid28689
  · exact MergedCutProfiles.Batch717.valid28690
  · exact MergedCutProfiles.Batch717.valid28691
  · exact MergedCutProfiles.Batch717.valid28692
  · exact MergedCutProfiles.Batch717.valid28693
  · exact MergedCutProfiles.Batch717.valid28694
  · exact MergedCutProfiles.Batch717.valid28695
  · exact MergedCutProfiles.Batch717.valid28696
  · exact MergedCutProfiles.Batch717.valid28697
theorem numericValid5177 : retention5177.NumericValid := by decide +kernel
def certificate5177 : RatCutBinCertificate := ⟨⟨retention5177,(244687782617338783/125000000000000000),(11895173549139047/50000000000000000),(17767111311624607767/1000000000000000000),(17137809829215648313311/1000000000000000000),(439707517174409607/200000000000000000)⟩,(249977992257868889/250000000000000000),(7574239015986871/10000000000000000),(1285573780118601/40000000000000000),(14394138223743231/1000000000000000000)⟩
theorem valid5177 : certificate5177.Valid := by decide +kernel
theorem sound5177 : certificate5177.Sound := rat_cut_bin_certificate_sound certificate5177 profilesValid5177 numericValid5177 valid5177

def retention5178 : RatCutRetentionCertificate := ⟨(33/500),(67/1000),(1015652327000000000/958430071261117944869),(155854675411100137/250000000000000000),4,(58147359453513502156625296334527887/24936748065776021920000000000000000),true,MergedCutProfiles.Batch717.profile28698,![MergedCutProfiles.Batch717.profile28698,MergedCutProfiles.Batch717.profile28699,MergedCutProfiles.Batch717.profile28700,MergedCutProfiles.Batch717.profile28701,MergedCutProfiles.Batch717.profile28702,MergedCutProfiles.Batch717.profile28703,MergedCutProfiles.Batch717.profile28704,MergedCutProfiles.Batch717.profile28694,MergedCutProfiles.Batch717.profile28696,MergedCutProfiles.Batch717.profile28697,MergedCutProfiles.Batch717.profile28705,MergedCutProfiles.Batch717.profile28706,MergedCutProfiles.Batch717.profile28707,MergedCutProfiles.Batch717.profile28708,MergedCutProfiles.Batch717.profile28709,MergedCutProfiles.Batch717.profile28710]⟩
theorem profilesValid5178 : retention5178.ProfilesValid := by
  change ∀ j : Fin 16, (retention5178.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch717.valid28698
  · exact MergedCutProfiles.Batch717.valid28699
  · exact MergedCutProfiles.Batch717.valid28700
  · exact MergedCutProfiles.Batch717.valid28701
  · exact MergedCutProfiles.Batch717.valid28702
  · exact MergedCutProfiles.Batch717.valid28703
  · exact MergedCutProfiles.Batch717.valid28704
  · exact MergedCutProfiles.Batch717.valid28694
  · exact MergedCutProfiles.Batch717.valid28696
  · exact MergedCutProfiles.Batch717.valid28697
  · exact MergedCutProfiles.Batch717.valid28705
  · exact MergedCutProfiles.Batch717.valid28706
  · exact MergedCutProfiles.Batch717.valid28707
  · exact MergedCutProfiles.Batch717.valid28708
  · exact MergedCutProfiles.Batch717.valid28709
  · exact MergedCutProfiles.Batch717.valid28710
theorem numericValid5178 : retention5178.NumericValid := by decide +kernel
def certificate5178 : RatCutBinCertificate := ⟨⟨retention5178,(244687782617338783/125000000000000000),(11895173549139047/50000000000000000),(17767111311624607767/1000000000000000000),(17137809829215648313311/1000000000000000000),(2226948777088602093/1000000000000000000)⟩,(249977992257868889/250000000000000000),(91680313571125511/125000000000000000),(39185866131970079/1000000000000000000),(17832510409223427/1000000000000000000)⟩
theorem valid5178 : certificate5178.Valid := by decide +kernel
theorem sound5178 : certificate5178.Sound := rat_cut_bin_certificate_sound certificate5178 profilesValid5178 numericValid5178 valid5178

def retention5179 : RatCutRetentionCertificate := ⟨(33/500),(67/1000),(1328018832657226607/958430071261117944869),(1015652327/1000000000),(31/10),(9901253859789837358339539743184082191/4062609308000000000000000000000000000),true,MergedCutProfiles.Batch717.profile28711,![MergedCutProfiles.Batch717.profile28711,MergedCutProfiles.Batch717.profile28685,MergedCutProfiles.Batch717.profile28701,MergedCutProfiles.Batch717.profile28712,MergedCutProfiles.Batch717.profile28713,MergedCutProfiles.Batch717.profile28714,MergedCutProfiles.Batch717.profile28696,MergedCutProfiles.Batch717.profile28715,MergedCutProfiles.Batch717.profile28706,MergedCutProfiles.Batch717.profile28707,MergedCutProfiles.Batch717.profile28716,MergedCutProfiles.Batch717.profile28710,MergedCutProfiles.Batch717.profile28717,MergedCutProfiles.Batch717.profile28718,MergedCutProfiles.Batch717.profile28719,MergedCutProfiles.Batch718.profile28720]⟩
theorem profilesValid5179 : retention5179.ProfilesValid := by
  change ∀ j : Fin 16, (retention5179.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch717.valid28711
  · exact MergedCutProfiles.Batch717.valid28685
  · exact MergedCutProfiles.Batch717.valid28701
  · exact MergedCutProfiles.Batch717.valid28712
  · exact MergedCutProfiles.Batch717.valid28713
  · exact MergedCutProfiles.Batch717.valid28714
  · exact MergedCutProfiles.Batch717.valid28696
  · exact MergedCutProfiles.Batch717.valid28715
  · exact MergedCutProfiles.Batch717.valid28706
  · exact MergedCutProfiles.Batch717.valid28707
  · exact MergedCutProfiles.Batch717.valid28716
  · exact MergedCutProfiles.Batch717.valid28710
  · exact MergedCutProfiles.Batch717.valid28717
  · exact MergedCutProfiles.Batch717.valid28718
  · exact MergedCutProfiles.Batch717.valid28719
  · exact MergedCutProfiles.Batch718.valid28720
theorem numericValid5179 : retention5179.NumericValid := by decide +kernel
def certificate5179 : RatCutBinCertificate := ⟨⟨retention5179,(244687782617338783/125000000000000000),(11895173549139047/50000000000000000),(17767111311624607767/1000000000000000000),(17137809829215648313311/1000000000000000000),(1177955595940710501/500000000000000000)⟩,(249977992257868889/250000000000000000),(260397936842123049/500000000000000000),(69719189505135311/500000000000000000),(21338832588819003/250000000000000000)⟩
theorem valid5179 : certificate5179.Valid := by decide +kernel
theorem sound5179 : certificate5179.Sound := rat_cut_bin_certificate_sound certificate5179 profilesValid5179 numericValid5179 valid5179

def retention5180 : RatCutRetentionCertificate := ⟨(33/500),(67/1000),(56540826143095425995/958430071261117944869),(1328018832657226607/1000000000000000000),(5/2),(8851092432462911308559646444422799747/4249660264503125142400000000000000000),false,MergedCutProfiles.Batch718.profile28721,(fun _ => MergedCutProfiles.Batch718.profile28721)⟩
theorem profilesValid5180 : retention5180.ProfilesValid := by
  exact MergedCutProfiles.Batch718.valid28721
theorem numericValid5180 : retention5180.NumericValid := by decide +kernel
def certificate5180 : RatCutBinCertificate := ⟨⟨retention5180,(244687782617338783/125000000000000000),(11895173549139047/50000000000000000),(17767111311624607767/1000000000000000000),(17137809829215648313311/1000000000000000000),(2017248304727524553/1000000000000000000)⟩,(249977992257868889/250000000000000000),(532914391977455331/1000000000000000000),(2633444292107317/20000000000000000),(85463971287258943/1000000000000000000)⟩
theorem valid5180 : certificate5180.Valid := by decide +kernel
theorem sound5180 : certificate5180.Sound := rat_cut_bin_certificate_sound certificate5180 profilesValid5180 numericValid5180 valid5180

def retention5181 : RatCutRetentionCertificate := ⟨(33/500),(67/1000),(64000000000000000000/958430071261117944869),(11308165228619085199/200000000000000000),1,(14384754466474778633635698912825021737/7067603267886928249375000000000000000),false,MergedCutProfiles.Batch718.profile28722,(fun _ => MergedCutProfiles.Batch718.profile28722)⟩
theorem profilesValid5181 : retention5181.ProfilesValid := by
  exact MergedCutProfiles.Batch718.valid28722
theorem numericValid5181 : retention5181.NumericValid := by decide +kernel
def certificate5181 : RatCutBinCertificate := ⟨⟨retention5181,(244687782617338783/125000000000000000),(11895173549139047/50000000000000000),(17767111311624607767/1000000000000000000),(17137809829215648313311/1000000000000000000),(2009097541086348629/1000000000000000000)⟩,(249977992257868889/250000000000000000),(147487247273432991/500000000000000000),(172437374672244459/500000000000000000),(334525687544323239/500000000000000000)⟩
theorem valid5181 : certificate5181.Valid := by decide +kernel
theorem sound5181 : certificate5181.Sound := rat_cut_bin_certificate_sound certificate5181 profilesValid5181 numericValid5181 valid5181

def retention5182 : RatCutRetentionCertificate := ⟨(33/500),(67/1000),(1/2),64,1,(255418053332003062582561760940652564719/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch718.profile28723,(fun _ => MergedCutProfiles.Batch718.profile28723)⟩
theorem profilesValid5182 : retention5182.ProfilesValid := by
  exact MergedCutProfiles.Batch718.valid28723
theorem numericValid5182 : retention5182.NumericValid := by decide +kernel
def certificate5182 : RatCutBinCertificate := ⟨⟨retention5182,(244687782617338783/125000000000000000),(11895173549139047/50000000000000000),(17767111311624607767/1000000000000000000),(17137809829215648313311/1000000000000000000),(485757802993356267/500000000000000000)⟩,(249977992257868889/250000000000000000),(608616302226018219/1000000000000000000),(445823851456523/5000000000000000),(3412882433327231/40000000000000000)⟩
theorem valid5182 : certificate5182.Valid := by decide +kernel
theorem sound5182 : certificate5182.Sound := rat_cut_bin_certificate_sound certificate5182 profilesValid5182 numericValid5182 valid5182

def retention5183 : RatCutRetentionCertificate := ⟨(33/500),(67/1000),(64000000000000000000/958430071261117944869),(27615565224615491981/500000000000000000),1,(1756062033366944480193256384533721947/862986413269234124406250000000000000),false,MergedCutProfiles.Batch718.profile28722,(fun _ => MergedCutProfiles.Batch718.profile28722)⟩
theorem profilesValid5183 : retention5183.ProfilesValid := by
  exact MergedCutProfiles.Batch718.valid28722
theorem numericValid5183 : retention5183.NumericValid := by decide +kernel
def certificate5183 : RatCutBinCertificate := ⟨⟨retention5183,(211514256617338783/125000000000000000),(11895173549139047/50000000000000000),(17767111311624607767/1000000000000000000),(17137809829215648313311/1000000000000000000),(2012208784648144957/1000000000000000000)⟩,(499961952046509939/500000000000000000),(14276763988282099/1000000000000000000),(445802866879425133/500000000000000000),(432724292964160277/250000000000000000)⟩
theorem valid5183 : certificate5183.Valid := by decide +kernel
theorem sound5183 : certificate5183.Sound := rat_cut_bin_certificate_sound certificate5183 profilesValid5183 numericValid5183 valid5183

def certificates : List RatCutBinCertificate := [certificate5172,certificate5173,certificate5174,certificate5175,certificate5176,certificate5177,certificate5178,certificate5179,certificate5180,certificate5181,certificate5182,certificate5183]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound5172,List.forall_mem_cons.mpr ⟨sound5173,List.forall_mem_cons.mpr ⟨sound5174,List.forall_mem_cons.mpr ⟨sound5175,List.forall_mem_cons.mpr ⟨sound5176,List.forall_mem_cons.mpr ⟨sound5177,List.forall_mem_cons.mpr ⟨sound5178,List.forall_mem_cons.mpr ⟨sound5179,List.forall_mem_cons.mpr ⟨sound5180,List.forall_mem_cons.mpr ⟨sound5181,List.forall_mem_cons.mpr ⟨sound5182,List.forall_mem_cons.mpr ⟨sound5183,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch431
