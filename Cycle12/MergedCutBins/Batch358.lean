import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch305
import Cycle12.MergedCutProfiles.Batch307
import Cycle12.MergedCutProfiles.Batch439
import Cycle12.MergedCutProfiles.Batch440
import Cycle12.MergedCutProfiles.Batch559
import Cycle12.MergedCutProfiles.Batch560
import Cycle12.MergedCutProfiles.Batch561
import Cycle12.MergedCutProfiles.Batch643
import Cycle12.MergedCutProfiles.Batch644

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch358

def retention4296 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(1/2),64,1,(255419871002463909042457265882361431119/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch305.profile12226,(fun _ => MergedCutProfiles.Batch305.profile12226)⟩
theorem profilesValid4296 : retention4296.ProfilesValid := by
  exact MergedCutProfiles.Batch305.valid12226
theorem numericValid4296 : retention4296.NumericValid := by decide +kernel
def certificate4296 : RatCutBinCertificate := ⟨⟨retention4296,(272103648983192311/125000000000000000),(121143195939341811/500000000000000000),(9058362351615182299/500000000000000000),(1710732776214571575263/500000000000000000),(968621728437453721/1000000000000000000)⟩,(199903011976271717/200000000000000000),(417527630788343629/1000000000000000000),(5445026235806867/25000000000000000),(1622809120531901/7812500000000000)⟩
theorem valid4296 : certificate4296.Valid := by decide +kernel
theorem sound4296 : certificate4296.Sound := rat_cut_bin_certificate_sound certificate4296 profilesValid4296 numericValid4296 valid4296

def retention4297 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(32000000000000000000/94125250331974770191),(22206295365177758759/1000000000000000000),1,(729040490022411878557270910686782181/555157384129443968975000000000000000),false,MergedCutProfiles.Batch643.profile25721,(fun _ => MergedCutProfiles.Batch643.profile25721)⟩
theorem profilesValid4297 : retention4297.ProfilesValid := by
  exact MergedCutProfiles.Batch643.valid25721
theorem numericValid4297 : retention4297.NumericValid := by decide +kernel
def certificate4297 : RatCutBinCertificate := ⟨⟨retention4297,(246079365233192311/125000000000000000),(121143195939341811/500000000000000000),(9058362351615182299/500000000000000000),(1710732776214571575263/500000000000000000),(1286886192758354917/1000000000000000000)⟩,(499780723211039243/500000000000000000),(19206545629134791/500000000000000000),(205047136385786771/250000000000000000),(997219817752308669/1000000000000000000)⟩
theorem valid4297 : certificate4297.Valid := by decide +kernel
theorem sound4297 : certificate4297.Sound := rat_cut_bin_certificate_sound certificate4297 profilesValid4297 numericValid4297 valid4297

def retention4298 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(1/2),64,1,(255419871002463909042457265882361431119/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch305.profile12226,(fun _ => MergedCutProfiles.Batch305.profile12226)⟩
theorem profilesValid4298 : retention4298.ProfilesValid := by
  exact MergedCutProfiles.Batch305.valid12226
theorem numericValid4298 : retention4298.NumericValid := by decide +kernel
def certificate4298 : RatCutBinCertificate := ⟨⟨retention4298,(246079365233192311/125000000000000000),(121143195939341811/500000000000000000),(9058362351615182299/500000000000000000),(1710732776214571575263/500000000000000000),(971406044870325981/1000000000000000000)⟩,(499780723211039243/500000000000000000),(12722094180511479/250000000000000000),(785989353335222371/1000000000000000000),(375882621309312101/500000000000000000)⟩
theorem valid4298 : certificate4298.Valid := by decide +kernel
theorem sound4298 : certificate4298.Sound := rat_cut_bin_certificate_sound certificate4298 profilesValid4298 numericValid4298 valid4298

def retention4299 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(434074622399711138/92447378412680925593),(859553707722200273/1000000000000000000),(16/5),(3146244557763088434669584075849689409/1343052668315937926562500000000000000),true,MergedCutProfiles.Batch643.profile25722,![MergedCutProfiles.Batch643.profile25722,MergedCutProfiles.Batch643.profile25723,MergedCutProfiles.Batch643.profile25724,MergedCutProfiles.Batch643.profile25725,MergedCutProfiles.Batch643.profile25726,MergedCutProfiles.Batch643.profile25727,MergedCutProfiles.Batch643.profile25728,MergedCutProfiles.Batch643.profile25729,MergedCutProfiles.Batch643.profile25730,MergedCutProfiles.Batch643.profile25731,MergedCutProfiles.Batch643.profile25732,MergedCutProfiles.Batch643.profile25733,MergedCutProfiles.Batch643.profile25734,MergedCutProfiles.Batch643.profile25735,MergedCutProfiles.Batch643.profile25736,MergedCutProfiles.Batch560.profile22402]⟩
theorem profilesValid4299 : retention4299.ProfilesValid := by
  change ∀ j : Fin 16, (retention4299.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch643.valid25722
  · exact MergedCutProfiles.Batch643.valid25723
  · exact MergedCutProfiles.Batch643.valid25724
  · exact MergedCutProfiles.Batch643.valid25725
  · exact MergedCutProfiles.Batch643.valid25726
  · exact MergedCutProfiles.Batch643.valid25727
  · exact MergedCutProfiles.Batch643.valid25728
  · exact MergedCutProfiles.Batch643.valid25729
  · exact MergedCutProfiles.Batch643.valid25730
  · exact MergedCutProfiles.Batch643.valid25731
  · exact MergedCutProfiles.Batch643.valid25732
  · exact MergedCutProfiles.Batch643.valid25733
  · exact MergedCutProfiles.Batch643.valid25734
  · exact MergedCutProfiles.Batch643.valid25735
  · exact MergedCutProfiles.Batch643.valid25736
  · exact MergedCutProfiles.Batch560.valid22402
theorem numericValid4299 : retention4299.NumericValid := by decide +kernel
def certificate4299 : RatCutBinCertificate := ⟨⟨retention4299,(546311116048427081/250000000000000000),(123364672097640231/500000000000000000),(365908636843307189/20000000000000000),(1696830763966484987757/500000000000000000),(1124150458235642609/500000000000000000)⟩,(12493900214194943/12500000000000000),(181754589750262193/500000000000000000),(13431674542176167/50000000000000000),(150249130988842033/1000000000000000000)⟩
theorem valid4299 : certificate4299.Valid := by decide +kernel
theorem sound4299 : certificate4299.Sound := rat_cut_bin_certificate_sound certificate4299 profilesValid4299 numericValid4299 valid4299

def retention4300 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(577566980500000000/92447378412680925593),(217037311199855569/250000000000000000),(16/5),(46713530809434117091/20000000000000000000),true,MergedCutProfiles.Batch643.profile25737,![MergedCutProfiles.Batch643.profile25737,MergedCutProfiles.Batch643.profile25738,MergedCutProfiles.Batch643.profile25725,MergedCutProfiles.Batch643.profile25739,MergedCutProfiles.Batch643.profile25740,MergedCutProfiles.Batch643.profile25729,MergedCutProfiles.Batch643.profile25741,MergedCutProfiles.Batch560.profile22401,MergedCutProfiles.Batch643.profile25733,MergedCutProfiles.Batch643.profile25742,MergedCutProfiles.Batch643.profile25743,MergedCutProfiles.Batch560.profile22402,MergedCutProfiles.Batch643.profile25744,MergedCutProfiles.Batch643.profile25745,MergedCutProfiles.Batch643.profile25746,MergedCutProfiles.Batch643.profile25747]⟩
theorem profilesValid4300 : retention4300.ProfilesValid := by
  change ∀ j : Fin 16, (retention4300.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch643.valid25737
  · exact MergedCutProfiles.Batch643.valid25738
  · exact MergedCutProfiles.Batch643.valid25725
  · exact MergedCutProfiles.Batch643.valid25739
  · exact MergedCutProfiles.Batch643.valid25740
  · exact MergedCutProfiles.Batch643.valid25729
  · exact MergedCutProfiles.Batch643.valid25741
  · exact MergedCutProfiles.Batch560.valid22401
  · exact MergedCutProfiles.Batch643.valid25733
  · exact MergedCutProfiles.Batch643.valid25742
  · exact MergedCutProfiles.Batch643.valid25743
  · exact MergedCutProfiles.Batch560.valid22402
  · exact MergedCutProfiles.Batch643.valid25744
  · exact MergedCutProfiles.Batch643.valid25745
  · exact MergedCutProfiles.Batch643.valid25746
  · exact MergedCutProfiles.Batch643.valid25747
theorem numericValid4300 : retention4300.NumericValid := by decide +kernel
def certificate4300 : RatCutBinCertificate := ⟨⟨retention4300,(546311116048427081/250000000000000000),(123364672097640231/500000000000000000),(365908636843307189/20000000000000000),(1696830763966484987757/500000000000000000),(4377676757406069/1953125000000000)⟩,(12493900214194943/12500000000000000),(90689916144834363/250000000000000000),(67348162502689103/250000000000000000),(150606315526205761/1000000000000000000)⟩
theorem valid4300 : certificate4300.Valid := by decide +kernel
theorem sound4300 : certificate4300.Sound := rat_cut_bin_certificate_sound certificate4300 profilesValid4300 numericValid4300 valid4300

def retention4301 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(1849348669858173407/184894756825361851186),(1155133961/1000000000),(13/5),(4618204245906325763/2000000000000000000),true,MergedCutProfiles.Batch643.profile25748,![MergedCutProfiles.Batch643.profile25748,MergedCutProfiles.Batch643.profile25749,MergedCutProfiles.Batch643.profile25750,MergedCutProfiles.Batch560.profile22415,MergedCutProfiles.Batch560.profile22401,MergedCutProfiles.Batch643.profile25751,MergedCutProfiles.Batch643.profile25736,MergedCutProfiles.Batch560.profile22416,MergedCutProfiles.Batch643.profile25752,MergedCutProfiles.Batch643.profile25747,MergedCutProfiles.Batch643.profile25753,MergedCutProfiles.Batch559.profile22388,MergedCutProfiles.Batch643.profile25754,MergedCutProfiles.Batch643.profile25755,MergedCutProfiles.Batch560.profile22404,MergedCutProfiles.Batch439.profile17564]⟩
theorem profilesValid4301 : retention4301.ProfilesValid := by
  change ∀ j : Fin 16, (retention4301.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch643.valid25748
  · exact MergedCutProfiles.Batch643.valid25749
  · exact MergedCutProfiles.Batch643.valid25750
  · exact MergedCutProfiles.Batch560.valid22415
  · exact MergedCutProfiles.Batch560.valid22401
  · exact MergedCutProfiles.Batch643.valid25751
  · exact MergedCutProfiles.Batch643.valid25736
  · exact MergedCutProfiles.Batch560.valid22416
  · exact MergedCutProfiles.Batch643.valid25752
  · exact MergedCutProfiles.Batch643.valid25747
  · exact MergedCutProfiles.Batch643.valid25753
  · exact MergedCutProfiles.Batch559.valid22388
  · exact MergedCutProfiles.Batch643.valid25754
  · exact MergedCutProfiles.Batch643.valid25755
  · exact MergedCutProfiles.Batch560.valid22404
  · exact MergedCutProfiles.Batch439.valid17564
theorem numericValid4301 : retention4301.NumericValid := by decide +kernel
def certificate4301 : RatCutBinCertificate := ⟨⟨retention4301,(546311116048427081/250000000000000000),(123364672097640231/500000000000000000),(365908636843307189/20000000000000000),(1696830763966484987757/500000000000000000),(279059826913063343/125000000000000000)⟩,(12493900214194943/12500000000000000),(15873667028186961/50000000000000000),(159127820417823387/500000000000000000),(42477688275226239/200000000000000000)⟩
theorem valid4301 : certificate4301.Valid := by decide +kernel
theorem sound4301 : certificate4301.Sound := rat_cut_bin_certificate_sound certificate4301 profilesValid4301 numericValid4301 valid4301

def retention4302 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(14268114762503031215/92447378412680925593),(1849348669858173407/1000000000000000000),(9/5),(2260643169090722272683/1280000000000000000000),true,MergedCutProfiles.Batch643.profile25756,![MergedCutProfiles.Batch643.profile25756,MergedCutProfiles.Batch643.profile25757,MergedCutProfiles.Batch643.profile25758,MergedCutProfiles.Batch643.profile25759,MergedCutProfiles.Batch644.profile25760,MergedCutProfiles.Batch644.profile25761,MergedCutProfiles.Batch644.profile25762,MergedCutProfiles.Batch644.profile25763,MergedCutProfiles.Batch644.profile25764,MergedCutProfiles.Batch644.profile25765,MergedCutProfiles.Batch644.profile25766,MergedCutProfiles.Batch644.profile25767,MergedCutProfiles.Batch644.profile25768,MergedCutProfiles.Batch644.profile25769,MergedCutProfiles.Batch644.profile25770,MergedCutProfiles.Batch644.profile25771]⟩
theorem profilesValid4302 : retention4302.ProfilesValid := by
  change ∀ j : Fin 16, (retention4302.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch643.valid25756
  · exact MergedCutProfiles.Batch643.valid25757
  · exact MergedCutProfiles.Batch643.valid25758
  · exact MergedCutProfiles.Batch643.valid25759
  · exact MergedCutProfiles.Batch644.valid25760
  · exact MergedCutProfiles.Batch644.valid25761
  · exact MergedCutProfiles.Batch644.valid25762
  · exact MergedCutProfiles.Batch644.valid25763
  · exact MergedCutProfiles.Batch644.valid25764
  · exact MergedCutProfiles.Batch644.valid25765
  · exact MergedCutProfiles.Batch644.valid25766
  · exact MergedCutProfiles.Batch644.valid25767
  · exact MergedCutProfiles.Batch644.valid25768
  · exact MergedCutProfiles.Batch644.valid25769
  · exact MergedCutProfiles.Batch644.valid25770
  · exact MergedCutProfiles.Batch644.valid25771
theorem numericValid4302 : retention4302.NumericValid := by decide +kernel
def certificate4302 : RatCutBinCertificate := ⟨⟨retention4302,(546311116048427081/250000000000000000),(123364672097640231/500000000000000000),(365908636843307189/20000000000000000),(1696830763966484987757/500000000000000000),(428270139412252841/250000000000000000)⟩,(12493900214194943/12500000000000000),(344574247848440307/1000000000000000000),(144146915492927759/500000000000000000),(106623813772147647/500000000000000000)⟩
theorem valid4302 : certificate4302.Valid := by decide +kernel
theorem sound4302 : certificate4302.Sound := rat_cut_bin_certificate_sound certificate4302 profilesValid4302 numericValid4302 valid4302

def retention4303 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(32000000000000000000/92447378412680925593),(2853622952500606243/100000000000000000),1,(9307798801969044794502369492779588349/7134057381251515607500000000000000000),false,MergedCutProfiles.Batch644.profile25772,(fun _ => MergedCutProfiles.Batch644.profile25772)⟩
theorem profilesValid4303 : retention4303.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25772
theorem numericValid4303 : retention4303.NumericValid := by decide +kernel
def certificate4303 : RatCutBinCertificate := ⟨⟨retention4303,(546311116048427081/250000000000000000),(123364672097640231/500000000000000000),(365908636843307189/20000000000000000),(1696830763966484987757/500000000000000000),(1275229236558240981/1000000000000000000)⟩,(12493900214194943/12500000000000000),(39790186522772497/125000000000000000),(317283964627937827/1000000000000000000),(77421647387833031/200000000000000000)⟩
theorem valid4303 : certificate4303.Valid := by decide +kernel
theorem sound4303 : certificate4303.Sound := rat_cut_bin_certificate_sound certificate4303 profilesValid4303 numericValid4303 valid4303

def retention4304 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(1/2),64,1,(10216831075443792460644374972913285751/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch307.profile12294,(fun _ => MergedCutProfiles.Batch307.profile12294)⟩
theorem profilesValid4304 : retention4304.ProfilesValid := by
  exact MergedCutProfiles.Batch307.valid12294
theorem numericValid4304 : retention4304.NumericValid := by decide +kernel
def certificate4304 : RatCutBinCertificate := ⟨⟨retention4304,(546311116048427081/250000000000000000),(123364672097640231/500000000000000000),(365908636843307189/20000000000000000),(1696830763966484987757/500000000000000000),(968267509755407297/1000000000000000000)⟩,(12493900214194943/12500000000000000),(411925314056465331/1000000000000000000),(111365872237884327/500000000000000000),(26543106062849223/125000000000000000)⟩
theorem valid4304 : certificate4304.Valid := by decide +kernel
theorem sound4304 : certificate4304.Sound := rat_cut_bin_certificate_sound certificate4304 profilesValid4304 numericValid4304 valid4304

def retention4305 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(32000000000000000000/92447378412680925593),(22032724629189966667/1000000000000000000),1,(3580851065275964824155347698764349833/2754090578648745833375000000000000000),false,MergedCutProfiles.Batch644.profile25772,(fun _ => MergedCutProfiles.Batch644.profile25772)⟩
theorem profilesValid4305 : retention4305.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25772
theorem numericValid4305 : retention4305.NumericValid := by decide +kernel
def certificate4305 : RatCutBinCertificate := ⟨⟨retention4305,(493128461798427081/250000000000000000),(123364672097640231/500000000000000000),(365908636843307189/20000000000000000),(1696830763966484987757/500000000000000000),(127359254168053917/100000000000000000)⟩,(31236235259486231/31250000000000000),(38613831603764479/1000000000000000000),(819624377231918613/1000000000000000000),(986374289140019911/1000000000000000000)⟩
theorem valid4305 : certificate4305.Valid := by decide +kernel
theorem sound4305 : certificate4305.Sound := rat_cut_bin_certificate_sound certificate4305 profilesValid4305 numericValid4305 valid4305

def retention4306 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(1/2),64,1,(10216831075443792460644374972913285751/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch307.profile12294,(fun _ => MergedCutProfiles.Batch307.profile12294)⟩
theorem profilesValid4306 : retention4306.ProfilesValid := by
  exact MergedCutProfiles.Batch307.valid12294
theorem numericValid4306 : retention4306.NumericValid := by decide +kernel
def certificate4306 : RatCutBinCertificate := ⟨⟨retention4306,(493128461798427081/250000000000000000),(123364672097640231/500000000000000000),(365908636843307189/20000000000000000),(1696830763966484987757/500000000000000000),(121392045622639149/125000000000000000)⟩,(31236235259486231/31250000000000000),(25319970351032607/500000000000000000),(393326872346926689/500000000000000000),(752193453634767359/1000000000000000000)⟩
theorem valid4306 : certificate4306.Valid := by decide +kernel
theorem sound4306 : certificate4306.Sound := rat_cut_bin_certificate_sound certificate4306 profilesValid4306 numericValid4306 valid4306

def retention4307 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(270990526509343347/125026698194473073587265),(284103060135010773/500000000000000000),4,(1664894401467884625390498122181833277/757608160360028728000000000000000000),true,MergedCutProfiles.Batch644.profile25773,![MergedCutProfiles.Batch644.profile25773,MergedCutProfiles.Batch561.profile22447,MergedCutProfiles.Batch561.profile22447,MergedCutProfiles.Batch561.profile22447,MergedCutProfiles.Batch561.profile22447,MergedCutProfiles.Batch561.profile22447,MergedCutProfiles.Batch561.profile22447,MergedCutProfiles.Batch561.profile22448,MergedCutProfiles.Batch561.profile22448,MergedCutProfiles.Batch561.profile22448,MergedCutProfiles.Batch561.profile22448,MergedCutProfiles.Batch561.profile22448,MergedCutProfiles.Batch561.profile22448,MergedCutProfiles.Batch561.profile22448,MergedCutProfiles.Batch561.profile22448,MergedCutProfiles.Batch440.profile17639]⟩
theorem profilesValid4307 : retention4307.ProfilesValid := by
  change ∀ j : Fin 16, (retention4307.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch644.valid25773
  · exact MergedCutProfiles.Batch561.valid22447
  · exact MergedCutProfiles.Batch561.valid22447
  · exact MergedCutProfiles.Batch561.valid22447
  · exact MergedCutProfiles.Batch561.valid22447
  · exact MergedCutProfiles.Batch561.valid22447
  · exact MergedCutProfiles.Batch561.valid22447
  · exact MergedCutProfiles.Batch561.valid22448
  · exact MergedCutProfiles.Batch561.valid22448
  · exact MergedCutProfiles.Batch561.valid22448
  · exact MergedCutProfiles.Batch561.valid22448
  · exact MergedCutProfiles.Batch561.valid22448
  · exact MergedCutProfiles.Batch561.valid22448
  · exact MergedCutProfiles.Batch561.valid22448
  · exact MergedCutProfiles.Batch561.valid22448
  · exact MergedCutProfiles.Batch440.valid17639
theorem numericValid4307 : retention4307.NumericValid := by decide +kernel
def certificate4307 : RatCutBinCertificate := ⟨⟨retention4307,(1842540530097226809/1000000000000000000),(637434242080419/1000000000000000000),(864707979900376041/125000000000000000),(2605974084985895537591801/1000000000000000000),(2196887486236195379/1000000000000000000)⟩,(3124997791274663/3125000000000000),(583972251017105547/1000000000000000000),(50954007328156567/500000000000000000),(9015452924580459/200000000000000000)⟩
theorem valid4307 : certificate4307.Valid := by decide +kernel
theorem sound4307 : certificate4307.Sound := rat_cut_bin_certificate_sound certificate4307 profilesValid4307 numericValid4307 valid4307

def certificates : List RatCutBinCertificate := [certificate4296,certificate4297,certificate4298,certificate4299,certificate4300,certificate4301,certificate4302,certificate4303,certificate4304,certificate4305,certificate4306,certificate4307]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4296,List.forall_mem_cons.mpr ⟨sound4297,List.forall_mem_cons.mpr ⟨sound4298,List.forall_mem_cons.mpr ⟨sound4299,List.forall_mem_cons.mpr ⟨sound4300,List.forall_mem_cons.mpr ⟨sound4301,List.forall_mem_cons.mpr ⟨sound4302,List.forall_mem_cons.mpr ⟨sound4303,List.forall_mem_cons.mpr ⟨sound4304,List.forall_mem_cons.mpr ⟨sound4305,List.forall_mem_cons.mpr ⟨sound4306,List.forall_mem_cons.mpr ⟨sound4307,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch358
