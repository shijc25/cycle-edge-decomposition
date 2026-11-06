import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch380
import Cycle12.MergedCutProfiles.Batch381
import Cycle12.MergedCutProfiles.Batch498
import Cycle12.MergedCutProfiles.Batch499
import Cycle12.MergedCutProfiles.Batch500

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch271

def retention3252 : RatCutRetentionCertificate := ⟨(103/2000),(13/250),(43519960528087229846/87180495143465975733),(43089069829789336481/1000000000000000000),1,(171897290314005167008406819709015688683/172356279319157345924000000000000000000),false,MergedCutProfiles.Batch498.profile19953,(fun _ => MergedCutProfiles.Batch498.profile19953)⟩
theorem profilesValid3252 : retention3252.ProfilesValid := by
  exact MergedCutProfiles.Batch498.valid19953
theorem numericValid3252 : retention3252.NumericValid := by decide +kernel
def certificate3252 : RatCutBinCertificate := ⟨⟨retention3252,(52594324540364433/25000000000000000),(65444215677591123/500000000000000000),(3415730931803916221/250000000000000000),(597297544153012880923/500000000000000000),(195436629035359631/200000000000000000)⟩,(124808007605054243/125000000000000000),(450104233127396533/1000000000000000000),(190588039816685473/1000000000000000000),(7273035254207549/40000000000000000)⟩
theorem valid3252 : certificate3252.Valid := by decide +kernel
theorem sound3252 : certificate3252.Sound := rat_cut_bin_certificate_sound certificate3252 profilesValid3252 numericValid3252 valid3252

def retention3253 : RatCutRetentionCertificate := ⟨(103/2000),(13/250),(1/2),(21759980264043614923/500000000000000000),1,(1354284399533309405096260018155908163/1359998766502725932687500000000000000),false,MergedCutProfiles.Batch498.profile19954,(fun _ => MergedCutProfiles.Batch498.profile19954)⟩
theorem profilesValid3253 : retention3253.ProfilesValid := by
  exact MergedCutProfiles.Batch498.valid19954
theorem numericValid3253 : retention3253.NumericValid := by decide +kernel
def certificate3253 : RatCutBinCertificate := ⟨⟨retention3253,(52594324540364433/25000000000000000),(65444215677591123/500000000000000000),(3415730931803916221/250000000000000000),(597297544153012880923/500000000000000000),(48782221300803761/50000000000000000)⟩,(124808007605054243/125000000000000000),(225363470526529981/500000000000000000),(38018276624642513/200000000000000000),(18111255627937287/100000000000000000)⟩
theorem valid3253 : certificate3253.Valid := by decide +kernel
theorem sound3253 : certificate3253.Sound := rat_cut_bin_certificate_sound certificate3253 profilesValid3253 numericValid3253 valid3253

def retention3254 : RatCutRetentionCertificate := ⟨(103/2000),(13/250),(40008938267578808543/87180495143465975733),(4967463689661759691/500000000000000000),1,(41914481172776888239213795643002484287/39739709517294077528000000000000000000),false,MergedCutProfiles.Batch498.profile19955,(fun _ => MergedCutProfiles.Batch498.profile19955)⟩
theorem profilesValid3254 : retention3254.ProfilesValid := by
  exact MergedCutProfiles.Batch498.valid19955
theorem numericValid3254 : retention3254.NumericValid := by decide +kernel
def certificate3254 : RatCutBinCertificate := ⟨⟨retention3254,(55243400040364433/25000000000000000),(65444215677591123/500000000000000000),(3415730931803916221/250000000000000000),(597297544153012880923/500000000000000000),(516778142083784877/500000000000000000)⟩,(199677336039351669/200000000000000000),(59956418906551961/500000000000000000),(623677818725304623/1000000000000000000),(116574556913871509/200000000000000000)⟩
theorem valid3254 : certificate3254.Valid := by decide +kernel
theorem sound3254 : certificate3254.Sound := rat_cut_bin_certificate_sound certificate3254 profilesValid3254 numericValid3254 valid3254

def retention3255 : RatCutRetentionCertificate := ⟨(103/2000),(13/250),(43323947088107614898/87180495143465975733),(40008938267578808543/1000000000000000000),1,(32049937916659637966049173684666831999/32007150614063046834400000000000000000),false,MergedCutProfiles.Batch498.profile19956,(fun _ => MergedCutProfiles.Batch498.profile19956)⟩
theorem profilesValid3255 : retention3255.ProfilesValid := by
  exact MergedCutProfiles.Batch498.valid19956
theorem numericValid3255 : retention3255.NumericValid := by decide +kernel
def certificate3255 : RatCutBinCertificate := ⟨⟨retention3255,(55243400040364433/25000000000000000),(65444215677591123/500000000000000000),(3415730931803916221/250000000000000000),(597297544153012880923/500000000000000000),(490083930105948551/500000000000000000)⟩,(199677336039351669/200000000000000000),(63222164337905833/500000000000000000),(152575621094322411/250000000000000000),(291469363653100141/500000000000000000)⟩
theorem valid3255 : certificate3255.Valid := by decide +kernel
theorem sound3255 : certificate3255.Sound := rat_cut_bin_certificate_sound certificate3255 profilesValid3255 numericValid3255 valid3255

def retention3256 : RatCutRetentionCertificate := ⟨(103/2000),(13/250),(1/2),(21661973544053807449/500000000000000000),1,(26962988392919647308711609573329751/27077466930067259311250000000000000),false,MergedCutProfiles.Batch498.profile19954,(fun _ => MergedCutProfiles.Batch498.profile19954)⟩
theorem profilesValid3256 : retention3256.ProfilesValid := by
  exact MergedCutProfiles.Batch498.valid19954
theorem numericValid3256 : retention3256.NumericValid := by decide +kernel
def certificate3256 : RatCutBinCertificate := ⟨⟨retention3256,(55243400040364433/25000000000000000),(65444215677591123/500000000000000000),(3415730931803916221/250000000000000000),(597297544153012880923/500000000000000000),(15228175696212427/15625000000000000)⟩,(199677336039351669/200000000000000000),(63583138967672479/500000000000000000),(304421114547893279/500000000000000000),(579376141196738921/1000000000000000000)⟩
theorem valid3256 : certificate3256.Valid := by decide +kernel
theorem sound3256 : certificate3256.Sound := rat_cut_bin_certificate_sound certificate3256 profilesValid3256 numericValid3256 valid3256

def retention3257 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(812044907056732924/83434655556689126119),(201001214618003199/250000000000000000),(17/5),(731958533681792101499/320000000000000000000),true,MergedCutProfiles.Batch498.profile19957,![MergedCutProfiles.Batch498.profile19957,MergedCutProfiles.Batch498.profile19958,MergedCutProfiles.Batch380.profile15231,MergedCutProfiles.Batch498.profile19959,MergedCutProfiles.Batch499.profile19960,MergedCutProfiles.Batch380.profile15232,MergedCutProfiles.Batch499.profile19961,MergedCutProfiles.Batch380.profile15217,MergedCutProfiles.Batch499.profile19962,MergedCutProfiles.Batch499.profile19963,MergedCutProfiles.Batch499.profile19964,MergedCutProfiles.Batch380.profile15234,MergedCutProfiles.Batch499.profile19965,MergedCutProfiles.Batch499.profile19966,MergedCutProfiles.Batch499.profile19967,MergedCutProfiles.Batch499.profile19968]⟩
theorem profilesValid3257 : retention3257.ProfilesValid := by
  change ∀ j : Fin 16, (retention3257.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch498.valid19957
  · exact MergedCutProfiles.Batch498.valid19958
  · exact MergedCutProfiles.Batch380.valid15231
  · exact MergedCutProfiles.Batch498.valid19959
  · exact MergedCutProfiles.Batch499.valid19960
  · exact MergedCutProfiles.Batch380.valid15232
  · exact MergedCutProfiles.Batch499.valid19961
  · exact MergedCutProfiles.Batch380.valid15217
  · exact MergedCutProfiles.Batch499.valid19962
  · exact MergedCutProfiles.Batch499.valid19963
  · exact MergedCutProfiles.Batch499.valid19964
  · exact MergedCutProfiles.Batch380.valid15234
  · exact MergedCutProfiles.Batch499.valid19965
  · exact MergedCutProfiles.Batch499.valid19966
  · exact MergedCutProfiles.Batch499.valid19967
  · exact MergedCutProfiles.Batch499.valid19968
theorem numericValid3257 : retention3257.NumericValid := by decide +kernel
def certificate3257 : RatCutBinCertificate := ⟨⟨retention3257,(1055108355159137459/500000000000000000),(136712609017002193/1000000000000000000),(13779305530758571177/1000000000000000000),(1156382762462842116309/1000000000000000000),(2216182547793271667/1000000000000000000)⟩,(499206813341826959/500000000000000000),(1588207770133907/4000000000000000),(236194406114997261/1000000000000000000),(62040256922420433/500000000000000000)⟩
theorem valid3257 : certificate3257.Valid := by decide +kernel
theorem sound3257 : certificate3257.Sound := rat_cut_bin_certificate_sound certificate3257 profilesValid3257 numericValid3257 valid3257

def retention3258 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(1000757598656908944/83434655556689126119),(203011226764183231/250000000000000000),(67/20),(726150635528089994539/320000000000000000000),true,MergedCutProfiles.Batch499.profile19969,![MergedCutProfiles.Batch499.profile19969,MergedCutProfiles.Batch499.profile19970,MergedCutProfiles.Batch499.profile19971,MergedCutProfiles.Batch499.profile19960,MergedCutProfiles.Batch499.profile19972,MergedCutProfiles.Batch499.profile19973,MergedCutProfiles.Batch499.profile19974,MergedCutProfiles.Batch499.profile19975,MergedCutProfiles.Batch499.profile19976,MergedCutProfiles.Batch499.profile19977,MergedCutProfiles.Batch381.profile15265,MergedCutProfiles.Batch380.profile15235,MergedCutProfiles.Batch499.profile19968,MergedCutProfiles.Batch499.profile19978,MergedCutProfiles.Batch499.profile19979,MergedCutProfiles.Batch499.profile19980]⟩
theorem profilesValid3258 : retention3258.ProfilesValid := by
  change ∀ j : Fin 16, (retention3258.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch499.valid19969
  · exact MergedCutProfiles.Batch499.valid19970
  · exact MergedCutProfiles.Batch499.valid19971
  · exact MergedCutProfiles.Batch499.valid19960
  · exact MergedCutProfiles.Batch499.valid19972
  · exact MergedCutProfiles.Batch499.valid19973
  · exact MergedCutProfiles.Batch499.valid19974
  · exact MergedCutProfiles.Batch499.valid19975
  · exact MergedCutProfiles.Batch499.valid19976
  · exact MergedCutProfiles.Batch499.valid19977
  · exact MergedCutProfiles.Batch381.valid15265
  · exact MergedCutProfiles.Batch380.valid15235
  · exact MergedCutProfiles.Batch499.valid19968
  · exact MergedCutProfiles.Batch499.valid19978
  · exact MergedCutProfiles.Batch499.valid19979
  · exact MergedCutProfiles.Batch499.valid19980
theorem numericValid3258 : retention3258.NumericValid := by decide +kernel
def certificate3258 : RatCutBinCertificate := ⟨⟨retention3258,(1055108355159137459/500000000000000000),(136712609017002193/1000000000000000000),(13779305530758571177/1000000000000000000),(1156382762462842116309/1000000000000000000),(87963189268444823/40000000000000000)⟩,(499206813341826959/500000000000000000),(24881503448652247/62500000000000000),(235224020772739153/1000000000000000000),(62080082365623619/500000000000000000)⟩
theorem valid3258 : certificate3258.Valid := by decide +kernel
theorem sound3258 : certificate3258.Sound := rat_cut_bin_certificate_sound certificate3258 profilesValid3258 numericValid3258 valid3258

def retention3259 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(1106853147000000000/83434655556689126119),(62547349916056809/62500000000000000),(14/5),(89928466548047838819/40000000000000000000),true,MergedCutProfiles.Batch499.profile19981,![MergedCutProfiles.Batch499.profile19981,MergedCutProfiles.Batch499.profile19982,MergedCutProfiles.Batch499.profile19983,MergedCutProfiles.Batch499.profile19984,MergedCutProfiles.Batch381.profile15263,MergedCutProfiles.Batch499.profile19985,MergedCutProfiles.Batch499.profile19986,MergedCutProfiles.Batch499.profile19987,MergedCutProfiles.Batch381.profile15250,MergedCutProfiles.Batch499.profile19988,MergedCutProfiles.Batch499.profile19967,MergedCutProfiles.Batch499.profile19989,MergedCutProfiles.Batch499.profile19990,MergedCutProfiles.Batch499.profile19991,MergedCutProfiles.Batch499.profile19992,MergedCutProfiles.Batch499.profile19993]⟩
theorem profilesValid3259 : retention3259.ProfilesValid := by
  change ∀ j : Fin 16, (retention3259.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch499.valid19981
  · exact MergedCutProfiles.Batch499.valid19982
  · exact MergedCutProfiles.Batch499.valid19983
  · exact MergedCutProfiles.Batch499.valid19984
  · exact MergedCutProfiles.Batch381.valid15263
  · exact MergedCutProfiles.Batch499.valid19985
  · exact MergedCutProfiles.Batch499.valid19986
  · exact MergedCutProfiles.Batch499.valid19987
  · exact MergedCutProfiles.Batch381.valid15250
  · exact MergedCutProfiles.Batch499.valid19988
  · exact MergedCutProfiles.Batch499.valid19967
  · exact MergedCutProfiles.Batch499.valid19989
  · exact MergedCutProfiles.Batch499.valid19990
  · exact MergedCutProfiles.Batch499.valid19991
  · exact MergedCutProfiles.Batch499.valid19992
  · exact MergedCutProfiles.Batch499.valid19993
theorem numericValid3259 : retention3259.NumericValid := by decide +kernel
def certificate3259 : RatCutBinCertificate := ⟨⟨retention3259,(1055108355159137459/500000000000000000),(136712609017002193/1000000000000000000),(13779305530758571177/1000000000000000000),(1156382762462842116309/1000000000000000000),(2189586421008896849/1000000000000000000)⟩,(499206813341826959/500000000000000000),(180636702266572631/500000000000000000),(10836104483453829/40000000000000000),(165315399126435439/1000000000000000000)⟩
theorem valid3259 : certificate3259.Valid := by decide +kernel
theorem sound3259 : certificate3259.Sound := rat_cut_bin_certificate_sound certificate3259 profilesValid3259 numericValid3259 valid3259

def retention3260 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(1535139933095821694/83434655556689126119),(1106853147/1000000000),(51/20),(35340481026009841001/16000000000000000000),true,MergedCutProfiles.Batch499.profile19994,![MergedCutProfiles.Batch499.profile19994,MergedCutProfiles.Batch499.profile19995,MergedCutProfiles.Batch499.profile19996,MergedCutProfiles.Batch499.profile19997,MergedCutProfiles.Batch499.profile19998,MergedCutProfiles.Batch499.profile19999,MergedCutProfiles.Batch500.profile20000,MergedCutProfiles.Batch500.profile20001,MergedCutProfiles.Batch500.profile20002,MergedCutProfiles.Batch500.profile20003,MergedCutProfiles.Batch380.profile15237,MergedCutProfiles.Batch500.profile20004,MergedCutProfiles.Batch500.profile20005,MergedCutProfiles.Batch500.profile20006,MergedCutProfiles.Batch500.profile20007,MergedCutProfiles.Batch500.profile20008]⟩
theorem profilesValid3260 : retention3260.ProfilesValid := by
  change ∀ j : Fin 16, (retention3260.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch499.valid19994
  · exact MergedCutProfiles.Batch499.valid19995
  · exact MergedCutProfiles.Batch499.valid19996
  · exact MergedCutProfiles.Batch499.valid19997
  · exact MergedCutProfiles.Batch499.valid19998
  · exact MergedCutProfiles.Batch499.valid19999
  · exact MergedCutProfiles.Batch500.valid20000
  · exact MergedCutProfiles.Batch500.valid20001
  · exact MergedCutProfiles.Batch500.valid20002
  · exact MergedCutProfiles.Batch500.valid20003
  · exact MergedCutProfiles.Batch380.valid15237
  · exact MergedCutProfiles.Batch500.valid20004
  · exact MergedCutProfiles.Batch500.valid20005
  · exact MergedCutProfiles.Batch500.valid20006
  · exact MergedCutProfiles.Batch500.valid20007
  · exact MergedCutProfiles.Batch500.valid20008
theorem numericValid3260 : retention3260.NumericValid := by decide +kernel
def certificate3260 : RatCutBinCertificate := ⟨⟨retention3260,(1055108355159137459/500000000000000000),(136712609017002193/1000000000000000000),(13779305530758571177/1000000000000000000),(1156382762462842116309/1000000000000000000),(1077694617173143531/500000000000000000)⟩,(499206813341826959/500000000000000000),(175424880777419349/500000000000000000),(35208189381875683/125000000000000000),(91435837127743083/500000000000000000)⟩
theorem valid3260 : certificate3260.Valid := by decide +kernel
theorem sound3260 : certificate3260.Sound := rat_cut_bin_certificate_sound certificate3260 profilesValid3260 numericValid3260 valid3260

def retention3261 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(10066711302830583822/83434655556689126119),(767569966547910847/500000000000000000),2,(236164450985836680839/128000000000000000000),true,MergedCutProfiles.Batch499.profile19977,![MergedCutProfiles.Batch499.profile19977,MergedCutProfiles.Batch500.profile20009,MergedCutProfiles.Batch380.profile15228,MergedCutProfiles.Batch500.profile20010,MergedCutProfiles.Batch500.profile20011,MergedCutProfiles.Batch500.profile20012,MergedCutProfiles.Batch500.profile20013,MergedCutProfiles.Batch500.profile20014,MergedCutProfiles.Batch500.profile20015,MergedCutProfiles.Batch500.profile20016,MergedCutProfiles.Batch500.profile20017,MergedCutProfiles.Batch500.profile20018,MergedCutProfiles.Batch500.profile20019,MergedCutProfiles.Batch500.profile20020,MergedCutProfiles.Batch500.profile20021,MergedCutProfiles.Batch500.profile20022]⟩
theorem profilesValid3261 : retention3261.ProfilesValid := by
  change ∀ j : Fin 16, (retention3261.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch499.valid19977
  · exact MergedCutProfiles.Batch500.valid20009
  · exact MergedCutProfiles.Batch380.valid15228
  · exact MergedCutProfiles.Batch500.valid20010
  · exact MergedCutProfiles.Batch500.valid20011
  · exact MergedCutProfiles.Batch500.valid20012
  · exact MergedCutProfiles.Batch500.valid20013
  · exact MergedCutProfiles.Batch500.valid20014
  · exact MergedCutProfiles.Batch500.valid20015
  · exact MergedCutProfiles.Batch500.valid20016
  · exact MergedCutProfiles.Batch500.valid20017
  · exact MergedCutProfiles.Batch500.valid20018
  · exact MergedCutProfiles.Batch500.valid20019
  · exact MergedCutProfiles.Batch500.valid20020
  · exact MergedCutProfiles.Batch500.valid20021
  · exact MergedCutProfiles.Batch500.valid20022
theorem numericValid3261 : retention3261.NumericValid := by decide +kernel
def certificate3261 : RatCutBinCertificate := ⟨⟨retention3261,(1055108355159137459/500000000000000000),(136712609017002193/1000000000000000000),(13779305530758571177/1000000000000000000),(1156382762462842116309/1000000000000000000),(1803159754277392607/1000000000000000000)⟩,(499206813341826959/500000000000000000),(92141271845823207/250000000000000000),(263552697036864397/1000000000000000000),(18334058609322391/100000000000000000)⟩
theorem valid3261 : certificate3261.Valid := by decide +kernel
theorem sound3261 : certificate3261.Sound := rat_cut_bin_certificate_sound certificate3261 profilesValid3261 numericValid3261 valid3261

def retention3262 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(38190179602111075025/83434655556689126119),(5033355651415291911/500000000000000000),(21/20),(4341920858825863710408871273564578556439/4026684521132233528800000000000000000000),false,MergedCutProfiles.Batch500.profile20023,(fun _ => MergedCutProfiles.Batch500.profile20023)⟩
theorem profilesValid3262 : retention3262.ProfilesValid := by
  exact MergedCutProfiles.Batch500.valid20023
theorem numericValid3262 : retention3262.NumericValid := by decide +kernel
def certificate3262 : RatCutBinCertificate := ⟨⟨retention3262,(1055108355159137459/500000000000000000),(136712609017002193/1000000000000000000),(13779305530758571177/1000000000000000000),(1156382762462842116309/1000000000000000000),(528151519222337399/500000000000000000)⟩,(499206813341826959/500000000000000000),(439149003064215759/1000000000000000000),(39893527202550443/200000000000000000),(91460121560316551/500000000000000000)⟩
theorem valid3262 : certificate3262.Valid := by decide +kernel
theorem sound3262 : certificate3262.Sound := rat_cut_bin_certificate_sound certificate3262 profilesValid3262 numericValid3262 valid3262

def retention3263 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(41354492071286701574/83434655556689126119),(1527607184084443001/40000000000000000),1,(153310273640969274805280555898034616179/152760718408444300100000000000000000000),false,MergedCutProfiles.Batch500.profile20024,(fun _ => MergedCutProfiles.Batch500.profile20024)⟩
theorem profilesValid3263 : retention3263.ProfilesValid := by
  exact MergedCutProfiles.Batch500.valid20024
theorem numericValid3263 : retention3263.NumericValid := by decide +kernel
def certificate3263 : RatCutBinCertificate := ⟨⟨retention3263,(1055108355159137459/500000000000000000),(136712609017002193/1000000000000000000),(13779305530758571177/1000000000000000000),(1156382762462842116309/1000000000000000000),(982660722347122969/1000000000000000000)⟩,(499206813341826959/500000000000000000),(444995366992856261/1000000000000000000),(194695379386960029/1000000000000000000),(37243926669154067/200000000000000000)⟩
theorem valid3263 : certificate3263.Valid := by decide +kernel
theorem sound3263 : certificate3263.Sound := rat_cut_bin_certificate_sound certificate3263 profilesValid3263 numericValid3263 valid3263

def certificates : List RatCutBinCertificate := [certificate3252,certificate3253,certificate3254,certificate3255,certificate3256,certificate3257,certificate3258,certificate3259,certificate3260,certificate3261,certificate3262,certificate3263]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3252,List.forall_mem_cons.mpr ⟨sound3253,List.forall_mem_cons.mpr ⟨sound3254,List.forall_mem_cons.mpr ⟨sound3255,List.forall_mem_cons.mpr ⟨sound3256,List.forall_mem_cons.mpr ⟨sound3257,List.forall_mem_cons.mpr ⟨sound3258,List.forall_mem_cons.mpr ⟨sound3259,List.forall_mem_cons.mpr ⟨sound3260,List.forall_mem_cons.mpr ⟨sound3261,List.forall_mem_cons.mpr ⟨sound3262,List.forall_mem_cons.mpr ⟨sound3263,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch271
