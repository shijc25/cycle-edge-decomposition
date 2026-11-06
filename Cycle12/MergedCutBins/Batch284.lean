import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch225
import Cycle12.MergedCutProfiles.Batch226
import Cycle12.MergedCutProfiles.Batch402
import Cycle12.MergedCutProfiles.Batch403
import Cycle12.MergedCutProfiles.Batch524
import Cycle12.MergedCutProfiles.Batch525

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch284

def retention3408 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(16792173030864414739/62434805177457448668),(2436466176771651239/1000000000000000000),(3/2),(57760815842933911887115996899814607903/38983458828346419824000000000000000000),false,MergedCutProfiles.Batch524.profile20969,(fun _ => MergedCutProfiles.Batch524.profile20969)⟩
theorem profilesValid3408 : retention3408.ProfilesValid := by
  exact MergedCutProfiles.Batch524.valid20969
theorem numericValid3408 : retention3408.NumericValid := by decide +kernel
def certificate3408 : RatCutBinCertificate := ⟨⟨retention3408,(1101732253151122287/500000000000000000),(182428996879551849/1000000000000000000),(7861754971596926307/500000000000000000),(98469645076024067049/100000000000000000),(1443325133760896411/1000000000000000000)⟩,(249540445982883979/250000000000000000),(70630054074208501/200000000000000000),(34907981664062427/125000000000000000),(53065852214311803/250000000000000000)⟩
theorem valid3408 : certificate3408.Valid := by decide +kernel
theorem sound3408 : certificate3408.Sound := rat_cut_bin_certificate_sound certificate3408 profilesValid3408 numericValid3408 valid3408

def retention3409 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(30204242878107263077/62434805177457448668),(16792173030864414739/1000000000000000000),1,(26716976112109532512407732755298801/26237770360725648029687500000000000),false,MergedCutProfiles.Batch524.profile20970,(fun _ => MergedCutProfiles.Batch524.profile20970)⟩
theorem profilesValid3409 : retention3409.ProfilesValid := by
  exact MergedCutProfiles.Batch524.valid20970
theorem numericValid3409 : retention3409.NumericValid := by decide +kernel
def certificate3409 : RatCutBinCertificate := ⟨⟨retention3409,(1101732253151122287/500000000000000000),(182428996879551849/1000000000000000000),(7861754971596926307/500000000000000000),(98469645076024067049/100000000000000000),(992698411454735861/1000000000000000000)⟩,(249540445982883979/250000000000000000),(406461031279727023/1000000000000000000),(227614322400345557/1000000000000000000),(10646691216966203/50000000000000000)⟩
theorem valid3409 : certificate3409.Valid := by decide +kernel
theorem sound3409 : certificate3409.Sound := rat_cut_bin_certificate_sound certificate3409 profilesValid3409 numericValid3409 valid3409

def retention3410 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(10373153880518930419/20811601725819149556),(30204242878107263077/1000000000000000000),1,(120381000015364050251426852645790481107/120816971512429052308000000000000000000),false,MergedCutProfiles.Batch524.profile20971,(fun _ => MergedCutProfiles.Batch524.profile20971)⟩
theorem profilesValid3410 : retention3410.ProfilesValid := by
  exact MergedCutProfiles.Batch524.valid20971
theorem numericValid3410 : retention3410.NumericValid := by decide +kernel
def certificate3410 : RatCutBinCertificate := ⟨⟨retention3410,(1101732253151122287/500000000000000000),(182428996879551849/1000000000000000000),(7861754971596926307/500000000000000000),(98469645076024067049/100000000000000000),(485413020943525917/500000000000000000)⟩,(249540445982883979/250000000000000000),(407372934989320983/1000000000000000000),(113397208970170499/500000000000000000),(42584199740462399/200000000000000000)⟩
theorem valid3410 : certificate3410.Valid := by decide +kernel
theorem sound3410 : certificate3410.Sound := rat_cut_bin_certificate_sound certificate3410 profilesValid3410 numericValid3410 valid3410

def retention3411 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(1/2),(31119461641556791257/1000000000000000000),1,(966205571836231940266555108357778209/972483176298649726781250000000000000),false,MergedCutProfiles.Batch402.profile16087,(fun _ => MergedCutProfiles.Batch402.profile16087)⟩
theorem profilesValid3411 : retention3411.ProfilesValid := by
  exact MergedCutProfiles.Batch402.valid16087
theorem numericValid3411 : retention3411.NumericValid := by decide +kernel
def certificate3411 : RatCutBinCertificate := ⟨⟨retention3411,(1101732253151122287/500000000000000000),(182428996879551849/1000000000000000000),(7861754971596926307/500000000000000000),(98469645076024067049/100000000000000000),(967979343157079243/1000000000000000000)⟩,(249540445982883979/250000000000000000),(102066614416102829/250000000000000000),(225993019355777663/1000000000000000000),(211759433752803333/1000000000000000000)⟩
theorem valid3411 : certificate3411.Valid := by decide +kernel
theorem sound3411 : certificate3411.Sound := rat_cut_bin_certificate_sound certificate3411 profilesValid3411 numericValid3411 valid3411

def retention3412 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(14413980425122004245/31217402588728724334),(9364803868152555641/1000000000000000000),1,(7848809163313688747323013393536058367/7491843094522044512800000000000000000),false,MergedCutProfiles.Batch524.profile20972,(fun _ => MergedCutProfiles.Batch524.profile20972)⟩
theorem profilesValid3412 : retention3412.ProfilesValid := by
  exact MergedCutProfiles.Batch524.valid20972
theorem numericValid3412 : retention3412.NumericValid := by decide +kernel
def certificate3412 : RatCutBinCertificate := ⟨⟨retention3412,(1137474946651122287/500000000000000000),(182428996879551849/1000000000000000000),(7861754971596926307/500000000000000000),(98469645076024067049/100000000000000000),(1021252106128952043/1000000000000000000)⟩,(998102123379863483/1000000000000000000),(59175548364769693/500000000000000000),(156730134142264103/250000000000000000),(576126933905264557/1000000000000000000)⟩
theorem valid3412 : certificate3412.Valid := by decide +kernel
theorem sound3412 : certificate3412.Sound := rat_cut_bin_certificate_sound certificate3412 profilesValid3412 numericValid3412 valid3412

def retention3413 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(15453737978351729711/31217402588728724334),(2882796085024400849/100000000000000000),1,(28905257412689667379854834799808400499/28827960850244008490000000000000000000),false,MergedCutProfiles.Batch524.profile20973,(fun _ => MergedCutProfiles.Batch524.profile20973)⟩
theorem profilesValid3413 : retention3413.ProfilesValid := by
  exact MergedCutProfiles.Batch524.valid20973
theorem numericValid3413 : retention3413.NumericValid := by decide +kernel
def certificate3413 : RatCutBinCertificate := ⟨⟨retention3413,(1137474946651122287/500000000000000000),(182428996879551849/1000000000000000000),(7861754971596926307/500000000000000000),(98469645076024067049/100000000000000000),(488143233734765177/500000000000000000)⟩,(998102123379863483/1000000000000000000),(24760418345445443/200000000000000000),(307838724522367143/500000000000000000),(580261471831944473/1000000000000000000)⟩
theorem valid3413 : certificate3413.Valid := by decide +kernel
theorem sound3413 : certificate3413.Sound := rat_cut_bin_certificate_sound certificate3413 profilesValid3413 numericValid3413 valid3413

def retention3414 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(31216550716270494017/62434805177457448668),(15453737978351729711/500000000000000000),1,(122828334579031791865686907567789995007/123629903826813837688000000000000000000),false,MergedCutProfiles.Batch524.profile20974,(fun _ => MergedCutProfiles.Batch524.profile20974)⟩
theorem profilesValid3414 : retention3414.ProfilesValid := by
  exact MergedCutProfiles.Batch524.valid20974
theorem numericValid3414 : retention3414.NumericValid := by decide +kernel
def certificate3414 : RatCutBinCertificate := ⟨⟨retention3414,(1137474946651122287/500000000000000000),(182428996879551849/1000000000000000000),(7861754971596926307/500000000000000000),(98469645076024067049/100000000000000000),(967121554204023807/1000000000000000000)⟩,(998102123379863483/1000000000000000000),(62487650219517023/500000000000000000),(613284890442261473/1000000000000000000),(574011707781842787/1000000000000000000)⟩
theorem valid3414 : certificate3414.Valid := by decide +kernel
theorem sound3414 : certificate3414.Sound := rat_cut_bin_certificate_sound certificate3414 profilesValid3414 numericValid3414 valid3414

def retention3415 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(1/2),(31216550716270494017/1000000000000000000),1,(484622236187974917923554213953548847/487758604941726469015625000000000000),false,MergedCutProfiles.Batch402.profile16087,(fun _ => MergedCutProfiles.Batch402.profile16087)⟩
theorem profilesValid3415 : retention3415.ProfilesValid := by
  exact MergedCutProfiles.Batch402.valid16087
theorem numericValid3415 : retention3415.NumericValid := by decide +kernel
def certificate3415 : RatCutBinCertificate := ⟨⟨retention3415,(1137474946651122287/500000000000000000),(182428996879551849/1000000000000000000),(7861754971596926307/500000000000000000),(98469645076024067049/100000000000000000),(241793752325081313/250000000000000000)⟩,(998102123379863483/1000000000000000000),(124968393140296971/1000000000000000000),(613298948759117263/1000000000000000000),(574228352306006459/1000000000000000000)⟩
theorem valid3415 : certificate3415.Valid := by decide +kernel
theorem sound3415 : certificate3415.Sound := rat_cut_bin_certificate_sound certificate3415 profilesValid3415 numericValid3415 valid3415

def retention3416 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(222400524512449251/15304809283902145730),(110099269560618441/125000000000000000),3,(8946849487276157403/4000000000000000000),true,MergedCutProfiles.Batch524.profile20975,![MergedCutProfiles.Batch524.profile20975,MergedCutProfiles.Batch524.profile20976,MergedCutProfiles.Batch524.profile20977,MergedCutProfiles.Batch524.profile20978,MergedCutProfiles.Batch225.profile9033,MergedCutProfiles.Batch403.profile16133,MergedCutProfiles.Batch226.profile9048,MergedCutProfiles.Batch524.profile20979,MergedCutProfiles.Batch524.profile20980,MergedCutProfiles.Batch524.profile20981,MergedCutProfiles.Batch524.profile20982,MergedCutProfiles.Batch524.profile20983,MergedCutProfiles.Batch402.profile16095,MergedCutProfiles.Batch524.profile20984,MergedCutProfiles.Batch524.profile20985,MergedCutProfiles.Batch524.profile20986]⟩
theorem profilesValid3416 : retention3416.ProfilesValid := by
  change ∀ j : Fin 16, (retention3416.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch524.valid20975
  · exact MergedCutProfiles.Batch524.valid20976
  · exact MergedCutProfiles.Batch524.valid20977
  · exact MergedCutProfiles.Batch524.valid20978
  · exact MergedCutProfiles.Batch225.valid9033
  · exact MergedCutProfiles.Batch403.valid16133
  · exact MergedCutProfiles.Batch226.valid9048
  · exact MergedCutProfiles.Batch524.valid20979
  · exact MergedCutProfiles.Batch524.valid20980
  · exact MergedCutProfiles.Batch524.valid20981
  · exact MergedCutProfiles.Batch524.valid20982
  · exact MergedCutProfiles.Batch524.valid20983
  · exact MergedCutProfiles.Batch402.valid16095
  · exact MergedCutProfiles.Batch524.valid20984
  · exact MergedCutProfiles.Batch524.valid20985
  · exact MergedCutProfiles.Batch524.valid20986
theorem numericValid3416 : retention3416.NumericValid := by decide +kernel
def certificate3416 : RatCutBinCertificate := ⟨⟨retention3416,(1105383553373305141/500000000000000000),(93024059904071007/500000000000000000),(15867731911002727811/1000000000000000000),(19487824611421009993/20000000000000000),(2158943453061210957/1000000000000000000)⟩,(124768032825785277/125000000000000000),(166635277770620287/500000000000000000),(37565281539379741/125000000000000000),(169600280696547591/1000000000000000000)⟩
theorem valid3416 : certificate3416.Valid := by decide +kernel
theorem sound3416 : certificate3416.Sound := rat_cut_bin_certificate_sound certificate3416 profilesValid3416 numericValid3416 valid3416

def retention3417 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(1064095303947825621/61219237135608582920),(222400524512449251/250000000000000000),(59/20),(22168972794147104097/10000000000000000000),true,MergedCutProfiles.Batch524.profile20987,![MergedCutProfiles.Batch524.profile20987,MergedCutProfiles.Batch524.profile20988,MergedCutProfiles.Batch524.profile20989,MergedCutProfiles.Batch524.profile20990,MergedCutProfiles.Batch524.profile20991,MergedCutProfiles.Batch524.profile20992,MergedCutProfiles.Batch524.profile20993,MergedCutProfiles.Batch524.profile20994,MergedCutProfiles.Batch524.profile20995,MergedCutProfiles.Batch524.profile20983,MergedCutProfiles.Batch524.profile20996,MergedCutProfiles.Batch524.profile20997,MergedCutProfiles.Batch402.profile16096,MergedCutProfiles.Batch524.profile20998,MergedCutProfiles.Batch524.profile20999,MergedCutProfiles.Batch525.profile21000]⟩
theorem profilesValid3417 : retention3417.ProfilesValid := by
  change ∀ j : Fin 16, (retention3417.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch524.valid20987
  · exact MergedCutProfiles.Batch524.valid20988
  · exact MergedCutProfiles.Batch524.valid20989
  · exact MergedCutProfiles.Batch524.valid20990
  · exact MergedCutProfiles.Batch524.valid20991
  · exact MergedCutProfiles.Batch524.valid20992
  · exact MergedCutProfiles.Batch524.valid20993
  · exact MergedCutProfiles.Batch524.valid20994
  · exact MergedCutProfiles.Batch524.valid20995
  · exact MergedCutProfiles.Batch524.valid20983
  · exact MergedCutProfiles.Batch524.valid20996
  · exact MergedCutProfiles.Batch524.valid20997
  · exact MergedCutProfiles.Batch402.valid16096
  · exact MergedCutProfiles.Batch524.valid20998
  · exact MergedCutProfiles.Batch524.valid20999
  · exact MergedCutProfiles.Batch525.valid21000
theorem numericValid3417 : retention3417.NumericValid := by decide +kernel
def certificate3417 : RatCutBinCertificate := ⟨⟨retention3417,(1105383553373305141/500000000000000000),(93024059904071007/500000000000000000),(15867731911002727811/1000000000000000000),(19487824611421009993/20000000000000000),(267553058910683577/125000000000000000)⟩,(124768032825785277/125000000000000000),(167296132742993311/500000000000000000),(149536454572857047/500000000000000000),(3392399790101361/20000000000000000)⟩
theorem valid3417 : certificate3417.Valid := by decide +kernel
theorem sound3417 : certificate3417.Sound := rat_cut_bin_certificate_sound certificate3417 profilesValid3417 numericValid3417 valid3417

def retention3418 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(1171600000000/65240672168047),(1064095303947825621/1000000000000000000),(13/5),(177372107528800724277/80000000000000000000),true,MergedCutProfiles.Batch525.profile21001,![MergedCutProfiles.Batch525.profile21001,MergedCutProfiles.Batch525.profile21002,MergedCutProfiles.Batch525.profile21003,MergedCutProfiles.Batch525.profile21004,MergedCutProfiles.Batch403.profile16122,MergedCutProfiles.Batch525.profile21005,MergedCutProfiles.Batch525.profile21006,MergedCutProfiles.Batch525.profile21007,MergedCutProfiles.Batch402.profile16110,MergedCutProfiles.Batch525.profile21008,MergedCutProfiles.Batch525.profile21009,MergedCutProfiles.Batch525.profile21010,MergedCutProfiles.Batch525.profile21011,MergedCutProfiles.Batch525.profile21012,MergedCutProfiles.Batch525.profile21013,MergedCutProfiles.Batch525.profile21014]⟩
theorem profilesValid3418 : retention3418.ProfilesValid := by
  change ∀ j : Fin 16, (retention3418.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch525.valid21001
  · exact MergedCutProfiles.Batch525.valid21002
  · exact MergedCutProfiles.Batch525.valid21003
  · exact MergedCutProfiles.Batch525.valid21004
  · exact MergedCutProfiles.Batch403.valid16122
  · exact MergedCutProfiles.Batch525.valid21005
  · exact MergedCutProfiles.Batch525.valid21006
  · exact MergedCutProfiles.Batch525.valid21007
  · exact MergedCutProfiles.Batch402.valid16110
  · exact MergedCutProfiles.Batch525.valid21008
  · exact MergedCutProfiles.Batch525.valid21009
  · exact MergedCutProfiles.Batch525.valid21010
  · exact MergedCutProfiles.Batch525.valid21011
  · exact MergedCutProfiles.Batch525.valid21012
  · exact MergedCutProfiles.Batch525.valid21013
  · exact MergedCutProfiles.Batch525.valid21014
theorem numericValid3418 : retention3418.NumericValid := by decide +kernel
def certificate3418 : RatCutBinCertificate := ⟨⟨retention3418,(1105383553373305141/500000000000000000),(93024059904071007/500000000000000000),(15867731911002727811/1000000000000000000),(19487824611421009993/20000000000000000),(134359489578455969/62500000000000000)⟩,(124768032825785277/125000000000000000),(76910407698551331/250000000000000000),(164842806467201709/500000000000000000),(209411328545926673/1000000000000000000)⟩
theorem valid3418 : certificate3418.Valid := by decide +kernel
theorem sound3418 : certificate3418.Sound := rat_cut_bin_certificate_sound certificate3418 profilesValid3418 numericValid3418 valid3418

def retention3419 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(1285543060824298273/61219237135608582920),(68711411/62500000),(51/20),(3528989860276176453/1600000000000000000),true,MergedCutProfiles.Batch525.profile21015,![MergedCutProfiles.Batch525.profile21015,MergedCutProfiles.Batch525.profile21016,MergedCutProfiles.Batch525.profile21017,MergedCutProfiles.Batch525.profile21018,MergedCutProfiles.Batch524.profile20992,MergedCutProfiles.Batch525.profile21006,MergedCutProfiles.Batch225.profile9034,MergedCutProfiles.Batch525.profile21019,MergedCutProfiles.Batch402.profile16095,MergedCutProfiles.Batch525.profile21020,MergedCutProfiles.Batch524.profile20986,MergedCutProfiles.Batch525.profile21021,MergedCutProfiles.Batch225.profile9020,MergedCutProfiles.Batch225.profile9036,MergedCutProfiles.Batch403.profile16126,MergedCutProfiles.Batch525.profile21022]⟩
theorem profilesValid3419 : retention3419.ProfilesValid := by
  change ∀ j : Fin 16, (retention3419.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch525.valid21015
  · exact MergedCutProfiles.Batch525.valid21016
  · exact MergedCutProfiles.Batch525.valid21017
  · exact MergedCutProfiles.Batch525.valid21018
  · exact MergedCutProfiles.Batch524.valid20992
  · exact MergedCutProfiles.Batch525.valid21006
  · exact MergedCutProfiles.Batch225.valid9034
  · exact MergedCutProfiles.Batch525.valid21019
  · exact MergedCutProfiles.Batch402.valid16095
  · exact MergedCutProfiles.Batch525.valid21020
  · exact MergedCutProfiles.Batch524.valid20986
  · exact MergedCutProfiles.Batch525.valid21021
  · exact MergedCutProfiles.Batch225.valid9020
  · exact MergedCutProfiles.Batch225.valid9036
  · exact MergedCutProfiles.Batch403.valid16126
  · exact MergedCutProfiles.Batch525.valid21022
theorem numericValid3419 : retention3419.NumericValid := by decide +kernel
def certificate3419 : RatCutBinCertificate := ⟨⟨retention3419,(1105383553373305141/500000000000000000),(93024059904071007/500000000000000000),(15867731911002727811/1000000000000000000),(19487824611421009993/20000000000000000),(2139515356102443783/1000000000000000000)⟩,(124768032825785277/125000000000000000),(304920961439168057/1000000000000000000),(83225858165372297/250000000000000000),(53626169738220759/250000000000000000)⟩
theorem valid3419 : certificate3419.Valid := by decide +kernel
theorem sound3419 : certificate3419.Sound := rat_cut_bin_certificate_sound certificate3419 profilesValid3419 numericValid3419 valid3419

def certificates : List RatCutBinCertificate := [certificate3408,certificate3409,certificate3410,certificate3411,certificate3412,certificate3413,certificate3414,certificate3415,certificate3416,certificate3417,certificate3418,certificate3419]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3408,List.forall_mem_cons.mpr ⟨sound3409,List.forall_mem_cons.mpr ⟨sound3410,List.forall_mem_cons.mpr ⟨sound3411,List.forall_mem_cons.mpr ⟨sound3412,List.forall_mem_cons.mpr ⟨sound3413,List.forall_mem_cons.mpr ⟨sound3414,List.forall_mem_cons.mpr ⟨sound3415,List.forall_mem_cons.mpr ⟨sound3416,List.forall_mem_cons.mpr ⟨sound3417,List.forall_mem_cons.mpr ⟨sound3418,List.forall_mem_cons.mpr ⟨sound3419,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch284
