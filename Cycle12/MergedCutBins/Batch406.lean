import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch106
import Cycle12.MergedCutProfiles.Batch107
import Cycle12.MergedCutProfiles.Batch684
import Cycle12.MergedCutProfiles.Batch685

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch406

def retention4872 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(1/40),(1325185800414161113/250000000000000000),(27/20),(291577908838043080202894785526026443851/132518580041416111300000000000000000000),false,MergedCutProfiles.Batch684.profile27382,(fun _ => MergedCutProfiles.Batch684.profile27382)⟩
theorem profilesValid4872 : retention4872.ProfilesValid := by
  exact MergedCutProfiles.Batch684.valid27382
theorem numericValid4872 : retention4872.NumericValid := by decide +kernel
def certificate4872 : RatCutBinCertificate := ⟨⟨retention4872,(931736723831560059/500000000000000000),(5622540848385301/62500000000000000),(2973523243523444443/250000000000000000),(3809134603006935974091/125000000000000000),(2181252097868158577/1000000000000000000)⟩,(999944077091803931/1000000000000000000),(357786604927534387/500000000000000000),(44944926980401827/1000000000000000000),(29619738728121423/500000000000000000)⟩
theorem valid4872 : certificate4872.Valid := by decide +kernel
theorem sound4872 : certificate4872.Sound := rat_cut_bin_certificate_sound certificate4872 profilesValid4872 numericValid4872 valid4872

def retention4873 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(625631743584976092/2484189479669223829747),(29468670153400417/50000000000000000),4,(144404771217626167009/64000000000000000000),true,MergedCutProfiles.Batch684.profile27383,![MergedCutProfiles.Batch684.profile27383,MergedCutProfiles.Batch684.profile27384,MergedCutProfiles.Batch684.profile27385,MergedCutProfiles.Batch684.profile27386,MergedCutProfiles.Batch684.profile27387,MergedCutProfiles.Batch684.profile27388,MergedCutProfiles.Batch684.profile27389,MergedCutProfiles.Batch684.profile27390,MergedCutProfiles.Batch684.profile27391,MergedCutProfiles.Batch684.profile27392,MergedCutProfiles.Batch684.profile27393,MergedCutProfiles.Batch684.profile27394,MergedCutProfiles.Batch684.profile27395,MergedCutProfiles.Batch684.profile27396,MergedCutProfiles.Batch684.profile27397,MergedCutProfiles.Batch684.profile27398]⟩
theorem profilesValid4873 : retention4873.ProfilesValid := by
  change ∀ j : Fin 16, (retention4873.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch684.valid27383
  · exact MergedCutProfiles.Batch684.valid27384
  · exact MergedCutProfiles.Batch684.valid27385
  · exact MergedCutProfiles.Batch684.valid27386
  · exact MergedCutProfiles.Batch684.valid27387
  · exact MergedCutProfiles.Batch684.valid27388
  · exact MergedCutProfiles.Batch684.valid27389
  · exact MergedCutProfiles.Batch684.valid27390
  · exact MergedCutProfiles.Batch684.valid27391
  · exact MergedCutProfiles.Batch684.valid27392
  · exact MergedCutProfiles.Batch684.valid27393
  · exact MergedCutProfiles.Batch684.valid27394
  · exact MergedCutProfiles.Batch684.valid27395
  · exact MergedCutProfiles.Batch684.valid27396
  · exact MergedCutProfiles.Batch684.valid27397
  · exact MergedCutProfiles.Batch684.valid27398
theorem numericValid4873 : retention4873.NumericValid := by decide +kernel
def certificate4873 : RatCutBinCertificate := ⟨⟨retention4873,(950607857891658239/500000000000000000),(23060041821265367/250000000000000000),(12083399313703635401/1000000000000000000),(30100436419524438813219/1000000000000000000),(1099135892896989181/500000000000000000)⟩,(499971259703401919/500000000000000000),(28118770080191783/40000000000000000),(49274770029363967/1000000000000000000),(878358691142523/40000000000000000)⟩
theorem valid4873 : certificate4873.Valid := by decide +kernel
theorem sound4873 : certificate4873.Sound := rat_cut_bin_certificate_sound certificate4873 profilesValid4873 numericValid4873 valid4873

def retention4874 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(1119366348000000000/2484189479669223829747),(156407935896244023/250000000000000000),4,(148347155842770807303/64000000000000000000),true,MergedCutProfiles.Batch684.profile27399,![MergedCutProfiles.Batch684.profile27399,MergedCutProfiles.Batch685.profile27400,MergedCutProfiles.Batch684.profile27387,MergedCutProfiles.Batch684.profile27389,MergedCutProfiles.Batch684.profile27391,MergedCutProfiles.Batch684.profile27393,MergedCutProfiles.Batch684.profile27394,MergedCutProfiles.Batch684.profile27396,MergedCutProfiles.Batch684.profile27398,MergedCutProfiles.Batch685.profile27401,MergedCutProfiles.Batch685.profile27402,MergedCutProfiles.Batch685.profile27403,MergedCutProfiles.Batch685.profile27404,MergedCutProfiles.Batch685.profile27405,MergedCutProfiles.Batch685.profile27406,MergedCutProfiles.Batch685.profile27407]⟩
theorem profilesValid4874 : retention4874.ProfilesValid := by
  change ∀ j : Fin 16, (retention4874.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch684.valid27399
  · exact MergedCutProfiles.Batch685.valid27400
  · exact MergedCutProfiles.Batch684.valid27387
  · exact MergedCutProfiles.Batch684.valid27389
  · exact MergedCutProfiles.Batch684.valid27391
  · exact MergedCutProfiles.Batch684.valid27393
  · exact MergedCutProfiles.Batch684.valid27394
  · exact MergedCutProfiles.Batch684.valid27396
  · exact MergedCutProfiles.Batch684.valid27398
  · exact MergedCutProfiles.Batch685.valid27401
  · exact MergedCutProfiles.Batch685.valid27402
  · exact MergedCutProfiles.Batch685.valid27403
  · exact MergedCutProfiles.Batch685.valid27404
  · exact MergedCutProfiles.Batch685.valid27405
  · exact MergedCutProfiles.Batch685.valid27406
  · exact MergedCutProfiles.Batch685.valid27407
theorem numericValid4874 : retention4874.NumericValid := by decide +kernel
def certificate4874 : RatCutBinCertificate := ⟨⟨retention4874,(950607857891658239/500000000000000000),(23060041821265367/250000000000000000),(12083399313703635401/1000000000000000000),(30100436419524438813219/1000000000000000000),(2259871549935153127/1000000000000000000)⟩,(499971259703401919/500000000000000000),(657373802101762759/1000000000000000000),(8357033073174637/125000000000000000),(3081276649981849/100000000000000000)⟩
theorem valid4874 : certificate4874.Valid := by decide +kernel
theorem sound4874 : certificate4874.Sound := rat_cut_bin_certificate_sound certificate4874 profilesValid4874 numericValid4874 valid4874

def retention4875 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(1428870269624845379/2484189479669223829747),(279841587/250000000),(57/20),(431420116920300082885793698735031759/179098615680000000000000000000000000),true,MergedCutProfiles.Batch685.profile27408,![MergedCutProfiles.Batch685.profile27408,MergedCutProfiles.Batch685.profile27409,MergedCutProfiles.Batch684.profile27389,MergedCutProfiles.Batch684.profile27391,MergedCutProfiles.Batch685.profile27410,MergedCutProfiles.Batch684.profile27396,MergedCutProfiles.Batch684.profile27398,MergedCutProfiles.Batch685.profile27401,MergedCutProfiles.Batch685.profile27402,MergedCutProfiles.Batch685.profile27411,MergedCutProfiles.Batch685.profile27405,MergedCutProfiles.Batch685.profile27406,MergedCutProfiles.Batch685.profile27412,MergedCutProfiles.Batch685.profile27413,MergedCutProfiles.Batch685.profile27414,MergedCutProfiles.Batch685.profile27415]⟩
theorem profilesValid4875 : retention4875.ProfilesValid := by
  change ∀ j : Fin 16, (retention4875.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch685.valid27408
  · exact MergedCutProfiles.Batch685.valid27409
  · exact MergedCutProfiles.Batch684.valid27389
  · exact MergedCutProfiles.Batch684.valid27391
  · exact MergedCutProfiles.Batch685.valid27410
  · exact MergedCutProfiles.Batch684.valid27396
  · exact MergedCutProfiles.Batch684.valid27398
  · exact MergedCutProfiles.Batch685.valid27401
  · exact MergedCutProfiles.Batch685.valid27402
  · exact MergedCutProfiles.Batch685.valid27411
  · exact MergedCutProfiles.Batch685.valid27405
  · exact MergedCutProfiles.Batch685.valid27406
  · exact MergedCutProfiles.Batch685.valid27412
  · exact MergedCutProfiles.Batch685.valid27413
  · exact MergedCutProfiles.Batch685.valid27414
  · exact MergedCutProfiles.Batch685.valid27415
theorem numericValid4875 : retention4875.NumericValid := by decide +kernel
def certificate4875 : RatCutBinCertificate := ⟨⟨retention4875,(950607857891658239/500000000000000000),(23060041821265367/250000000000000000),(12083399313703635401/1000000000000000000),(30100436419524438813219/1000000000000000000),(591869644515953487/250000000000000000)⟩,(499971259703401919/500000000000000000),(446584914602590347/1000000000000000000),(193411188458850461/1000000000000000000),(12746442830453447/100000000000000000)⟩
theorem valid4875 : certificate4875.Valid := by decide +kernel
theorem sound4875 : certificate4875.Sound := rat_cut_bin_certificate_sound certificate4875 profilesValid4875 numericValid4875 valid4875

def retention4876 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(64000000000000000000/2484189479669223829747),(1428870269624845379/1000000000000000000),(47/20),(2805051064950432313027/1280000000000000000000),true,MergedCutProfiles.Batch685.profile27416,![MergedCutProfiles.Batch685.profile27416,MergedCutProfiles.Batch685.profile27417,MergedCutProfiles.Batch685.profile27418,MergedCutProfiles.Batch685.profile27419,MergedCutProfiles.Batch685.profile27420,MergedCutProfiles.Batch685.profile27421,MergedCutProfiles.Batch106.profile4249,MergedCutProfiles.Batch685.profile27422,MergedCutProfiles.Batch685.profile27423,MergedCutProfiles.Batch685.profile27424,MergedCutProfiles.Batch106.profile4276,MergedCutProfiles.Batch685.profile27425,MergedCutProfiles.Batch685.profile27426,MergedCutProfiles.Batch685.profile27427,MergedCutProfiles.Batch685.profile27428,MergedCutProfiles.Batch685.profile27429]⟩
theorem profilesValid4876 : retention4876.ProfilesValid := by
  change ∀ j : Fin 16, (retention4876.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch685.valid27416
  · exact MergedCutProfiles.Batch685.valid27417
  · exact MergedCutProfiles.Batch685.valid27418
  · exact MergedCutProfiles.Batch685.valid27419
  · exact MergedCutProfiles.Batch685.valid27420
  · exact MergedCutProfiles.Batch685.valid27421
  · exact MergedCutProfiles.Batch106.valid4249
  · exact MergedCutProfiles.Batch685.valid27422
  · exact MergedCutProfiles.Batch685.valid27423
  · exact MergedCutProfiles.Batch685.valid27424
  · exact MergedCutProfiles.Batch106.valid4276
  · exact MergedCutProfiles.Batch685.valid27425
  · exact MergedCutProfiles.Batch685.valid27426
  · exact MergedCutProfiles.Batch685.valid27427
  · exact MergedCutProfiles.Batch685.valid27428
  · exact MergedCutProfiles.Batch685.valid27429
theorem numericValid4876 : retention4876.NumericValid := by decide +kernel
def certificate4876 : RatCutBinCertificate := ⟨⟨retention4876,(950607857891658239/500000000000000000),(23060041821265367/250000000000000000),(12083399313703635401/1000000000000000000),(30100436419524438813219/1000000000000000000),(67416879955222941/31250000000000000)⟩,(499971259703401919/500000000000000000),(2722460340797381/6250000000000000),(101203887113138553/500000000000000000),(9119400340151547/62500000000000000)⟩
theorem valid4876 : certificate4876.Valid := by decide +kernel
theorem sound4876 : certificate4876.Sound := rat_cut_bin_certificate_sound certificate4876 profilesValid4876 numericValid4876 valid4876

def retention4877 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(1/2),64,1,(3990436861649661312644417111789967351/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch107.profile4319,(fun _ => MergedCutProfiles.Batch107.profile4319)⟩
theorem profilesValid4877 : retention4877.ProfilesValid := by
  exact MergedCutProfiles.Batch107.valid4319
theorem numericValid4877 : retention4877.NumericValid := by decide +kernel
def certificate4877 : RatCutBinCertificate := ⟨⟨retention4877,(950607857891658239/500000000000000000),(23060041821265367/250000000000000000),(12083399313703635401/1000000000000000000),(30100436419524438813219/1000000000000000000),(122887005307780759/125000000000000000)⟩,(499971259703401919/500000000000000000),(533066330185629773/1000000000000000000),(131576607279623077/1000000000000000000),(127388141017015143/1000000000000000000)⟩
theorem valid4877 : certificate4877.Valid := by decide +kernel
theorem sound4877 : certificate4877.Sound := rat_cut_bin_certificate_sound certificate4877 profilesValid4877 numericValid4877 valid4877

def retention4878 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(64000000000000000000/2484189479669223829747),(33017748347725111/1000000000000000),1,(4470760504728293873102704132771874251/2063609271732819437500000000000000000),false,MergedCutProfiles.Batch685.profile27430,(fun _ => MergedCutProfiles.Batch685.profile27430)⟩
theorem profilesValid4878 : retention4878.ProfilesValid := by
  exact MergedCutProfiles.Batch685.valid27430
theorem numericValid4878 : retention4878.NumericValid := by decide +kernel
def certificate4878 : RatCutBinCertificate := ⟨⟨retention4878,(878605368891658239/500000000000000000),(23060041821265367/250000000000000000),(12083399313703635401/1000000000000000000),(30100436419524438813219/1000000000000000000),(134566398157529829/62500000000000000)⟩,(999946873218399981/1000000000000000000),(4924464351095751/250000000000000000),(109364975198245143/125000000000000000),(884171299304767499/500000000000000000)⟩
theorem valid4878 : certificate4878.Valid := by decide +kernel
theorem sound4878 : certificate4878.Sound := rat_cut_bin_certificate_sound certificate4878 profilesValid4878 numericValid4878 valid4878

def retention4879 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(1/2),64,1,(3990436861649661312644417111789967351/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch107.profile4319,(fun _ => MergedCutProfiles.Batch107.profile4319)⟩
theorem profilesValid4879 : retention4879.ProfilesValid := by
  exact MergedCutProfiles.Batch107.valid4319
theorem numericValid4879 : retention4879.NumericValid := by decide +kernel
def certificate4879 : RatCutBinCertificate := ⟨⟨retention4879,(878605368891658239/500000000000000000),(23060041821265367/250000000000000000),(12083399313703635401/1000000000000000000),(30100436419524438813219/1000000000000000000),(49209766142556521/50000000000000000)⟩,(999946873218399981/1000000000000000000),(2693235438926579/62500000000000000),(201789827695106039/250000000000000000),(782329073724044443/1000000000000000000)⟩
theorem valid4879 : certificate4879.Valid := by decide +kernel
theorem sound4879 : certificate4879.Sound := rat_cut_bin_certificate_sound certificate4879 profilesValid4879 numericValid4879 valid4879

def retention4880 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(698106465075470403/2484189479669223829747),(691194519876703369/1000000000000000000),4,(414324844077244558558607047337991117/172798629969175842250000000000000000),false,MergedCutProfiles.Batch685.profile27431,(fun _ => MergedCutProfiles.Batch685.profile27431)⟩
theorem profilesValid4880 : retention4880.ProfilesValid := by
  exact MergedCutProfiles.Batch685.valid27431
theorem numericValid4880 : retention4880.NumericValid := by decide +kernel
def certificate4880 : RatCutBinCertificate := ⟨⟨retention4880,(926794816391658239/500000000000000000),(23060041821265367/250000000000000000),(12083399313703635401/1000000000000000000),(30100436419524438813219/1000000000000000000),(2341133715588219981/1000000000000000000)⟩,(62496497457666677/62500000000000000),(871203689543804271/1000000000000000000),(867520542485223/100000000000000000),(419010059022607/100000000000000000)⟩
theorem valid4880 : certificate4880.Valid := by decide +kernel
theorem sound4880 : certificate4880.Sound := rat_cut_bin_certificate_sound certificate4880 profilesValid4880 numericValid4880 valid4880

def retention4881 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(868944188874090432/2484189479669223829747),(698106465075470403/1000000000000000000),4,(6705301557811458090645480959414824343/2792425860301881612000000000000000000),false,MergedCutProfiles.Batch685.profile27432,(fun _ => MergedCutProfiles.Batch685.profile27432)⟩
theorem profilesValid4881 : retention4881.ProfilesValid := by
  exact MergedCutProfiles.Batch685.valid27432
theorem numericValid4881 : retention4881.NumericValid := by decide +kernel
def certificate4881 : RatCutBinCertificate := ⟨⟨retention4881,(926794816391658239/500000000000000000),(23060041821265367/250000000000000000),(12083399313703635401/1000000000000000000),(30100436419524438813219/1000000000000000000),(2344647534664704073/1000000000000000000)⟩,(62496497457666677/62500000000000000),(433880137890105847/500000000000000000),(9156795490259123/1000000000000000000),(2217933592540637/500000000000000000)⟩
theorem valid4881 : certificate4881.Valid := by decide +kernel
theorem sound4881 : certificate4881.Sound := rat_cut_bin_certificate_sound certificate4881 profilesValid4881 numericValid4881 valid4881

def retention4882 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(4487645651528306441/2484189479669223829747),(13577252951157663/15625000000000000),(37/10),(13059632196447677202620028022438623791/5430901180463065200000000000000000000),false,MergedCutProfiles.Batch685.profile27433,(fun _ => MergedCutProfiles.Batch685.profile27433)⟩
theorem profilesValid4882 : retention4882.ProfilesValid := by
  exact MergedCutProfiles.Batch685.valid27433
theorem numericValid4882 : retention4882.NumericValid := by decide +kernel
def certificate4882 : RatCutBinCertificate := ⟨⟨retention4882,(926794816391658239/500000000000000000),(23060041821265367/250000000000000000),(12083399313703635401/1000000000000000000),(30100436419524438813219/1000000000000000000),(588084024016621709/250000000000000000)⟩,(62496497457666677/62500000000000000),(411515918068212123/500000000000000000),(4168539380161983/250000000000000000),(8850116616684889/1000000000000000000)⟩
theorem valid4882 : certificate4882.Valid := by decide +kernel
theorem sound4882 : certificate4882.Sound := rat_cut_bin_certificate_sound certificate4882 profilesValid4882 numericValid4882 valid4882

def retention4883 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(57317896732995664685/2484189479669223829747),(4487645651528306441/1000000000000000000),(29/20),(15912731258415793198066942207183801575039/7180233042445290305600000000000000000000),false,MergedCutProfiles.Batch685.profile27434,(fun _ => MergedCutProfiles.Batch685.profile27434)⟩
theorem profilesValid4883 : retention4883.ProfilesValid := by
  exact MergedCutProfiles.Batch685.valid27434
theorem numericValid4883 : retention4883.NumericValid := by decide +kernel
def certificate4883 : RatCutBinCertificate := ⟨⟨retention4883,(926794816391658239/500000000000000000),(23060041821265367/250000000000000000),(12083399313703635401/1000000000000000000),(30100436419524438813219/1000000000000000000),(439133791310994401/200000000000000000)⟩,(62496497457666677/62500000000000000),(733867882054733529/1000000000000000000),(19527060549838679/500000000000000000),(11992756957944031/250000000000000000)⟩
theorem valid4883 : certificate4883.Valid := by decide +kernel
theorem sound4883 : certificate4883.Sound := rat_cut_bin_certificate_sound certificate4883 profilesValid4883 numericValid4883 valid4883

def certificates : List RatCutBinCertificate := [certificate4872,certificate4873,certificate4874,certificate4875,certificate4876,certificate4877,certificate4878,certificate4879,certificate4880,certificate4881,certificate4882,certificate4883]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4872,List.forall_mem_cons.mpr ⟨sound4873,List.forall_mem_cons.mpr ⟨sound4874,List.forall_mem_cons.mpr ⟨sound4875,List.forall_mem_cons.mpr ⟨sound4876,List.forall_mem_cons.mpr ⟨sound4877,List.forall_mem_cons.mpr ⟨sound4878,List.forall_mem_cons.mpr ⟨sound4879,List.forall_mem_cons.mpr ⟨sound4880,List.forall_mem_cons.mpr ⟨sound4881,List.forall_mem_cons.mpr ⟨sound4882,List.forall_mem_cons.mpr ⟨sound4883,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch406
