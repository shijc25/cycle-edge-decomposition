import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch022
import Cycle12.MergedCutProfiles.Batch023
import Cycle12.MergedCutProfiles.Batch319
import Cycle12.MergedCutProfiles.Batch320
import Cycle12.MergedCutProfiles.Batch454
import Cycle12.MergedCutProfiles.Batch455
import Cycle12.MergedCutProfiles.Batch579
import Cycle12.MergedCutProfiles.Batch648
import Cycle12.MergedCutProfiles.Batch649

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch372

def retention4464 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(8093730670642882067/7764035718697559137017),(320494529/250000000),(49/20),(9348339776744662233/4000000000000000000),true,MergedCutProfiles.Batch579.profile23182,![MergedCutProfiles.Batch579.profile23182,MergedCutProfiles.Batch319.profile12772,MergedCutProfiles.Batch454.profile18191,MergedCutProfiles.Batch022.profile889,MergedCutProfiles.Batch455.profile18205,MergedCutProfiles.Batch319.profile12774,MergedCutProfiles.Batch319.profile12798,MergedCutProfiles.Batch022.profile890,MergedCutProfiles.Batch454.profile18197,MergedCutProfiles.Batch023.profile934,MergedCutProfiles.Batch455.profile18201,MergedCutProfiles.Batch022.profile891,MergedCutProfiles.Batch648.profile25953,MergedCutProfiles.Batch319.profile12777,MergedCutProfiles.Batch319.profile12788,MergedCutProfiles.Batch022.profile892]⟩
theorem profilesValid4464 : retention4464.ProfilesValid := by
  change ∀ j : Fin 16, (retention4464.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch579.valid23182
  · exact MergedCutProfiles.Batch319.valid12772
  · exact MergedCutProfiles.Batch454.valid18191
  · exact MergedCutProfiles.Batch022.valid889
  · exact MergedCutProfiles.Batch455.valid18205
  · exact MergedCutProfiles.Batch319.valid12774
  · exact MergedCutProfiles.Batch319.valid12798
  · exact MergedCutProfiles.Batch022.valid890
  · exact MergedCutProfiles.Batch454.valid18197
  · exact MergedCutProfiles.Batch023.valid934
  · exact MergedCutProfiles.Batch455.valid18201
  · exact MergedCutProfiles.Batch022.valid891
  · exact MergedCutProfiles.Batch648.valid25953
  · exact MergedCutProfiles.Batch319.valid12777
  · exact MergedCutProfiles.Batch319.valid12788
  · exact MergedCutProfiles.Batch022.valid892
theorem numericValid4464 : retention4464.NumericValid := by decide +kernel
def certificate4464 : RatCutBinCertificate := ⟨⟨retention4464,(469889899374411831/250000000000000000),(15120529320228081/1000000000000000000),(8325289973709849721/1000000000000000000),(6494436180428026453419/50000000000000000),(2328721410182169807/1000000000000000000)⟩,(249996431284106979/250000000000000000),(331622683635743401/1000000000000000000),(151168290521996471/500000000000000000),(110302594131514321/500000000000000000)⟩
theorem valid4464 : certificate4464.Valid := by decide +kernel
theorem sound4464 : certificate4464.Sound := rat_cut_bin_certificate_sound certificate4464 profilesValid4464 numericValid4464 valid4464

def retention4465 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(32000000000000000000/7764035718697559137017),(8093730670642882067/500000000000000000),1,(145821176924314136908657440936728877799/64749845365143056536000000000000000000),false,MergedCutProfiles.Batch648.profile25954,(fun _ => MergedCutProfiles.Batch648.profile25954)⟩
theorem profilesValid4465 : retention4465.ProfilesValid := by
  exact MergedCutProfiles.Batch648.valid25954
theorem numericValid4465 : retention4465.NumericValid := by decide +kernel
def certificate4465 : RatCutBinCertificate := ⟨⟨retention4465,(469889899374411831/250000000000000000),(15120529320228081/1000000000000000000),(8325289973709849721/1000000000000000000),(6494436180428026453419/50000000000000000),(562164049898076747/250000000000000000)⟩,(249996431284106979/250000000000000000),(190655717948403197/1000000000000000000),(123249932588853613/250000000000000000),(121669758937948689/125000000000000000)⟩
theorem valid4465 : certificate4465.Valid := by decide +kernel
theorem sound4465 : certificate4465.Sound := rat_cut_bin_certificate_sound certificate4465 profilesValid4465 numericValid4465 valid4465

def retention4466 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(1/2),64,1,(255370911039032911357452645744173379951/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch023.profile947,(fun _ => MergedCutProfiles.Batch023.profile947)⟩
theorem profilesValid4466 : retention4466.ProfilesValid := by
  exact MergedCutProfiles.Batch023.valid947
theorem numericValid4466 : retention4466.NumericValid := by decide +kernel
def certificate4466 : RatCutBinCertificate := ⟨⟨retention4466,(469889899374411831/250000000000000000),(15120529320228081/1000000000000000000),(8325289973709849721/1000000000000000000),(6494436180428026453419/50000000000000000),(198825786803593453/200000000000000000)⟩,(249996431284106979/250000000000000000),(409047227758933509/1000000000000000000),(225294348818604283/1000000000000000000),(220542659254593947/1000000000000000000)⟩
theorem valid4466 : certificate4466.Valid := by decide +kernel
theorem sound4466 : certificate4466.Sound := rat_cut_bin_certificate_sound certificate4466 profilesValid4466 numericValid4466 valid4466

def retention4467 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(32000000000000000000/7764035718697559137017),(8801683970370830627/500000000000000000),1,(159053523103051472059680006107944148839/70413471762966645016000000000000000000),false,MergedCutProfiles.Batch648.profile25954,(fun _ => MergedCutProfiles.Batch648.profile25954)⟩
theorem profilesValid4467 : retention4467.ProfilesValid := by
  exact MergedCutProfiles.Batch648.valid25954
theorem numericValid4467 : retention4467.NumericValid := by decide +kernel
def certificate4467 : RatCutBinCertificate := ⟨⟨retention4467,(448247833624411831/250000000000000000),(15120529320228081/1000000000000000000),(8325289973709849721/1000000000000000000),(6494436180428026453419/50000000000000000),(2255594283803094893/1000000000000000000)⟩,(124998297825559157/125000000000000000),(13807606874826793/500000000000000000),(170247671223601327/200000000000000000),(340388827801292777/200000000000000000)⟩
theorem valid4467 : certificate4467.Valid := by decide +kernel
theorem sound4467 : certificate4467.Sound := rat_cut_bin_certificate_sound certificate4467 profilesValid4467 numericValid4467 valid4467

def retention4468 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(1/2),64,1,(255370911039032911357452645744173379951/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch023.profile947,(fun _ => MergedCutProfiles.Batch023.profile947)⟩
theorem profilesValid4468 : retention4468.ProfilesValid := by
  exact MergedCutProfiles.Batch023.valid947
theorem numericValid4468 : retention4468.NumericValid := by decide +kernel
def certificate4468 : RatCutBinCertificate := ⟨⟨retention4468,(448247833624411831/250000000000000000),(15120529320228081/1000000000000000000),(8325289973709849721/1000000000000000000),(6494436180428026453419/50000000000000000),(198857232145807529/200000000000000000)⟩,(124998297825559157/125000000000000000),(31323335645166517/500000000000000000),(755279711575798997/1000000000000000000),(369732857496112431/500000000000000000)⟩
theorem valid4468 : certificate4468.Valid := by decide +kernel
theorem sound4468 : certificate4468.Sound := rat_cut_bin_certificate_sound certificate4468 profilesValid4468 numericValid4468 valid4468

def retention4469 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(341972251279604189/7764035718697559137017),(677172774811097403/1000000000000000000),4,(10038010095332471728311190468739399/4232329842569358768750000000000000),false,MergedCutProfiles.Batch648.profile25955,(fun _ => MergedCutProfiles.Batch648.profile25955)⟩
theorem profilesValid4469 : retention4469.ProfilesValid := by
  exact MergedCutProfiles.Batch648.valid25955
theorem numericValid4469 : retention4469.NumericValid := by decide +kernel
def certificate4469 : RatCutBinCertificate := ⟨⟨retention4469,(442917845624411831/250000000000000000),(15120529320228081/1000000000000000000),(8325289973709849721/1000000000000000000),(6494436180428026453419/50000000000000000),(2358874741692519819/1000000000000000000)⟩,(999986544525095491/1000000000000000000),(789424168964603931/1000000000000000000),(239153026663597/10000000000000000),(11581605513515459/1000000000000000000)⟩
theorem valid4469 : certificate4469.Valid := by decide +kernel
theorem sound4469 : certificate4469.Sound := rat_cut_bin_certificate_sound certificate4469 profilesValid4469 numericValid4469 valid4469

def retention4470 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(845738072589402625/7764035718697559137017),(341972251279604189/500000000000000000),4,(324683792488635196580949911655666443/136788900511841675600000000000000000),false,MergedCutProfiles.Batch648.profile25956,(fun _ => MergedCutProfiles.Batch648.profile25956)⟩
theorem profilesValid4470 : retention4470.ProfilesValid := by
  exact MergedCutProfiles.Batch648.valid25956
theorem numericValid4470 : retention4470.NumericValid := by decide +kernel
def certificate4470 : RatCutBinCertificate := ⟨⟨retention4470,(442917845624411831/250000000000000000),(15120529320228081/1000000000000000000),(8325289973709849721/1000000000000000000),(6494436180428026453419/50000000000000000),(1180370583289972663/500000000000000000)⟩,(999986544525095491/1000000000000000000),(393197613559956869/500000000000000000),(12318659413561467/500000000000000000),(11960197821394099/1000000000000000000)⟩
theorem valid4470 : certificate4470.Valid := by decide +kernel
theorem sound4470 : certificate4470.Sound := rat_cut_bin_certificate_sound certificate4470 profilesValid4470 numericValid4470 valid4470

def retention4471 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(32000000000000000000/7764035718697559137017),(6765904580715221/4000000000000000),(9/4),(63033532352906173258029515935097467959/27063618322860884000000000000000000000),false,MergedCutProfiles.Batch648.profile25954,(fun _ => MergedCutProfiles.Batch648.profile25954)⟩
theorem profilesValid4471 : retention4471.ProfilesValid := by
  exact MergedCutProfiles.Batch648.valid25954
theorem numericValid4471 : retention4471.NumericValid := by decide +kernel
def certificate4471 : RatCutBinCertificate := ⟨⟨retention4471,(442917845624411831/250000000000000000),(15120529320228081/1000000000000000000),(8325289973709849721/1000000000000000000),(6494436180428026453419/50000000000000000),(148598238997509/64000000000000)⟩,(999986544525095491/1000000000000000000),(653925396264478201/1000000000000000000),(17077984974441547/250000000000000000),(55455662720135041/1000000000000000000)⟩
theorem valid4471 : certificate4471.Valid := by decide +kernel
theorem sound4471 : certificate4471.Sound := rat_cut_bin_certificate_sound certificate4471 profilesValid4471 numericValid4471 valid4471

def retention4472 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(1/40),64,1,(34575885041178835378600304786729183799/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch648.profile25957,(fun _ => MergedCutProfiles.Batch648.profile25957)⟩
theorem profilesValid4472 : retention4472.ProfilesValid := by
  exact MergedCutProfiles.Batch648.valid25957
theorem numericValid4472 : retention4472.NumericValid := by decide +kernel
def certificate4472 : RatCutBinCertificate := ⟨⟨retention4472,(442917845624411831/250000000000000000),(15120529320228081/1000000000000000000),(8325289973709849721/1000000000000000000),(6494436180428026453419/50000000000000000),(2157775076205939739/1000000000000000000)⟩,(999986544525095491/1000000000000000000),(600075457194386971/1000000000000000000),(93466084037914901/1000000000000000000),(24387283141470611/125000000000000000)⟩
theorem valid4472 : certificate4472.Valid := by decide +kernel
theorem sound4472 : certificate4472.Sound := rat_cut_bin_certificate_sound certificate4472 profilesValid4472 numericValid4472 valid4472

def retention4473 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(709941012641398688/13947560834922328059369),(617622391581774283/1000000000000000000),4,(70936430868189624445668162419839377/30881119579088714150000000000000000),true,MergedCutProfiles.Batch648.profile25958,![MergedCutProfiles.Batch648.profile25958,MergedCutProfiles.Batch648.profile25959,MergedCutProfiles.Batch649.profile25960,MergedCutProfiles.Batch649.profile25961,MergedCutProfiles.Batch649.profile25962,MergedCutProfiles.Batch649.profile25962,MergedCutProfiles.Batch649.profile25963,MergedCutProfiles.Batch649.profile25964,MergedCutProfiles.Batch649.profile25964,MergedCutProfiles.Batch649.profile25965,MergedCutProfiles.Batch649.profile25966,MergedCutProfiles.Batch649.profile25966,MergedCutProfiles.Batch649.profile25967,MergedCutProfiles.Batch649.profile25967,MergedCutProfiles.Batch649.profile25968,MergedCutProfiles.Batch649.profile25968]⟩
theorem profilesValid4473 : retention4473.ProfilesValid := by
  change ∀ j : Fin 16, (retention4473.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch648.valid25958
  · exact MergedCutProfiles.Batch648.valid25959
  · exact MergedCutProfiles.Batch649.valid25960
  · exact MergedCutProfiles.Batch649.valid25961
  · exact MergedCutProfiles.Batch649.valid25962
  · exact MergedCutProfiles.Batch649.valid25962
  · exact MergedCutProfiles.Batch649.valid25963
  · exact MergedCutProfiles.Batch649.valid25964
  · exact MergedCutProfiles.Batch649.valid25964
  · exact MergedCutProfiles.Batch649.valid25965
  · exact MergedCutProfiles.Batch649.valid25966
  · exact MergedCutProfiles.Batch649.valid25966
  · exact MergedCutProfiles.Batch649.valid25967
  · exact MergedCutProfiles.Batch649.valid25967
  · exact MergedCutProfiles.Batch649.valid25968
  · exact MergedCutProfiles.Batch649.valid25968
theorem numericValid4473 : retention4473.NumericValid := by decide +kernel
def certificate4473 : RatCutBinCertificate := ⟨⟨retention4473,(376519520824818943/200000000000000000),(16814618099358171/1000000000000000000),(4217252556058038791/500000000000000000),(118201867122811528571737/1000000000000000000),(2282068709553168169/1000000000000000000)⟩,(999984313850334839/1000000000000000000),(512612816553704571/1000000000000000000),(144841601420099693/1000000000000000000),(67130463009836823/1000000000000000000)⟩
theorem valid4473 : certificate4473.Valid := by decide +kernel
theorem sound4473 : certificate4473.Sound := rat_cut_bin_certificate_sound certificate4473 profilesValid4473 numericValid4473 valid4473

def retention4474 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(38291647000000000/422653358634009941193),(22185656645043709/31250000000000000),4,(38342686468256120489/16000000000000000000),true,MergedCutProfiles.Batch649.profile25969,![MergedCutProfiles.Batch649.profile25969,MergedCutProfiles.Batch649.profile25960,MergedCutProfiles.Batch649.profile25962,MergedCutProfiles.Batch649.profile25963,MergedCutProfiles.Batch649.profile25964,MergedCutProfiles.Batch649.profile25965,MergedCutProfiles.Batch649.profile25966,MergedCutProfiles.Batch649.profile25967,MergedCutProfiles.Batch649.profile25968,MergedCutProfiles.Batch455.profile18212,MergedCutProfiles.Batch649.profile25970,MergedCutProfiles.Batch649.profile25970,MergedCutProfiles.Batch649.profile25971,MergedCutProfiles.Batch649.profile25972,MergedCutProfiles.Batch649.profile25972,MergedCutProfiles.Batch649.profile25973]⟩
theorem profilesValid4474 : retention4474.ProfilesValid := by
  change ∀ j : Fin 16, (retention4474.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch649.valid25969
  · exact MergedCutProfiles.Batch649.valid25960
  · exact MergedCutProfiles.Batch649.valid25962
  · exact MergedCutProfiles.Batch649.valid25963
  · exact MergedCutProfiles.Batch649.valid25964
  · exact MergedCutProfiles.Batch649.valid25965
  · exact MergedCutProfiles.Batch649.valid25966
  · exact MergedCutProfiles.Batch649.valid25967
  · exact MergedCutProfiles.Batch649.valid25968
  · exact MergedCutProfiles.Batch455.valid18212
  · exact MergedCutProfiles.Batch649.valid25970
  · exact MergedCutProfiles.Batch649.valid25970
  · exact MergedCutProfiles.Batch649.valid25971
  · exact MergedCutProfiles.Batch649.valid25972
  · exact MergedCutProfiles.Batch649.valid25972
  · exact MergedCutProfiles.Batch649.valid25973
theorem numericValid4474 : retention4474.NumericValid := by decide +kernel
def certificate4474 : RatCutBinCertificate := ⟨⟨retention4474,(376519520824818943/200000000000000000),(16814618099358171/1000000000000000000),(4217252556058038791/500000000000000000),(118201867122811528571737/1000000000000000000),(238140568438443783/100000000000000000)⟩,(999984313850334839/1000000000000000000),(449134370872645601/1000000000000000000),(47840823594248459/250000000000000000),(94181380064940517/1000000000000000000)⟩
theorem valid4474 : certificate4474.Valid := by decide +kernel
theorem sound4474 : certificate4474.Sound := rat_cut_bin_certificate_sound certificate4474 profilesValid4474 numericValid4474 valid4474

def retention4475 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(423222965022401902/1267960075902029823579),(1263624351/1000000000),(5/2),(37785376573458093149/16000000000000000000),true,MergedCutProfiles.Batch649.profile25963,![MergedCutProfiles.Batch649.profile25963,MergedCutProfiles.Batch649.profile25967,MergedCutProfiles.Batch649.profile25970,MergedCutProfiles.Batch649.profile25972,MergedCutProfiles.Batch649.profile25974,MergedCutProfiles.Batch649.profile25975,MergedCutProfiles.Batch320.profile12806,MergedCutProfiles.Batch455.profile18214,MergedCutProfiles.Batch649.profile25976,MergedCutProfiles.Batch649.profile25977,MergedCutProfiles.Batch649.profile25978,MergedCutProfiles.Batch649.profile25979,MergedCutProfiles.Batch320.profile12817,MergedCutProfiles.Batch320.profile12807,MergedCutProfiles.Batch649.profile25980,MergedCutProfiles.Batch455.profile18216]⟩
theorem profilesValid4475 : retention4475.ProfilesValid := by
  change ∀ j : Fin 16, (retention4475.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch649.valid25963
  · exact MergedCutProfiles.Batch649.valid25967
  · exact MergedCutProfiles.Batch649.valid25970
  · exact MergedCutProfiles.Batch649.valid25972
  · exact MergedCutProfiles.Batch649.valid25974
  · exact MergedCutProfiles.Batch649.valid25975
  · exact MergedCutProfiles.Batch320.valid12806
  · exact MergedCutProfiles.Batch455.valid18214
  · exact MergedCutProfiles.Batch649.valid25976
  · exact MergedCutProfiles.Batch649.valid25977
  · exact MergedCutProfiles.Batch649.valid25978
  · exact MergedCutProfiles.Batch649.valid25979
  · exact MergedCutProfiles.Batch320.valid12817
  · exact MergedCutProfiles.Batch320.valid12807
  · exact MergedCutProfiles.Batch649.valid25980
  · exact MergedCutProfiles.Batch455.valid18216
theorem numericValid4475 : retention4475.NumericValid := by decide +kernel
def certificate4475 : RatCutBinCertificate := ⟨⟨retention4475,(376519520824818943/200000000000000000),(16814618099358171/1000000000000000000),(4217252556058038791/500000000000000000),(118201867122811528571737/1000000000000000000),(470440679692531009/200000000000000000)⟩,(999984313850334839/1000000000000000000),(10305590686215389/31250000000000000),(152188147240935713/500000000000000000),(882629044762041/4000000000000000)⟩
theorem valid4475 : certificate4475.Valid := by decide +kernel
theorem sound4475 : certificate4475.Sound := rat_cut_bin_certificate_sound certificate4475 profilesValid4475 numericValid4475 valid4475

def certificates : List RatCutBinCertificate := [certificate4464,certificate4465,certificate4466,certificate4467,certificate4468,certificate4469,certificate4470,certificate4471,certificate4472,certificate4473,certificate4474,certificate4475]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4464,List.forall_mem_cons.mpr ⟨sound4465,List.forall_mem_cons.mpr ⟨sound4466,List.forall_mem_cons.mpr ⟨sound4467,List.forall_mem_cons.mpr ⟨sound4468,List.forall_mem_cons.mpr ⟨sound4469,List.forall_mem_cons.mpr ⟨sound4470,List.forall_mem_cons.mpr ⟨sound4471,List.forall_mem_cons.mpr ⟨sound4472,List.forall_mem_cons.mpr ⟨sound4473,List.forall_mem_cons.mpr ⟨sound4474,List.forall_mem_cons.mpr ⟨sound4475,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch372
