import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch100
import Cycle12.MergedCutProfiles.Batch101

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch050

def retention600 : RatCutRetentionCertificate := ⟨(43/1000),(87/2000),(938052963961029383/26140889609024163467),(891406537/1000000000),(57/20),(16843975651620662269/8000000000000000000),true,MergedCutProfiles.Batch100.profile4024,![MergedCutProfiles.Batch100.profile4024,MergedCutProfiles.Batch100.profile4025,MergedCutProfiles.Batch100.profile4026,MergedCutProfiles.Batch100.profile4027,MergedCutProfiles.Batch100.profile4028,MergedCutProfiles.Batch100.profile4029,MergedCutProfiles.Batch100.profile4030,MergedCutProfiles.Batch100.profile4031,MergedCutProfiles.Batch100.profile4032,MergedCutProfiles.Batch100.profile4033,MergedCutProfiles.Batch100.profile4034,MergedCutProfiles.Batch100.profile4035,MergedCutProfiles.Batch100.profile4036,MergedCutProfiles.Batch100.profile4037,MergedCutProfiles.Batch100.profile4038,MergedCutProfiles.Batch100.profile4039]⟩
theorem profilesValid600 : retention600.ProfilesValid := by
  change ∀ j : Fin 16, (retention600.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch100.valid4024
  · exact MergedCutProfiles.Batch100.valid4025
  · exact MergedCutProfiles.Batch100.valid4026
  · exact MergedCutProfiles.Batch100.valid4027
  · exact MergedCutProfiles.Batch100.valid4028
  · exact MergedCutProfiles.Batch100.valid4029
  · exact MergedCutProfiles.Batch100.valid4030
  · exact MergedCutProfiles.Batch100.valid4031
  · exact MergedCutProfiles.Batch100.valid4032
  · exact MergedCutProfiles.Batch100.valid4033
  · exact MergedCutProfiles.Batch100.valid4034
  · exact MergedCutProfiles.Batch100.valid4035
  · exact MergedCutProfiles.Batch100.valid4036
  · exact MergedCutProfiles.Batch100.valid4037
  · exact MergedCutProfiles.Batch100.valid4038
  · exact MergedCutProfiles.Batch100.valid4039
theorem numericValid600 : retention600.NumericValid := by decide +kernel
def certificate600 : RatCutBinCertificate := ⟨⟨retention600,(2096038742167493743/1000000000000000000),(87716241548175929/1000000000000000000),(11892637746559233419/1000000000000000000),(311738188183217569999/1000000000000000000),(2061431924593757713/1000000000000000000)⟩,(496923799963887517/500000000000000000),(190077080475047837/500000000000000000),(25216650567386021/100000000000000000),(140948152077687303/1000000000000000000)⟩
theorem valid600 : certificate600.Valid := by decide +kernel
theorem sound600 : certificate600.Sound := rat_cut_bin_certificate_sound certificate600 profilesValid600 numericValid600 valid600

def retention601 : RatCutRetentionCertificate := ⟨(43/1000),(87/2000),(3962191943676459/74902262490040583),(938052963961029383/1000000000000000000),(11/4),(131086113101195464161/64000000000000000000),true,MergedCutProfiles.Batch101.profile4040,![MergedCutProfiles.Batch101.profile4040,MergedCutProfiles.Batch101.profile4041,MergedCutProfiles.Batch101.profile4042,MergedCutProfiles.Batch101.profile4043,MergedCutProfiles.Batch101.profile4044,MergedCutProfiles.Batch101.profile4045,MergedCutProfiles.Batch101.profile4046,MergedCutProfiles.Batch101.profile4047,MergedCutProfiles.Batch100.profile4021,MergedCutProfiles.Batch101.profile4048,MergedCutProfiles.Batch101.profile4049,MergedCutProfiles.Batch101.profile4050,MergedCutProfiles.Batch101.profile4051,MergedCutProfiles.Batch101.profile4052,MergedCutProfiles.Batch101.profile4053,MergedCutProfiles.Batch101.profile4054]⟩
theorem profilesValid601 : retention601.ProfilesValid := by
  change ∀ j : Fin 16, (retention601.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch101.valid4040
  · exact MergedCutProfiles.Batch101.valid4041
  · exact MergedCutProfiles.Batch101.valid4042
  · exact MergedCutProfiles.Batch101.valid4043
  · exact MergedCutProfiles.Batch101.valid4044
  · exact MergedCutProfiles.Batch101.valid4045
  · exact MergedCutProfiles.Batch101.valid4046
  · exact MergedCutProfiles.Batch101.valid4047
  · exact MergedCutProfiles.Batch100.valid4021
  · exact MergedCutProfiles.Batch101.valid4048
  · exact MergedCutProfiles.Batch101.valid4049
  · exact MergedCutProfiles.Batch101.valid4050
  · exact MergedCutProfiles.Batch101.valid4051
  · exact MergedCutProfiles.Batch101.valid4052
  · exact MergedCutProfiles.Batch101.valid4053
  · exact MergedCutProfiles.Batch101.valid4054
theorem numericValid601 : retention601.NumericValid := by decide +kernel
def certificate601 : RatCutBinCertificate := ⟨⟨retention601,(2096038742167493743/1000000000000000000),(87716241548175929/1000000000000000000),(11892637746559233419/1000000000000000000),(311738188183217569999/1000000000000000000),(501425424563585963/250000000000000000)⟩,(496923799963887517/500000000000000000),(191312059186348263/500000000000000000),(249785793802787579/1000000000000000000),(28200397956199161/200000000000000000)⟩
theorem valid601 : certificate601.Valid := by decide +kernel
theorem sound601 : certificate601.Sound := rat_cut_bin_certificate_sound certificate601 profilesValid601 numericValid601 valid601

def retention602 : RatCutRetentionCertificate := ⟨(43/1000),(87/2000),(4796590692364378677/26140889609024163467),(1382804988343084191/1000000000000000000),(41/20),(3708132595072477907276907971617111715999/2212487981348934705600000000000000000000),false,MergedCutProfiles.Batch101.profile4055,(fun _ => MergedCutProfiles.Batch101.profile4055)⟩
theorem profilesValid602 : retention602.ProfilesValid := by
  exact MergedCutProfiles.Batch101.valid4055
theorem numericValid602 : retention602.NumericValid := by decide +kernel
def certificate602 : RatCutBinCertificate := ⟨⟨retention602,(2096038742167493743/1000000000000000000),(87716241548175929/1000000000000000000),(11892637746559233419/1000000000000000000),(311738188183217569999/1000000000000000000),(822152850953712949/500000000000000000)⟩,(496923799963887517/500000000000000000),(203022606296283627/500000000000000000),(22798886897717371/100000000000000000),(35381208062848691/250000000000000000)⟩
theorem valid602 : certificate602.Valid := by decide +kernel
theorem sound602 : certificate602.Sound := rat_cut_bin_certificate_sound certificate602 profilesValid602 numericValid602 valid602

def retention603 : RatCutRetentionCertificate := ⟨(43/1000),(87/2000),(876897490392702401/2010837662232627959),(4796590692364378677/1000000000000000000),(11/10),(2126858322093030304924907898067481774111/1918636276945751470800000000000000000000),false,MergedCutProfiles.Batch101.profile4056,(fun _ => MergedCutProfiles.Batch101.profile4056)⟩
theorem profilesValid603 : retention603.ProfilesValid := by
  exact MergedCutProfiles.Batch101.valid4056
theorem numericValid603 : retention603.NumericValid := by decide +kernel
def certificate603 : RatCutBinCertificate := ⟨⟨retention603,(2096038742167493743/1000000000000000000),(87716241548175929/1000000000000000000),(11892637746559233419/1000000000000000000),(311738188183217569999/1000000000000000000),(1091519485353901857/1000000000000000000)⟩,(496923799963887517/500000000000000000),(1186191523156767/2500000000000000),(171780572817277659/1000000000000000000),(142511047635366301/1000000000000000000)⟩
theorem valid603 : certificate603.Valid := by decide +kernel
theorem sound603 : certificate603.Sound := rat_cut_bin_certificate_sound certificate603 profilesValid603 numericValid603 valid603

def retention604 : RatCutRetentionCertificate := ⟨(43/1000),(87/2000),(12845430533447271657/26140889609024163467),(11399667375105131213/1000000000000000000),(21/20),(2643068799009788627763462052691474960273/2605638257166887134400000000000000000000),false,MergedCutProfiles.Batch101.profile4057,(fun _ => MergedCutProfiles.Batch101.profile4057)⟩
theorem profilesValid604 : retention604.ProfilesValid := by
  exact MergedCutProfiles.Batch101.valid4057
theorem numericValid604 : retention604.NumericValid := by decide +kernel
def certificate604 : RatCutBinCertificate := ⟨⟨retention604,(2096038742167493743/1000000000000000000),(87716241548175929/1000000000000000000),(11892637746559233419/1000000000000000000),(311738188183217569999/1000000000000000000),(499066070641410623/500000000000000000)⟩,(496923799963887517/500000000000000000),(7557275105787759/15625000000000000),(41254556170422377/250000000000000000),(28878389751210667/200000000000000000)⟩
theorem valid604 : certificate604.Valid := by decide +kernel
theorem sound604 : certificate604.Sound := rat_cut_bin_certificate_sound certificate604 profilesValid604 numericValid604 valid604

def retention605 : RatCutRetentionCertificate := ⟨(43/1000),(87/2000),(12973884838781744374/26140889609024163467),(12845430533447271657/1000000000000000000),(21/20),(20682358564231800132205250181125522725511/20552688853515634651200000000000000000000),false,MergedCutProfiles.Batch101.profile4058,(fun _ => MergedCutProfiles.Batch101.profile4058)⟩
theorem profilesValid605 : retention605.ProfilesValid := by
  exact MergedCutProfiles.Batch101.valid4058
theorem numericValid605 : retention605.NumericValid := by decide +kernel
def certificate605 : RatCutBinCertificate := ⟨⟨retention605,(2096038742167493743/1000000000000000000),(87716241548175929/1000000000000000000),(11892637746559233419/1000000000000000000),(311738188183217569999/1000000000000000000),(495038054943859607/500000000000000000)⟩,(496923799963887517/500000000000000000),(484699426282376557/1000000000000000000),(16426840523843371/100000000000000000),(3596169499626777/25000000000000000)⟩
theorem valid605 : certificate605.Valid := by decide +kernel
theorem sound605 : certificate605.Sound := rat_cut_bin_certificate_sound certificate605 profilesValid605 numericValid605 valid605

def retention606 : RatCutRetentionCertificate := ⟨(43/1000),(87/2000),(1/2),(6486942419390872187/500000000000000000),(21/20),(5185011265515723342416114853002340141311/5189553935512697749600000000000000000000),false,MergedCutProfiles.Batch101.profile4059,(fun _ => MergedCutProfiles.Batch101.profile4059)⟩
theorem profilesValid606 : retention606.ProfilesValid := by
  exact MergedCutProfiles.Batch101.valid4059
theorem numericValid606 : retention606.NumericValid := by decide +kernel
def certificate606 : RatCutBinCertificate := ⟨⟨retention606,(2096038742167493743/1000000000000000000),(87716241548175929/1000000000000000000),(11892637746559233419/1000000000000000000),(311738188183217569999/1000000000000000000),(982891628328024747/1000000000000000000)⟩,(496923799963887517/500000000000000000),(488014171100527869/1000000000000000000),(161879097871370339/1000000000000000000),(352208630950991/2500000000000000)⟩
theorem valid606 : certificate606.Valid := by decide +kernel
theorem sound606 : certificate606.Sound := rat_cut_bin_certificate_sound certificate606 profilesValid606 numericValid606 valid606

def retention607 : RatCutRetentionCertificate := ⟨(43/1000),(87/2000),(11557116454988920958/26140889609024163467),(929293473136722631/250000000000000000),(6/5),(412194246358733386659971297839977187079/371717389254689052400000000000000000000),false,MergedCutProfiles.Batch101.profile4060,(fun _ => MergedCutProfiles.Batch101.profile4060)⟩
theorem profilesValid607 : retention607.ProfilesValid := by
  exact MergedCutProfiles.Batch101.valid4060
theorem numericValid607 : retention607.NumericValid := by decide +kernel
def certificate607 : RatCutBinCertificate := ⟨⟨retention607,(2477374260167493743/1000000000000000000),(87716241548175929/1000000000000000000),(11892637746559233419/1000000000000000000),(311738188183217569999/1000000000000000000),(13587041581401703/12500000000000000)⟩,(248181880850174043/250000000000000000),(75251650812989497/200000000000000000),(255954279314479897/1000000000000000000),(95592117353947993/500000000000000000)⟩
theorem valid607 : certificate607.Valid := by decide +kernel
theorem sound607 : certificate607.Sound := rat_cut_bin_certificate_sound certificate607 profilesValid607 numericValid607 valid607

def retention608 : RatCutRetentionCertificate := ⟨(43/1000),(87/2000),(12893909007556013807/26140889609024163467),(5778558227494460479/500000000000000000),(21/20),(4673356987468340217022289808769506018839/4622846581995568383200000000000000000000),false,MergedCutProfiles.Batch101.profile4061,(fun _ => MergedCutProfiles.Batch101.profile4061)⟩
theorem profilesValid608 : retention608.ProfilesValid := by
  exact MergedCutProfiles.Batch101.valid4061
theorem numericValid608 : retention608.NumericValid := by decide +kernel
def certificate608 : RatCutBinCertificate := ⟨⟨retention608,(2477374260167493743/1000000000000000000),(87716241548175929/1000000000000000000),(11892637746559233419/1000000000000000000),(311738188183217569999/1000000000000000000),(991739886094619041/1000000000000000000)⟩,(248181880850174043/250000000000000000),(206192636396124703/500000000000000000),(111162035419875771/500000000000000000),(193355488906532713/1000000000000000000)⟩
theorem valid608 : certificate608.Valid := by decide +kernel
theorem sound608 : certificate608.Sound := rat_cut_bin_certificate_sound certificate608 profilesValid608 numericValid608 valid608

def retention609 : RatCutRetentionCertificate := ⟨(43/1000),(87/2000),(13022848097631573946/26140889609024163467),(12893909007556013807/1000000000000000000),(21/20),(20684963335309910382317041507411322313071/20630254412089622091200000000000000000000),false,MergedCutProfiles.Batch101.profile4062,(fun _ => MergedCutProfiles.Batch101.profile4062)⟩
theorem profilesValid609 : retention609.ProfilesValid := by
  exact MergedCutProfiles.Batch101.valid4062
theorem numericValid609 : retention609.NumericValid := by decide +kernel
def certificate609 : RatCutBinCertificate := ⟨⟨retention609,(2477374260167493743/1000000000000000000),(87716241548175929/1000000000000000000),(11892637746559233419/1000000000000000000),(311738188183217569999/1000000000000000000),(245866388605302661/250000000000000000)⟩,(248181880850174043/250000000000000000),(207927426450017453/500000000000000000),(109632687402149157/500000000000000000),(190639448619960527/1000000000000000000)⟩
theorem valid609 : certificate609.Valid := by decide +kernel
theorem sound609 : certificate609.Sound := rat_cut_bin_certificate_sound certificate609 profilesValid609 numericValid609 valid609

def retention610 : RatCutRetentionCertificate := ⟨(43/1000),(87/2000),(1/2),(6511424048815786973/500000000000000000),(21/20),(5204798564199181000541745181359211094591/5209139239052629578400000000000000000000),false,MergedCutProfiles.Batch101.profile4059,(fun _ => MergedCutProfiles.Batch101.profile4059)⟩
theorem profilesValid610 : retention610.ProfilesValid := by
  exact MergedCutProfiles.Batch101.valid4059
theorem numericValid610 : retention610.NumericValid := by decide +kernel
def certificate610 : RatCutBinCertificate := ⟨⟨retention610,(2477374260167493743/1000000000000000000),(87716241548175929/1000000000000000000),(11892637746559233419/1000000000000000000),(311738188183217569999/1000000000000000000),(195996079894370737/200000000000000000)⟩,(248181880850174043/250000000000000000),(83466755801748101/200000000000000000),(108985200362307547/500000000000000000),(7560254478821029/40000000000000000)⟩
theorem valid610 : certificate610.Valid := by decide +kernel
theorem sound610 : certificate610.Sound := rat_cut_bin_certificate_sound certificate610 profilesValid610 numericValid610 valid610

def retention611 : RatCutRetentionCertificate := ⟨(87/2000),(7/160),(81873141872315687/2580748214001379806),(202656291763157641/250000000000000000),(31/10),(680942795054704100729/320000000000000000000),true,MergedCutProfiles.Batch101.profile4063,![MergedCutProfiles.Batch101.profile4063,MergedCutProfiles.Batch101.profile4064,MergedCutProfiles.Batch101.profile4065,MergedCutProfiles.Batch101.profile4066,MergedCutProfiles.Batch101.profile4067,MergedCutProfiles.Batch101.profile4068,MergedCutProfiles.Batch101.profile4069,MergedCutProfiles.Batch101.profile4070,MergedCutProfiles.Batch101.profile4071,MergedCutProfiles.Batch101.profile4072,MergedCutProfiles.Batch101.profile4073,MergedCutProfiles.Batch101.profile4074,MergedCutProfiles.Batch101.profile4075,MergedCutProfiles.Batch101.profile4076,MergedCutProfiles.Batch101.profile4077,MergedCutProfiles.Batch101.profile4078]⟩
theorem profilesValid611 : retention611.ProfilesValid := by
  change ∀ j : Fin 16, (retention611.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch101.valid4063
  · exact MergedCutProfiles.Batch101.valid4064
  · exact MergedCutProfiles.Batch101.valid4065
  · exact MergedCutProfiles.Batch101.valid4066
  · exact MergedCutProfiles.Batch101.valid4067
  · exact MergedCutProfiles.Batch101.valid4068
  · exact MergedCutProfiles.Batch101.valid4069
  · exact MergedCutProfiles.Batch101.valid4070
  · exact MergedCutProfiles.Batch101.valid4071
  · exact MergedCutProfiles.Batch101.valid4072
  · exact MergedCutProfiles.Batch101.valid4073
  · exact MergedCutProfiles.Batch101.valid4074
  · exact MergedCutProfiles.Batch101.valid4075
  · exact MergedCutProfiles.Batch101.valid4076
  · exact MergedCutProfiles.Batch101.valid4077
  · exact MergedCutProfiles.Batch101.valid4078
theorem numericValid611 : retention611.NumericValid := by decide +kernel
def certificate611 : RatCutBinCertificate := ⟨⟨retention611,(525250416165231327/250000000000000000),(22208520138960273/250000000000000000),(5993337883701644691/500000000000000000),(30977154396792592491/100000000000000000),(259958956843301699/125000000000000000)⟩,(3975234993582157/4000000000000000),(97717621474618151/250000000000000000),(241952213986473959/1000000000000000000),(15897527495852619/125000000000000000)⟩
theorem valid611 : certificate611.Valid := by decide +kernel
theorem sound611 : certificate611.Sound := rat_cut_bin_certificate_sound certificate611 profilesValid611 numericValid611 valid611

def certificates : List RatCutBinCertificate := [certificate600,certificate601,certificate602,certificate603,certificate604,certificate605,certificate606,certificate607,certificate608,certificate609,certificate610,certificate611]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound600,List.forall_mem_cons.mpr ⟨sound601,List.forall_mem_cons.mpr ⟨sound602,List.forall_mem_cons.mpr ⟨sound603,List.forall_mem_cons.mpr ⟨sound604,List.forall_mem_cons.mpr ⟨sound605,List.forall_mem_cons.mpr ⟨sound606,List.forall_mem_cons.mpr ⟨sound607,List.forall_mem_cons.mpr ⟨sound608,List.forall_mem_cons.mpr ⟨sound609,List.forall_mem_cons.mpr ⟨sound610,List.forall_mem_cons.mpr ⟨sound611,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch050
