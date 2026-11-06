import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch017
import Cycle12.MergedCutProfiles.Batch018
import Cycle12.MergedCutProfiles.Batch019
import Cycle12.MergedCutProfiles.Batch316
import Cycle12.MergedCutProfiles.Batch452
import Cycle12.MergedCutProfiles.Batch575
import Cycle12.MergedCutProfiles.Batch647

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch369

def retention4428 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(1/40),64,1,(22098109596983918218357525785440079871/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch647.profile25899,(fun _ => MergedCutProfiles.Batch647.profile25899)⟩
theorem profilesValid4428 : retention4428.ProfilesValid := by
  exact MergedCutProfiles.Batch647.valid25899
theorem numericValid4428 : retention4428.NumericValid := by decide +kernel
def certificate4428 : RatCutBinCertificate := ⟨⟨retention4428,(174545750218207757/100000000000000000),(9292470143341151/1000000000000000000),(790946750439235613/100000000000000000),(40343640626005903294591/200000000000000000),(2155967857466557121/1000000000000000000)⟩,(999991416853303063/1000000000000000000),(24316191602005799/40000000000000000),(2797453124445303/31250000000000000),(5834616096632509/31250000000000000)⟩
theorem valid4428 : certificate4428.Valid := by decide +kernel
theorem sound4428 : certificate4428.Sound := rat_cut_bin_certificate_sound certificate4428 profilesValid4428 numericValid4428 valid4428

def retention4429 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(676254919077888577/22208186754729867564364),(600141904017421419/1000000000000000000),4,(120875617123614289110936405592648827/53345947023770792800000000000000000),true,MergedCutProfiles.Batch647.profile25900,![MergedCutProfiles.Batch647.profile25900,MergedCutProfiles.Batch647.profile25901,MergedCutProfiles.Batch647.profile25902,MergedCutProfiles.Batch647.profile25903,MergedCutProfiles.Batch575.profile23015,MergedCutProfiles.Batch575.profile23015,MergedCutProfiles.Batch647.profile25904,MergedCutProfiles.Batch647.profile25904,MergedCutProfiles.Batch575.profile23016,MergedCutProfiles.Batch575.profile23016,MergedCutProfiles.Batch647.profile25905,MergedCutProfiles.Batch647.profile25905,MergedCutProfiles.Batch575.profile23017,MergedCutProfiles.Batch575.profile23017,MergedCutProfiles.Batch575.profile23017,MergedCutProfiles.Batch452.profile18089]⟩
theorem profilesValid4429 : retention4429.ProfilesValid := by
  change ∀ j : Fin 16, (retention4429.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch647.valid25900
  · exact MergedCutProfiles.Batch647.valid25901
  · exact MergedCutProfiles.Batch647.valid25902
  · exact MergedCutProfiles.Batch647.valid25903
  · exact MergedCutProfiles.Batch575.valid23015
  · exact MergedCutProfiles.Batch575.valid23015
  · exact MergedCutProfiles.Batch647.valid25904
  · exact MergedCutProfiles.Batch647.valid25904
  · exact MergedCutProfiles.Batch575.valid23016
  · exact MergedCutProfiles.Batch575.valid23016
  · exact MergedCutProfiles.Batch647.valid25905
  · exact MergedCutProfiles.Batch647.valid25905
  · exact MergedCutProfiles.Batch575.valid23017
  · exact MergedCutProfiles.Batch575.valid23017
  · exact MergedCutProfiles.Batch575.valid23017
  · exact MergedCutProfiles.Batch452.valid18089
theorem numericValid4429 : retention4429.NumericValid := by decide +kernel
def certificate4429 : RatCutBinCertificate := ⟨⟨retention4429,(1862755924439784127/1000000000000000000),(1060946273715283/100000000000000000),(8010376979594533009/1000000000000000000),(89362533641297081802843/500000000000000000),(2256013305599684551/1000000000000000000)⟩,(999989674383524241/1000000000000000000),(535948818206083529/1000000000000000000),(4055343369393987/31250000000000000),(3704128770429341/62500000000000000)⟩
theorem valid4429 : certificate4429.Valid := by decide +kernel
theorem sound4429 : certificate4429.Sound := rat_cut_bin_certificate_sound certificate4429 profilesValid4429 numericValid4429 valid4429

def retention4430 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(321414970500000000/5552046688682466891091),(676254919077888577/1000000000000000000),4,(400445175363035710848701942914232253/169063729769472144250000000000000000),true,MergedCutProfiles.Batch647.profile25901,![MergedCutProfiles.Batch647.profile25901,MergedCutProfiles.Batch647.profile25903,MergedCutProfiles.Batch575.profile23015,MergedCutProfiles.Batch647.profile25904,MergedCutProfiles.Batch575.profile23016,MergedCutProfiles.Batch647.profile25905,MergedCutProfiles.Batch575.profile23017,MergedCutProfiles.Batch452.profile18089,MergedCutProfiles.Batch452.profile18089,MergedCutProfiles.Batch575.profile23018,MergedCutProfiles.Batch575.profile23018,MergedCutProfiles.Batch575.profile23019,MergedCutProfiles.Batch575.profile23020,MergedCutProfiles.Batch575.profile23020,MergedCutProfiles.Batch647.profile25906,MergedCutProfiles.Batch647.profile25906]⟩
theorem profilesValid4430 : retention4430.ProfilesValid := by
  change ∀ j : Fin 16, (retention4430.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch647.valid25901
  · exact MergedCutProfiles.Batch647.valid25903
  · exact MergedCutProfiles.Batch575.valid23015
  · exact MergedCutProfiles.Batch647.valid25904
  · exact MergedCutProfiles.Batch575.valid23016
  · exact MergedCutProfiles.Batch647.valid25905
  · exact MergedCutProfiles.Batch575.valid23017
  · exact MergedCutProfiles.Batch452.valid18089
  · exact MergedCutProfiles.Batch452.valid18089
  · exact MergedCutProfiles.Batch575.valid23018
  · exact MergedCutProfiles.Batch575.valid23018
  · exact MergedCutProfiles.Batch575.valid23019
  · exact MergedCutProfiles.Batch575.valid23020
  · exact MergedCutProfiles.Batch575.valid23020
  · exact MergedCutProfiles.Batch647.valid25906
  · exact MergedCutProfiles.Batch647.valid25906
theorem numericValid4430 : retention4430.NumericValid := by decide +kernel
def certificate4430 : RatCutBinCertificate := ⟨⟨retention4430,(1862755924439784127/1000000000000000000),(1060946273715283/100000000000000000),(8010376979594533009/1000000000000000000),(89362533641297081802843/500000000000000000),(1179368130403322451/500000000000000000)⟩,(999989674383524241/1000000000000000000),(47403468644430073/100000000000000000),(172110249259016349/1000000000000000000),(4166246480056541/50000000000000000)⟩
theorem valid4430 : certificate4430.Valid := by decide +kernel
theorem sound4430 : certificate4430.Sound := rat_cut_bin_certificate_sound certificate4430 profilesValid4430 numericValid4430 valid4430

def retention4431 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(17506513543944173209/22208186754729867564364),(642829941/500000000),(5/2),(4840492543852880078940024340294271/2057055811200000000000000000000000),true,MergedCutProfiles.Batch575.profile23020,![MergedCutProfiles.Batch575.profile23020,MergedCutProfiles.Batch452.profile18091,MergedCutProfiles.Batch452.profile18099,MergedCutProfiles.Batch452.profile18108,MergedCutProfiles.Batch575.profile23025,MergedCutProfiles.Batch452.profile18095,MergedCutProfiles.Batch017.profile704,MergedCutProfiles.Batch452.profile18109,MergedCutProfiles.Batch316.profile12669,MergedCutProfiles.Batch452.profile18102,MergedCutProfiles.Batch017.profile705,MergedCutProfiles.Batch575.profile23027,MergedCutProfiles.Batch452.profile18104,MergedCutProfiles.Batch018.profile720,MergedCutProfiles.Batch647.profile25907,MergedCutProfiles.Batch316.profile12671]⟩
theorem profilesValid4431 : retention4431.ProfilesValid := by
  change ∀ j : Fin 16, (retention4431.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch575.valid23020
  · exact MergedCutProfiles.Batch452.valid18091
  · exact MergedCutProfiles.Batch452.valid18099
  · exact MergedCutProfiles.Batch452.valid18108
  · exact MergedCutProfiles.Batch575.valid23025
  · exact MergedCutProfiles.Batch452.valid18095
  · exact MergedCutProfiles.Batch017.valid704
  · exact MergedCutProfiles.Batch452.valid18109
  · exact MergedCutProfiles.Batch316.valid12669
  · exact MergedCutProfiles.Batch452.valid18102
  · exact MergedCutProfiles.Batch017.valid705
  · exact MergedCutProfiles.Batch575.valid23027
  · exact MergedCutProfiles.Batch452.valid18104
  · exact MergedCutProfiles.Batch018.valid720
  · exact MergedCutProfiles.Batch647.valid25907
  · exact MergedCutProfiles.Batch316.valid12671
theorem numericValid4431 : retention4431.NumericValid := by decide +kernel
def certificate4431 : RatCutBinCertificate := ⟨⟨retention4431,(1862755924439784127/1000000000000000000),(1060946273715283/100000000000000000),(8010376979594533009/1000000000000000000),(89362533641297081802843/500000000000000000),(293368611453262971/125000000000000000)⟩,(999989674383524241/1000000000000000000),(41440602196919607/125000000000000000),(75611147364968211/250000000000000000),(109871724023216411/500000000000000000)⟩
theorem valid4431 : certificate4431.Valid := by decide +kernel
theorem sound4431 : certificate4431.Sound := rat_cut_bin_certificate_sound certificate4431 profilesValid4431 numericValid4431 valid4431

def retention4432 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(16000000000000000000/5552046688682466891091),(17506513543944173209/1000000000000000000),1,(159098302060762480888860495619342227243/70026054175776692836000000000000000000),false,MergedCutProfiles.Batch647.profile25908,(fun _ => MergedCutProfiles.Batch647.profile25908)⟩
theorem profilesValid4432 : retention4432.ProfilesValid := by
  exact MergedCutProfiles.Batch647.valid25908
theorem numericValid4432 : retention4432.NumericValid := by decide +kernel
def certificate4432 : RatCutBinCertificate := ⟨⟨retention4432,(1862755924439784127/1000000000000000000),(1060946273715283/100000000000000000),(8010376979594533009/1000000000000000000),(89362533641297081802843/500000000000000000),(2269520092471071967/1000000000000000000)⟩,(999989674383524241/1000000000000000000),(188775876766242183/1000000000000000000),(496106864238606943/1000000000000000000),(1557346164222879/1562500000000000)⟩
theorem valid4432 : certificate4432.Valid := by decide +kernel
theorem sound4432 : certificate4432.Sound := rat_cut_bin_certificate_sound certificate4432 profilesValid4432 numericValid4432 valid4432

def retention4433 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(1/2),64,1,(255370070520985369056173916463207973031/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch019.profile763,(fun _ => MergedCutProfiles.Batch019.profile763)⟩
theorem profilesValid4433 : retention4433.ProfilesValid := by
  exact MergedCutProfiles.Batch019.valid763
theorem numericValid4433 : retention4433.NumericValid := by decide +kernel
def certificate4433 : RatCutBinCertificate := ⟨⟨retention4433,(1862755924439784127/1000000000000000000),(1060946273715283/100000000000000000),(8010376979594533009/1000000000000000000),(89362533641297081802843/500000000000000000),(995072183226021173/1000000000000000000)⟩,(999989674383524241/1000000000000000000),(102580155746862769/250000000000000000),(224158048593835941/1000000000000000000),(54909052945633031/250000000000000000)⟩
theorem valid4433 : certificate4433.Valid := by decide +kernel
theorem sound4433 : certificate4433.Sound := rat_cut_bin_certificate_sound certificate4433 profilesValid4433 numericValid4433 valid4433

def retention4434 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(16000000000000000000/5552046688682466891091),(2124736048827398507/125000000000000000),1,(30863074042089470306649266545354444107/13598310712495350444800000000000000000),false,MergedCutProfiles.Batch647.profile25908,(fun _ => MergedCutProfiles.Batch647.profile25908)⟩
theorem profilesValid4434 : retention4434.ProfilesValid := by
  exact MergedCutProfiles.Batch647.valid25908
theorem numericValid4434 : retention4434.NumericValid := by decide +kernel
def certificate4434 : RatCutBinCertificate := ⟨⟨retention4434,(1790111073439784127/1000000000000000000),(1060946273715283/100000000000000000),(8010376979594533009/1000000000000000000),(89362533641297081802843/500000000000000000),(453450931163446699/200000000000000000)⟩,(999990077068025381/1000000000000000000),(28563239844330343/1000000000000000000),(848455750274690273/1000000000000000000),(848628870361974167/500000000000000000)⟩
theorem valid4434 : certificate4434.Valid := by decide +kernel
theorem sound4434 : certificate4434.Sound := rat_cut_bin_certificate_sound certificate4434 profilesValid4434 numericValid4434 valid4434

def retention4435 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(1/2),64,1,(255370070520985369056173916463207973031/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch019.profile763,(fun _ => MergedCutProfiles.Batch019.profile763)⟩
theorem profilesValid4435 : retention4435.ProfilesValid := by
  exact MergedCutProfiles.Batch019.valid763
theorem numericValid4435 : retention4435.NumericValid := by decide +kernel
def certificate4435 : RatCutBinCertificate := ⟨⟨retention4435,(1790111073439784127/1000000000000000000),(1060946273715283/100000000000000000),(8010376979594533009/1000000000000000000),(89362533641297081802843/500000000000000000),(995168398777724759/1000000000000000000)⟩,(999990077068025381/1000000000000000000),(65074552811183811/1000000000000000000),(187278204789520353/250000000000000000),(45879468321927849/62500000000000000)⟩
theorem valid4435 : certificate4435.Valid := by decide +kernel
theorem sound4435 : certificate4435.Sound := rat_cut_bin_certificate_sound certificate4435 profilesValid4435 numericValid4435 valid4435

def retention4436 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(674889773038276485/22208186754729867564364),(66820769607750147/100000000000000000),4,(12626182136553958822521461922439579/5345661568620011760000000000000000),false,MergedCutProfiles.Batch647.profile25909,(fun _ => MergedCutProfiles.Batch647.profile25909)⟩
theorem profilesValid4436 : retention4436.ProfilesValid := by
  exact MergedCutProfiles.Batch647.valid25909
theorem numericValid4436 : retention4436.NumericValid := by decide +kernel
def certificate4436 : RatCutBinCertificate := ⟨⟨retention4436,(1751945636439784127/1000000000000000000),(1060946273715283/100000000000000000),(8010376979594533009/1000000000000000000),(89362533641297081802843/500000000000000000),(235266783850675181/100000000000000000)⟩,(499995144313222497/500000000000000000),(402523840877949943/500000000000000000),(814987694425689/40000000000000000),(9822175278123249/1000000000000000000)⟩
theorem valid4436 : certificate4436.Valid := by decide +kernel
theorem sound4436 : certificate4436.Sound := rat_cut_bin_certificate_sound certificate4436 profilesValid4436 numericValid4436 valid4436

def retention4437 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(1996469084091984377/22208186754729867564364),(134977954607655297/200000000000000000),4,(2127472256362307810141335699528672653/899853030717701980000000000000000000),false,MergedCutProfiles.Batch647.profile25910,(fun _ => MergedCutProfiles.Batch647.profile25910)⟩
theorem profilesValid4437 : retention4437.ProfilesValid := by
  exact MergedCutProfiles.Batch647.valid25910
theorem numericValid4437 : retention4437.NumericValid := by decide +kernel
def certificate4437 : RatCutBinCertificate := ⟨⟨retention4437,(1751945636439784127/1000000000000000000),(1060946273715283/100000000000000000),(8010376979594533009/1000000000000000000),(89362533641297081802843/500000000000000000),(147185161247000547/62500000000000000)⟩,(499995144313222497/500000000000000000),(200441906086574743/250000000000000000),(4218535269564123/200000000000000000),(10194646808100317/1000000000000000000)⟩
theorem valid4437 : certificate4437.Valid := by decide +kernel
theorem sound4437 : certificate4437.Sound := rat_cut_bin_certificate_sound certificate4437 profilesValid4437 numericValid4437 valid4437

def retention4438 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(16000000000000000000/5552046688682466891091),(1996469084091984377/1000000000000000000),(41/20),(159227755195322470792241767277600444673/67964904990365425600000000000000000000),false,MergedCutProfiles.Batch647.profile25908,(fun _ => MergedCutProfiles.Batch647.profile25908)⟩
theorem profilesValid4438 : retention4438.ProfilesValid := by
  exact MergedCutProfiles.Batch647.valid25908
theorem numericValid4438 : retention4438.NumericValid := by decide +kernel
def certificate4438 : RatCutBinCertificate := ⟨⟨retention4438,(1751945636439784127/1000000000000000000),(1060946273715283/100000000000000000),(8010376979594533009/1000000000000000000),(89362533641297081802843/500000000000000000),(2338036957891021851/1000000000000000000)⟩,(499995144313222497/500000000000000000),(160294456789056189/250000000000000000),(36925844124063739/500000000000000000),(1646784535842909/25000000000000000)⟩
theorem valid4438 : certificate4438.Valid := by decide +kernel
theorem sound4438 : certificate4438.Sound := rat_cut_bin_certificate_sound certificate4438 profilesValid4438 numericValid4438 valid4438

def retention4439 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(1/40),64,1,(5526358913070303987943350207456150831/2560000000000000000000000000000000000),false,MergedCutProfiles.Batch647.profile25911,(fun _ => MergedCutProfiles.Batch647.profile25911)⟩
theorem profilesValid4439 : retention4439.ProfilesValid := by
  exact MergedCutProfiles.Batch647.valid25911
theorem numericValid4439 : retention4439.NumericValid := by decide +kernel
def certificate4439 : RatCutBinCertificate := ⟨⟨retention4439,(1751945636439784127/1000000000000000000),(1060946273715283/100000000000000000),(8010376979594533009/1000000000000000000),(89362533641297081802843/500000000000000000),(2156413560003015367/1000000000000000000)⟩,(499995144313222497/500000000000000000),(151481443991761863/250000000000000000),(18101350653827837/200000000000000000),(188806440948027167/1000000000000000000)⟩
theorem valid4439 : certificate4439.Valid := by decide +kernel
theorem sound4439 : certificate4439.Sound := rat_cut_bin_certificate_sound certificate4439 profilesValid4439 numericValid4439 valid4439

def certificates : List RatCutBinCertificate := [certificate4428,certificate4429,certificate4430,certificate4431,certificate4432,certificate4433,certificate4434,certificate4435,certificate4436,certificate4437,certificate4438,certificate4439]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4428,List.forall_mem_cons.mpr ⟨sound4429,List.forall_mem_cons.mpr ⟨sound4430,List.forall_mem_cons.mpr ⟨sound4431,List.forall_mem_cons.mpr ⟨sound4432,List.forall_mem_cons.mpr ⟨sound4433,List.forall_mem_cons.mpr ⟨sound4434,List.forall_mem_cons.mpr ⟨sound4435,List.forall_mem_cons.mpr ⟨sound4436,List.forall_mem_cons.mpr ⟨sound4437,List.forall_mem_cons.mpr ⟨sound4438,List.forall_mem_cons.mpr ⟨sound4439,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch369
