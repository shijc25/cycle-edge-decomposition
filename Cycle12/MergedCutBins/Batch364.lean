import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch010
import Cycle12.MergedCutProfiles.Batch011
import Cycle12.MergedCutProfiles.Batch311
import Cycle12.MergedCutProfiles.Batch312
import Cycle12.MergedCutProfiles.Batch445
import Cycle12.MergedCutProfiles.Batch446
import Cycle12.MergedCutProfiles.Batch645
import Cycle12.MergedCutProfiles.Batch646

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch364

def retention4368 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(1158362414624175514/2015117488404070940429),(647897479/500000000),(49/20),(37524880200742640591/16000000000000000000),true,MergedCutProfiles.Batch645.profile25826,![MergedCutProfiles.Batch645.profile25826,MergedCutProfiles.Batch645.profile25827,MergedCutProfiles.Batch311.profile12458,MergedCutProfiles.Batch445.profile17825,MergedCutProfiles.Batch011.profile447,MergedCutProfiles.Batch311.profile12445,MergedCutProfiles.Batch311.profile12446,MergedCutProfiles.Batch311.profile12447,MergedCutProfiles.Batch311.profile12448,MergedCutProfiles.Batch311.profile12449,MergedCutProfiles.Batch010.profile423,MergedCutProfiles.Batch311.profile12450,MergedCutProfiles.Batch010.profile424,MergedCutProfiles.Batch311.profile12452,MergedCutProfiles.Batch010.profile425,MergedCutProfiles.Batch010.profile426]⟩
theorem profilesValid4368 : retention4368.ProfilesValid := by
  change ∀ j : Fin 16, (retention4368.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch645.valid25826
  · exact MergedCutProfiles.Batch645.valid25827
  · exact MergedCutProfiles.Batch311.valid12458
  · exact MergedCutProfiles.Batch445.valid17825
  · exact MergedCutProfiles.Batch011.valid447
  · exact MergedCutProfiles.Batch311.valid12445
  · exact MergedCutProfiles.Batch311.valid12446
  · exact MergedCutProfiles.Batch311.valid12447
  · exact MergedCutProfiles.Batch311.valid12448
  · exact MergedCutProfiles.Batch311.valid12449
  · exact MergedCutProfiles.Batch010.valid423
  · exact MergedCutProfiles.Batch311.valid12450
  · exact MergedCutProfiles.Batch010.valid424
  · exact MergedCutProfiles.Batch311.valid12452
  · exact MergedCutProfiles.Batch010.valid425
  · exact MergedCutProfiles.Batch010.valid426
theorem numericValid4368 : retention4368.NumericValid := by decide +kernel
def certificate4368 : RatCutBinCertificate := ⟨⟨retention4368,(920098431516911947/500000000000000000),(4061079806220747/1000000000000000000),(7433116774958187683/1000000000000000000),(218167913631906075246811/500000000000000000),(2342841805376146017/1000000000000000000)⟩,(999995796441060671/1000000000000000000),(16801344591135651/50000000000000000),(148752820506790371/500000000000000000),(218635882286776071/1000000000000000000)⟩
theorem valid4368 : certificate4368.Valid := by decide +kernel
theorem sound4368 : certificate4368.Sound := rat_cut_bin_certificate_sound certificate4368 profilesValid4368 numericValid4368 valid4368

def retention4369 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(64000000000000000000/58438407163718057272441),(16796255012050544953/500000000000000000),1,(24160183442335131283535946193152411651/10336156930492643048000000000000000000),false,MergedCutProfiles.Batch645.profile25828,(fun _ => MergedCutProfiles.Batch645.profile25828)⟩
theorem profilesValid4369 : retention4369.ProfilesValid := by
  exact MergedCutProfiles.Batch645.valid25828
theorem numericValid4369 : retention4369.NumericValid := by decide +kernel
def certificate4369 : RatCutBinCertificate := ⟨⟨retention4369,(920098431516911947/500000000000000000),(4061079806220747/1000000000000000000),(7433116774958187683/1000000000000000000),(218167913631906075246811/500000000000000000),(93457526734160151/40000000000000000)⟩,(999995796441060671/1000000000000000000),(1396240661112871/7812500000000000),(513037853770515179/1000000000000000000),(1120726912274110657/1000000000000000000)⟩
theorem valid4369 : certificate4369.Valid := by decide +kernel
theorem sound4369 : certificate4369.Sound := rat_cut_bin_certificate_sound certificate4369 profilesValid4369 numericValid4369 valid4369

def retention4370 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(1/2),64,1,(62345958716102427160851921466530999/62500000000000000000000000000000000),false,MergedCutProfiles.Batch011.profile461,(fun _ => MergedCutProfiles.Batch011.profile461)⟩
theorem profilesValid4370 : retention4370.ProfilesValid := by
  exact MergedCutProfiles.Batch011.valid461
theorem numericValid4370 : retention4370.NumericValid := by decide +kernel
def certificate4370 : RatCutBinCertificate := ⟨⟨retention4370,(920098431516911947/500000000000000000),(4061079806220747/1000000000000000000),(7433116774958187683/1000000000000000000),(218167913631906075246811/500000000000000000),(996529948778697663/1000000000000000000)⟩,(999995796441060671/1000000000000000000),(51493459490526557/125000000000000000),(55677978172462593/250000000000000000),(109267691837014057/500000000000000000)⟩
theorem valid4370 : certificate4370.Valid := by decide +kernel
theorem sound4370 : certificate4370.Sound := rat_cut_bin_certificate_sound certificate4370 profilesValid4370 numericValid4370 valid4370

def retention4371 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(64000000000000000000/58438407163718057272441),(1986062178075019083/125000000000000000),1,(414728319964606155077029171333963809/181065497716241056000000000000000000),false,MergedCutProfiles.Batch645.profile25828,(fun _ => MergedCutProfiles.Batch645.profile25828)⟩
theorem profilesValid4371 : retention4371.ProfilesValid := by
  exact MergedCutProfiles.Batch645.valid25828
theorem numericValid4371 : retention4371.NumericValid := by decide +kernel
def certificate4371 : RatCutBinCertificate := ⟨⟨retention4371,(837959268516911947/500000000000000000),(4061079806220747/1000000000000000000),(7433116774958187683/1000000000000000000),(218167913631906075246811/500000000000000000),(1144786099149279403/500000000000000000)⟩,(999996171701799543/1000000000000000000),(6547040253977827/200000000000000000),(41817063514107453/50000000000000000),(836837673133735037/500000000000000000)⟩
theorem valid4371 : certificate4371.Valid := by decide +kernel
theorem sound4371 : certificate4371.Sound := rat_cut_bin_certificate_sound certificate4371 profilesValid4371 numericValid4371 valid4371

def retention4372 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(1/2),64,1,(62345958716102427160851921466530999/62500000000000000000000000000000000),false,MergedCutProfiles.Batch011.profile461,(fun _ => MergedCutProfiles.Batch011.profile461)⟩
theorem profilesValid4372 : retention4372.ProfilesValid := by
  exact MergedCutProfiles.Batch011.valid461
theorem numericValid4372 : retention4372.NumericValid := by decide +kernel
def certificate4372 : RatCutBinCertificate := ⟨⟨retention4372,(837959268516911947/500000000000000000),(4061079806220747/1000000000000000000),(7433116774958187683/1000000000000000000),(218167913631906075246811/500000000000000000),(15572182846309379/15625000000000000)⟩,(999996171701799543/1000000000000000000),(15040763607325803/200000000000000000),(723995677459498383/1000000000000000000),(44405113490281897/62500000000000000)⟩
theorem valid4372 : certificate4372.Valid := by decide +kernel
theorem sound4372 : certificate4372.Sound := rat_cut_bin_certificate_sound certificate4372 profilesValid4372 numericValid4372 valid4372

def retention4373 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(688329270444159181/58438407163718057272441),(170378532288158213/250000000000000000),4,(1294271144907841634088843257075835611/545211303322106281600000000000000000),false,MergedCutProfiles.Batch645.profile25829,(fun _ => MergedCutProfiles.Batch645.profile25829)⟩
theorem profilesValid4373 : retention4373.ProfilesValid := by
  exact MergedCutProfiles.Batch645.valid25829
theorem numericValid4373 : retention4373.NumericValid := by decide +kernel
def certificate4373 : RatCutBinCertificate := ⟨⟨retention4373,(878316375016911947/500000000000000000),(4061079806220747/1000000000000000000),(7433116774958187683/1000000000000000000),(218167913631906075246811/500000000000000000),(1185025055910602841/500000000000000000)⟩,(199999197465288283/200000000000000000),(147098160728407519/200000000000000000),(4819217466333261/125000000000000000),(3752977822389259/200000000000000000)⟩
theorem valid4373 : certificate4373.Valid := by decide +kernel
theorem sound4373 : certificate4373.Sound := rat_cut_bin_certificate_sound certificate4373 profilesValid4373 numericValid4373 valid4373

def retention4374 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(3966048525437221332/58438407163718057272441),(688329270444159181/1000000000000000000),4,(6536915263948230440982665293600529007/2753317081776636724000000000000000000),false,MergedCutProfiles.Batch645.profile25830,(fun _ => MergedCutProfiles.Batch645.profile25830)⟩
theorem profilesValid4374 : retention4374.ProfilesValid := by
  exact MergedCutProfiles.Batch645.valid25830
theorem numericValid4374 : retention4374.NumericValid := by decide +kernel
def certificate4374 : RatCutBinCertificate := ⟨⟨retention4374,(878316375016911947/500000000000000000),(4061079806220747/1000000000000000000),(7433116774958187683/1000000000000000000),(218167913631906075246811/500000000000000000),(2370357371079351713/1000000000000000000)⟩,(199999197465288283/200000000000000000),(146605339334930487/200000000000000000),(39314888231483173/1000000000000000000),(3834257491414041/200000000000000000)⟩
theorem valid4374 : certificate4374.Valid := by decide +kernel
theorem sound4374 : certificate4374.Sound := rat_cut_bin_certificate_sound certificate4374 profilesValid4374 numericValid4374 valid4374

def retention4375 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(1/40),(991512131359305333/250000000000000000),(29/20),(6704025219799951083597485247861797407/3098475410497829165625000000000000000),false,MergedCutProfiles.Batch645.profile25831,(fun _ => MergedCutProfiles.Batch645.profile25831)⟩
theorem profilesValid4375 : retention4375.ProfilesValid := by
  exact MergedCutProfiles.Batch645.valid25831
theorem numericValid4375 : retention4375.NumericValid := by decide +kernel
def certificate4375 : RatCutBinCertificate := ⟨⟨retention4375,(878316375016911947/500000000000000000),(4061079806220747/1000000000000000000),(7433116774958187683/1000000000000000000),(218167913631906075246811/500000000000000000),(2162261255267770291/1000000000000000000)⟩,(199999197465288283/200000000000000000),(11779342958706677/20000000000000000),(248106379340813/2500000000000000),(14689757366600067/125000000000000000)⟩
theorem valid4375 : certificate4375.Valid := by decide +kernel
theorem sound4375 : certificate4375.Sound := rat_cut_bin_certificate_sound certificate4375 profilesValid4375 numericValid4375 valid4375

def retention4376 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(653964847868781972/48078438475687214310245),(290180298795897327/500000000000000000),4,(10091110787929494288785515906761613/4534067168685895734375000000000000),true,MergedCutProfiles.Batch645.profile25832,![MergedCutProfiles.Batch645.profile25832,MergedCutProfiles.Batch645.profile25833,MergedCutProfiles.Batch645.profile25834,MergedCutProfiles.Batch645.profile25834,MergedCutProfiles.Batch645.profile25835,MergedCutProfiles.Batch645.profile25835,MergedCutProfiles.Batch645.profile25835,MergedCutProfiles.Batch645.profile25836,MergedCutProfiles.Batch645.profile25836,MergedCutProfiles.Batch645.profile25836,MergedCutProfiles.Batch645.profile25837,MergedCutProfiles.Batch645.profile25837,MergedCutProfiles.Batch645.profile25837,MergedCutProfiles.Batch645.profile25838,MergedCutProfiles.Batch645.profile25838,MergedCutProfiles.Batch645.profile25838]⟩
theorem profilesValid4376 : retention4376.ProfilesValid := by
  change ∀ j : Fin 16, (retention4376.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch645.valid25832
  · exact MergedCutProfiles.Batch645.valid25833
  · exact MergedCutProfiles.Batch645.valid25834
  · exact MergedCutProfiles.Batch645.valid25834
  · exact MergedCutProfiles.Batch645.valid25835
  · exact MergedCutProfiles.Batch645.valid25835
  · exact MergedCutProfiles.Batch645.valid25835
  · exact MergedCutProfiles.Batch645.valid25836
  · exact MergedCutProfiles.Batch645.valid25836
  · exact MergedCutProfiles.Batch645.valid25836
  · exact MergedCutProfiles.Batch645.valid25837
  · exact MergedCutProfiles.Batch645.valid25837
  · exact MergedCutProfiles.Batch645.valid25837
  · exact MergedCutProfiles.Batch645.valid25838
  · exact MergedCutProfiles.Batch645.valid25838
  · exact MergedCutProfiles.Batch645.valid25838
theorem numericValid4376 : retention4376.NumericValid := by decide +kernel
def certificate4376 : RatCutBinCertificate := ⟨⟨retention4376,(113439164896524909/62500000000000000),(246507623072377/50000000000000000),(1881196017164384497/250000000000000000),(45427313556122745628759/125000000000000000),(1110431654410964949/500000000000000000)⟩,(999995025966853767/1000000000000000000),(284671356105283883/500000000000000000),(54981033035316609/500000000000000000),(49268778647947767/1000000000000000000)⟩
theorem valid4376 : certificate4376.Valid := by decide +kernel
theorem sound4376 : certificate4376.Sound := rat_cut_bin_certificate_sound certificate4376 profilesValid4376 numericValid4376 valid4376

def retention4377 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(255225381400000000/9615687695137442862049),(163491211967195493/250000000000000000),4,(681372536376950329119563137033292391/290651043497236432000000000000000000),true,MergedCutProfiles.Batch645.profile25833,![MergedCutProfiles.Batch645.profile25833,MergedCutProfiles.Batch645.profile25834,MergedCutProfiles.Batch645.profile25835,MergedCutProfiles.Batch645.profile25836,MergedCutProfiles.Batch645.profile25836,MergedCutProfiles.Batch645.profile25837,MergedCutProfiles.Batch645.profile25837,MergedCutProfiles.Batch645.profile25838,MergedCutProfiles.Batch645.profile25838,MergedCutProfiles.Batch446.profile17842,MergedCutProfiles.Batch446.profile17842,MergedCutProfiles.Batch645.profile25839,MergedCutProfiles.Batch645.profile25839,MergedCutProfiles.Batch645.profile25839,MergedCutProfiles.Batch646.profile25840,MergedCutProfiles.Batch646.profile25840]⟩
theorem profilesValid4377 : retention4377.ProfilesValid := by
  change ∀ j : Fin 16, (retention4377.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch645.valid25833
  · exact MergedCutProfiles.Batch645.valid25834
  · exact MergedCutProfiles.Batch645.valid25835
  · exact MergedCutProfiles.Batch645.valid25836
  · exact MergedCutProfiles.Batch645.valid25836
  · exact MergedCutProfiles.Batch645.valid25837
  · exact MergedCutProfiles.Batch645.valid25837
  · exact MergedCutProfiles.Batch645.valid25838
  · exact MergedCutProfiles.Batch645.valid25838
  · exact MergedCutProfiles.Batch446.valid17842
  · exact MergedCutProfiles.Batch446.valid17842
  · exact MergedCutProfiles.Batch645.valid25839
  · exact MergedCutProfiles.Batch645.valid25839
  · exact MergedCutProfiles.Batch645.valid25839
  · exact MergedCutProfiles.Batch646.valid25840
  · exact MergedCutProfiles.Batch646.valid25840
theorem numericValid4377 : retention4377.NumericValid := by decide +kernel
def certificate4377 : RatCutBinCertificate := ⟨⟨retention4377,(113439164896524909/62500000000000000),(246507623072377/50000000000000000),(1881196017164384497/250000000000000000),(45427313556122745628759/125000000000000000),(1169770417985856389/500000000000000000)⟩,(999995025966853767/1000000000000000000),(4991395674590297/10000000000000000),(154023504612659509/1000000000000000000),(73623842296763527/1000000000000000000)⟩
theorem valid4377 : certificate4377.Valid := by decide +kernel
theorem sound4377 : certificate4377.Sound := rat_cut_bin_certificate_sound certificate4377 profilesValid4377 numericValid4377 valid4377

def retention4378 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(8107033574726446839/48078438475687214310245),(1276126907/1000000000),(5/2),(37846395345949696711/16000000000000000000),true,MergedCutProfiles.Batch645.profile25837,![MergedCutProfiles.Batch645.profile25837,MergedCutProfiles.Batch645.profile25839,MergedCutProfiles.Batch446.profile17843,MergedCutProfiles.Batch646.profile25841,MergedCutProfiles.Batch446.profile17844,MergedCutProfiles.Batch446.profile17845,MergedCutProfiles.Batch312.profile12483,MergedCutProfiles.Batch011.profile462,MergedCutProfiles.Batch646.profile25842,MergedCutProfiles.Batch312.profile12484,MergedCutProfiles.Batch646.profile25843,MergedCutProfiles.Batch446.profile17847,MergedCutProfiles.Batch446.profile17847,MergedCutProfiles.Batch446.profile17848,MergedCutProfiles.Batch011.profile463,MergedCutProfiles.Batch011.profile478]⟩
theorem profilesValid4378 : retention4378.ProfilesValid := by
  change ∀ j : Fin 16, (retention4378.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch645.valid25837
  · exact MergedCutProfiles.Batch645.valid25839
  · exact MergedCutProfiles.Batch446.valid17843
  · exact MergedCutProfiles.Batch646.valid25841
  · exact MergedCutProfiles.Batch446.valid17844
  · exact MergedCutProfiles.Batch446.valid17845
  · exact MergedCutProfiles.Batch312.valid12483
  · exact MergedCutProfiles.Batch011.valid462
  · exact MergedCutProfiles.Batch646.valid25842
  · exact MergedCutProfiles.Batch312.valid12484
  · exact MergedCutProfiles.Batch646.valid25843
  · exact MergedCutProfiles.Batch446.valid17847
  · exact MergedCutProfiles.Batch446.valid17847
  · exact MergedCutProfiles.Batch446.valid17848
  · exact MergedCutProfiles.Batch011.valid463
  · exact MergedCutProfiles.Batch011.valid478
theorem numericValid4378 : retention4378.NumericValid := by decide +kernel
def certificate4378 : RatCutBinCertificate := ⟨⟨retention4378,(113439164896524909/62500000000000000),(246507623072377/50000000000000000),(1881196017164384497/250000000000000000),(45427313556122745628759/125000000000000000),(2362426747371382307/1000000000000000000)⟩,(999995025966853767/1000000000000000000),(336992758384658269/1000000000000000000),(296453917081474057/1000000000000000000),(27015388336748359/125000000000000000)⟩
theorem valid4378 : certificate4378.Valid := by decide +kernel
theorem sound4378 : certificate4378.Sound := rat_cut_bin_certificate_sound certificate4378 profilesValid4378 numericValid4378 valid4378

def retention4379 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(12800000000000000000/9615687695137442862049),(8107033574726446839/1000000000000000000),(11/10),(7456501016125998499825471481836812874799/3242813429890578735600000000000000000000),false,MergedCutProfiles.Batch646.profile25844,(fun _ => MergedCutProfiles.Batch646.profile25844)⟩
theorem profilesValid4379 : retention4379.ProfilesValid := by
  exact MergedCutProfiles.Batch646.valid25844
theorem numericValid4379 : retention4379.NumericValid := by decide +kernel
def certificate4379 : RatCutBinCertificate := ⟨⟨retention4379,(113439164896524909/62500000000000000),(246507623072377/50000000000000000),(1881196017164384497/250000000000000000),(45427313556122745628759/125000000000000000),(2298084438937644401/1000000000000000000)⟩,(999995025966853767/1000000000000000000),(40640523756708579/200000000000000000),(94541829651117333/200000000000000000),(400059412990540921/500000000000000000)⟩
theorem valid4379 : certificate4379.Valid := by decide +kernel
theorem sound4379 : certificate4379.Sound := rat_cut_bin_certificate_sound certificate4379 profilesValid4379 numericValid4379 valid4379

def certificates : List RatCutBinCertificate := [certificate4368,certificate4369,certificate4370,certificate4371,certificate4372,certificate4373,certificate4374,certificate4375,certificate4376,certificate4377,certificate4378,certificate4379]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4368,List.forall_mem_cons.mpr ⟨sound4369,List.forall_mem_cons.mpr ⟨sound4370,List.forall_mem_cons.mpr ⟨sound4371,List.forall_mem_cons.mpr ⟨sound4372,List.forall_mem_cons.mpr ⟨sound4373,List.forall_mem_cons.mpr ⟨sound4374,List.forall_mem_cons.mpr ⟨sound4375,List.forall_mem_cons.mpr ⟨sound4376,List.forall_mem_cons.mpr ⟨sound4377,List.forall_mem_cons.mpr ⟨sound4378,List.forall_mem_cons.mpr ⟨sound4379,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch364
