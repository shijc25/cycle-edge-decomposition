import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch047
import Cycle12.MergedCutProfiles.Batch048
import Cycle12.MergedCutProfiles.Batch049
import Cycle12.MergedCutProfiles.Batch335
import Cycle12.MergedCutProfiles.Batch336
import Cycle12.MergedCutProfiles.Batch464
import Cycle12.MergedCutProfiles.Batch465
import Cycle12.MergedCutProfiles.Batch595
import Cycle12.MergedCutProfiles.Batch596
import Cycle12.MergedCutProfiles.Batch597
import Cycle12.MergedCutProfiles.Batch656

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch384

def retention4608 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(1182925567000000000/5134451270410500746393),(318285437274342543/500000000000000000),4,(5926401410239161319557854513100869111/2546283498194740344000000000000000000),true,MergedCutProfiles.Batch656.profile26250,![MergedCutProfiles.Batch656.profile26250,MergedCutProfiles.Batch656.profile26251,MergedCutProfiles.Batch656.profile26243,MergedCutProfiles.Batch656.profile26244,MergedCutProfiles.Batch595.profile23839,MergedCutProfiles.Batch656.profile26247,MergedCutProfiles.Batch596.profile23840,MergedCutProfiles.Batch656.profile26248,MergedCutProfiles.Batch656.profile26252,MergedCutProfiles.Batch596.profile23841,MergedCutProfiles.Batch464.profile18578,MergedCutProfiles.Batch596.profile23842,MergedCutProfiles.Batch656.profile26253,MergedCutProfiles.Batch596.profile23843,MergedCutProfiles.Batch596.profile23851,MergedCutProfiles.Batch596.profile23844]⟩
theorem profilesValid4608 : retention4608.ProfilesValid := by
  change ∀ j : Fin 16, (retention4608.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch656.valid26250
  · exact MergedCutProfiles.Batch656.valid26251
  · exact MergedCutProfiles.Batch656.valid26243
  · exact MergedCutProfiles.Batch656.valid26244
  · exact MergedCutProfiles.Batch595.valid23839
  · exact MergedCutProfiles.Batch656.valid26247
  · exact MergedCutProfiles.Batch596.valid23840
  · exact MergedCutProfiles.Batch656.valid26248
  · exact MergedCutProfiles.Batch656.valid26252
  · exact MergedCutProfiles.Batch596.valid23841
  · exact MergedCutProfiles.Batch464.valid18578
  · exact MergedCutProfiles.Batch596.valid23842
  · exact MergedCutProfiles.Batch656.valid26253
  · exact MergedCutProfiles.Batch596.valid23843
  · exact MergedCutProfiles.Batch596.valid23851
  · exact MergedCutProfiles.Batch596.valid23844
theorem numericValid4608 : retention4608.NumericValid := by decide +kernel
def certificate4608 : RatCutBinCertificate := ⟨⟨retention4608,(928424619889688411/500000000000000000),(9018985876591161/200000000000000000),(4968587493102325573/500000000000000000),(2051325527390199155699/40000000000000000),(2293765600244058009/1000000000000000000)⟩,(999965318181749223/1000000000000000000),(154938381788707369/250000000000000000),(41867837426395499/500000000000000000),(19594858434005099/500000000000000000)⟩
theorem valid4608 : certificate4608.Valid := by decide +kernel
theorem sound4608 : certificate4608.Sound := rat_cut_bin_certificate_sound certificate4608 profilesValid4608 numericValid4608 valid4608

def retention4609 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(4387259044980385146/5134451270410500746393),(1182925567/1000000000),(27/10),(112502382954214723299023805149998271/47317022680000000000000000000000000),true,MergedCutProfiles.Batch656.profile26254,![MergedCutProfiles.Batch656.profile26254,MergedCutProfiles.Batch656.profile26248,MergedCutProfiles.Batch464.profile18578,MergedCutProfiles.Batch596.profile23843,MergedCutProfiles.Batch656.profile26255,MergedCutProfiles.Batch464.profile18579,MergedCutProfiles.Batch596.profile23846,MergedCutProfiles.Batch335.profile13413,MergedCutProfiles.Batch464.profile18580,MergedCutProfiles.Batch656.profile26256,MergedCutProfiles.Batch464.profile18596,MergedCutProfiles.Batch464.profile18581,MergedCutProfiles.Batch336.profile13442,MergedCutProfiles.Batch656.profile26257,MergedCutProfiles.Batch464.profile18582,MergedCutProfiles.Batch464.profile18591]⟩
theorem profilesValid4609 : retention4609.ProfilesValid := by
  change ∀ j : Fin 16, (retention4609.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch656.valid26254
  · exact MergedCutProfiles.Batch656.valid26248
  · exact MergedCutProfiles.Batch464.valid18578
  · exact MergedCutProfiles.Batch596.valid23843
  · exact MergedCutProfiles.Batch656.valid26255
  · exact MergedCutProfiles.Batch464.valid18579
  · exact MergedCutProfiles.Batch596.valid23846
  · exact MergedCutProfiles.Batch335.valid13413
  · exact MergedCutProfiles.Batch464.valid18580
  · exact MergedCutProfiles.Batch656.valid26256
  · exact MergedCutProfiles.Batch464.valid18596
  · exact MergedCutProfiles.Batch464.valid18581
  · exact MergedCutProfiles.Batch336.valid13442
  · exact MergedCutProfiles.Batch656.valid26257
  · exact MergedCutProfiles.Batch464.valid18582
  · exact MergedCutProfiles.Batch464.valid18591
theorem numericValid4609 : retention4609.NumericValid := by decide +kernel
def certificate4609 : RatCutBinCertificate := ⟨⟨retention4609,(928424619889688411/500000000000000000),(9018985876591161/200000000000000000),(4968587493102325573/500000000000000000),(2051325527390199155699/40000000000000000),(58871974151372153/25000000000000000)⟩,(999965318181749223/1000000000000000000),(210332987016814247/500000000000000000),(107535922244391593/500000000000000000),(14733868595249981/100000000000000000)⟩
theorem valid4609 : certificate4609.Valid := by decide +kernel
theorem sound4609 : certificate4609.Sound := rat_cut_bin_certificate_sound certificate4609 profilesValid4609 numericValid4609 valid4609

def retention4610 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(64000000000000000000/5134451270410500746393),(2193629522490192573/500000000000000000),(13/10),(243925779993743387788992721844964492521/109681476124509628650000000000000000000),true,MergedCutProfiles.Batch464.profile18582,![MergedCutProfiles.Batch464.profile18582,MergedCutProfiles.Batch596.profile23858,MergedCutProfiles.Batch656.profile26258,MergedCutProfiles.Batch464.profile18595,MergedCutProfiles.Batch335.profile13421,MergedCutProfiles.Batch656.profile26259,MergedCutProfiles.Batch336.profile13446,MergedCutProfiles.Batch465.profile18605,MergedCutProfiles.Batch048.profile1944,MergedCutProfiles.Batch596.profile23861,MergedCutProfiles.Batch047.profile1913,MergedCutProfiles.Batch656.profile26260,MergedCutProfiles.Batch656.profile26261,MergedCutProfiles.Batch656.profile26262,MergedCutProfiles.Batch047.profile1888,MergedCutProfiles.Batch048.profile1936]⟩
theorem profilesValid4610 : retention4610.ProfilesValid := by
  change ∀ j : Fin 16, (retention4610.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch464.valid18582
  · exact MergedCutProfiles.Batch596.valid23858
  · exact MergedCutProfiles.Batch656.valid26258
  · exact MergedCutProfiles.Batch464.valid18595
  · exact MergedCutProfiles.Batch335.valid13421
  · exact MergedCutProfiles.Batch656.valid26259
  · exact MergedCutProfiles.Batch336.valid13446
  · exact MergedCutProfiles.Batch465.valid18605
  · exact MergedCutProfiles.Batch048.valid1944
  · exact MergedCutProfiles.Batch596.valid23861
  · exact MergedCutProfiles.Batch047.valid1913
  · exact MergedCutProfiles.Batch656.valid26260
  · exact MergedCutProfiles.Batch656.valid26261
  · exact MergedCutProfiles.Batch656.valid26262
  · exact MergedCutProfiles.Batch047.valid1888
  · exact MergedCutProfiles.Batch048.valid1936
theorem numericValid4610 : retention4610.NumericValid := by decide +kernel
def certificate4610 : RatCutBinCertificate := ⟨⟨retention4610,(928424619889688411/500000000000000000),(9018985876591161/200000000000000000),(4968587493102325573/500000000000000000),(2051325527390199155699/40000000000000000),(553248151385214967/250000000000000000)⟩,(999965318181749223/1000000000000000000),(281920702483842001/1000000000000000000),(180547018906255679/500000000000000000),(118344729508890217/250000000000000000)⟩
theorem valid4610 : certificate4610.Valid := by decide +kernel
theorem sound4610 : certificate4610.Sound := rat_cut_bin_certificate_sound certificate4610 profilesValid4610 numericValid4610 valid4610

def retention4611 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(1/2),64,1,(255377162141591932400424606355354448199/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch049.profile1962,(fun _ => MergedCutProfiles.Batch049.profile1962)⟩
theorem profilesValid4611 : retention4611.ProfilesValid := by
  exact MergedCutProfiles.Batch049.valid1962
theorem numericValid4611 : retention4611.NumericValid := by decide +kernel
def certificate4611 : RatCutBinCertificate := ⟨⟨retention4611,(928424619889688411/500000000000000000),(9018985876591161/200000000000000000),(4968587493102325573/500000000000000000),(2051325527390199155699/40000000000000000),(98914065217556481/100000000000000000)⟩,(999965318181749223/1000000000000000000),(62906348123198013/125000000000000000),(151183636917387983/1000000000000000000),(147260686512364167/1000000000000000000)⟩
theorem valid4611 : certificate4611.Valid := by decide +kernel
theorem sound4611 : certificate4611.Sound := rat_cut_bin_certificate_sound certificate4611 profilesValid4611 numericValid4611 valid4611

def retention4612 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(64000000000000000000/5134451270410500746393),(1286446251076297099/50000000000000000),1,(228564859941066940912384222343448842479/102915700086103767920000000000000000000),false,MergedCutProfiles.Batch656.profile26263,(fun _ => MergedCutProfiles.Batch656.profile26263)⟩
theorem profilesValid4612 : retention4612.ProfilesValid := by
  exact MergedCutProfiles.Batch656.valid26263
theorem numericValid4612 : retention4612.NumericValid := by decide +kernel
def certificate4612 : RatCutBinCertificate := ⟨⟨retention4612,(879613622889688411/500000000000000000),(9018985876591161/200000000000000000),(4968587493102325573/500000000000000000),(2051325527390199155699/40000000000000000),(2212910612690866099/1000000000000000000)⟩,(999967141546336779/1000000000000000000),(734054608493503/31250000000000000),(172695631382085389/200000000000000000),(1759411182532339469/1000000000000000000)⟩
theorem valid4612 : certificate4612.Valid := by decide +kernel
theorem sound4612 : certificate4612.Sound := rat_cut_bin_certificate_sound certificate4612 profilesValid4612 numericValid4612 valid4612

def retention4613 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(1/2),64,1,(255377162141591932400424606355354448199/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch049.profile1962,(fun _ => MergedCutProfiles.Batch049.profile1962)⟩
theorem profilesValid4613 : retention4613.ProfilesValid := by
  exact MergedCutProfiles.Batch049.valid1962
theorem numericValid4613 : retention4613.NumericValid := by decide +kernel
def certificate4613 : RatCutBinCertificate := ⟨⟨retention4613,(879613622889688411/500000000000000000),(9018985876591161/200000000000000000),(4968587493102325573/500000000000000000),(2051325527390199155699/40000000000000000),(989583661078220737/1000000000000000000)⟩,(999967141546336779/1000000000000000000),(52527859456693679/1000000000000000000),(390810680961290553/500000000000000000),(190419209343529601/250000000000000000)⟩
theorem valid4613 : certificate4613.Valid := by decide +kernel
theorem sound4613 : certificate4613.Sound := rat_cut_bin_certificate_sound certificate4613 profilesValid4613 numericValid4613 valid4613

def retention4614 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(676417168949609379/5134451270410500746393),(669719969257038989/1000000000000000000),4,(6346514528038659776642051742255881911/2678879877028155956000000000000000000),false,MergedCutProfiles.Batch656.profile26264,(fun _ => MergedCutProfiles.Batch656.profile26264)⟩
theorem profilesValid4614 : retention4614.ProfilesValid := by
  exact MergedCutProfiles.Batch656.valid26264
theorem numericValid4614 : retention4614.NumericValid := by decide +kernel
def certificate4614 : RatCutBinCertificate := ⟨⟨retention4614,(896463205889688411/500000000000000000),(9018985876591161/200000000000000000),(4968587493102325573/500000000000000000),(2051325527390199155699/40000000000000000),(1168273690521845141/500000000000000000)⟩,(999966512119911761/1000000000000000000),(106702214215727/122070312500000),(8280061984007439/1000000000000000000),(992669964786611/250000000000000000)⟩
theorem valid4614 : certificate4614.Valid := by decide +kernel
theorem sound4614 : certificate4614.Sound := rat_cut_bin_certificate_sound certificate4614 profilesValid4614 numericValid4614 valid4614

def retention4615 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(141035611582266421/733493038630071535199),(676417168949609379/1000000000000000000),4,(6421207107376324744332927721653143087/2705668675798437516000000000000000000),false,MergedCutProfiles.Batch656.profile26265,(fun _ => MergedCutProfiles.Batch656.profile26265)⟩
theorem profilesValid4615 : retention4615.ProfilesValid := by
  exact MergedCutProfiles.Batch656.valid26265
theorem numericValid4615 : retention4615.NumericValid := by decide +kernel
def certificate4615 : RatCutBinCertificate := ⟨⟨retention4615,(896463205889688411/500000000000000000),(9018985876591161/200000000000000000),(4968587493102325573/500000000000000000),(2051325527390199155699/40000000000000000),(1170348488970725043/500000000000000000)⟩,(999966512119911761/1000000000000000000),(8701389539023823/10000000000000000),(8822661508206983/1000000000000000000),(106114579298029/25000000000000000)⟩
theorem valid4615 : certificate4615.Valid := by decide +kernel
theorem sound4615 : certificate4615.Sound := rat_cut_bin_certificate_sound certificate4615 profilesValid4615 numericValid4615 valid4615

def retention4616 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(2009720146370642604/733493038630071535199),(987249281075864947/1000000000000000000),(67/20),(534718219412616624660560436766348070897/225656978531626273600000000000000000000),false,MergedCutProfiles.Batch656.profile26266,(fun _ => MergedCutProfiles.Batch656.profile26266)⟩
theorem profilesValid4616 : retention4616.ProfilesValid := by
  exact MergedCutProfiles.Batch656.valid26266
theorem numericValid4616 : retention4616.NumericValid := by decide +kernel
def certificate4616 : RatCutBinCertificate := ⟨⟨retention4616,(896463205889688411/500000000000000000),(9018985876591161/200000000000000000),(4968587493102325573/500000000000000000),(2051325527390199155699/40000000000000000),(468469952978069907/200000000000000000)⟩,(999966512119911761/1000000000000000000),(158702535687206477/200000000000000000),(5739784412009357/250000000000000000),(2650225887833109/200000000000000000)⟩
theorem valid4616 : certificate4616.Valid := by decide +kernel
theorem sound4616 : certificate4616.Sound := rat_cut_bin_certificate_sound certificate4616 profilesValid4616 numericValid4616 valid4616

def retention4617 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(1/40),(3517010256148624557/250000000000000000),(11/10),(438250837531681017092727604661306753177/200972014637064260400000000000000000000),false,MergedCutProfiles.Batch656.profile26267,(fun _ => MergedCutProfiles.Batch656.profile26267)⟩
theorem profilesValid4617 : retention4617.ProfilesValid := by
  exact MergedCutProfiles.Batch656.valid26267
theorem numericValid4617 : retention4617.NumericValid := by decide +kernel
def certificate4617 : RatCutBinCertificate := ⟨⟨retention4617,(896463205889688411/500000000000000000),(9018985876591161/200000000000000000),(4968587493102325573/500000000000000000),(2051325527390199155699/40000000000000000),(542926525832061369/250000000000000000)⟩,(999966512119911761/1000000000000000000),(689972283061540359/1000000000000000000),(53976345134770241/1000000000000000000),(5906490425904619/62500000000000000)⟩
theorem valid4617 : certificate4617.Valid := by decide +kernel
theorem sound4617 : certificate4617.Sound := rat_cut_bin_certificate_sound certificate4617 profilesValid4617 numericValid4617 valid4617

def retention4618 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(595692881151912386/4803249501802636639505),(141695334191912401/250000000000000000),4,(311864690787702795252413698635739791/141695334191912401000000000000000000),true,MergedCutProfiles.Batch656.profile26268,![MergedCutProfiles.Batch656.profile26268,MergedCutProfiles.Batch656.profile26269,MergedCutProfiles.Batch656.profile26270,MergedCutProfiles.Batch656.profile26271,MergedCutProfiles.Batch596.profile23875,MergedCutProfiles.Batch656.profile26272,MergedCutProfiles.Batch656.profile26273,MergedCutProfiles.Batch656.profile26274,MergedCutProfiles.Batch596.profile23876,MergedCutProfiles.Batch656.profile26275,MergedCutProfiles.Batch656.profile26275,MergedCutProfiles.Batch656.profile26276,MergedCutProfiles.Batch656.profile26277,MergedCutProfiles.Batch596.profile23877,MergedCutProfiles.Batch656.profile26278,MergedCutProfiles.Batch656.profile26278]⟩
theorem profilesValid4618 : retention4618.ProfilesValid := by
  change ∀ j : Fin 16, (retention4618.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch656.valid26268
  · exact MergedCutProfiles.Batch656.valid26269
  · exact MergedCutProfiles.Batch656.valid26270
  · exact MergedCutProfiles.Batch656.valid26271
  · exact MergedCutProfiles.Batch596.valid23875
  · exact MergedCutProfiles.Batch656.valid26272
  · exact MergedCutProfiles.Batch656.valid26273
  · exact MergedCutProfiles.Batch656.valid26274
  · exact MergedCutProfiles.Batch596.valid23876
  · exact MergedCutProfiles.Batch656.valid26275
  · exact MergedCutProfiles.Batch656.valid26275
  · exact MergedCutProfiles.Batch656.valid26276
  · exact MergedCutProfiles.Batch656.valid26277
  · exact MergedCutProfiles.Batch596.valid23877
  · exact MergedCutProfiles.Batch656.valid26278
  · exact MergedCutProfiles.Batch656.valid26278
theorem numericValid4618 : retention4618.NumericValid := by decide +kernel
def certificate4618 : RatCutBinCertificate := ⟨⟨retention4618,(1860062754391343549/1000000000000000000),(481579510880593/10000000000000000),(10080661328367137021/1000000000000000000),(24334652116046352788149/500000000000000000),(2165408397615670811/1000000000000000000)⟩,(499981752498362213/500000000000000000),(711401153266796711/1000000000000000000),(2317669043867679/50000000000000000),(5063917963299717/250000000000000000)⟩
theorem valid4618 : certificate4618.Valid := by decide +kernel
theorem sound4618 : certificate4618.Sound := rat_cut_bin_certificate_sound certificate4618 profilesValid4618 numericValid4618 valid4618

def retention4619 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(237241127600000000/960649900360527327901),(297846440575956193/500000000000000000),4,(5386973869631404085830835054412822567/2382771524607649544000000000000000000),true,MergedCutProfiles.Batch656.profile26269,![MergedCutProfiles.Batch656.profile26269,MergedCutProfiles.Batch656.profile26271,MergedCutProfiles.Batch656.profile26272,MergedCutProfiles.Batch656.profile26274,MergedCutProfiles.Batch596.profile23876,MergedCutProfiles.Batch656.profile26276,MergedCutProfiles.Batch596.profile23877,MergedCutProfiles.Batch656.profile26278,MergedCutProfiles.Batch596.profile23878,MergedCutProfiles.Batch597.profile23885,MergedCutProfiles.Batch465.profile18610,MergedCutProfiles.Batch596.profile23879,MergedCutProfiles.Batch656.profile26279,MergedCutProfiles.Batch597.profile23880,MergedCutProfiles.Batch597.profile23886,MergedCutProfiles.Batch597.profile23881]⟩
theorem profilesValid4619 : retention4619.ProfilesValid := by
  change ∀ j : Fin 16, (retention4619.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch656.valid26269
  · exact MergedCutProfiles.Batch656.valid26271
  · exact MergedCutProfiles.Batch656.valid26272
  · exact MergedCutProfiles.Batch656.valid26274
  · exact MergedCutProfiles.Batch596.valid23876
  · exact MergedCutProfiles.Batch656.valid26276
  · exact MergedCutProfiles.Batch596.valid23877
  · exact MergedCutProfiles.Batch656.valid26278
  · exact MergedCutProfiles.Batch596.valid23878
  · exact MergedCutProfiles.Batch597.valid23885
  · exact MergedCutProfiles.Batch465.valid18610
  · exact MergedCutProfiles.Batch596.valid23879
  · exact MergedCutProfiles.Batch656.valid26279
  · exact MergedCutProfiles.Batch597.valid23880
  · exact MergedCutProfiles.Batch597.valid23886
  · exact MergedCutProfiles.Batch597.valid23881
theorem numericValid4619 : retention4619.NumericValid := by decide +kernel
def certificate4619 : RatCutBinCertificate := ⟨⟨retention4619,(1860062754391343549/1000000000000000000),(481579510880593/10000000000000000),(10080661328367137021/1000000000000000000),(24334652116046352788149/500000000000000000),(2225257645151758513/1000000000000000000)⟩,(499981752498362213/500000000000000000),(167341866067095911/250000000000000000),(61933645392540033/1000000000000000000),(13965871523397549/500000000000000000)⟩
theorem valid4619 : certificate4619.Valid := by decide +kernel
theorem sound4619 : certificate4619.Sound := rat_cut_bin_certificate_sound certificate4619 profilesValid4619 numericValid4619 valid4619

def certificates : List RatCutBinCertificate := [certificate4608,certificate4609,certificate4610,certificate4611,certificate4612,certificate4613,certificate4614,certificate4615,certificate4616,certificate4617,certificate4618,certificate4619]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4608,List.forall_mem_cons.mpr ⟨sound4609,List.forall_mem_cons.mpr ⟨sound4610,List.forall_mem_cons.mpr ⟨sound4611,List.forall_mem_cons.mpr ⟨sound4612,List.forall_mem_cons.mpr ⟨sound4613,List.forall_mem_cons.mpr ⟨sound4614,List.forall_mem_cons.mpr ⟨sound4615,List.forall_mem_cons.mpr ⟨sound4616,List.forall_mem_cons.mpr ⟨sound4617,List.forall_mem_cons.mpr ⟨sound4618,List.forall_mem_cons.mpr ⟨sound4619,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch384
