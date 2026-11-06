import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch045
import Cycle12.MergedCutProfiles.Batch046
import Cycle12.MergedCutProfiles.Batch047
import Cycle12.MergedCutProfiles.Batch048
import Cycle12.MergedCutProfiles.Batch049
import Cycle12.MergedCutProfiles.Batch333
import Cycle12.MergedCutProfiles.Batch334
import Cycle12.MergedCutProfiles.Batch335
import Cycle12.MergedCutProfiles.Batch463
import Cycle12.MergedCutProfiles.Batch464
import Cycle12.MergedCutProfiles.Batch595
import Cycle12.MergedCutProfiles.Batch596

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch326

def retention3912 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(587970221307359533/1099811408547601213188),(559433490908499097/1000000000000000000),4,(4874039353607290967964537482071289319/2237733963633996388000000000000000000),true,MergedCutProfiles.Batch595.profile23816,![MergedCutProfiles.Batch595.profile23816,MergedCutProfiles.Batch595.profile23817,MergedCutProfiles.Batch595.profile23818,MergedCutProfiles.Batch595.profile23819,MergedCutProfiles.Batch595.profile23820,MergedCutProfiles.Batch595.profile23821,MergedCutProfiles.Batch595.profile23822,MergedCutProfiles.Batch464.profile18563,MergedCutProfiles.Batch463.profile18553,MergedCutProfiles.Batch595.profile23823,MergedCutProfiles.Batch595.profile23824,MergedCutProfiles.Batch595.profile23825,MergedCutProfiles.Batch595.profile23826,MergedCutProfiles.Batch595.profile23827,MergedCutProfiles.Batch595.profile23828,MergedCutProfiles.Batch464.profile18564]⟩
theorem profilesValid3912 : retention3912.ProfilesValid := by
  change ∀ j : Fin 16, (retention3912.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch595.valid23816
  · exact MergedCutProfiles.Batch595.valid23817
  · exact MergedCutProfiles.Batch595.valid23818
  · exact MergedCutProfiles.Batch595.valid23819
  · exact MergedCutProfiles.Batch595.valid23820
  · exact MergedCutProfiles.Batch595.valid23821
  · exact MergedCutProfiles.Batch595.valid23822
  · exact MergedCutProfiles.Batch464.valid18563
  · exact MergedCutProfiles.Batch463.valid18553
  · exact MergedCutProfiles.Batch595.valid23823
  · exact MergedCutProfiles.Batch595.valid23824
  · exact MergedCutProfiles.Batch595.valid23825
  · exact MergedCutProfiles.Batch595.valid23826
  · exact MergedCutProfiles.Batch595.valid23827
  · exact MergedCutProfiles.Batch595.valid23828
  · exact MergedCutProfiles.Batch464.valid18564
theorem numericValid3912 : retention3912.NumericValid := by decide +kernel
def certificate3912 : RatCutBinCertificate := ⟨⟨retention3912,(1838399706796521769/1000000000000000000),(42146381475855499/1000000000000000000),(4898400603781243909/500000000000000000),(10829462736502444557451/1000000000000000000),(2146478212096613073/1000000000000000000)⟩,(999836913154546787/1000000000000000000),(370738150496959471/500000000000000000),(9184795306144223/250000000000000000),(15898520854497031/1000000000000000000)⟩
theorem valid3912 : certificate3912.Valid := by decide +kernel
theorem sound3912 : certificate3912.Sound := rat_cut_bin_certificate_sound certificate3912 profilesValid3912 numericValid3912 valid3912

def retention3913 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(97768092000000000/91650950712300101099),(587970221307359533/1000000000000000000),4,(10268801994780250179987829363405077/4593517353963746351562500000000000),true,MergedCutProfiles.Batch595.profile23817,![MergedCutProfiles.Batch595.profile23817,MergedCutProfiles.Batch595.profile23819,MergedCutProfiles.Batch595.profile23821,MergedCutProfiles.Batch464.profile18563,MergedCutProfiles.Batch595.profile23823,MergedCutProfiles.Batch333.profile13346,MergedCutProfiles.Batch595.profile23827,MergedCutProfiles.Batch464.profile18564,MergedCutProfiles.Batch463.profile18555,MergedCutProfiles.Batch334.profile13370,MergedCutProfiles.Batch463.profile18556,MergedCutProfiles.Batch333.profile13347,MergedCutProfiles.Batch595.profile23829,MergedCutProfiles.Batch595.profile23830,MergedCutProfiles.Batch045.profile1813,MergedCutProfiles.Batch333.profile13359]⟩
theorem profilesValid3913 : retention3913.ProfilesValid := by
  change ∀ j : Fin 16, (retention3913.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch595.valid23817
  · exact MergedCutProfiles.Batch595.valid23819
  · exact MergedCutProfiles.Batch595.valid23821
  · exact MergedCutProfiles.Batch464.valid18563
  · exact MergedCutProfiles.Batch595.valid23823
  · exact MergedCutProfiles.Batch333.valid13346
  · exact MergedCutProfiles.Batch595.valid23827
  · exact MergedCutProfiles.Batch464.valid18564
  · exact MergedCutProfiles.Batch463.valid18555
  · exact MergedCutProfiles.Batch334.valid13370
  · exact MergedCutProfiles.Batch463.valid18556
  · exact MergedCutProfiles.Batch333.valid13347
  · exact MergedCutProfiles.Batch595.valid23829
  · exact MergedCutProfiles.Batch595.valid23830
  · exact MergedCutProfiles.Batch045.valid1813
  · exact MergedCutProfiles.Batch333.valid13359
theorem numericValid3913 : retention3913.NumericValid := by decide +kernel
def certificate3913 : RatCutBinCertificate := ⟨⟨retention3913,(1838399706796521769/1000000000000000000),(42146381475855499/1000000000000000000),(4898400603781243909/500000000000000000),(10829462736502444557451/1000000000000000000),(2203863041078085449/1000000000000000000)⟩,(999836913154546787/1000000000000000000),(87277414579792447/125000000000000000),(25482465588860221/500000000000000000),(22745843623175613/1000000000000000000)⟩
theorem valid3913 : certificate3913.Valid := by decide +kernel
theorem sound3913 : certificate3913.Sound := rat_cut_bin_certificate_sound certificate3913 profilesValid3913 numericValid3913 valid3913

def retention3914 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(1543578028052172511/1099811408547601213188),(73326069/62500000),(27/10),(11088251911325188817237994436275849911/4692868416000000000000000000000000000),true,MergedCutProfiles.Batch595.profile23831,![MergedCutProfiles.Batch595.profile23831,MergedCutProfiles.Batch595.profile23832,MergedCutProfiles.Batch464.profile18563,MergedCutProfiles.Batch595.profile23833,MergedCutProfiles.Batch595.profile23826,MergedCutProfiles.Batch333.profile13358,MergedCutProfiles.Batch463.profile18555,MergedCutProfiles.Batch595.profile23834,MergedCutProfiles.Batch333.profile13347,MergedCutProfiles.Batch595.profile23829,MergedCutProfiles.Batch595.profile23835,MergedCutProfiles.Batch333.profile13359,MergedCutProfiles.Batch045.profile1828,MergedCutProfiles.Batch046.profile1841,MergedCutProfiles.Batch464.profile18566,MergedCutProfiles.Batch595.profile23836]⟩
theorem profilesValid3914 : retention3914.ProfilesValid := by
  change ∀ j : Fin 16, (retention3914.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch595.valid23831
  · exact MergedCutProfiles.Batch595.valid23832
  · exact MergedCutProfiles.Batch464.valid18563
  · exact MergedCutProfiles.Batch595.valid23833
  · exact MergedCutProfiles.Batch595.valid23826
  · exact MergedCutProfiles.Batch333.valid13358
  · exact MergedCutProfiles.Batch463.valid18555
  · exact MergedCutProfiles.Batch595.valid23834
  · exact MergedCutProfiles.Batch333.valid13347
  · exact MergedCutProfiles.Batch595.valid23829
  · exact MergedCutProfiles.Batch595.valid23835
  · exact MergedCutProfiles.Batch333.valid13359
  · exact MergedCutProfiles.Batch045.valid1828
  · exact MergedCutProfiles.Batch046.valid1841
  · exact MergedCutProfiles.Batch464.valid18566
  · exact MergedCutProfiles.Batch595.valid23836
theorem numericValid3914 : retention3914.NumericValid := by decide +kernel
def certificate3914 : RatCutBinCertificate := ⟨⟨retention3914,(1838399706796521769/1000000000000000000),(42146381475855499/1000000000000000000),(4898400603781243909/500000000000000000),(10829462736502444557451/1000000000000000000),(2341433680746167941/1000000000000000000)⟩,(999836913154546787/1000000000000000000),(17469681037819527/40000000000000000),(201454953816379749/1000000000000000000),(68563972690689317/500000000000000000)⟩
theorem valid3914 : certificate3914.Valid := by decide +kernel
theorem sound3914 : certificate3914.Sound := rat_cut_bin_certificate_sound certificate3914 profilesValid3914 numericValid3914 valid3914

def retention3915 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(16000000000000000000/274952852136900303297),(1543578028052172511/1000000000000000000),(11/5),(78643231598171124112050259939354994151/38589450701304312775000000000000000000),false,MergedCutProfiles.Batch595.profile23837,(fun _ => MergedCutProfiles.Batch595.profile23837)⟩
theorem profilesValid3915 : retention3915.ProfilesValid := by
  exact MergedCutProfiles.Batch595.valid23837
theorem numericValid3915 : retention3915.NumericValid := by decide +kernel
def certificate3915 : RatCutBinCertificate := ⟨⟨retention3915,(1838399706796521769/1000000000000000000),(42146381475855499/1000000000000000000),(4898400603781243909/500000000000000000),(10829462736502444557451/1000000000000000000),(2020546791932136447/1000000000000000000)⟩,(999836913154546787/1000000000000000000),(222260712872953691/500000000000000000),(195079372934810249/1000000000000000000),(14099956885680393/100000000000000000)⟩
theorem valid3915 : certificate3915.Valid := by decide +kernel
theorem sound3915 : certificate3915.Sound := rat_cut_bin_certificate_sound certificate3915 profilesValid3915 numericValid3915 valid3915

def retention3916 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(1/2),64,1,(63844131674568793248260656909441386031/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch046.profile1873,(fun _ => MergedCutProfiles.Batch046.profile1873)⟩
theorem profilesValid3916 : retention3916.ProfilesValid := by
  exact MergedCutProfiles.Batch046.valid1873
theorem numericValid3916 : retention3916.NumericValid := by decide +kernel
def certificate3916 : RatCutBinCertificate := ⟨⟨retention3916,(1838399706796521769/1000000000000000000),(42146381475855499/1000000000000000000),(4898400603781243909/500000000000000000),(10829462736502444557451/1000000000000000000),(247413914889956479/250000000000000000)⟩,(999836913154546787/1000000000000000000),(129724322499988191/250000000000000000),(7034023634312613/50000000000000000),(68541277894768901/500000000000000000)⟩
theorem valid3916 : certificate3916.Valid := by decide +kernel
theorem sound3916 : certificate3916.Sound := rat_cut_bin_certificate_sound certificate3916 profilesValid3916 numericValid3916 valid3916

def retention3917 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(16000000000000000000/274952852136900303297),(5402923156193151391/250000000000000000),1,(539094894132566694871973744282706681/270146157809657569550000000000000000),false,MergedCutProfiles.Batch595.profile23837,(fun _ => MergedCutProfiles.Batch595.profile23837)⟩
theorem profilesValid3917 : retention3917.ProfilesValid := by
  exact MergedCutProfiles.Batch595.valid23837
theorem numericValid3917 : retention3917.NumericValid := by decide +kernel
def certificate3917 : RatCutBinCertificate := ⟨⟨retention3917,(1807010124796521769/1000000000000000000),(42146381475855499/1000000000000000000),(4898400603781243909/500000000000000000),(10829462736502444557451/1000000000000000000),(124237102873263661/62500000000000000)⟩,(999839697783737471/1000000000000000000),(15920717922626633/500000000000000000),(419459393647542723/500000000000000000),(11928781581885467/7812500000000000)⟩
theorem valid3917 : certificate3917.Valid := by decide +kernel
theorem sound3917 : certificate3917.Sound := rat_cut_bin_certificate_sound certificate3917 profilesValid3917 numericValid3917 valid3917

def retention3918 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(1/2),64,1,(63844131674568793248260656909441386031/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch046.profile1873,(fun _ => MergedCutProfiles.Batch046.profile1873)⟩
theorem profilesValid3918 : retention3918.ProfilesValid := by
  exact MergedCutProfiles.Batch046.valid1873
theorem numericValid3918 : retention3918.NumericValid := by decide +kernel
def certificate3918 : RatCutBinCertificate := ⟨⟨retention3918,(1807010124796521769/1000000000000000000),(42146381475855499/1000000000000000000),(4898400603781243909/500000000000000000),(10829462736502444557451/1000000000000000000),(494895349644293137/500000000000000000)⟩,(999839697783737471/1000000000000000000),(63947058602711963/1000000000000000000),(2349904613539689/3125000000000000),(732838284419640943/1000000000000000000)⟩
theorem valid3918 : certificate3918.Valid := by decide +kernel
theorem sound3918 : certificate3918.Sound := rat_cut_bin_certificate_sound certificate3918 profilesValid3918 numericValid3918 valid3918

def retention3919 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(284208043723998157/513445127041050074639),(140697051348513939/250000000000000000),4,(410177304174543223318737253402572741/187596068464685252000000000000000000),true,MergedCutProfiles.Batch595.profile23838,![MergedCutProfiles.Batch595.profile23838,MergedCutProfiles.Batch595.profile23839,MergedCutProfiles.Batch596.profile23840,MergedCutProfiles.Batch596.profile23841,MergedCutProfiles.Batch596.profile23842,MergedCutProfiles.Batch596.profile23843,MergedCutProfiles.Batch596.profile23844,MergedCutProfiles.Batch464.profile18590,MergedCutProfiles.Batch464.profile18579,MergedCutProfiles.Batch596.profile23845,MergedCutProfiles.Batch596.profile23846,MergedCutProfiles.Batch596.profile23847,MergedCutProfiles.Batch596.profile23848,MergedCutProfiles.Batch596.profile23849,MergedCutProfiles.Batch596.profile23850,MergedCutProfiles.Batch335.profile13429]⟩
theorem profilesValid3919 : retention3919.ProfilesValid := by
  change ∀ j : Fin 16, (retention3919.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch595.valid23838
  · exact MergedCutProfiles.Batch595.valid23839
  · exact MergedCutProfiles.Batch596.valid23840
  · exact MergedCutProfiles.Batch596.valid23841
  · exact MergedCutProfiles.Batch596.valid23842
  · exact MergedCutProfiles.Batch596.valid23843
  · exact MergedCutProfiles.Batch596.valid23844
  · exact MergedCutProfiles.Batch464.valid18590
  · exact MergedCutProfiles.Batch464.valid18579
  · exact MergedCutProfiles.Batch596.valid23845
  · exact MergedCutProfiles.Batch596.valid23846
  · exact MergedCutProfiles.Batch596.valid23847
  · exact MergedCutProfiles.Batch596.valid23848
  · exact MergedCutProfiles.Batch596.valid23849
  · exact MergedCutProfiles.Batch596.valid23850
  · exact MergedCutProfiles.Batch335.valid13429
theorem numericValid3919 : retention3919.NumericValid := by decide +kernel
def certificate3919 : RatCutBinCertificate := ⟨⟨retention3919,(1843023411896884107/1000000000000000000),(9018985876591161/200000000000000000),(124214676063420639/12500000000000000),(1282078338356391269001/125000000000000000),(2153037355557687989/1000000000000000000)⟩,(999827881030328191/1000000000000000000),(367944320341832801/500000000000000000),(9607906227530257/250000000000000000),(16690985730769833/1000000000000000000)⟩
theorem valid3919 : certificate3919.Valid := by decide +kernel
theorem sound3919 : certificate3919.Sound := rat_cut_bin_certificate_sound certificate3919 profilesValid3919 numericValid3919 valid3919

def retention3920 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(589575201000000000/513445127041050074639),(284208043723998157/500000000000000000),4,(70245083975494536361/32000000000000000000),true,MergedCutProfiles.Batch595.profile23839,![MergedCutProfiles.Batch595.profile23839,MergedCutProfiles.Batch596.profile23841,MergedCutProfiles.Batch596.profile23851,MergedCutProfiles.Batch464.profile18590,MergedCutProfiles.Batch596.profile23845,MergedCutProfiles.Batch335.profile13413,MergedCutProfiles.Batch596.profile23849,MergedCutProfiles.Batch464.profile18596,MergedCutProfiles.Batch596.profile23852,MergedCutProfiles.Batch596.profile23853,MergedCutProfiles.Batch464.profile18582,MergedCutProfiles.Batch335.profile13414,MergedCutProfiles.Batch596.profile23854,MergedCutProfiles.Batch596.profile23855,MergedCutProfiles.Batch596.profile23856,MergedCutProfiles.Batch464.profile18597]⟩
theorem profilesValid3920 : retention3920.ProfilesValid := by
  change ∀ j : Fin 16, (retention3920.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch595.valid23839
  · exact MergedCutProfiles.Batch596.valid23841
  · exact MergedCutProfiles.Batch596.valid23851
  · exact MergedCutProfiles.Batch464.valid18590
  · exact MergedCutProfiles.Batch596.valid23845
  · exact MergedCutProfiles.Batch335.valid13413
  · exact MergedCutProfiles.Batch596.valid23849
  · exact MergedCutProfiles.Batch464.valid18596
  · exact MergedCutProfiles.Batch596.valid23852
  · exact MergedCutProfiles.Batch596.valid23853
  · exact MergedCutProfiles.Batch464.valid18582
  · exact MergedCutProfiles.Batch335.valid13414
  · exact MergedCutProfiles.Batch596.valid23854
  · exact MergedCutProfiles.Batch596.valid23855
  · exact MergedCutProfiles.Batch596.valid23856
  · exact MergedCutProfiles.Batch464.valid18597
theorem numericValid3920 : retention3920.NumericValid := by decide +kernel
def certificate3920 : RatCutBinCertificate := ⟨⟨retention3920,(1843023411896884107/1000000000000000000),(9018985876591161/200000000000000000),(124214676063420639/12500000000000000),(1282078338356391269001/125000000000000000),(1080852111900956757/500000000000000000)⟩,(999827881030328191/1000000000000000000),(1455993142265711/2000000000000000),(40894408503463493/1000000000000000000),(17852458541643869/1000000000000000000)⟩
theorem valid3920 : certificate3920.Valid := by decide +kernel
theorem sound3920 : certificate3920.Sound := rat_cut_bin_certificate_sound certificate3920 profilesValid3920 numericValid3920 valid3920

def retention3921 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(2289067980540595915/1026890254082100149278),(589575201/500000000),(27/10),(18818375904442157457/8000000000000000000),true,MergedCutProfiles.Batch596.profile23841,![MergedCutProfiles.Batch596.profile23841,MergedCutProfiles.Batch464.profile18590,MergedCutProfiles.Batch596.profile23847,MergedCutProfiles.Batch335.profile13429,MergedCutProfiles.Batch596.profile23853,MergedCutProfiles.Batch464.profile18591,MergedCutProfiles.Batch464.profile18583,MergedCutProfiles.Batch335.profile13430,MergedCutProfiles.Batch596.profile23857,MergedCutProfiles.Batch048.profile1929,MergedCutProfiles.Batch596.profile23858,MergedCutProfiles.Batch335.profile13431,MergedCutProfiles.Batch596.profile23859,MergedCutProfiles.Batch596.profile23860,MergedCutProfiles.Batch464.profile18587,MergedCutProfiles.Batch335.profile13432]⟩
theorem profilesValid3921 : retention3921.ProfilesValid := by
  change ∀ j : Fin 16, (retention3921.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch596.valid23841
  · exact MergedCutProfiles.Batch464.valid18590
  · exact MergedCutProfiles.Batch596.valid23847
  · exact MergedCutProfiles.Batch335.valid13429
  · exact MergedCutProfiles.Batch596.valid23853
  · exact MergedCutProfiles.Batch464.valid18591
  · exact MergedCutProfiles.Batch464.valid18583
  · exact MergedCutProfiles.Batch335.valid13430
  · exact MergedCutProfiles.Batch596.valid23857
  · exact MergedCutProfiles.Batch048.valid1929
  · exact MergedCutProfiles.Batch596.valid23858
  · exact MergedCutProfiles.Batch335.valid13431
  · exact MergedCutProfiles.Batch596.valid23859
  · exact MergedCutProfiles.Batch596.valid23860
  · exact MergedCutProfiles.Batch464.valid18587
  · exact MergedCutProfiles.Batch335.valid13432
theorem numericValid3921 : retention3921.NumericValid := by decide +kernel
def certificate3921 : RatCutBinCertificate := ⟨⟨retention3921,(1843023411896884107/1000000000000000000),(9018985876591161/200000000000000000),(124214676063420639/12500000000000000),(1282078338356391269001/125000000000000000),(2329715111495485009/1000000000000000000)⟩,(999827881030328191/1000000000000000000),(10950059152581273/25000000000000000),(25051588237160297/125000000000000000),(17003378684145093/125000000000000000)⟩
theorem valid3921 : certificate3921.Valid := by decide +kernel
theorem sound3921 : certificate3921.Sound := rat_cut_bin_certificate_sound certificate3921 profilesValid3921 numericValid3921 valid3921

def retention3922 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(32000000000000000000/513445127041050074639),(457813596108119183/200000000000000000),(17/10),(514841016978813838883/256000000000000000000),true,MergedCutProfiles.Batch335.profile13421,![MergedCutProfiles.Batch335.profile13421,MergedCutProfiles.Batch596.profile23861,MergedCutProfiles.Batch047.profile1888,MergedCutProfiles.Batch596.profile23862,MergedCutProfiles.Batch596.profile23863,MergedCutProfiles.Batch596.profile23864,MergedCutProfiles.Batch596.profile23865,MergedCutProfiles.Batch596.profile23866,MergedCutProfiles.Batch048.profile1952,MergedCutProfiles.Batch596.profile23867,MergedCutProfiles.Batch596.profile23868,MergedCutProfiles.Batch596.profile23869,MergedCutProfiles.Batch596.profile23870,MergedCutProfiles.Batch596.profile23871,MergedCutProfiles.Batch596.profile23872,MergedCutProfiles.Batch596.profile23873]⟩
theorem profilesValid3922 : retention3922.ProfilesValid := by
  change ∀ j : Fin 16, (retention3922.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch335.valid13421
  · exact MergedCutProfiles.Batch596.valid23861
  · exact MergedCutProfiles.Batch047.valid1888
  · exact MergedCutProfiles.Batch596.valid23862
  · exact MergedCutProfiles.Batch596.valid23863
  · exact MergedCutProfiles.Batch596.valid23864
  · exact MergedCutProfiles.Batch596.valid23865
  · exact MergedCutProfiles.Batch596.valid23866
  · exact MergedCutProfiles.Batch048.valid1952
  · exact MergedCutProfiles.Batch596.valid23867
  · exact MergedCutProfiles.Batch596.valid23868
  · exact MergedCutProfiles.Batch596.valid23869
  · exact MergedCutProfiles.Batch596.valid23870
  · exact MergedCutProfiles.Batch596.valid23871
  · exact MergedCutProfiles.Batch596.valid23872
  · exact MergedCutProfiles.Batch596.valid23873
theorem numericValid3922 : retention3922.NumericValid := by decide +kernel
def certificate3922 : RatCutBinCertificate := ⟨⟨retention3922,(1843023411896884107/1000000000000000000),(9018985876591161/200000000000000000),(124214676063420639/12500000000000000),(1282078338356391269001/125000000000000000),(79875180302789971/40000000000000000)⟩,(999827881030328191/1000000000000000000),(385967645758097673/1000000000000000000),(24658843922150979/100000000000000000),(222448892814019519/1000000000000000000)⟩
theorem valid3922 : certificate3922.Valid := by decide +kernel
theorem sound3922 : certificate3922.Sound := rat_cut_bin_certificate_sound certificate3922 profilesValid3922 numericValid3922 valid3922

def retention3923 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(1/2),64,1,(255377162141591932400424606355354448199/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch049.profile1962,(fun _ => MergedCutProfiles.Batch049.profile1962)⟩
theorem profilesValid3923 : retention3923.ProfilesValid := by
  exact MergedCutProfiles.Batch049.valid1962
theorem numericValid3923 : retention3923.NumericValid := by decide +kernel
def certificate3923 : RatCutBinCertificate := ⟨⟨retention3923,(1843023411896884107/1000000000000000000),(9018985876591161/200000000000000000),(124214676063420639/12500000000000000),(1282078338356391269001/125000000000000000),(989203392606026523/1000000000000000000)⟩,(999827881030328191/1000000000000000000),(520574317486809321/1000000000000000000),(139582968570940309/1000000000000000000),(33987667336972751/250000000000000000)⟩
theorem valid3923 : certificate3923.Valid := by decide +kernel
theorem sound3923 : certificate3923.Sound := rat_cut_bin_certificate_sound certificate3923 profilesValid3923 numericValid3923 valid3923

def certificates : List RatCutBinCertificate := [certificate3912,certificate3913,certificate3914,certificate3915,certificate3916,certificate3917,certificate3918,certificate3919,certificate3920,certificate3921,certificate3922,certificate3923]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3912,List.forall_mem_cons.mpr ⟨sound3913,List.forall_mem_cons.mpr ⟨sound3914,List.forall_mem_cons.mpr ⟨sound3915,List.forall_mem_cons.mpr ⟨sound3916,List.forall_mem_cons.mpr ⟨sound3917,List.forall_mem_cons.mpr ⟨sound3918,List.forall_mem_cons.mpr ⟨sound3919,List.forall_mem_cons.mpr ⟨sound3920,List.forall_mem_cons.mpr ⟨sound3921,List.forall_mem_cons.mpr ⟨sound3922,List.forall_mem_cons.mpr ⟨sound3923,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch326
