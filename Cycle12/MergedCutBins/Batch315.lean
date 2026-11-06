import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch017
import Cycle12.MergedCutProfiles.Batch018
import Cycle12.MergedCutProfiles.Batch019
import Cycle12.MergedCutProfiles.Batch575
import Cycle12.MergedCutProfiles.Batch576
import Cycle12.MergedCutProfiles.Batch577

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch315

def retention3780 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(8000000000000000000/555204668868246689109),(2556638215227126553/500000000000000000),(6/5),(34731805401264918779457416858997454237/15978988845169540956250000000000000000),true,MergedCutProfiles.Batch017.profile707,![MergedCutProfiles.Batch017.profile707,MergedCutProfiles.Batch017.profile712,MergedCutProfiles.Batch017.profile717,MergedCutProfiles.Batch575.profile23030,MergedCutProfiles.Batch018.profile740,MergedCutProfiles.Batch575.profile23031,MergedCutProfiles.Batch575.profile23032,MergedCutProfiles.Batch575.profile23033,MergedCutProfiles.Batch575.profile23034,MergedCutProfiles.Batch575.profile23035,MergedCutProfiles.Batch575.profile23036,MergedCutProfiles.Batch575.profile23037,MergedCutProfiles.Batch575.profile23038,MergedCutProfiles.Batch575.profile23039,MergedCutProfiles.Batch576.profile23040,MergedCutProfiles.Batch576.profile23041]⟩
theorem profilesValid3780 : retention3780.ProfilesValid := by
  change ∀ j : Fin 16, (retention3780.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch017.valid707
  · exact MergedCutProfiles.Batch017.valid712
  · exact MergedCutProfiles.Batch017.valid717
  · exact MergedCutProfiles.Batch575.valid23030
  · exact MergedCutProfiles.Batch018.valid740
  · exact MergedCutProfiles.Batch575.valid23031
  · exact MergedCutProfiles.Batch575.valid23032
  · exact MergedCutProfiles.Batch575.valid23033
  · exact MergedCutProfiles.Batch575.valid23034
  · exact MergedCutProfiles.Batch575.valid23035
  · exact MergedCutProfiles.Batch575.valid23036
  · exact MergedCutProfiles.Batch575.valid23037
  · exact MergedCutProfiles.Batch575.valid23038
  · exact MergedCutProfiles.Batch575.valid23039
  · exact MergedCutProfiles.Batch576.valid23040
  · exact MergedCutProfiles.Batch576.valid23041
theorem numericValid3780 : retention3780.NumericValid := by decide +kernel
def certificate3780 : RatCutBinCertificate := ⟨⟨retention3780,(360673200239784127/200000000000000000),(1060946273715283/100000000000000000),(200259423284588121/25000000000000000),(7149002648276999136387/200000000000000000),(2170725998700086699/1000000000000000000)⟩,(999950017947899449/1000000000000000000),(6434691948856697/25000000000000000),(393222747502793373/1000000000000000000),(549329424038509073/1000000000000000000)⟩
theorem valid3780 : certificate3780.Valid := by decide +kernel
theorem sound3780 : certificate3780.Sound := rat_cut_bin_certificate_sound certificate3780 profilesValid3780 numericValid3780 valid3780

def retention3781 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(1/2),64,1,(255370070520985369056173916463207973031/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch019.profile763,(fun _ => MergedCutProfiles.Batch019.profile763)⟩
theorem profilesValid3781 : retention3781.ProfilesValid := by
  exact MergedCutProfiles.Batch019.valid763
theorem numericValid3781 : retention3781.NumericValid := by decide +kernel
def certificate3781 : RatCutBinCertificate := ⟨⟨retention3781,(360673200239784127/200000000000000000),(1060946273715283/100000000000000000),(200259423284588121/25000000000000000),(7149002648276999136387/200000000000000000),(99515084306857781/100000000000000000)⟩,(999950017947899449/1000000000000000000),(459236414451946207/1000000000000000000),(91695065660469249/500000000000000000),(718789939094887/4000000000000000)⟩
theorem valid3781 : certificate3781.Valid := by decide +kernel
theorem sound3781 : certificate3781.Sound := rat_cut_bin_certificate_sound certificate3781 profilesValid3781 numericValid3781 valid3781

def retention3782 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(8000000000000000000/555204668868246689109),(17649339354736071723/1000000000000000000),1,(153206225955616148746106827796675374691/70597357418944286892000000000000000000),false,MergedCutProfiles.Batch576.profile23042,(fun _ => MergedCutProfiles.Batch576.profile23042)⟩
theorem profilesValid3782 : retention3782.ProfilesValid := by
  exact MergedCutProfiles.Batch576.valid23042
theorem numericValid3782 : retention3782.NumericValid := by decide +kernel
def certificate3782 : RatCutBinCertificate := ⟨⟨retention3782,(355207338439784127/200000000000000000),(1060946273715283/100000000000000000),(200259423284588121/25000000000000000),(7149002648276999136387/200000000000000000),(2167788788594687013/1000000000000000000)⟩,(199990155081354281/200000000000000000),(2026419827181869/62500000000000000),(209310336285843521/250000000000000000),(1616342418504475653/1000000000000000000)⟩
theorem valid3782 : certificate3782.Valid := by decide +kernel
theorem sound3782 : certificate3782.Sound := rat_cut_bin_certificate_sound certificate3782 profilesValid3782 numericValid3782 valid3782

def retention3783 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(1/2),64,1,(255370070520985369056173916463207973031/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch019.profile763,(fun _ => MergedCutProfiles.Batch019.profile763)⟩
theorem profilesValid3783 : retention3783.ProfilesValid := by
  exact MergedCutProfiles.Batch019.valid763
theorem numericValid3783 : retention3783.NumericValid := by decide +kernel
def certificate3783 : RatCutBinCertificate := ⟨⟨retention3783,(355207338439784127/200000000000000000),(1060946273715283/100000000000000000),(200259423284588121/25000000000000000),(7149002648276999136387/200000000000000000),(199037407955616599/200000000000000000)⟩,(199990155081354281/200000000000000000),(70625520739585219/1000000000000000000),(735228101868857861/1000000000000000000),(90056285849358149/125000000000000000)⟩
theorem valid3783 : certificate3783.Valid := by decide +kernel
theorem sound3783 : certificate3783.Sound := rat_cut_bin_certificate_sound certificate3783 profilesValid3783 numericValid3783 valid3783

def retention3784 : RatCutRetentionCertificate := ⟨(2/125),(33/2000),(16868700107062511/119051006160241798305),(561749627123939413/1000000000000000000),4,(4903627268884634319273369835360686063/2246998508495757652000000000000000000),true,MergedCutProfiles.Batch576.profile23043,![MergedCutProfiles.Batch576.profile23043,MergedCutProfiles.Batch576.profile23044,MergedCutProfiles.Batch576.profile23045,MergedCutProfiles.Batch576.profile23046,MergedCutProfiles.Batch576.profile23047,MergedCutProfiles.Batch576.profile23048,MergedCutProfiles.Batch576.profile23049,MergedCutProfiles.Batch576.profile23050,MergedCutProfiles.Batch576.profile23051,MergedCutProfiles.Batch576.profile23052,MergedCutProfiles.Batch576.profile23053,MergedCutProfiles.Batch576.profile23054,MergedCutProfiles.Batch576.profile23054,MergedCutProfiles.Batch576.profile23055,MergedCutProfiles.Batch576.profile23056,MergedCutProfiles.Batch576.profile23057]⟩
theorem profilesValid3784 : retention3784.ProfilesValid := by
  change ∀ j : Fin 16, (retention3784.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch576.valid23043
  · exact MergedCutProfiles.Batch576.valid23044
  · exact MergedCutProfiles.Batch576.valid23045
  · exact MergedCutProfiles.Batch576.valid23046
  · exact MergedCutProfiles.Batch576.valid23047
  · exact MergedCutProfiles.Batch576.valid23048
  · exact MergedCutProfiles.Batch576.valid23049
  · exact MergedCutProfiles.Batch576.valid23050
  · exact MergedCutProfiles.Batch576.valid23051
  · exact MergedCutProfiles.Batch576.valid23052
  · exact MergedCutProfiles.Batch576.valid23053
  · exact MergedCutProfiles.Batch576.valid23054
  · exact MergedCutProfiles.Batch576.valid23054
  · exact MergedCutProfiles.Batch576.valid23055
  · exact MergedCutProfiles.Batch576.valid23056
  · exact MergedCutProfiles.Batch576.valid23057
theorem numericValid3784 : retention3784.NumericValid := by decide +kernel
def certificate3784 : RatCutBinCertificate := ⟨⟨retention3784,(451474951292943807/250000000000000000),(353207060666619/31250000000000000),(4056640789768914621/500000000000000000),(8471332555205504958753/250000000000000000),(1086118934603137773/500000000000000000)⟩,(499973635476218731/500000000000000000),(673387399988559557/1000000000000000000),(30166000648051461/500000000000000000),(5277000395007817/200000000000000000)⟩
theorem valid3784 : certificate3784.Valid := by decide +kernel
theorem sound3784 : certificate3784.Sound := rat_cut_bin_certificate_sound certificate3784 profilesValid3784 numericValid3784 valid3784

def retention3785 : RatCutRetentionCertificate := ⟨(2/125),(33/2000),(16903087720000000/55557136208112839209),(118080900749437577/200000000000000000),4,(756119086628632376570541049363085193/337374002141250220000000000000000000),true,MergedCutProfiles.Batch576.profile23044,![MergedCutProfiles.Batch576.profile23044,MergedCutProfiles.Batch576.profile23046,MergedCutProfiles.Batch576.profile23058,MergedCutProfiles.Batch576.profile23050,MergedCutProfiles.Batch576.profile23052,MergedCutProfiles.Batch576.profile23054,MergedCutProfiles.Batch576.profile23056,MergedCutProfiles.Batch576.profile23059,MergedCutProfiles.Batch576.profile23060,MergedCutProfiles.Batch576.profile23061,MergedCutProfiles.Batch576.profile23062,MergedCutProfiles.Batch576.profile23063,MergedCutProfiles.Batch576.profile23064,MergedCutProfiles.Batch576.profile23065,MergedCutProfiles.Batch576.profile23066,MergedCutProfiles.Batch576.profile23067]⟩
theorem profilesValid3785 : retention3785.ProfilesValid := by
  change ∀ j : Fin 16, (retention3785.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch576.valid23044
  · exact MergedCutProfiles.Batch576.valid23046
  · exact MergedCutProfiles.Batch576.valid23058
  · exact MergedCutProfiles.Batch576.valid23050
  · exact MergedCutProfiles.Batch576.valid23052
  · exact MergedCutProfiles.Batch576.valid23054
  · exact MergedCutProfiles.Batch576.valid23056
  · exact MergedCutProfiles.Batch576.valid23059
  · exact MergedCutProfiles.Batch576.valid23060
  · exact MergedCutProfiles.Batch576.valid23061
  · exact MergedCutProfiles.Batch576.valid23062
  · exact MergedCutProfiles.Batch576.valid23063
  · exact MergedCutProfiles.Batch576.valid23064
  · exact MergedCutProfiles.Batch576.valid23065
  · exact MergedCutProfiles.Batch576.valid23066
  · exact MergedCutProfiles.Batch576.valid23067
theorem numericValid3785 : retention3785.NumericValid := by decide +kernel
def certificate3785 : RatCutBinCertificate := ⟨⟨retention3785,(451474951292943807/250000000000000000),(353207060666619/31250000000000000),(4056640789768914621/500000000000000000),(8471332555205504958753/250000000000000000),(446225267282516009/200000000000000000)⟩,(499973635476218731/500000000000000000),(633612779015717443/1000000000000000000),(4828672959529319/62500000000000000),(8714464866274779/250000000000000000)⟩
theorem valid3785 : certificate3785.Valid := by decide +kernel
theorem sound3785 : certificate3785.Sound := rat_cut_bin_certificate_sound certificate3785 profilesValid3785 numericValid3785 valid3785

def retention3786 : RatCutRetentionCertificate := ⟨(2/125),(33/2000),(2080625867118722821/1388928405202820980225),(1267731579/1000000000),(51/20),(3965117098901223628325674766221712613/1690308772000000000000000000000000000),true,MergedCutProfiles.Batch576.profile23052,![MergedCutProfiles.Batch576.profile23052,MergedCutProfiles.Batch576.profile23061,MergedCutProfiles.Batch576.profile23066,MergedCutProfiles.Batch576.profile23068,MergedCutProfiles.Batch576.profile23069,MergedCutProfiles.Batch576.profile23070,MergedCutProfiles.Batch576.profile23071,MergedCutProfiles.Batch576.profile23072,MergedCutProfiles.Batch576.profile23073,MergedCutProfiles.Batch576.profile23074,MergedCutProfiles.Batch576.profile23075,MergedCutProfiles.Batch576.profile23076,MergedCutProfiles.Batch576.profile23077,MergedCutProfiles.Batch576.profile23078,MergedCutProfiles.Batch576.profile23079,MergedCutProfiles.Batch577.profile23080]⟩
theorem profilesValid3786 : retention3786.ProfilesValid := by
  change ∀ j : Fin 16, (retention3786.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch576.valid23052
  · exact MergedCutProfiles.Batch576.valid23061
  · exact MergedCutProfiles.Batch576.valid23066
  · exact MergedCutProfiles.Batch576.valid23068
  · exact MergedCutProfiles.Batch576.valid23069
  · exact MergedCutProfiles.Batch576.valid23070
  · exact MergedCutProfiles.Batch576.valid23071
  · exact MergedCutProfiles.Batch576.valid23072
  · exact MergedCutProfiles.Batch576.valid23073
  · exact MergedCutProfiles.Batch576.valid23074
  · exact MergedCutProfiles.Batch576.valid23075
  · exact MergedCutProfiles.Batch576.valid23076
  · exact MergedCutProfiles.Batch576.valid23077
  · exact MergedCutProfiles.Batch576.valid23078
  · exact MergedCutProfiles.Batch576.valid23079
  · exact MergedCutProfiles.Batch577.valid23080
theorem numericValid3786 : retention3786.NumericValid := by decide +kernel
def certificate3786 : RatCutBinCertificate := ⟨⟨retention3786,(451474951292943807/250000000000000000),(353207060666619/31250000000000000),(4056640789768914621/500000000000000000),(8471332555205504958753/250000000000000000),(2339379250538822539/1000000000000000000)⟩,(499973635476218731/500000000000000000),(384514334669698029/1000000000000000000),(123987321612020629/500000000000000000),(88596921352040651/500000000000000000)⟩
theorem valid3786 : certificate3786.Valid := by decide +kernel
theorem sound3786 : certificate3786.Sound := rat_cut_bin_certificate_sound certificate3786 profilesValid3786 numericValid3786 valid3786

def retention3787 : RatCutRetentionCertificate := ⟨(2/125),(33/2000),(2560000000000000000/166671408624338517627),(6241877601356168463/1000000000000000000),(23/20),(7236212544302483606710824295935189861333/3329001387389956513600000000000000000000),true,MergedCutProfiles.Batch577.profile23081,![MergedCutProfiles.Batch577.profile23081,MergedCutProfiles.Batch577.profile23082,MergedCutProfiles.Batch577.profile23083,MergedCutProfiles.Batch577.profile23084,MergedCutProfiles.Batch577.profile23085,MergedCutProfiles.Batch577.profile23086,MergedCutProfiles.Batch577.profile23087,MergedCutProfiles.Batch577.profile23088,MergedCutProfiles.Batch577.profile23089,MergedCutProfiles.Batch577.profile23090,MergedCutProfiles.Batch577.profile23091,MergedCutProfiles.Batch577.profile23092,MergedCutProfiles.Batch577.profile23093,MergedCutProfiles.Batch577.profile23094,MergedCutProfiles.Batch577.profile23095,MergedCutProfiles.Batch577.profile23096]⟩
theorem profilesValid3787 : retention3787.ProfilesValid := by
  change ∀ j : Fin 16, (retention3787.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch577.valid23081
  · exact MergedCutProfiles.Batch577.valid23082
  · exact MergedCutProfiles.Batch577.valid23083
  · exact MergedCutProfiles.Batch577.valid23084
  · exact MergedCutProfiles.Batch577.valid23085
  · exact MergedCutProfiles.Batch577.valid23086
  · exact MergedCutProfiles.Batch577.valid23087
  · exact MergedCutProfiles.Batch577.valid23088
  · exact MergedCutProfiles.Batch577.valid23089
  · exact MergedCutProfiles.Batch577.valid23090
  · exact MergedCutProfiles.Batch577.valid23091
  · exact MergedCutProfiles.Batch577.valid23092
  · exact MergedCutProfiles.Batch577.valid23093
  · exact MergedCutProfiles.Batch577.valid23094
  · exact MergedCutProfiles.Batch577.valid23095
  · exact MergedCutProfiles.Batch577.valid23096
theorem numericValid3787 : retention3787.NumericValid := by decide +kernel
def certificate3787 : RatCutBinCertificate := ⟨⟨retention3787,(451474951292943807/250000000000000000),(353207060666619/31250000000000000),(4056640789768914621/500000000000000000),(8471332555205504958753/250000000000000000),(1085397740692823763/500000000000000000)⟩,(499973635476218731/500000000000000000),(249854631769765441/1000000000000000000),(100885692872880749/250000000000000000),(3015524845001937/5000000000000000)⟩
theorem valid3787 : certificate3787.Valid := by decide +kernel
theorem sound3787 : certificate3787.Sound := rat_cut_bin_certificate_sound certificate3787 profilesValid3787 numericValid3787 valid3787

def retention3788 : RatCutRetentionCertificate := ⟨(2/125),(33/2000),(1/2),64,1,(255370377740200481787033762328595473671/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch577.profile23097,(fun _ => MergedCutProfiles.Batch577.profile23097)⟩
theorem profilesValid3788 : retention3788.ProfilesValid := by
  exact MergedCutProfiles.Batch577.valid23097
theorem numericValid3788 : retention3788.NumericValid := by decide +kernel
def certificate3788 : RatCutBinCertificate := ⟨⟨retention3788,(451474951292943807/250000000000000000),(353207060666619/31250000000000000),(4056640789768914621/500000000000000000),(8471332555205504958753/250000000000000000),(995024736039351221/1000000000000000000)⟩,(499973635476218731/500000000000000000),(462539349780245937/1000000000000000000),(90415845204954127/500000000000000000),(177167958176816351/1000000000000000000)⟩
theorem valid3788 : certificate3788.Valid := by decide +kernel
theorem sound3788 : certificate3788.Sound := rat_cut_bin_certificate_sound certificate3788 profilesValid3788 numericValid3788 valid3788

def retention3789 : RatCutRetentionCertificate := ⟨(2/125),(33/2000),(2560000000000000000/166671408624338517627),(3573369315314114979/200000000000000000),1,(154773844450548563750149138906719304691/71467386306282299580000000000000000000),false,MergedCutProfiles.Batch577.profile23098,(fun _ => MergedCutProfiles.Batch577.profile23098)⟩
theorem profilesValid3789 : retention3789.ProfilesValid := by
  exact MergedCutProfiles.Batch577.valid23098
theorem numericValid3789 : retention3789.NumericValid := by decide +kernel
def certificate3789 : RatCutBinCertificate := ⟨⟨retention3789,(444475029292943807/250000000000000000),(353207060666619/31250000000000000),(4056640789768914621/500000000000000000),(8471332555205504958753/250000000000000000),(2163180190722504039/1000000000000000000)⟩,(999948088493752827/1000000000000000000),(6458313164879179/200000000000000000),(837619461772766793/1000000000000000000),(323230726393650517/200000000000000000)⟩
theorem valid3789 : certificate3789.Valid := by decide +kernel
theorem sound3789 : certificate3789.Sound := rat_cut_bin_certificate_sound certificate3789 profilesValid3789 numericValid3789 valid3789

def retention3790 : RatCutRetentionCertificate := ⟨(2/125),(33/2000),(1/2),64,1,(255370377740200481787033762328595473671/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch577.profile23097,(fun _ => MergedCutProfiles.Batch577.profile23097)⟩
theorem profilesValid3790 : retention3790.ProfilesValid := by
  exact MergedCutProfiles.Batch577.valid23097
theorem numericValid3790 : retention3790.NumericValid := by decide +kernel
def certificate3790 : RatCutBinCertificate := ⟨⟨retention3790,(444475029292943807/250000000000000000),(353207060666619/31250000000000000),(4056640789768914621/500000000000000000),(8471332555205504958753/250000000000000000),(995063742451058357/1000000000000000000)⟩,(999948088493752827/1000000000000000000),(14039799168379539/200000000000000000),(184071133013494229/250000000000000000),(721395508299069129/1000000000000000000)⟩
theorem valid3790 : certificate3790.Valid := by decide +kernel
theorem sound3790 : certificate3790.Sound := rat_cut_bin_certificate_sound certificate3790 profilesValid3790 numericValid3790 valid3790

def retention3791 : RatCutRetentionCertificate := ⟨(33/2000),(17/1000),(316542127172242394/1958051853593993522639),(280915065522790267/500000000000000000),4,(4904522701831812625266125267929628607/2247320524182322136000000000000000000),true,MergedCutProfiles.Batch577.profile23099,![MergedCutProfiles.Batch577.profile23099,MergedCutProfiles.Batch577.profile23100,MergedCutProfiles.Batch577.profile23101,MergedCutProfiles.Batch577.profile23102,MergedCutProfiles.Batch577.profile23103,MergedCutProfiles.Batch577.profile23104,MergedCutProfiles.Batch577.profile23105,MergedCutProfiles.Batch577.profile23106,MergedCutProfiles.Batch577.profile23107,MergedCutProfiles.Batch577.profile23108,MergedCutProfiles.Batch577.profile23109,MergedCutProfiles.Batch577.profile23110,MergedCutProfiles.Batch577.profile23111,MergedCutProfiles.Batch577.profile23112,MergedCutProfiles.Batch577.profile23113,MergedCutProfiles.Batch577.profile23114]⟩
theorem profilesValid3791 : retention3791.ProfilesValid := by
  change ∀ j : Fin 16, (retention3791.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch577.valid23099
  · exact MergedCutProfiles.Batch577.valid23100
  · exact MergedCutProfiles.Batch577.valid23101
  · exact MergedCutProfiles.Batch577.valid23102
  · exact MergedCutProfiles.Batch577.valid23103
  · exact MergedCutProfiles.Batch577.valid23104
  · exact MergedCutProfiles.Batch577.valid23105
  · exact MergedCutProfiles.Batch577.valid23106
  · exact MergedCutProfiles.Batch577.valid23107
  · exact MergedCutProfiles.Batch577.valid23108
  · exact MergedCutProfiles.Batch577.valid23109
  · exact MergedCutProfiles.Batch577.valid23110
  · exact MergedCutProfiles.Batch577.valid23111
  · exact MergedCutProfiles.Batch577.valid23112
  · exact MergedCutProfiles.Batch577.valid23113
  · exact MergedCutProfiles.Batch577.valid23114
theorem numericValid3791 : retention3791.NumericValid := by decide +kernel
def certificate3791 : RatCutBinCertificate := ⟨⟨retention3791,(1807303819852339791/1000000000000000000),(12019078477736559/1000000000000000000),(1020687319340430753/125000000000000000),(2003244153128702748469/62500000000000000),(2171745891583246941/1000000000000000000)⟩,(499972125251230043/500000000000000000),(337615523948949787/500000000000000000),(59605480875057547/1000000000000000000),(5212629939776813/200000000000000000)⟩
theorem valid3791 : certificate3791.Valid := by decide +kernel
theorem sound3791 : certificate3791.Sound := rat_cut_bin_certificate_sound certificate3791 profilesValid3791 numericValid3791 valid3791

def certificates : List RatCutBinCertificate := [certificate3780,certificate3781,certificate3782,certificate3783,certificate3784,certificate3785,certificate3786,certificate3787,certificate3788,certificate3789,certificate3790,certificate3791]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3780,List.forall_mem_cons.mpr ⟨sound3781,List.forall_mem_cons.mpr ⟨sound3782,List.forall_mem_cons.mpr ⟨sound3783,List.forall_mem_cons.mpr ⟨sound3784,List.forall_mem_cons.mpr ⟨sound3785,List.forall_mem_cons.mpr ⟨sound3786,List.forall_mem_cons.mpr ⟨sound3787,List.forall_mem_cons.mpr ⟨sound3788,List.forall_mem_cons.mpr ⟨sound3789,List.forall_mem_cons.mpr ⟨sound3790,List.forall_mem_cons.mpr ⟨sound3791,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch315
