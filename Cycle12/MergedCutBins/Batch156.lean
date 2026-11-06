import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch297
import Cycle12.MergedCutProfiles.Batch298
import Cycle12.MergedCutProfiles.Batch299
import Cycle12.MergedCutProfiles.Batch300

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch156

def retention1872 : RatCutRetentionCertificate := ⟨(133/2000),(533/8000),(2085596047262182430/9715824122799784559),(113664905268987981/100000000000000000),2,(40820438743636529037/25600000000000000000),true,MergedCutProfiles.Batch297.profile11905,![MergedCutProfiles.Batch297.profile11905,MergedCutProfiles.Batch297.profile11906,MergedCutProfiles.Batch297.profile11907,MergedCutProfiles.Batch297.profile11908,MergedCutProfiles.Batch297.profile11909,MergedCutProfiles.Batch297.profile11910,MergedCutProfiles.Batch297.profile11911,MergedCutProfiles.Batch297.profile11912,MergedCutProfiles.Batch297.profile11913,MergedCutProfiles.Batch297.profile11914,MergedCutProfiles.Batch297.profile11915,MergedCutProfiles.Batch297.profile11916,MergedCutProfiles.Batch297.profile11917,MergedCutProfiles.Batch297.profile11918,MergedCutProfiles.Batch297.profile11919,MergedCutProfiles.Batch298.profile11920]⟩
theorem profilesValid1872 : retention1872.ProfilesValid := by
  change ∀ j : Fin 16, (retention1872.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch297.valid11905
  · exact MergedCutProfiles.Batch297.valid11906
  · exact MergedCutProfiles.Batch297.valid11907
  · exact MergedCutProfiles.Batch297.valid11908
  · exact MergedCutProfiles.Batch297.valid11909
  · exact MergedCutProfiles.Batch297.valid11910
  · exact MergedCutProfiles.Batch297.valid11911
  · exact MergedCutProfiles.Batch297.valid11912
  · exact MergedCutProfiles.Batch297.valid11913
  · exact MergedCutProfiles.Batch297.valid11914
  · exact MergedCutProfiles.Batch297.valid11915
  · exact MergedCutProfiles.Batch297.valid11916
  · exact MergedCutProfiles.Batch297.valid11917
  · exact MergedCutProfiles.Batch297.valid11918
  · exact MergedCutProfiles.Batch297.valid11919
  · exact MergedCutProfiles.Batch298.valid11920
theorem numericValid1872 : retention1872.NumericValid := by decide +kernel
def certificate1872 : RatCutBinCertificate := ⟨⟨retention1872,(2417909638712551331/1000000000000000000),(29331900029289919/125000000000000000),(8965038059610232297/500000000000000000),(43586218850587268037/250000000000000000),(191402924187068289/125000000000000000)⟩,(494667213896005769/500000000000000000),(174079657994591979/500000000000000000),(71123343266178079/250000000000000000),(160820987814615271/1000000000000000000)⟩
theorem valid1872 : certificate1872.Valid := by decide +kernel
theorem sound1872 : certificate1872.Sound := rat_cut_bin_certificate_sound certificate1872 profilesValid1872 numericValid1872 valid1872

def retention1873 : RatCutRetentionCertificate := ⟨(133/2000),(533/8000),(3751381637227250722/9715824122799784559),(208559604726218243/100000000000000000),(13/10),(154161205586855113927/128000000000000000000),true,MergedCutProfiles.Batch298.profile11921,![MergedCutProfiles.Batch298.profile11921,MergedCutProfiles.Batch298.profile11922,MergedCutProfiles.Batch298.profile11923,MergedCutProfiles.Batch298.profile11924,MergedCutProfiles.Batch297.profile11913,MergedCutProfiles.Batch298.profile11925,MergedCutProfiles.Batch298.profile11926,MergedCutProfiles.Batch298.profile11927,MergedCutProfiles.Batch298.profile11928,MergedCutProfiles.Batch298.profile11929,MergedCutProfiles.Batch298.profile11930,MergedCutProfiles.Batch298.profile11931,MergedCutProfiles.Batch298.profile11932,MergedCutProfiles.Batch298.profile11933,MergedCutProfiles.Batch298.profile11934,MergedCutProfiles.Batch298.profile11935]⟩
theorem profilesValid1873 : retention1873.ProfilesValid := by
  change ∀ j : Fin 16, (retention1873.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch298.valid11921
  · exact MergedCutProfiles.Batch298.valid11922
  · exact MergedCutProfiles.Batch298.valid11923
  · exact MergedCutProfiles.Batch298.valid11924
  · exact MergedCutProfiles.Batch297.valid11913
  · exact MergedCutProfiles.Batch298.valid11925
  · exact MergedCutProfiles.Batch298.valid11926
  · exact MergedCutProfiles.Batch298.valid11927
  · exact MergedCutProfiles.Batch298.valid11928
  · exact MergedCutProfiles.Batch298.valid11929
  · exact MergedCutProfiles.Batch298.valid11930
  · exact MergedCutProfiles.Batch298.valid11931
  · exact MergedCutProfiles.Batch298.valid11932
  · exact MergedCutProfiles.Batch298.valid11933
  · exact MergedCutProfiles.Batch298.valid11934
  · exact MergedCutProfiles.Batch298.valid11935
theorem numericValid1873 : retention1873.NumericValid := by decide +kernel
def certificate1873 : RatCutBinCertificate := ⟨⟨retention1873,(2417909638712551331/1000000000000000000),(29331900029289919/125000000000000000),(8965038059610232297/500000000000000000),(43586218850587268037/250000000000000000),(5816135531501677/5000000000000000)⟩,(494667213896005769/500000000000000000),(194277024398344091/500000000000000000),(244134977295155873/1000000000000000000),(20271450772114387/125000000000000000)⟩
theorem valid1873 : certificate1873.Valid := by decide +kernel
theorem sound1873 : certificate1873.Sound := rat_cut_bin_certificate_sound certificate1873 profilesValid1873 numericValid1873 valid1873

def retention1874 : RatCutRetentionCertificate := ⟨(133/2000),(533/8000),(4623172494886272145/9715824122799784559),(1875690818613625361/500000000000000000),1,(127860679554353933561/128000000000000000000),true,MergedCutProfiles.Batch298.profile11936,![MergedCutProfiles.Batch298.profile11936,MergedCutProfiles.Batch298.profile11937,MergedCutProfiles.Batch298.profile11938,MergedCutProfiles.Batch298.profile11939,MergedCutProfiles.Batch298.profile11940,MergedCutProfiles.Batch298.profile11941,MergedCutProfiles.Batch298.profile11942,MergedCutProfiles.Batch298.profile11943,MergedCutProfiles.Batch298.profile11944,MergedCutProfiles.Batch298.profile11945,MergedCutProfiles.Batch298.profile11946,MergedCutProfiles.Batch298.profile11947,MergedCutProfiles.Batch298.profile11948,MergedCutProfiles.Batch298.profile11949,MergedCutProfiles.Batch298.profile11950,MergedCutProfiles.Batch298.profile11951]⟩
theorem profilesValid1874 : retention1874.ProfilesValid := by
  change ∀ j : Fin 16, (retention1874.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch298.valid11936
  · exact MergedCutProfiles.Batch298.valid11937
  · exact MergedCutProfiles.Batch298.valid11938
  · exact MergedCutProfiles.Batch298.valid11939
  · exact MergedCutProfiles.Batch298.valid11940
  · exact MergedCutProfiles.Batch298.valid11941
  · exact MergedCutProfiles.Batch298.valid11942
  · exact MergedCutProfiles.Batch298.valid11943
  · exact MergedCutProfiles.Batch298.valid11944
  · exact MergedCutProfiles.Batch298.valid11945
  · exact MergedCutProfiles.Batch298.valid11946
  · exact MergedCutProfiles.Batch298.valid11947
  · exact MergedCutProfiles.Batch298.valid11948
  · exact MergedCutProfiles.Batch298.valid11949
  · exact MergedCutProfiles.Batch298.valid11950
  · exact MergedCutProfiles.Batch298.valid11951
theorem numericValid1874 : retention1874.NumericValid := by decide +kernel
def certificate1874 : RatCutBinCertificate := ⟨⟨retention1874,(2417909638712551331/1000000000000000000),(29331900029289919/125000000000000000),(8965038059610232297/500000000000000000),(43586218850587268037/250000000000000000),(967256443324055273/1000000000000000000)⟩,(494667213896005769/500000000000000000),(52832895813843017/125000000000000000),(53336804968218811/250000000000000000),(16206504086110879/100000000000000000)⟩
theorem valid1874 : certificate1874.Valid := by decide +kernel
theorem sound1874 : certificate1874.Sound := rat_cut_bin_certificate_sound certificate1874 profilesValid1874 numericValid1874 valid1874

def retention1875 : RatCutRetentionCertificate := ⟨(133/2000),(533/8000),(4810891837100359290/9715824122799784559),(924634498977254429/200000000000000000),(11/10),(73604714004357927686430878958150898511/73970759918180354320000000000000000000),false,MergedCutProfiles.Batch298.profile11952,(fun _ => MergedCutProfiles.Batch298.profile11952)⟩
theorem profilesValid1875 : retention1875.ProfilesValid := by
  exact MergedCutProfiles.Batch298.valid11952
theorem numericValid1875 : retention1875.NumericValid := by decide +kernel
def certificate1875 : RatCutBinCertificate := ⟨⟨retention1875,(2417909638712551331/1000000000000000000),(29331900029289919/125000000000000000),(8965038059610232297/500000000000000000),(43586218850587268037/250000000000000000),(960234127180759261/1000000000000000000)⟩,(494667213896005769/500000000000000000),(41514413039505757/100000000000000000),(43977913099475161/200000000000000000),(40471825578510517/250000000000000000)⟩
theorem valid1875 : certificate1875.Valid := by decide +kernel
theorem sound1875 : certificate1875.Sound := rat_cut_bin_certificate_sound certificate1875 profilesValid1875 numericValid1875 valid1875

def retention1876 : RatCutRetentionCertificate := ⟨(133/2000),(533/8000),(1/2),(481089183710035929/100000000000000000),(11/10),(950216442333942135788339634347069497/962178367420071858000000000000000000),false,MergedCutProfiles.Batch298.profile11953,(fun _ => MergedCutProfiles.Batch298.profile11953)⟩
theorem profilesValid1876 : retention1876.ProfilesValid := by
  exact MergedCutProfiles.Batch298.valid11953
theorem numericValid1876 : retention1876.NumericValid := by decide +kernel
def certificate1876 : RatCutBinCertificate := ⟨⟨retention1876,(2417909638712551331/1000000000000000000),(29331900029289919/125000000000000000),(8965038059610232297/500000000000000000),(43586218850587268037/250000000000000000),(952750879903844153/1000000000000000000)⟩,(494667213896005769/500000000000000000),(416609357725622917/1000000000000000000),(218604061122185077/1000000000000000000),(160788425798575359/1000000000000000000)⟩
theorem valid1876 : certificate1876.Valid := by decide +kernel
theorem sound1876 : certificate1876.Sound := rat_cut_bin_certificate_sound certificate1876 profilesValid1876 numericValid1876 valid1876

def retention1877 : RatCutRetentionCertificate := ⟨(133/2000),(533/8000),(1/2),64,1,(255419002050035343154198833189531686439/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch298.profile11953,(fun _ => MergedCutProfiles.Batch298.profile11953)⟩
theorem profilesValid1877 : retention1877.ProfilesValid := by
  exact MergedCutProfiles.Batch298.valid11953
theorem numericValid1877 : retention1877.NumericValid := by decide +kernel
def certificate1877 : RatCutBinCertificate := ⟨⟨retention1877,(2417909638712551331/1000000000000000000),(29331900029289919/125000000000000000),(8965038059610232297/500000000000000000),(43586218850587268037/250000000000000000),(966086048781530867/1000000000000000000)⟩,(494667213896005769/500000000000000000),(185264163839612627/500000000000000000),(130799260585045149/500000000000000000),(123143003321996177/500000000000000000)⟩
theorem valid1877 : certificate1877.Valid := by decide +kernel
theorem sound1877 : certificate1877.Sound := rat_cut_bin_certificate_sound certificate1877 profilesValid1877 numericValid1877 valid1877

def retention1878 : RatCutRetentionCertificate := ⟨(133/2000),(533/8000),(4487874930922828268/9715824122799784559),(573599707040021293/200000000000000000),(5/4),(195857070910524151676267014573971457711/183551906252806813760000000000000000000),false,MergedCutProfiles.Batch298.profile11954,(fun _ => MergedCutProfiles.Batch298.profile11954)⟩
theorem profilesValid1878 : retention1878.ProfilesValid := by
  exact MergedCutProfiles.Batch298.valid11954
theorem numericValid1878 : retention1878.NumericValid := by decide +kernel
def certificate1878 : RatCutBinCertificate := ⟨⟨retention1878,(2724154338712551331/1000000000000000000),(29331900029289919/125000000000000000),(8965038059610232297/500000000000000000),(43586218850587268037/250000000000000000),(25561446212752551/25000000000000000)⟩,(30874331722991641/31250000000000000),(186696119464191169/500000000000000000),(258766455140091533/1000000000000000000),(84996268162053063/500000000000000000)⟩
theorem valid1878 : certificate1878.Valid := by decide +kernel
theorem sound1878 : certificate1878.Sound := rat_cut_bin_certificate_sound certificate1878 profilesValid1878 numericValid1878 valid1878

def retention1879 : RatCutRetentionCertificate := ⟨(133/2000),(533/8000),(4811609369277169669/9715824122799784559),(1121968732730707067/250000000000000000),(11/10),(13934618661817440025611266430224977687/14024609159133838337500000000000000000),false,MergedCutProfiles.Batch298.profile11955,(fun _ => MergedCutProfiles.Batch298.profile11955)⟩
theorem profilesValid1879 : retention1879.ProfilesValid := by
  exact MergedCutProfiles.Batch298.valid11955
theorem numericValid1879 : retention1879.NumericValid := by decide +kernel
def certificate1879 : RatCutBinCertificate := ⟨⟨retention1879,(2724154338712551331/1000000000000000000),(29331900029289919/125000000000000000),(8965038059610232297/500000000000000000),(43586218850587268037/250000000000000000),(47717793407635537/50000000000000000)⟩,(30874331722991641/31250000000000000),(20001858740810603/50000000000000000),(233448303382514177/1000000000000000000),(1359871337224771/8000000000000000)⟩
theorem valid1879 : certificate1879.Valid := by decide +kernel
theorem sound1879 : certificate1879.Sound := rat_cut_bin_certificate_sound certificate1879 profilesValid1879 numericValid1879 valid1879

def retention1880 : RatCutRetentionCertificate := ⟨(133/2000),(533/8000),(1/2),(4811609369277169669/1000000000000000000),(11/10),(1900727840864720139693660556746507404959/1924643747710867867600000000000000000000),false,MergedCutProfiles.Batch298.profile11953,(fun _ => MergedCutProfiles.Batch298.profile11953)⟩
theorem profilesValid1880 : retention1880.ProfilesValid := by
  exact MergedCutProfiles.Batch298.valid11953
theorem numericValid1880 : retention1880.NumericValid := by decide +kernel
def certificate1880 : RatCutBinCertificate := ⟨⟨retention1880,(2724154338712551331/1000000000000000000),(29331900029289919/125000000000000000),(8965038059610232297/500000000000000000),(43586218850587268037/250000000000000000),(948347053722678229/1000000000000000000)⟩,(30874331722991641/31250000000000000),(20128592363230229/50000000000000000),(23113415453081631/100000000000000000),(169100046880885893/1000000000000000000)⟩
theorem valid1880 : certificate1880.Valid := by decide +kernel
theorem sound1880 : certificate1880.Sound := rat_cut_bin_certificate_sound certificate1880 profilesValid1880 numericValid1880 valid1880

def retention1881 : RatCutRetentionCertificate := ⟨(533/8000),(267/4000),(125211026197315426/967172269176527221),(450824224646158339/500000000000000000),(49/20),(290406299433697158117/160000000000000000000),true,MergedCutProfiles.Batch298.profile11956,![MergedCutProfiles.Batch298.profile11956,MergedCutProfiles.Batch298.profile11957,MergedCutProfiles.Batch298.profile11958,MergedCutProfiles.Batch298.profile11959,MergedCutProfiles.Batch299.profile11960,MergedCutProfiles.Batch299.profile11961,MergedCutProfiles.Batch299.profile11962,MergedCutProfiles.Batch299.profile11963,MergedCutProfiles.Batch299.profile11964,MergedCutProfiles.Batch299.profile11965,MergedCutProfiles.Batch299.profile11966,MergedCutProfiles.Batch299.profile11967,MergedCutProfiles.Batch299.profile11968,MergedCutProfiles.Batch299.profile11969,MergedCutProfiles.Batch299.profile11970,MergedCutProfiles.Batch299.profile11971]⟩
theorem profilesValid1881 : retention1881.ProfilesValid := by
  change ∀ j : Fin 16, (retention1881.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch298.valid11956
  · exact MergedCutProfiles.Batch298.valid11957
  · exact MergedCutProfiles.Batch298.valid11958
  · exact MergedCutProfiles.Batch298.valid11959
  · exact MergedCutProfiles.Batch299.valid11960
  · exact MergedCutProfiles.Batch299.valid11961
  · exact MergedCutProfiles.Batch299.valid11962
  · exact MergedCutProfiles.Batch299.valid11963
  · exact MergedCutProfiles.Batch299.valid11964
  · exact MergedCutProfiles.Batch299.valid11965
  · exact MergedCutProfiles.Batch299.valid11966
  · exact MergedCutProfiles.Batch299.valid11967
  · exact MergedCutProfiles.Batch299.valid11968
  · exact MergedCutProfiles.Batch299.valid11969
  · exact MergedCutProfiles.Batch299.valid11970
  · exact MergedCutProfiles.Batch299.valid11971
theorem numericValid1881 : retention1881.NumericValid := by decide +kernel
def certificate1881 : RatCutBinCertificate := ⟨⟨retention1881,(2418384026863338841/1000000000000000000),(58933568729026887/250000000000000000),(4493440654925608833/250000000000000000),(173976484208467857237/1000000000000000000),(868641016586852749/500000000000000000)⟩,(494662241135546001/500000000000000000),(329584063043018857/1000000000000000000),(304592437954154193/1000000000000000000),(20169971941887929/125000000000000000)⟩
theorem valid1881 : certificate1881.Valid := by decide +kernel
theorem sound1881 : certificate1881.Sound := rat_cut_bin_certificate_sound certificate1881 profilesValid1881 numericValid1881 valid1881

def retention1882 : RatCutRetentionCertificate := ⟨(533/8000),(267/4000),(2414644747447853311/9671722691765272210),(62605513098657713/50000000000000000),(37/20),(96701637052394814629/64000000000000000000),true,MergedCutProfiles.Batch299.profile11972,![MergedCutProfiles.Batch299.profile11972,MergedCutProfiles.Batch299.profile11973,MergedCutProfiles.Batch299.profile11974,MergedCutProfiles.Batch299.profile11975,MergedCutProfiles.Batch299.profile11976,MergedCutProfiles.Batch299.profile11977,MergedCutProfiles.Batch299.profile11978,MergedCutProfiles.Batch299.profile11979,MergedCutProfiles.Batch299.profile11980,MergedCutProfiles.Batch299.profile11981,MergedCutProfiles.Batch299.profile11982,MergedCutProfiles.Batch299.profile11983,MergedCutProfiles.Batch299.profile11984,MergedCutProfiles.Batch299.profile11985,MergedCutProfiles.Batch299.profile11986,MergedCutProfiles.Batch299.profile11987]⟩
theorem profilesValid1882 : retention1882.ProfilesValid := by
  change ∀ j : Fin 16, (retention1882.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch299.valid11972
  · exact MergedCutProfiles.Batch299.valid11973
  · exact MergedCutProfiles.Batch299.valid11974
  · exact MergedCutProfiles.Batch299.valid11975
  · exact MergedCutProfiles.Batch299.valid11976
  · exact MergedCutProfiles.Batch299.valid11977
  · exact MergedCutProfiles.Batch299.valid11978
  · exact MergedCutProfiles.Batch299.valid11979
  · exact MergedCutProfiles.Batch299.valid11980
  · exact MergedCutProfiles.Batch299.valid11981
  · exact MergedCutProfiles.Batch299.valid11982
  · exact MergedCutProfiles.Batch299.valid11983
  · exact MergedCutProfiles.Batch299.valid11984
  · exact MergedCutProfiles.Batch299.valid11985
  · exact MergedCutProfiles.Batch299.valid11986
  · exact MergedCutProfiles.Batch299.valid11987
theorem numericValid1882 : retention1882.NumericValid := by decide +kernel
def certificate1882 : RatCutBinCertificate := ⟨⟨retention1882,(2418384026863338841/1000000000000000000),(58933568729026887/250000000000000000),(4493440654925608833/250000000000000000),(173976484208467857237/1000000000000000000),(145225002235718467/100000000000000000)⟩,(494662241135546001/500000000000000000),(352419701387582501/1000000000000000000),(280024919148587589/1000000000000000000),(162053683009803891/1000000000000000000)⟩
theorem valid1882 : certificate1882.Valid := by decide +kernel
theorem sound1882 : certificate1882.Sound := rat_cut_bin_certificate_sound certificate1882 profilesValid1882 numericValid1882 valid1882

def retention1883 : RatCutRetentionCertificate := ⟨(533/8000),(267/4000),(405102274206195168/967172269176527221),(2414644747447853311/1000000000000000000),(23/20),(1440080225803422894287/1280000000000000000000),true,MergedCutProfiles.Batch299.profile11988,![MergedCutProfiles.Batch299.profile11988,MergedCutProfiles.Batch299.profile11989,MergedCutProfiles.Batch299.profile11990,MergedCutProfiles.Batch299.profile11991,MergedCutProfiles.Batch299.profile11992,MergedCutProfiles.Batch299.profile11993,MergedCutProfiles.Batch299.profile11994,MergedCutProfiles.Batch299.profile11995,MergedCutProfiles.Batch299.profile11996,MergedCutProfiles.Batch299.profile11997,MergedCutProfiles.Batch299.profile11998,MergedCutProfiles.Batch299.profile11999,MergedCutProfiles.Batch300.profile12000,MergedCutProfiles.Batch300.profile12001,MergedCutProfiles.Batch300.profile12002,MergedCutProfiles.Batch300.profile12003]⟩
theorem profilesValid1883 : retention1883.ProfilesValid := by
  change ∀ j : Fin 16, (retention1883.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch299.valid11988
  · exact MergedCutProfiles.Batch299.valid11989
  · exact MergedCutProfiles.Batch299.valid11990
  · exact MergedCutProfiles.Batch299.valid11991
  · exact MergedCutProfiles.Batch299.valid11992
  · exact MergedCutProfiles.Batch299.valid11993
  · exact MergedCutProfiles.Batch299.valid11994
  · exact MergedCutProfiles.Batch299.valid11995
  · exact MergedCutProfiles.Batch299.valid11996
  · exact MergedCutProfiles.Batch299.valid11997
  · exact MergedCutProfiles.Batch299.valid11998
  · exact MergedCutProfiles.Batch299.valid11999
  · exact MergedCutProfiles.Batch300.valid12000
  · exact MergedCutProfiles.Batch300.valid12001
  · exact MergedCutProfiles.Batch300.valid12002
  · exact MergedCutProfiles.Batch300.valid12003
theorem numericValid1883 : retention1883.NumericValid := by decide +kernel
def certificate1883 : RatCutBinCertificate := ⟨⟨retention1883,(2418384026863338841/1000000000000000000),(58933568729026887/250000000000000000),(4493440654925608833/250000000000000000),(173976484208467857237/1000000000000000000),(1088568908853008967/1000000000000000000)⟩,(494662241135546001/500000000000000000),(50125166048294773/125000000000000000),(232566147630002913/1000000000000000000),(40528183892044361/250000000000000000)⟩
theorem valid1883 : certificate1883.Valid := by decide +kernel
theorem sound1883 : certificate1883.Sound := rat_cut_bin_certificate_sound certificate1883 profilesValid1883 numericValid1883 valid1883

def certificates : List RatCutBinCertificate := [certificate1872,certificate1873,certificate1874,certificate1875,certificate1876,certificate1877,certificate1878,certificate1879,certificate1880,certificate1881,certificate1882,certificate1883]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1872,List.forall_mem_cons.mpr ⟨sound1873,List.forall_mem_cons.mpr ⟨sound1874,List.forall_mem_cons.mpr ⟨sound1875,List.forall_mem_cons.mpr ⟨sound1876,List.forall_mem_cons.mpr ⟨sound1877,List.forall_mem_cons.mpr ⟨sound1878,List.forall_mem_cons.mpr ⟨sound1879,List.forall_mem_cons.mpr ⟨sound1880,List.forall_mem_cons.mpr ⟨sound1881,List.forall_mem_cons.mpr ⟨sound1882,List.forall_mem_cons.mpr ⟨sound1883,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch156
