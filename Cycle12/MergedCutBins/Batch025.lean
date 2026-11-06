import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch049
import Cycle12.MergedCutProfiles.Batch050
import Cycle12.MergedCutProfiles.Batch051

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch025

def retention300 : RatCutRetentionCertificate := ⟨(4/125),(13/400),(740426087164021124/49649338197438694597),(183273783951490377/250000000000000000),(71/20),(710028911746260970709/320000000000000000000),true,MergedCutProfiles.Batch049.profile1965,![MergedCutProfiles.Batch049.profile1965,MergedCutProfiles.Batch049.profile1966,MergedCutProfiles.Batch049.profile1967,MergedCutProfiles.Batch049.profile1968,MergedCutProfiles.Batch049.profile1969,MergedCutProfiles.Batch049.profile1970,MergedCutProfiles.Batch049.profile1971,MergedCutProfiles.Batch049.profile1972,MergedCutProfiles.Batch049.profile1973,MergedCutProfiles.Batch049.profile1974,MergedCutProfiles.Batch049.profile1975,MergedCutProfiles.Batch049.profile1976,MergedCutProfiles.Batch049.profile1977,MergedCutProfiles.Batch049.profile1978,MergedCutProfiles.Batch049.profile1979,MergedCutProfiles.Batch049.profile1980]⟩
theorem profilesValid300 : retention300.ProfilesValid := by
  change ∀ j : Fin 16, (retention300.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch049.valid1965
  · exact MergedCutProfiles.Batch049.valid1966
  · exact MergedCutProfiles.Batch049.valid1967
  · exact MergedCutProfiles.Batch049.valid1968
  · exact MergedCutProfiles.Batch049.valid1969
  · exact MergedCutProfiles.Batch049.valid1970
  · exact MergedCutProfiles.Batch049.valid1971
  · exact MergedCutProfiles.Batch049.valid1972
  · exact MergedCutProfiles.Batch049.valid1973
  · exact MergedCutProfiles.Batch049.valid1974
  · exact MergedCutProfiles.Batch049.valid1975
  · exact MergedCutProfiles.Batch049.valid1976
  · exact MergedCutProfiles.Batch049.valid1977
  · exact MergedCutProfiles.Batch049.valid1978
  · exact MergedCutProfiles.Batch049.valid1979
  · exact MergedCutProfiles.Batch049.valid1980
theorem numericValid300 : retention300.NumericValid := by decide +kernel
def certificate300 : RatCutBinCertificate := ⟨⟨retention300,(20120702923783363/10000000000000000),(23306010813845147/500000000000000000),(630016111035320111/62500000000000000),(4014106551538133733/8000000000000000),(2185809989369547239/1000000000000000000)⟩,(996170132070776577/1000000000000000000),(108685885944645397/250000000000000000),(203115072760619827/1000000000000000000),(3146311959907513/31250000000000000)⟩
theorem valid300 : certificate300.Valid := by decide +kernel
theorem sound300 : certificate300.Sound := rat_cut_bin_certificate_sound certificate300 profilesValid300 numericValid300 valid300

def retention301 : RatCutRetentionCertificate := ⟨(4/125),(13/400),(868207817952944186/49649338197438694597),(185106521791005281/250000000000000000),(7/2),(140939570554582847373/64000000000000000000),true,MergedCutProfiles.Batch049.profile1981,![MergedCutProfiles.Batch049.profile1981,MergedCutProfiles.Batch049.profile1982,MergedCutProfiles.Batch049.profile1983,MergedCutProfiles.Batch049.profile1984,MergedCutProfiles.Batch049.profile1985,MergedCutProfiles.Batch049.profile1971,MergedCutProfiles.Batch049.profile1986,MergedCutProfiles.Batch049.profile1987,MergedCutProfiles.Batch049.profile1988,MergedCutProfiles.Batch049.profile1989,MergedCutProfiles.Batch049.profile1990,MergedCutProfiles.Batch049.profile1991,MergedCutProfiles.Batch049.profile1992,MergedCutProfiles.Batch049.profile1993,MergedCutProfiles.Batch049.profile1994,MergedCutProfiles.Batch049.profile1995]⟩
theorem profilesValid301 : retention301.ProfilesValid := by
  change ∀ j : Fin 16, (retention301.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch049.valid1981
  · exact MergedCutProfiles.Batch049.valid1982
  · exact MergedCutProfiles.Batch049.valid1983
  · exact MergedCutProfiles.Batch049.valid1984
  · exact MergedCutProfiles.Batch049.valid1985
  · exact MergedCutProfiles.Batch049.valid1971
  · exact MergedCutProfiles.Batch049.valid1986
  · exact MergedCutProfiles.Batch049.valid1987
  · exact MergedCutProfiles.Batch049.valid1988
  · exact MergedCutProfiles.Batch049.valid1989
  · exact MergedCutProfiles.Batch049.valid1990
  · exact MergedCutProfiles.Batch049.valid1991
  · exact MergedCutProfiles.Batch049.valid1992
  · exact MergedCutProfiles.Batch049.valid1993
  · exact MergedCutProfiles.Batch049.valid1994
  · exact MergedCutProfiles.Batch049.valid1995
theorem numericValid301 : retention301.NumericValid := by decide +kernel
def certificate301 : RatCutBinCertificate := ⟨⟨retention301,(20120702923783363/10000000000000000),(23306010813845147/500000000000000000),(630016111035320111/62500000000000000),(4014106551538133733/8000000000000000),(2169615641481276231/1000000000000000000)⟩,(996170132070776577/1000000000000000000),(435768633616046339/1000000000000000000),(2528279953341573/12500000000000000),(100725226164990807/1000000000000000000)⟩
theorem valid301 : certificate301.Valid := by decide +kernel
theorem sound301 : certificate301.Sound := rat_cut_bin_certificate_sound certificate301 profilesValid301 numericValid301 valid301

def retention302 : RatCutRetentionCertificate := ⟨(4/125),(13/400),(1008798894000000000/49649338197438694597),(434103908976472093/500000000000000000),(61/20),(1395057793937579401701/640000000000000000000),true,MergedCutProfiles.Batch049.profile1996,![MergedCutProfiles.Batch049.profile1996,MergedCutProfiles.Batch049.profile1997,MergedCutProfiles.Batch049.profile1998,MergedCutProfiles.Batch049.profile1999,MergedCutProfiles.Batch050.profile2000,MergedCutProfiles.Batch050.profile2001,MergedCutProfiles.Batch050.profile2002,MergedCutProfiles.Batch050.profile2003,MergedCutProfiles.Batch050.profile2004,MergedCutProfiles.Batch050.profile2005,MergedCutProfiles.Batch049.profile1979,MergedCutProfiles.Batch050.profile2006,MergedCutProfiles.Batch050.profile2007,MergedCutProfiles.Batch050.profile2008,MergedCutProfiles.Batch050.profile2009,MergedCutProfiles.Batch050.profile2010]⟩
theorem profilesValid302 : retention302.ProfilesValid := by
  change ∀ j : Fin 16, (retention302.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch049.valid1996
  · exact MergedCutProfiles.Batch049.valid1997
  · exact MergedCutProfiles.Batch049.valid1998
  · exact MergedCutProfiles.Batch049.valid1999
  · exact MergedCutProfiles.Batch050.valid2000
  · exact MergedCutProfiles.Batch050.valid2001
  · exact MergedCutProfiles.Batch050.valid2002
  · exact MergedCutProfiles.Batch050.valid2003
  · exact MergedCutProfiles.Batch050.valid2004
  · exact MergedCutProfiles.Batch050.valid2005
  · exact MergedCutProfiles.Batch049.valid1979
  · exact MergedCutProfiles.Batch050.valid2006
  · exact MergedCutProfiles.Batch050.valid2007
  · exact MergedCutProfiles.Batch050.valid2008
  · exact MergedCutProfiles.Batch050.valid2009
  · exact MergedCutProfiles.Batch050.valid2010
theorem numericValid302 : retention302.NumericValid := by decide +kernel
def certificate302 : RatCutBinCertificate := ⟨⟨retention302,(20120702923783363/10000000000000000),(23306010813845147/500000000000000000),(630016111035320111/62500000000000000),(4014106551538133733/8000000000000000),(430279924793944737/200000000000000000)⟩,(996170132070776577/1000000000000000000),(25406838360244287/62500000000000000),(113785384873857989/500000000000000000),(12619349703249023/100000000000000000)⟩
theorem valid302 : certificate302.Valid := by decide +kernel
theorem sound302 : certificate302.Sound := rat_cut_bin_certificate_sound certificate302 profilesValid302 numericValid302 valid302

def retention303 : RatCutRetentionCertificate := ⟨(4/125),(13/400),(1102393548581141981/49649338197438694597),(504399447/500000000),(27/10),(17315251542759187283/8000000000000000000),true,MergedCutProfiles.Batch050.profile2011,![MergedCutProfiles.Batch050.profile2011,MergedCutProfiles.Batch050.profile2012,MergedCutProfiles.Batch050.profile2013,MergedCutProfiles.Batch050.profile2014,MergedCutProfiles.Batch050.profile2015,MergedCutProfiles.Batch050.profile2016,MergedCutProfiles.Batch050.profile2017,MergedCutProfiles.Batch050.profile2018,MergedCutProfiles.Batch050.profile2019,MergedCutProfiles.Batch050.profile2020,MergedCutProfiles.Batch049.profile1993,MergedCutProfiles.Batch050.profile2021,MergedCutProfiles.Batch050.profile2022,MergedCutProfiles.Batch050.profile2023,MergedCutProfiles.Batch050.profile2024,MergedCutProfiles.Batch050.profile2025]⟩
theorem profilesValid303 : retention303.ProfilesValid := by
  change ∀ j : Fin 16, (retention303.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch050.valid2011
  · exact MergedCutProfiles.Batch050.valid2012
  · exact MergedCutProfiles.Batch050.valid2013
  · exact MergedCutProfiles.Batch050.valid2014
  · exact MergedCutProfiles.Batch050.valid2015
  · exact MergedCutProfiles.Batch050.valid2016
  · exact MergedCutProfiles.Batch050.valid2017
  · exact MergedCutProfiles.Batch050.valid2018
  · exact MergedCutProfiles.Batch050.valid2019
  · exact MergedCutProfiles.Batch050.valid2020
  · exact MergedCutProfiles.Batch049.valid1993
  · exact MergedCutProfiles.Batch050.valid2021
  · exact MergedCutProfiles.Batch050.valid2022
  · exact MergedCutProfiles.Batch050.valid2023
  · exact MergedCutProfiles.Batch050.valid2024
  · exact MergedCutProfiles.Batch050.valid2025
theorem numericValid303 : retention303.NumericValid := by decide +kernel
def certificate303 : RatCutBinCertificate := ⟨⟨retention303,(20120702923783363/10000000000000000),(23306010813845147/500000000000000000),(630016111035320111/62500000000000000),(4014106551538133733/8000000000000000),(1069642400319107439/500000000000000000)⟩,(996170132070776577/1000000000000000000),(382053128704552719/1000000000000000000),(250334732599781053/1000000000000000000),(152971311428805507/1000000000000000000)⟩
theorem valid303 : certificate303.Valid := by decide +kernel
theorem sound303 : certificate303.Sound := rat_cut_bin_certificate_sound certificate303 profilesValid303 numericValid303 valid303

def retention304 : RatCutRetentionCertificate := ⟨(4/125),(13/400),(2443692554476593630/49649338197438694597),(1102393548581141981/1000000000000000000),(5/2),(131542538475545373593/64000000000000000000),true,MergedCutProfiles.Batch050.profile2026,![MergedCutProfiles.Batch050.profile2026,MergedCutProfiles.Batch050.profile2027,MergedCutProfiles.Batch050.profile2028,MergedCutProfiles.Batch050.profile2029,MergedCutProfiles.Batch049.profile1993,MergedCutProfiles.Batch050.profile2030,MergedCutProfiles.Batch050.profile2031,MergedCutProfiles.Batch050.profile2032,MergedCutProfiles.Batch050.profile2033,MergedCutProfiles.Batch050.profile2034,MergedCutProfiles.Batch050.profile2035,MergedCutProfiles.Batch050.profile2036,MergedCutProfiles.Batch050.profile2037,MergedCutProfiles.Batch050.profile2038,MergedCutProfiles.Batch050.profile2039,MergedCutProfiles.Batch051.profile2040]⟩
theorem profilesValid304 : retention304.ProfilesValid := by
  change ∀ j : Fin 16, (retention304.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch050.valid2026
  · exact MergedCutProfiles.Batch050.valid2027
  · exact MergedCutProfiles.Batch050.valid2028
  · exact MergedCutProfiles.Batch050.valid2029
  · exact MergedCutProfiles.Batch049.valid1993
  · exact MergedCutProfiles.Batch050.valid2030
  · exact MergedCutProfiles.Batch050.valid2031
  · exact MergedCutProfiles.Batch050.valid2032
  · exact MergedCutProfiles.Batch050.valid2033
  · exact MergedCutProfiles.Batch050.valid2034
  · exact MergedCutProfiles.Batch050.valid2035
  · exact MergedCutProfiles.Batch050.valid2036
  · exact MergedCutProfiles.Batch050.valid2037
  · exact MergedCutProfiles.Batch050.valid2038
  · exact MergedCutProfiles.Batch050.valid2039
  · exact MergedCutProfiles.Batch051.valid2040
theorem numericValid304 : retention304.NumericValid := by decide +kernel
def certificate304 : RatCutBinCertificate := ⟨⟨retention304,(20120702923783363/10000000000000000),(23306010813845147/500000000000000000),(630016111035320111/62500000000000000),(4014106551538133733/8000000000000000),(2032091393135834819/1000000000000000000)⟩,(996170132070776577/1000000000000000000),(387437063395056857/1000000000000000000),(122596216096063831/500000000000000000),(76614521875779199/500000000000000000)⟩
theorem valid304 : certificate304.Valid := by decide +kernel
theorem sound304 : certificate304.Sound := rat_cut_bin_certificate_sound certificate304 profilesValid304 numericValid304 valid304

def retention305 : RatCutRetentionCertificate := ⟨(4/125),(13/400),(14506828361677147862/49649338197438694597),(244369255447659363/100000000000000000),(3/2),(3488031745148340039655557725535806909/2443692554476593630000000000000000000),false,MergedCutProfiles.Batch051.profile2041,(fun _ => MergedCutProfiles.Batch051.profile2041)⟩
theorem profilesValid305 : retention305.ProfilesValid := by
  exact MergedCutProfiles.Batch051.valid2041
theorem numericValid305 : retention305.NumericValid := by decide +kernel
def certificate305 : RatCutBinCertificate := ⟨⟨retention305,(20120702923783363/10000000000000000),(23306010813845147/500000000000000000),(630016111035320111/62500000000000000),(4014106551538133733/8000000000000000),(706702387948353769/500000000000000000)⟩,(996170132070776577/1000000000000000000),(26962783136939133/62500000000000000),(5147731798732193/25000000000000000),(153684768171161943/1000000000000000000)⟩
theorem valid305 : certificate305.Valid := by decide +kernel
theorem sound305 : certificate305.Sound := rat_cut_bin_certificate_sound certificate305 profilesValid305 numericValid305 valid305

def retention306 : RatCutRetentionCertificate := ⟨(4/125),(13/400),(24096975473218000055/49649338197438694597),(7253414180838573931/500000000000000000),(21/20),(5972638386940705953454643152185111928679/5802731344670859144800000000000000000000),false,MergedCutProfiles.Batch051.profile2042,(fun _ => MergedCutProfiles.Batch051.profile2042)⟩
theorem profilesValid306 : retention306.ProfilesValid := by
  exact MergedCutProfiles.Batch051.valid2042
theorem numericValid306 : retention306.NumericValid := by decide +kernel
def certificate306 : RatCutBinCertificate := ⟨⟨retention306,(20120702923783363/10000000000000000),(23306010813845147/500000000000000000),(630016111035320111/62500000000000000),(4014106551538133733/8000000000000000),(1019511274886180239/1000000000000000000)⟩,(996170132070776577/1000000000000000000),(239526151229079799/500000000000000000),(168391207473004103/1000000000000000000),(153095466160415297/1000000000000000000)⟩
theorem valid306 : certificate306.Valid := by decide +kernel
theorem sound306 : certificate306.Sound := rat_cut_bin_certificate_sound certificate306 profilesValid306 numericValid306 valid306

def retention307 : RatCutRetentionCertificate := ⟨(4/125),(13/400),(24581324680229681857/49649338197438694597),(4819395094643600011/200000000000000000),1,(24113818301375257590988250036891851921/24096975473218000055000000000000000000),false,MergedCutProfiles.Batch051.profile2043,(fun _ => MergedCutProfiles.Batch051.profile2043)⟩
theorem profilesValid307 : retention307.ProfilesValid := by
  exact MergedCutProfiles.Batch051.valid2043
theorem numericValid307 : retention307.NumericValid := by decide +kernel
def certificate307 : RatCutBinCertificate := ⟨⟨retention307,(20120702923783363/10000000000000000),(23306010813845147/500000000000000000),(630016111035320111/62500000000000000),(4014106551538133733/8000000000000000),(991394929782136373/1000000000000000000)⟩,(996170132070776577/1000000000000000000),(482770115730428117/1000000000000000000),(165669501572467231/1000000000000000000),(9821020931835741/62500000000000000)⟩
theorem valid307 : certificate307.Valid := by decide +kernel
theorem sound307 : certificate307.Sound := rat_cut_bin_certificate_sound certificate307 profilesValid307 numericValid307 valid307

def retention308 : RatCutRetentionCertificate := ⟨(4/125),(13/400),(1/2),(24581324680229681857/1000000000000000000),1,(24367149546634486076131915046046965949/24581324680229681857000000000000000000),false,MergedCutProfiles.Batch051.profile2044,(fun _ => MergedCutProfiles.Batch051.profile2044)⟩
theorem profilesValid308 : retention308.ProfilesValid := by
  exact MergedCutProfiles.Batch051.valid2044
theorem numericValid308 : retention308.NumericValid := by decide +kernel
def certificate308 : RatCutBinCertificate := ⟨⟨retention308,(20120702923783363/10000000000000000),(23306010813845147/500000000000000000),(630016111035320111/62500000000000000),(4014106551538133733/8000000000000000),(981983049493524369/1000000000000000000)⟩,(996170132070776577/1000000000000000000),(15221884557555647/31250000000000000),(162535568403439341/1000000000000000000),(15287574677590189/100000000000000000)⟩
theorem valid308 : certificate308.Valid := by decide +kernel
theorem sound308 : certificate308.Sound := rat_cut_bin_certificate_sound certificate308 profilesValid308 numericValid308 valid308

def retention309 : RatCutRetentionCertificate := ⟨(4/125),(13/400),(20988148567539389077/49649338197438694597),(1839516645824970237/500000000000000000),(5/4),(13583988796246995608094719599880123299/11772906533279809516800000000000000000),false,MergedCutProfiles.Batch051.profile2045,(fun _ => MergedCutProfiles.Batch051.profile2045)⟩
theorem profilesValid309 : retention309.ProfilesValid := by
  exact MergedCutProfiles.Batch051.valid2045
theorem numericValid309 : retention309.NumericValid := by decide +kernel
def certificate309 : RatCutBinCertificate := ⟨⟨retention309,(23958114583783363/10000000000000000),(23306010813845147/500000000000000000),(630016111035320111/62500000000000000),(4014106551538133733/8000000000000000),(569993210397071051/500000000000000000)⟩,(995439544031800477/1000000000000000000),(357678296460723171/1000000000000000000),(274580354338308649/1000000000000000000),(12996294955500877/62500000000000000)⟩
theorem valid309 : certificate309.Valid := by decide +kernel
theorem sound309 : certificate309.Sound := rat_cut_bin_certificate_sound certificate309 profilesValid309 numericValid309 valid309

def retention310 : RatCutRetentionCertificate := ⟨(4/125),(13/400),(24610254806782601050/49649338197438694597),(20988148567539389077/1000000000000000000),1,(16756722552343065489793025773557621407/16790518854031511261600000000000000000),false,MergedCutProfiles.Batch051.profile2046,(fun _ => MergedCutProfiles.Batch051.profile2046)⟩
theorem profilesValid310 : retention310.ProfilesValid := by
  exact MergedCutProfiles.Batch051.valid2046
theorem numericValid310 : retention310.NumericValid := by decide +kernel
def certificate310 : RatCutBinCertificate := ⟨⟨retention310,(23958114583783363/10000000000000000),(23306010813845147/500000000000000000),(630016111035320111/62500000000000000),(4014106551538133733/8000000000000000),(246727170502480263/250000000000000000)⟩,(995439544031800477/1000000000000000000),(413157172908432189/1000000000000000000),(221641067485833751/1000000000000000000),(1663545913760051/8000000000000000)⟩
theorem valid310 : certificate310.Valid := by decide +kernel
theorem sound310 : certificate310.Sound := rat_cut_bin_certificate_sound certificate310 profilesValid310 numericValid310 valid310

def retention311 : RatCutRetentionCertificate := ⟨(4/125),(13/400),(1/2),(492205096135652021/20000000000000000),1,(24396122712095757570176988748670928051/24610254806782601050000000000000000000),false,MergedCutProfiles.Batch051.profile2044,(fun _ => MergedCutProfiles.Batch051.profile2044)⟩
theorem profilesValid311 : retention311.ProfilesValid := by
  exact MergedCutProfiles.Batch051.valid2044
theorem numericValid311 : retention311.NumericValid := by decide +kernel
def certificate311 : RatCutBinCertificate := ⟨⟨retention311,(23958114583783363/10000000000000000),(23306010813845147/500000000000000000),(630016111035320111/62500000000000000),(4014106551538133733/8000000000000000),(490110290093592661/500000000000000000)⟩,(995439544031800477/1000000000000000000),(41597616824178619/100000000000000000),(109579475608755599/500000000000000000),(51409115483637379/250000000000000000)⟩
theorem valid311 : certificate311.Valid := by decide +kernel
theorem sound311 : certificate311.Sound := rat_cut_bin_certificate_sound certificate311 profilesValid311 numericValid311 valid311

def certificates : List RatCutBinCertificate := [certificate300,certificate301,certificate302,certificate303,certificate304,certificate305,certificate306,certificate307,certificate308,certificate309,certificate310,certificate311]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound300,List.forall_mem_cons.mpr ⟨sound301,List.forall_mem_cons.mpr ⟨sound302,List.forall_mem_cons.mpr ⟨sound303,List.forall_mem_cons.mpr ⟨sound304,List.forall_mem_cons.mpr ⟨sound305,List.forall_mem_cons.mpr ⟨sound306,List.forall_mem_cons.mpr ⟨sound307,List.forall_mem_cons.mpr ⟨sound308,List.forall_mem_cons.mpr ⟨sound309,List.forall_mem_cons.mpr ⟨sound310,List.forall_mem_cons.mpr ⟨sound311,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch025
