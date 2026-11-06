import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch068
import Cycle12.MergedCutProfiles.Batch069
import Cycle12.MergedCutProfiles.Batch070
import Cycle12.MergedCutProfiles.Batch343
import Cycle12.MergedCutProfiles.Batch344
import Cycle12.MergedCutProfiles.Batch345
import Cycle12.MergedCutProfiles.Batch346
import Cycle12.MergedCutProfiles.Batch468
import Cycle12.MergedCutProfiles.Batch469
import Cycle12.MergedCutProfiles.Batch599
import Cycle12.MergedCutProfiles.Batch600

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch329

def retention3948 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(591365617816115561/794719304457696456462),(568290735124224207/1000000000000000000),4,(140777412030934334703/64000000000000000000),true,MergedCutProfiles.Batch599.profile23966,![MergedCutProfiles.Batch599.profile23966,MergedCutProfiles.Batch599.profile23967,MergedCutProfiles.Batch599.profile23968,MergedCutProfiles.Batch599.profile23969,MergedCutProfiles.Batch599.profile23970,MergedCutProfiles.Batch599.profile23971,MergedCutProfiles.Batch468.profile18752,MergedCutProfiles.Batch599.profile23972,MergedCutProfiles.Batch599.profile23973,MergedCutProfiles.Batch599.profile23974,MergedCutProfiles.Batch599.profile23975,MergedCutProfiles.Batch599.profile23976,MergedCutProfiles.Batch599.profile23977,MergedCutProfiles.Batch599.profile23978,MergedCutProfiles.Batch599.profile23979,MergedCutProfiles.Batch343.profile13730]⟩
theorem profilesValid3948 : retention3948.ProfilesValid := by
  change ∀ j : Fin 16, (retention3948.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch599.valid23966
  · exact MergedCutProfiles.Batch599.valid23967
  · exact MergedCutProfiles.Batch599.valid23968
  · exact MergedCutProfiles.Batch599.valid23969
  · exact MergedCutProfiles.Batch599.valid23970
  · exact MergedCutProfiles.Batch599.valid23971
  · exact MergedCutProfiles.Batch468.valid18752
  · exact MergedCutProfiles.Batch599.valid23972
  · exact MergedCutProfiles.Batch599.valid23973
  · exact MergedCutProfiles.Batch599.valid23974
  · exact MergedCutProfiles.Batch599.valid23975
  · exact MergedCutProfiles.Batch599.valid23976
  · exact MergedCutProfiles.Batch599.valid23977
  · exact MergedCutProfiles.Batch599.valid23978
  · exact MergedCutProfiles.Batch599.valid23979
  · exact MergedCutProfiles.Batch343.valid13730
theorem numericValid3948 : retention3948.NumericValid := by decide +kernel
def certificate3948 : RatCutBinCertificate := ⟨⟨retention3948,(371137458382606451/200000000000000000),(3628243259175483/62500000000000000),(10530755362721025409/1000000000000000000),(2103221777589503003203/250000000000000000),(2158728256372244607/1000000000000000000)⟩,(999791471851012039/1000000000000000000),(369101089415947933/500000000000000000),(7545150022437/200000000000000),(16449421928297059/1000000000000000000)⟩
theorem valid3948 : certificate3948.Valid := by decide +kernel
theorem sound3948 : certificate3948.Sound := rat_cut_bin_certificate_sound certificate3948 profilesValid3948 numericValid3948 valid3948

def retention3949 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(579988100000000000/397359652228848228231),(591365617816115561/1000000000000000000),4,(1793742364899967507/800000000000000000),true,MergedCutProfiles.Batch599.profile23967,![MergedCutProfiles.Batch599.profile23967,MergedCutProfiles.Batch599.profile23969,MergedCutProfiles.Batch599.profile23980,MergedCutProfiles.Batch599.profile23972,MergedCutProfiles.Batch599.profile23981,MergedCutProfiles.Batch599.profile23982,MergedCutProfiles.Batch468.profile18743,MergedCutProfiles.Batch343.profile13730,MergedCutProfiles.Batch599.profile23983,MergedCutProfiles.Batch344.profile13760,MergedCutProfiles.Batch599.profile23984,MergedCutProfiles.Batch469.profile18763,MergedCutProfiles.Batch599.profile23985,MergedCutProfiles.Batch468.profile18745,MergedCutProfiles.Batch599.profile23986,MergedCutProfiles.Batch468.profile18746]⟩
theorem profilesValid3949 : retention3949.ProfilesValid := by
  change ∀ j : Fin 16, (retention3949.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch599.valid23967
  · exact MergedCutProfiles.Batch599.valid23969
  · exact MergedCutProfiles.Batch599.valid23980
  · exact MergedCutProfiles.Batch599.valid23972
  · exact MergedCutProfiles.Batch599.valid23981
  · exact MergedCutProfiles.Batch599.valid23982
  · exact MergedCutProfiles.Batch468.valid18743
  · exact MergedCutProfiles.Batch343.valid13730
  · exact MergedCutProfiles.Batch599.valid23983
  · exact MergedCutProfiles.Batch344.valid13760
  · exact MergedCutProfiles.Batch599.valid23984
  · exact MergedCutProfiles.Batch469.valid18763
  · exact MergedCutProfiles.Batch599.valid23985
  · exact MergedCutProfiles.Batch468.valid18745
  · exact MergedCutProfiles.Batch599.valid23986
  · exact MergedCutProfiles.Batch468.valid18746
theorem numericValid3949 : retention3949.NumericValid := by decide +kernel
def certificate3949 : RatCutBinCertificate := ⟨⟨retention3949,(371137458382606451/200000000000000000),(3628243259175483/62500000000000000),(10530755362721025409/1000000000000000000),(2103221777589503003203/250000000000000000),(34394674286883617/15625000000000000)⟩,(999791471851012039/1000000000000000000),(704855805452634347/1000000000000000000),(24306199162284459/500000000000000000),(2712193398356783/125000000000000000)⟩
theorem valid3949 : certificate3949.Valid := by decide +kernel
theorem sound3949 : certificate3949.Sound := rat_cut_bin_certificate_sound certificate3949 profilesValid3949 numericValid3949 valid3949

def retention3950 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(1067292096001744235/397359652228848228231),(5799881/5000000),(11/4),(18827741188892498683/8000000000000000000),true,MergedCutProfiles.Batch599.profile23987,![MergedCutProfiles.Batch599.profile23987,MergedCutProfiles.Batch599.profile23988,MergedCutProfiles.Batch599.profile23989,MergedCutProfiles.Batch599.profile23990,MergedCutProfiles.Batch343.profile13745,MergedCutProfiles.Batch599.profile23984,MergedCutProfiles.Batch599.profile23985,MergedCutProfiles.Batch599.profile23986,MergedCutProfiles.Batch599.profile23991,MergedCutProfiles.Batch599.profile23992,MergedCutProfiles.Batch599.profile23993,MergedCutProfiles.Batch344.profile13771,MergedCutProfiles.Batch343.profile13732,MergedCutProfiles.Batch599.profile23994,MergedCutProfiles.Batch469.profile18764,MergedCutProfiles.Batch344.profile13762]⟩
theorem profilesValid3950 : retention3950.ProfilesValid := by
  change ∀ j : Fin 16, (retention3950.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch599.valid23987
  · exact MergedCutProfiles.Batch599.valid23988
  · exact MergedCutProfiles.Batch599.valid23989
  · exact MergedCutProfiles.Batch599.valid23990
  · exact MergedCutProfiles.Batch343.valid13745
  · exact MergedCutProfiles.Batch599.valid23984
  · exact MergedCutProfiles.Batch599.valid23985
  · exact MergedCutProfiles.Batch599.valid23986
  · exact MergedCutProfiles.Batch599.valid23991
  · exact MergedCutProfiles.Batch599.valid23992
  · exact MergedCutProfiles.Batch599.valid23993
  · exact MergedCutProfiles.Batch344.valid13771
  · exact MergedCutProfiles.Batch343.valid13732
  · exact MergedCutProfiles.Batch599.valid23994
  · exact MergedCutProfiles.Batch469.valid18764
  · exact MergedCutProfiles.Batch344.valid13762
theorem numericValid3950 : retention3950.NumericValid := by decide +kernel
def certificate3950 : RatCutBinCertificate := ⟨⟨retention3950,(371137458382606451/200000000000000000),(3628243259175483/62500000000000000),(10530755362721025409/1000000000000000000),(2103221777589503003203/250000000000000000),(1162667996804341923/500000000000000000)⟩,(999791471851012039/1000000000000000000),(17966156740179357/40000000000000000),(7653905936500421/40000000000000000),(127866049538141507/1000000000000000000)⟩
theorem valid3950 : certificate3950.Valid := by decide +kernel
theorem sound3950 : certificate3950.Sound := rat_cut_bin_certificate_sound certificate3950 profilesValid3950 numericValid3950 valid3950

def retention3951 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(32000000000000000000/397359652228848228231),(213458419200348847/100000000000000000),(9/5),(3349791200084249997935683674421428091/1707667353602790776000000000000000000),false,MergedCutProfiles.Batch599.profile23995,(fun _ => MergedCutProfiles.Batch599.profile23995)⟩
theorem profilesValid3951 : retention3951.ProfilesValid := by
  exact MergedCutProfiles.Batch599.valid23995
theorem numericValid3951 : retention3951.NumericValid := by decide +kernel
def certificate3951 : RatCutBinCertificate := ⟨⟨retention3951,(371137458382606451/200000000000000000),(3628243259175483/62500000000000000),(10530755362721025409/1000000000000000000),(2103221777589503003203/250000000000000000),(1943204665987164613/1000000000000000000)⟩,(999791471851012039/1000000000000000000),(82710715010519543/200000000000000000),(55322719472840993/250000000000000000),(186452777144050439/1000000000000000000)⟩
theorem valid3951 : certificate3951.Valid := by decide +kernel
theorem sound3951 : certificate3951.Sound := rat_cut_bin_certificate_sound certificate3951 profilesValid3951 numericValid3951 valid3951

def retention3952 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(1/2),64,1,(63844992829629538494070841750131834791/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch344.profile13789,(fun _ => MergedCutProfiles.Batch344.profile13789)⟩
theorem profilesValid3952 : retention3952.ProfilesValid := by
  exact MergedCutProfiles.Batch344.valid13789
theorem numericValid3952 : retention3952.NumericValid := by decide +kernel
def certificate3952 : RatCutBinCertificate := ⟨⟨retention3952,(371137458382606451/200000000000000000),(3628243259175483/62500000000000000),(10530755362721025409/1000000000000000000),(2103221777589503003203/250000000000000000),(123418542657519939/125000000000000000)⟩,(999791471851012039/1000000000000000000),(266654534909113779/500000000000000000),(131423952888220691/1000000000000000000),(63881436724025111/500000000000000000)⟩
theorem valid3952 : certificate3952.Valid := by decide +kernel
theorem sound3952 : certificate3952.Sound := rat_cut_bin_certificate_sound certificate3952 profilesValid3952 numericValid3952 valid3952

def retention3953 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(32000000000000000000/397359652228848228231),(22809629885876930449/1000000000000000000),1,(35165807544515938019323519889225143367/18247703908701544359200000000000000000),false,MergedCutProfiles.Batch599.profile23995,(fun _ => MergedCutProfiles.Batch599.profile23995)⟩
theorem profilesValid3953 : retention3953.ProfilesValid := by
  exact MergedCutProfiles.Batch599.valid23995
theorem numericValid3953 : retention3953.NumericValid := by decide +kernel
def certificate3953 : RatCutBinCertificate := ⟨⟨retention3953,(363867498182606451/200000000000000000),(3628243259175483/62500000000000000),(10530755362721025409/1000000000000000000),(2103221777589503003203/250000000000000000),(383421346345439291/200000000000000000)⟩,(249948889153972873/250000000000000000),(3992743141721867/125000000000000000),(419314224821347827/500000000000000000),(185347326043765869/125000000000000000)⟩
theorem valid3953 : certificate3953.Valid := by decide +kernel
theorem sound3953 : certificate3953.Sound := rat_cut_bin_certificate_sound certificate3953 profilesValid3953 numericValid3953 valid3953

def retention3954 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(1/2),64,1,(63844992829629538494070841750131834791/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch344.profile13789,(fun _ => MergedCutProfiles.Batch344.profile13789)⟩
theorem profilesValid3954 : retention3954.ProfilesValid := by
  exact MergedCutProfiles.Batch344.valid13789
theorem numericValid3954 : retention3954.NumericValid := by decide +kernel
def certificate3954 : RatCutBinCertificate := ⟨⟨retention3954,(363867498182606451/200000000000000000),(3628243259175483/62500000000000000),(10530755362721025409/1000000000000000000),(2103221777589503003203/250000000000000000),(987548723367809151/1000000000000000000)⟩,(249948889153972873/250000000000000000),(62008199283159329/1000000000000000000),(378455559390138151/500000000000000000),(183993976324763589/250000000000000000)⟩
theorem valid3954 : certificate3954.Valid := by decide +kernel
theorem sound3954 : certificate3954.Sound := rat_cut_bin_certificate_sound certificate3954 profilesValid3954 numericValid3954 valid3954

def retention3955 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(36455836930908611/46774558057064058789),(285900103369541111/500000000000000000),4,(70650850147058793071/32000000000000000000),true,MergedCutProfiles.Batch599.profile23996,![MergedCutProfiles.Batch599.profile23996,MergedCutProfiles.Batch599.profile23997,MergedCutProfiles.Batch599.profile23998,MergedCutProfiles.Batch599.profile23999,MergedCutProfiles.Batch469.profile18785,MergedCutProfiles.Batch600.profile24000,MergedCutProfiles.Batch600.profile24001,MergedCutProfiles.Batch469.profile18795,MergedCutProfiles.Batch600.profile24002,MergedCutProfiles.Batch600.profile24003,MergedCutProfiles.Batch600.profile24004,MergedCutProfiles.Batch600.profile24005,MergedCutProfiles.Batch344.profile13793,MergedCutProfiles.Batch469.profile18787,MergedCutProfiles.Batch600.profile24006,MergedCutProfiles.Batch600.profile24007]⟩
theorem profilesValid3955 : retention3955.ProfilesValid := by
  change ∀ j : Fin 16, (retention3955.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch599.valid23996
  · exact MergedCutProfiles.Batch599.valid23997
  · exact MergedCutProfiles.Batch599.valid23998
  · exact MergedCutProfiles.Batch599.valid23999
  · exact MergedCutProfiles.Batch469.valid18785
  · exact MergedCutProfiles.Batch600.valid24000
  · exact MergedCutProfiles.Batch600.valid24001
  · exact MergedCutProfiles.Batch469.valid18795
  · exact MergedCutProfiles.Batch600.valid24002
  · exact MergedCutProfiles.Batch600.valid24003
  · exact MergedCutProfiles.Batch600.valid24004
  · exact MergedCutProfiles.Batch600.valid24005
  · exact MergedCutProfiles.Batch344.valid13793
  · exact MergedCutProfiles.Batch469.valid18787
  · exact MergedCutProfiles.Batch600.valid24006
  · exact MergedCutProfiles.Batch600.valid24007
theorem numericValid3955 : retention3955.NumericValid := by decide +kernel
def certificate3955 : RatCutBinCertificate := ⟨⟨retention3955,(1860342387483647183/1000000000000000000),(61591158108543061/1000000000000000000),(2671917448581533249/250000000000000000),(1608156605809442427953/200000000000000000),(216495562175731851/100000000000000000)⟩,(999782064813889151/1000000000000000000),(732638648701175007/1000000000000000000),(19717754122806213/500000000000000000),(17255155819603403/1000000000000000000)⟩
theorem valid3955 : certificate3955.Valid := by decide +kernel
theorem sound3955 : certificate3955.Sound := rat_cut_bin_certificate_sound certificate3955 profilesValid3955 numericValid3955 valid3955

def retention3956 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(72878425812500000/46774558057064058789),(36455836930908611/62500000000000000),4,(35619565842031463003/16000000000000000000),true,MergedCutProfiles.Batch599.profile23997,![MergedCutProfiles.Batch599.profile23997,MergedCutProfiles.Batch599.profile23999,MergedCutProfiles.Batch600.profile24000,MergedCutProfiles.Batch469.profile18795,MergedCutProfiles.Batch600.profile24003,MergedCutProfiles.Batch600.profile24005,MergedCutProfiles.Batch469.profile18787,MergedCutProfiles.Batch600.profile24007,MergedCutProfiles.Batch600.profile24008,MergedCutProfiles.Batch600.profile24009,MergedCutProfiles.Batch600.profile24010,MergedCutProfiles.Batch346.profile13844,MergedCutProfiles.Batch344.profile13794,MergedCutProfiles.Batch600.profile24011,MergedCutProfiles.Batch068.profile2757,MergedCutProfiles.Batch345.profile13805]⟩
theorem profilesValid3956 : retention3956.ProfilesValid := by
  change ∀ j : Fin 16, (retention3956.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch599.valid23997
  · exact MergedCutProfiles.Batch599.valid23999
  · exact MergedCutProfiles.Batch600.valid24000
  · exact MergedCutProfiles.Batch469.valid18795
  · exact MergedCutProfiles.Batch600.valid24003
  · exact MergedCutProfiles.Batch600.valid24005
  · exact MergedCutProfiles.Batch469.valid18787
  · exact MergedCutProfiles.Batch600.valid24007
  · exact MergedCutProfiles.Batch600.valid24008
  · exact MergedCutProfiles.Batch600.valid24009
  · exact MergedCutProfiles.Batch600.valid24010
  · exact MergedCutProfiles.Batch346.valid13844
  · exact MergedCutProfiles.Batch344.valid13794
  · exact MergedCutProfiles.Batch600.valid24011
  · exact MergedCutProfiles.Batch068.valid2757
  · exact MergedCutProfiles.Batch345.valid13805
theorem numericValid3956 : retention3956.NumericValid := by decide +kernel
def certificate3956 : RatCutBinCertificate := ⟨⟨retention3956,(1860342387483647183/1000000000000000000),(61591158108543061/1000000000000000000),(2671917448581533249/250000000000000000),(1608156605809442427953/200000000000000000),(2183339422618507509/1000000000000000000)⟩,(999782064813889151/1000000000000000000),(716834186048145173/1000000000000000000),(44524024744342657/1000000000000000000),(19689977267532487/1000000000000000000)⟩
theorem valid3956 : certificate3956.Valid := by decide +kernel
theorem sound3956 : certificate3956.Sound := rat_cut_bin_certificate_sound certificate3956 profilesValid3956 numericValid3956 valid3956

def retention3957 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(753101891562440753/187098232228256235156),(1166054813/1000000000),(27/10),(1865958520898580997/800000000000000000),true,MergedCutProfiles.Batch600.profile24012,![MergedCutProfiles.Batch600.profile24012,MergedCutProfiles.Batch600.profile24003,MergedCutProfiles.Batch345.profile13804,MergedCutProfiles.Batch600.profile24013,MergedCutProfiles.Batch344.profile13794,MergedCutProfiles.Batch600.profile24014,MergedCutProfiles.Batch600.profile24015,MergedCutProfiles.Batch069.profile2787,MergedCutProfiles.Batch600.profile24016,MergedCutProfiles.Batch344.profile13796,MergedCutProfiles.Batch345.profile13832,MergedCutProfiles.Batch600.profile24017,MergedCutProfiles.Batch600.profile24018,MergedCutProfiles.Batch600.profile24019,MergedCutProfiles.Batch344.profile13798,MergedCutProfiles.Batch069.profile2788]⟩
theorem profilesValid3957 : retention3957.ProfilesValid := by
  change ∀ j : Fin 16, (retention3957.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch600.valid24012
  · exact MergedCutProfiles.Batch600.valid24003
  · exact MergedCutProfiles.Batch345.valid13804
  · exact MergedCutProfiles.Batch600.valid24013
  · exact MergedCutProfiles.Batch344.valid13794
  · exact MergedCutProfiles.Batch600.valid24014
  · exact MergedCutProfiles.Batch600.valid24015
  · exact MergedCutProfiles.Batch069.valid2787
  · exact MergedCutProfiles.Batch600.valid24016
  · exact MergedCutProfiles.Batch344.valid13796
  · exact MergedCutProfiles.Batch345.valid13832
  · exact MergedCutProfiles.Batch600.valid24017
  · exact MergedCutProfiles.Batch600.valid24018
  · exact MergedCutProfiles.Batch600.valid24019
  · exact MergedCutProfiles.Batch344.valid13798
  · exact MergedCutProfiles.Batch069.valid2788
theorem numericValid3957 : retention3957.NumericValid := by decide +kernel
def certificate3957 : RatCutBinCertificate := ⟨⟨retention3957,(1860342387483647183/1000000000000000000),(61591158108543061/1000000000000000000),(2671917448581533249/250000000000000000),(1608156605809442427953/200000000000000000),(1151750926017775037/500000000000000000)⟩,(999782064813889151/1000000000000000000),(226177840337289179/500000000000000000),(94398202198009503/500000000000000000),(63349003490167971/500000000000000000)⟩
theorem valid3957 : certificate3957.Valid := by decide +kernel
theorem sound3957 : certificate3957.Sound := rat_cut_bin_certificate_sound certificate3957 profilesValid3957 numericValid3957 valid3957

def retention3958 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(4000000000000000000/46774558057064058789),(753101891562440753/250000000000000000),(3/2),(124022381169486018477/64000000000000000000),true,MergedCutProfiles.Batch345.profile13822,![MergedCutProfiles.Batch345.profile13822,MergedCutProfiles.Batch600.profile24020,MergedCutProfiles.Batch069.profile2766,MergedCutProfiles.Batch600.profile24021,MergedCutProfiles.Batch600.profile24022,MergedCutProfiles.Batch600.profile24023,MergedCutProfiles.Batch600.profile24024,MergedCutProfiles.Batch600.profile24025,MergedCutProfiles.Batch600.profile24026,MergedCutProfiles.Batch600.profile24027,MergedCutProfiles.Batch600.profile24028,MergedCutProfiles.Batch600.profile24029,MergedCutProfiles.Batch600.profile24030,MergedCutProfiles.Batch600.profile24031,MergedCutProfiles.Batch600.profile24032,MergedCutProfiles.Batch600.profile24033]⟩
theorem profilesValid3958 : retention3958.ProfilesValid := by
  change ∀ j : Fin 16, (retention3958.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch345.valid13822
  · exact MergedCutProfiles.Batch600.valid24020
  · exact MergedCutProfiles.Batch069.valid2766
  · exact MergedCutProfiles.Batch600.valid24021
  · exact MergedCutProfiles.Batch600.valid24022
  · exact MergedCutProfiles.Batch600.valid24023
  · exact MergedCutProfiles.Batch600.valid24024
  · exact MergedCutProfiles.Batch600.valid24025
  · exact MergedCutProfiles.Batch600.valid24026
  · exact MergedCutProfiles.Batch600.valid24027
  · exact MergedCutProfiles.Batch600.valid24028
  · exact MergedCutProfiles.Batch600.valid24029
  · exact MergedCutProfiles.Batch600.valid24030
  · exact MergedCutProfiles.Batch600.valid24031
  · exact MergedCutProfiles.Batch600.valid24032
  · exact MergedCutProfiles.Batch600.valid24033
theorem numericValid3958 : retention3958.NumericValid := by decide +kernel
def certificate3958 : RatCutBinCertificate := ⟨⟨retention3958,(1860342387483647183/1000000000000000000),(61591158108543061/1000000000000000000),(2671917448581533249/250000000000000000),(1608156605809442427953/200000000000000000),(960884220183481257/500000000000000000)⟩,(999782064813889151/1000000000000000000),(375226862595248431/1000000000000000000),(256963774613579397/1000000000000000000),(256430601684608801/1000000000000000000)⟩
theorem valid3958 : certificate3958.Valid := by decide +kernel
theorem sound3958 : certificate3958.Sound := rat_cut_bin_certificate_sound certificate3958 profilesValid3958 numericValid3958 valid3958

def retention3959 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(1/2),64,1,(15961296343634275519387494158967405759/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch070.profile2821,(fun _ => MergedCutProfiles.Batch070.profile2821)⟩
theorem profilesValid3959 : retention3959.ProfilesValid := by
  exact MergedCutProfiles.Batch070.valid2821
theorem numericValid3959 : retention3959.NumericValid := by decide +kernel
def certificate3959 : RatCutBinCertificate := ⟨⟨retention3959,(1860342387483647183/1000000000000000000),(61591158108543061/1000000000000000000),(2671917448581533249/250000000000000000),(1608156605809442427953/200000000000000000),(49343009738177219/50000000000000000)⟩,(999782064813889151/1000000000000000000),(267501749569891079/500000000000000000),(65180716354481343/500000000000000000),(63333521931071683/500000000000000000)⟩
theorem valid3959 : certificate3959.Valid := by decide +kernel
theorem sound3959 : certificate3959.Sound := rat_cut_bin_certificate_sound certificate3959 profilesValid3959 numericValid3959 valid3959

def certificates : List RatCutBinCertificate := [certificate3948,certificate3949,certificate3950,certificate3951,certificate3952,certificate3953,certificate3954,certificate3955,certificate3956,certificate3957,certificate3958,certificate3959]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3948,List.forall_mem_cons.mpr ⟨sound3949,List.forall_mem_cons.mpr ⟨sound3950,List.forall_mem_cons.mpr ⟨sound3951,List.forall_mem_cons.mpr ⟨sound3952,List.forall_mem_cons.mpr ⟨sound3953,List.forall_mem_cons.mpr ⟨sound3954,List.forall_mem_cons.mpr ⟨sound3955,List.forall_mem_cons.mpr ⟨sound3956,List.forall_mem_cons.mpr ⟨sound3957,List.forall_mem_cons.mpr ⟨sound3958,List.forall_mem_cons.mpr ⟨sound3959,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch329
