import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch073
import Cycle12.MergedCutProfiles.Batch074
import Cycle12.MergedCutProfiles.Batch075
import Cycle12.MergedCutProfiles.Batch076

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch037

def retention444 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(479814477959825930/5041250208371305727),(1158202221330349133/1000000000000000000),(47/20),(2440358320571855069629/1280000000000000000000),true,MergedCutProfiles.Batch074.profile2964,![MergedCutProfiles.Batch074.profile2964,MergedCutProfiles.Batch073.profile2942,MergedCutProfiles.Batch074.profile2965,MergedCutProfiles.Batch074.profile2966,MergedCutProfiles.Batch074.profile2967,MergedCutProfiles.Batch074.profile2968,MergedCutProfiles.Batch074.profile2969,MergedCutProfiles.Batch074.profile2970,MergedCutProfiles.Batch074.profile2971,MergedCutProfiles.Batch074.profile2972,MergedCutProfiles.Batch074.profile2973,MergedCutProfiles.Batch074.profile2974,MergedCutProfiles.Batch074.profile2975,MergedCutProfiles.Batch074.profile2976,MergedCutProfiles.Batch074.profile2977,MergedCutProfiles.Batch074.profile2978]⟩
theorem profilesValid444 : retention444.ProfilesValid := by
  change ∀ j : Fin 16, (retention444.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch074.valid2964
  · exact MergedCutProfiles.Batch073.valid2942
  · exact MergedCutProfiles.Batch074.valid2965
  · exact MergedCutProfiles.Batch074.valid2966
  · exact MergedCutProfiles.Batch074.valid2967
  · exact MergedCutProfiles.Batch074.valid2968
  · exact MergedCutProfiles.Batch074.valid2969
  · exact MergedCutProfiles.Batch074.valid2970
  · exact MergedCutProfiles.Batch074.valid2971
  · exact MergedCutProfiles.Batch074.valid2972
  · exact MergedCutProfiles.Batch074.valid2973
  · exact MergedCutProfiles.Batch074.valid2974
  · exact MergedCutProfiles.Batch074.valid2975
  · exact MergedCutProfiles.Batch074.valid2976
  · exact MergedCutProfiles.Batch074.valid2977
  · exact MergedCutProfiles.Batch074.valid2978
theorem numericValid444 : retention444.NumericValid := by decide +kernel
def certificate444 : RatCutBinCertificate := ⟨⟨retention444,(514170209211313733/250000000000000000),(65254397982896969/1000000000000000000),(10929067132421787051/1000000000000000000),(193348572747214585511/500000000000000000),(234708808231290823/125000000000000000)⟩,(995016948275565787/1000000000000000000),(78739374477953171/200000000000000000),(119653751888462573/500000000000000000),(146963648113191113/1000000000000000000)⟩
theorem valid444 : certificate444.Valid := by decide +kernel
theorem sound444 : certificate444.Sound := rat_cut_bin_certificate_sound certificate444 profilesValid444 numericValid444 valid444

def retention445 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(13259311399457061258/35288751458599140089),(335870134571878151/100000000000000000),(13/10),(16795983300626543391747065045772746391/13434805382875126040000000000000000000),false,MergedCutProfiles.Batch074.profile2979,(fun _ => MergedCutProfiles.Batch074.profile2979)⟩
theorem profilesValid445 : retention445.ProfilesValid := by
  exact MergedCutProfiles.Batch074.valid2979
theorem numericValid445 : retention445.NumericValid := by decide +kernel
def certificate445 : RatCutBinCertificate := ⟨⟨retention445,(514170209211313733/250000000000000000),(65254397982896969/1000000000000000000),(10929067132421787051/1000000000000000000),(193348572747214585511/500000000000000000),(617109949214569513/500000000000000000)⟩,(995016948275565787/1000000000000000000),(1761741833845231/3906250000000000),(94934581888906219/500000000000000000),(18406507066122011/125000000000000000)⟩
theorem valid445 : certificate445.Valid := by decide +kernel
theorem sound445 : certificate445.Sound := rat_cut_bin_certificate_sound certificate445 profilesValid445 numericValid445 valid445

def retention446 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(17345948890488732231/35288751458599140089),(6629655699728530629/500000000000000000),(21/20),(5388985390718164876834605268786451390279/5303724559782824503200000000000000000000),false,MergedCutProfiles.Batch074.profile2980,(fun _ => MergedCutProfiles.Batch074.profile2980)⟩
theorem profilesValid446 : retention446.ProfilesValid := by
  exact MergedCutProfiles.Batch074.valid2980
theorem numericValid446 : retention446.NumericValid := by decide +kernel
def certificate446 : RatCutBinCertificate := ⟨⟨retention446,(514170209211313733/250000000000000000),(65254397982896969/1000000000000000000),(10929067132421787051/1000000000000000000),(193348572747214585511/500000000000000000),(501590818748194873/500000000000000000)⟩,(995016948275565787/1000000000000000000),(48334186660254441/100000000000000000),(165253484436258681/1000000000000000000),(73491213673281051/500000000000000000)⟩
theorem valid446 : certificate446.Valid := by decide +kernel
theorem sound446 : certificate446.Sound := rat_cut_bin_certificate_sound certificate446 profilesValid446 numericValid446 valid446

def retention447 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(17519408379393619554/35288751458599140089),(17345948890488732231/1000000000000000000),1,(718366787784577956272457574365626673/722747870437030509625000000000000000),false,MergedCutProfiles.Batch074.profile2981,(fun _ => MergedCutProfiles.Batch074.profile2981)⟩
theorem profilesValid447 : retention447.ProfilesValid := by
  exact MergedCutProfiles.Batch074.valid2981
theorem numericValid447 : retention447.NumericValid := by decide +kernel
def certificate447 : RatCutBinCertificate := ⟨⟨retention447,(514170209211313733/250000000000000000),(65254397982896969/1000000000000000000),(10929067132421787051/1000000000000000000),(193348572747214585511/500000000000000000),(490829156422791683/500000000000000000)⟩,(995016948275565787/1000000000000000000),(488096791455370703/1000000000000000000),(161819832349511113/1000000000000000000),(9348228211034999/62500000000000000)⟩
theorem valid447 : certificate447.Valid := by decide +kernel
theorem sound447 : certificate447.Sound := rat_cut_bin_certificate_sound certificate447 profilesValid447 numericValid447 valid447

def retention448 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(1/2),(8759704189696809777/500000000000000000),1,(69180014285870037662144379871942290503/70077633517574478216000000000000000000),false,MergedCutProfiles.Batch074.profile2982,(fun _ => MergedCutProfiles.Batch074.profile2982)⟩
theorem profilesValid448 : retention448.ProfilesValid := by
  exact MergedCutProfiles.Batch074.valid2982
theorem numericValid448 : retention448.NumericValid := by decide +kernel
def certificate448 : RatCutBinCertificate := ⟨⟨retention448,(514170209211313733/250000000000000000),(65254397982896969/1000000000000000000),(10929067132421787051/1000000000000000000),(193348572747214585511/500000000000000000),(97491109049944179/100000000000000000)⟩,(995016948275565787/1000000000000000000),(9825717061698299/20000000000000000),(159542908498700937/1000000000000000000),(18323106257146569/125000000000000000)⟩
theorem valid448 : certificate448.Valid := by decide +kernel
theorem sound448 : certificate448.Sound := rat_cut_bin_certificate_sound certificate448 profilesValid448 numericValid448 valid448

def retention449 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(2171307162399090500/5041250208371305727),(3736849452142867737/1000000000000000000),(5/4),(272308521595095660936698919473622296639/239158364937143535168000000000000000000),false,MergedCutProfiles.Batch074.profile2983,(fun _ => MergedCutProfiles.Batch074.profile2983)⟩
theorem profilesValid449 : retention449.ProfilesValid := by
  exact MergedCutProfiles.Batch074.valid2983
theorem numericValid449 : retention449.NumericValid := by decide +kernel
def certificate449 : RatCutBinCertificate := ⟨⟨retention449,(610310064461313733/250000000000000000),(65254397982896969/1000000000000000000),(10929067132421787051/1000000000000000000),(193348572747214585511/500000000000000000),(1120391127876261267/1000000000000000000)⟩,(198816968235162199/200000000000000000),(89913867217420117/250000000000000000),(272553293123727243/1000000000000000000),(25456205675704219/125000000000000000)⟩
theorem valid449 : certificate449.Valid := by decide +kernel
theorem sound449 : certificate449.Sound := rat_cut_bin_certificate_sound certificate449 profilesValid449 numericValid449 valid449

def retention450 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(17471031145371361413/35288751458599140089),(30398300273587267/2000000000000000),1,(3778982012760844390132392340864044099/3799787534198408375000000000000000000),false,MergedCutProfiles.Batch074.profile2984,(fun _ => MergedCutProfiles.Batch074.profile2984)⟩
theorem profilesValid450 : retention450.ProfilesValid := by
  exact MergedCutProfiles.Batch074.valid2984
theorem numericValid450 : retention450.NumericValid := by decide +kernel
def certificate450 : RatCutBinCertificate := ⟨⟨retention450,(610310064461313733/250000000000000000),(65254397982896969/1000000000000000000),(10929067132421787051/1000000000000000000),(193348572747214585511/500000000000000000),(979948433160382343/1000000000000000000)⟩,(198816968235162199/200000000000000000),(102800000178126121/250000000000000000),(55843913077857349/250000000000000000),(25548367384119413/125000000000000000)⟩
theorem valid450 : certificate450.Valid := by decide +kernel
theorem sound450 : certificate450.Sound := rat_cut_bin_certificate_sound certificate450 profilesValid450 numericValid450 valid450

def retention451 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(1/2),(17471031145371361413/1000000000000000000),1,(68986214328630643738987681179886170707/69884124581485445652000000000000000000),false,MergedCutProfiles.Batch074.profile2982,(fun _ => MergedCutProfiles.Batch074.profile2982)⟩
theorem profilesValid451 : retention451.ProfilesValid := by
  exact MergedCutProfiles.Batch074.valid2982
theorem numericValid451 : retention451.NumericValid := by decide +kernel
def certificate451 : RatCutBinCertificate := ⟨⟨retention451,(610310064461313733/250000000000000000),(65254397982896969/1000000000000000000),(10929067132421787051/1000000000000000000),(193348572747214585511/500000000000000000),(243143834802922179/250000000000000000)⟩,(198816968235162199/200000000000000000),(207158654022822479/500000000000000000),(220617251437864767/1000000000000000000),(12626228890583263/62500000000000000)⟩
theorem valid451 : certificate451.Valid := by decide +kernel
theorem sound451 : certificate451.Sound := rat_cut_bin_certificate_sound certificate451 profilesValid451 numericValid451 valid451

def retention452 : RatCutRetentionCertificate := ⟨(19/500),(77/2000),(783658426304562295/34286796735121599626),(775899431984715143/1000000000000000000),(33/10),(173776519631161733133/80000000000000000000),true,MergedCutProfiles.Batch074.profile2985,![MergedCutProfiles.Batch074.profile2985,MergedCutProfiles.Batch074.profile2986,MergedCutProfiles.Batch074.profile2987,MergedCutProfiles.Batch074.profile2988,MergedCutProfiles.Batch074.profile2989,MergedCutProfiles.Batch074.profile2990,MergedCutProfiles.Batch074.profile2991,MergedCutProfiles.Batch074.profile2992,MergedCutProfiles.Batch074.profile2993,MergedCutProfiles.Batch074.profile2994,MergedCutProfiles.Batch074.profile2995,MergedCutProfiles.Batch074.profile2996,MergedCutProfiles.Batch074.profile2997,MergedCutProfiles.Batch074.profile2998,MergedCutProfiles.Batch074.profile2999,MergedCutProfiles.Batch075.profile3000]⟩
theorem profilesValid452 : retention452.ProfilesValid := by
  change ∀ j : Fin 16, (retention452.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch074.valid2985
  · exact MergedCutProfiles.Batch074.valid2986
  · exact MergedCutProfiles.Batch074.valid2987
  · exact MergedCutProfiles.Batch074.valid2988
  · exact MergedCutProfiles.Batch074.valid2989
  · exact MergedCutProfiles.Batch074.valid2990
  · exact MergedCutProfiles.Batch074.valid2991
  · exact MergedCutProfiles.Batch074.valid2992
  · exact MergedCutProfiles.Batch074.valid2993
  · exact MergedCutProfiles.Batch074.valid2994
  · exact MergedCutProfiles.Batch074.valid2995
  · exact MergedCutProfiles.Batch074.valid2996
  · exact MergedCutProfiles.Batch074.valid2997
  · exact MergedCutProfiles.Batch074.valid2998
  · exact MergedCutProfiles.Batch074.valid2999
  · exact MergedCutProfiles.Batch075.valid3000
theorem numericValid452 : retention452.NumericValid := by decide +kernel
def certificate452 : RatCutBinCertificate := ⟨⟨retention452,(1025146501431020301/500000000000000000),(6713316315302437/100000000000000000),(88093019625623847/8000000000000000),(75711793260584595709/200000000000000000),(532738611038780903/250000000000000000)⟩,(994935557362310849/1000000000000000000),(81932096735870609/200000000000000000),(224746622734970289/1000000000000000000),(115210488031045119/1000000000000000000)⟩
theorem valid452 : certificate452.Valid := by decide +kernel
theorem sound452 : certificate452.Sound := rat_cut_bin_certificate_sound certificate452 profilesValid452 numericValid452 valid452

def retention453 : RatCutRetentionCertificate := ⟨(19/500),(77/2000),(891876389132148491/34286796735121599626),(156731685260912459/200000000000000000),(13/4),(551831109225718249603/256000000000000000000),true,MergedCutProfiles.Batch075.profile3001,![MergedCutProfiles.Batch075.profile3001,MergedCutProfiles.Batch075.profile3002,MergedCutProfiles.Batch075.profile3003,MergedCutProfiles.Batch075.profile3004,MergedCutProfiles.Batch075.profile3005,MergedCutProfiles.Batch075.profile3006,MergedCutProfiles.Batch074.profile2992,MergedCutProfiles.Batch075.profile3007,MergedCutProfiles.Batch075.profile3008,MergedCutProfiles.Batch075.profile3009,MergedCutProfiles.Batch075.profile3010,MergedCutProfiles.Batch075.profile3011,MergedCutProfiles.Batch075.profile3012,MergedCutProfiles.Batch075.profile3013,MergedCutProfiles.Batch075.profile3014,MergedCutProfiles.Batch075.profile3015]⟩
theorem profilesValid453 : retention453.ProfilesValid := by
  change ∀ j : Fin 16, (retention453.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch075.valid3001
  · exact MergedCutProfiles.Batch075.valid3002
  · exact MergedCutProfiles.Batch075.valid3003
  · exact MergedCutProfiles.Batch075.valid3004
  · exact MergedCutProfiles.Batch075.valid3005
  · exact MergedCutProfiles.Batch075.valid3006
  · exact MergedCutProfiles.Batch074.valid2992
  · exact MergedCutProfiles.Batch075.valid3007
  · exact MergedCutProfiles.Batch075.valid3008
  · exact MergedCutProfiles.Batch075.valid3009
  · exact MergedCutProfiles.Batch075.valid3010
  · exact MergedCutProfiles.Batch075.valid3011
  · exact MergedCutProfiles.Batch075.valid3012
  · exact MergedCutProfiles.Batch075.valid3013
  · exact MergedCutProfiles.Batch075.valid3014
  · exact MergedCutProfiles.Batch075.valid3015
theorem numericValid453 : retention453.NumericValid := by decide +kernel
def certificate453 : RatCutBinCertificate := ⟨⟨retention453,(1025146501431020301/500000000000000000),(6713316315302437/100000000000000000),(88093019625623847/8000000000000000),(75711793260584595709/200000000000000000),(1057481617628743977/500000000000000000)⟩,(994935557362310849/1000000000000000000),(205415968050529399/500000000000000000),(223702896235144397/1000000000000000000),(115260645187894011/1000000000000000000)⟩
theorem valid453 : certificate453.Valid := by decide +kernel
theorem sound453 : certificate453.Sound := rat_cut_bin_certificate_sound certificate453 profilesValid453 numericValid453 valid453

def retention454 : RatCutRetentionCertificate := ⟨(19/500),(77/2000),(472523554500000000/17143398367560799813),(891876389132148491/1000000000000000000),(29/10),(2738705226933523504231/1280000000000000000000),true,MergedCutProfiles.Batch075.profile3016,![MergedCutProfiles.Batch075.profile3016,MergedCutProfiles.Batch075.profile3017,MergedCutProfiles.Batch075.profile3018,MergedCutProfiles.Batch075.profile3019,MergedCutProfiles.Batch075.profile3020,MergedCutProfiles.Batch075.profile3021,MergedCutProfiles.Batch075.profile3022,MergedCutProfiles.Batch075.profile3023,MergedCutProfiles.Batch075.profile3024,MergedCutProfiles.Batch074.profile2996,MergedCutProfiles.Batch075.profile3025,MergedCutProfiles.Batch075.profile3026,MergedCutProfiles.Batch075.profile3027,MergedCutProfiles.Batch075.profile3028,MergedCutProfiles.Batch075.profile3029,MergedCutProfiles.Batch075.profile3030]⟩
theorem profilesValid454 : retention454.ProfilesValid := by
  change ∀ j : Fin 16, (retention454.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch075.valid3016
  · exact MergedCutProfiles.Batch075.valid3017
  · exact MergedCutProfiles.Batch075.valid3018
  · exact MergedCutProfiles.Batch075.valid3019
  · exact MergedCutProfiles.Batch075.valid3020
  · exact MergedCutProfiles.Batch075.valid3021
  · exact MergedCutProfiles.Batch075.valid3022
  · exact MergedCutProfiles.Batch075.valid3023
  · exact MergedCutProfiles.Batch075.valid3024
  · exact MergedCutProfiles.Batch074.valid2996
  · exact MergedCutProfiles.Batch075.valid3025
  · exact MergedCutProfiles.Batch075.valid3026
  · exact MergedCutProfiles.Batch075.valid3027
  · exact MergedCutProfiles.Batch075.valid3028
  · exact MergedCutProfiles.Batch075.valid3029
  · exact MergedCutProfiles.Batch075.valid3030
theorem numericValid454 : retention454.NumericValid := by decide +kernel
def certificate454 : RatCutBinCertificate := ⟨⟨retention454,(1025146501431020301/500000000000000000),(6713316315302437/100000000000000000),(88093019625623847/8000000000000000),(75711793260584595709/200000000000000000),(1051680840577020817/500000000000000000)⟩,(994935557362310849/1000000000000000000),(389599668997364883/1000000000000000000),(60786998087698567/250000000000000000),(68458430374620441/500000000000000000)⟩
theorem valid454 : certificate454.Valid := by decide +kernel
theorem sound454 : certificate454.Sound := rat_cut_bin_certificate_sound certificate454 profilesValid454 numericValid454 valid454

def retention455 : RatCutRetentionCertificate := ⟨(19/500),(77/2000),(1066815691484957043/34286796735121599626),(945047109/1000000000),(11/4),(8482702248656367861/4000000000000000000),true,MergedCutProfiles.Batch075.profile3031,![MergedCutProfiles.Batch075.profile3031,MergedCutProfiles.Batch075.profile3032,MergedCutProfiles.Batch075.profile3033,MergedCutProfiles.Batch075.profile3034,MergedCutProfiles.Batch075.profile3035,MergedCutProfiles.Batch075.profile3036,MergedCutProfiles.Batch075.profile3037,MergedCutProfiles.Batch075.profile3024,MergedCutProfiles.Batch075.profile3038,MergedCutProfiles.Batch075.profile3039,MergedCutProfiles.Batch074.profile2999,MergedCutProfiles.Batch076.profile3040,MergedCutProfiles.Batch076.profile3041,MergedCutProfiles.Batch076.profile3042,MergedCutProfiles.Batch076.profile3043,MergedCutProfiles.Batch076.profile3044]⟩
theorem profilesValid455 : retention455.ProfilesValid := by
  change ∀ j : Fin 16, (retention455.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch075.valid3031
  · exact MergedCutProfiles.Batch075.valid3032
  · exact MergedCutProfiles.Batch075.valid3033
  · exact MergedCutProfiles.Batch075.valid3034
  · exact MergedCutProfiles.Batch075.valid3035
  · exact MergedCutProfiles.Batch075.valid3036
  · exact MergedCutProfiles.Batch075.valid3037
  · exact MergedCutProfiles.Batch075.valid3024
  · exact MergedCutProfiles.Batch075.valid3038
  · exact MergedCutProfiles.Batch075.valid3039
  · exact MergedCutProfiles.Batch074.valid2999
  · exact MergedCutProfiles.Batch076.valid3040
  · exact MergedCutProfiles.Batch076.valid3041
  · exact MergedCutProfiles.Batch076.valid3042
  · exact MergedCutProfiles.Batch076.valid3043
  · exact MergedCutProfiles.Batch076.valid3044
theorem numericValid455 : retention455.NumericValid := by decide +kernel
def certificate455 : RatCutBinCertificate := ⟨⟨retention455,(1025146501431020301/500000000000000000),(6713316315302437/100000000000000000),(88093019625623847/8000000000000000),(75711793260584595709/200000000000000000),(2086298887989939549/1000000000000000000)⟩,(994935557362310849/1000000000000000000),(15325357607638803/40000000000000000),(1558102376300097/6250000000000000),(145530599348483991/1000000000000000000)⟩
theorem valid455 : certificate455.Valid := by decide +kernel
theorem sound455 : certificate455.Sound := rat_cut_bin_certificate_sound certificate455 profilesValid455 numericValid455 valid455

def certificates : List RatCutBinCertificate := [certificate444,certificate445,certificate446,certificate447,certificate448,certificate449,certificate450,certificate451,certificate452,certificate453,certificate454,certificate455]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound444,List.forall_mem_cons.mpr ⟨sound445,List.forall_mem_cons.mpr ⟨sound446,List.forall_mem_cons.mpr ⟨sound447,List.forall_mem_cons.mpr ⟨sound448,List.forall_mem_cons.mpr ⟨sound449,List.forall_mem_cons.mpr ⟨sound450,List.forall_mem_cons.mpr ⟨sound451,List.forall_mem_cons.mpr ⟨sound452,List.forall_mem_cons.mpr ⟨sound453,List.forall_mem_cons.mpr ⟨sound454,List.forall_mem_cons.mpr ⟨sound455,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch037
