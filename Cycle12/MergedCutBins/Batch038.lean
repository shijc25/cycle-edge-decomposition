import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch075
import Cycle12.MergedCutProfiles.Batch076
import Cycle12.MergedCutProfiles.Batch077

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch038

def retention456 : RatCutRetentionCertificate := ⟨(19/500),(77/2000),(1230424009623749555/17143398367560799813),(1066815691484957043/1000000000000000000),(5/2),(101410326511356426927/51200000000000000000),true,MergedCutProfiles.Batch076.profile3045,![MergedCutProfiles.Batch076.profile3045,MergedCutProfiles.Batch076.profile3046,MergedCutProfiles.Batch076.profile3047,MergedCutProfiles.Batch076.profile3048,MergedCutProfiles.Batch075.profile3027,MergedCutProfiles.Batch076.profile3049,MergedCutProfiles.Batch076.profile3050,MergedCutProfiles.Batch076.profile3051,MergedCutProfiles.Batch076.profile3052,MergedCutProfiles.Batch076.profile3053,MergedCutProfiles.Batch076.profile3054,MergedCutProfiles.Batch076.profile3055,MergedCutProfiles.Batch076.profile3056,MergedCutProfiles.Batch076.profile3057,MergedCutProfiles.Batch076.profile3058,MergedCutProfiles.Batch076.profile3059]⟩
theorem profilesValid456 : retention456.ProfilesValid := by
  change ∀ j : Fin 16, (retention456.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch076.valid3045
  · exact MergedCutProfiles.Batch076.valid3046
  · exact MergedCutProfiles.Batch076.valid3047
  · exact MergedCutProfiles.Batch076.valid3048
  · exact MergedCutProfiles.Batch075.valid3027
  · exact MergedCutProfiles.Batch076.valid3049
  · exact MergedCutProfiles.Batch076.valid3050
  · exact MergedCutProfiles.Batch076.valid3051
  · exact MergedCutProfiles.Batch076.valid3052
  · exact MergedCutProfiles.Batch076.valid3053
  · exact MergedCutProfiles.Batch076.valid3054
  · exact MergedCutProfiles.Batch076.valid3055
  · exact MergedCutProfiles.Batch076.valid3056
  · exact MergedCutProfiles.Batch076.valid3057
  · exact MergedCutProfiles.Batch076.valid3058
  · exact MergedCutProfiles.Batch076.valid3059
theorem numericValid456 : retention456.NumericValid := by decide +kernel
def certificate456 : RatCutBinCertificate := ⟨⟨retention456,(1025146501431020301/500000000000000000),(6713316315302437/100000000000000000),(88093019625623847/8000000000000000),(75711793260584595709/200000000000000000),(487354743048370693/250000000000000000)⟩,(994935557362310849/1000000000000000000),(390258552079389079/1000000000000000000),(242527498372032813/1000000000000000000),(145471142072890159/1000000000000000000)⟩
theorem valid456 : certificate456.Valid := by decide +kernel
theorem sound456 : certificate456.Sound := rat_cut_bin_certificate_sound certificate456 profilesValid456 numericValid456 valid456

def retention457 : RatCutRetentionCertificate := ⟨(19/500),(77/2000),(10946892672470775495/34286796735121599626),(246084801924749911/100000000000000000),(29/20),(10763433421726850662405185495718860099/7874713661591997152000000000000000000),false,MergedCutProfiles.Batch076.profile3060,(fun _ => MergedCutProfiles.Batch076.profile3060)⟩
theorem profilesValid457 : retention457.ProfilesValid := by
  exact MergedCutProfiles.Batch076.valid3060
theorem numericValid457 : retention457.NumericValid := by decide +kernel
def certificate457 : RatCutBinCertificate := ⟨⟨retention457,(1025146501431020301/500000000000000000),(6713316315302437/100000000000000000),(88093019625623847/8000000000000000),(75711793260584595709/200000000000000000),(1348709348352758711/1000000000000000000)⟩,(994935557362310849/1000000000000000000),(109599770196654263/250000000000000000),(50021347612038753/250000000000000000),(73392988054764351/500000000000000000)⟩
theorem valid457 : certificate457.Valid := by decide +kernel
theorem sound457 : certificate457.Sound := rat_cut_bin_certificate_sound certificate457 profilesValid457 numericValid457 valid457

def retention458 : RatCutRetentionCertificate := ⟨(19/500),(77/2000),(8313014984292207951/17143398367560799813),(2189378534494155099/200000000000000000),(21/20),(719111803012235727618974887429230880271/700601131038129631680000000000000000000),false,MergedCutProfiles.Batch076.profile3061,(fun _ => MergedCutProfiles.Batch076.profile3061)⟩
theorem profilesValid458 : retention458.ProfilesValid := by
  exact MergedCutProfiles.Batch076.valid3061
theorem numericValid458 : retention458.NumericValid := by decide +kernel
def certificate458 : RatCutBinCertificate := ⟨⟨retention458,(1025146501431020301/500000000000000000),(6713316315302437/100000000000000000),(88093019625623847/8000000000000000),(75711793260584595709/200000000000000000),(1013296181597384799/1000000000000000000)⟩,(994935557362310849/1000000000000000000),(242138464680760979/500000000000000000),(2571477680325901/15625000000000000),(14574485859331631/100000000000000000)⟩
theorem valid458 : certificate458.Valid := by decide +kernel
theorem sound458 : certificate458.Sound := rat_cut_bin_certificate_sound certificate458 profilesValid458 numericValid458 valid458

def retention459 : RatCutRetentionCertificate := ⟨(19/500),(77/2000),(16960213170952962663/34286796735121599626),(8313014984292207951/500000000000000000),(21/20),(2242787616652535199532461043467622468293/2216803995811255453600000000000000000000),false,MergedCutProfiles.Batch076.profile3062,(fun _ => MergedCutProfiles.Batch076.profile3062)⟩
theorem profilesValid459 : retention459.ProfilesValid := by
  exact MergedCutProfiles.Batch076.valid3062
theorem numericValid459 : retention459.NumericValid := by decide +kernel
def certificate459 : RatCutBinCertificate := ⟨⟨retention459,(1025146501431020301/500000000000000000),(6713316315302437/100000000000000000),(88093019625623847/8000000000000000),(75711793260584595709/200000000000000000),(998596331081455859/1000000000000000000)⟩,(994935557362310849/1000000000000000000),(481431133497754293/1000000000000000000),(41661605574052649/250000000000000000),(74757916998428107/500000000000000000)⟩
theorem valid459 : certificate459.Valid := by decide +kernel
theorem sound459 : certificate459.Sound := rat_cut_bin_certificate_sound certificate459 profilesValid459 numericValid459 valid459

def retention460 : RatCutRetentionCertificate := ⟨(19/500),(77/2000),(8564907651331246145/17143398367560799813),(16960213170952962663/1000000000000000000),(21/20),(27189208305314110748163305849019058737311/27136341073524740260800000000000000000000),false,MergedCutProfiles.Batch076.profile3063,(fun _ => MergedCutProfiles.Batch076.profile3063)⟩
theorem profilesValid460 : retention460.ProfilesValid := by
  exact MergedCutProfiles.Batch076.valid3063
theorem numericValid460 : retention460.NumericValid := by decide +kernel
def certificate460 : RatCutBinCertificate := ⟨⟨retention460,(1025146501431020301/500000000000000000),(6713316315302437/100000000000000000),(88093019625623847/8000000000000000),(75711793260584595709/200000000000000000),(494411666737415199/500000000000000000)⟩,(994935557362310849/1000000000000000000),(485806754126723589/1000000000000000000),(6538708658374567/40000000000000000),(145449089611204291/1000000000000000000)⟩
theorem valid460 : certificate460.Valid := by decide +kernel
theorem sound460 : certificate460.Sound := rat_cut_bin_certificate_sound certificate460 profilesValid460 numericValid460 valid460

def retention461 : RatCutRetentionCertificate := ⟨(19/500),(77/2000),(1/2),(1712981530266249229/100000000000000000),1,(16904851823975143996913552638177909899/17129815302662492290000000000000000000),false,MergedCutProfiles.Batch076.profile3064,(fun _ => MergedCutProfiles.Batch076.profile3064)⟩
theorem profilesValid461 : retention461.ProfilesValid := by
  exact MergedCutProfiles.Batch076.valid3064
theorem numericValid461 : retention461.NumericValid := by decide +kernel
def certificate461 : RatCutBinCertificate := ⟨⟨retention461,(1025146501431020301/500000000000000000),(6713316315302437/100000000000000000),(88093019625623847/8000000000000000),(75711793260584595709/200000000000000000),(121795906751960333/125000000000000000)⟩,(994935557362310849/1000000000000000000),(246411556762664953/500000000000000000),(31690547784401671/200000000000000000),(29063853704274847/200000000000000000)⟩
theorem valid461 : certificate461.Valid := by decide +kernel
theorem sound461 : certificate461.Sound := rat_cut_bin_certificate_sound certificate461 profilesValid461 numericValid461 valid461

def retention462 : RatCutRetentionCertificate := ⟨(19/500),(77/2000),(14819822526274554853/34286796735121599626),(75079853489752187/20000000000000000),(5/4),(68216172124046708820581237854107309079/60063882791801749600000000000000000000),false,MergedCutProfiles.Batch076.profile3065,(fun _ => MergedCutProfiles.Batch076.profile3065)⟩
theorem profilesValid462 : retention462.ProfilesValid := by
  exact MergedCutProfiles.Batch076.valid3065
theorem numericValid462 : retention462.NumericValid := by decide +kernel
def certificate462 : RatCutBinCertificate := ⟨⟨retention462,(1222518097931020301/500000000000000000),(6713316315302437/100000000000000000),(88093019625623847/8000000000000000),(75711793260584595709/200000000000000000),(558546677471451007/500000000000000000)⟩,(993960088432333113/1000000000000000000),(14363105831607721/40000000000000000),(273144570732829327/1000000000000000000),(50927254849815369/250000000000000000)⟩
theorem valid462 : certificate462.Valid := by decide +kernel
theorem sound462 : certificate462.Sound := rat_cut_bin_certificate_sound certificate462 profilesValid462 numericValid462 valid462

def retention463 : RatCutRetentionCertificate := ⟨(19/500),(77/2000),(17035003838710636263/34286796735121599626),(14819822526274554853/1000000000000000000),1,(58728301841189537419253472562717080211/59279290105098219412000000000000000000),false,MergedCutProfiles.Batch076.profile3066,(fun _ => MergedCutProfiles.Batch076.profile3066)⟩
theorem profilesValid463 : retention463.ProfilesValid := by
  exact MergedCutProfiles.Batch076.valid3066
theorem numericValid463 : retention463.NumericValid := by decide +kernel
def certificate463 : RatCutBinCertificate := ⟨⟨retention463,(1222518097931020301/500000000000000000),(6713316315302437/100000000000000000),(88093019625623847/8000000000000000),(75711793260584595709/200000000000000000),(97579870094318979/100000000000000000)⟩,(993960088432333113/1000000000000000000),(102767930422803159/250000000000000000),(6984052093002201/31250000000000000),(203336330577248207/1000000000000000000)⟩
theorem valid463 : certificate463.Valid := by decide +kernel
theorem sound463 : certificate463.Sound := rat_cut_bin_certificate_sound certificate463 profilesValid463 numericValid463 valid463

def retention464 : RatCutRetentionCertificate := ⟨(19/500),(77/2000),(1/2),(17035003838710636263/1000000000000000000),1,(1867766401803018879364133320698241577/1892778204301181807000000000000000000),false,MergedCutProfiles.Batch076.profile3064,(fun _ => MergedCutProfiles.Batch076.profile3064)⟩
theorem profilesValid464 : retention464.ProfilesValid := by
  exact MergedCutProfiles.Batch076.valid3064
theorem numericValid464 : retention464.NumericValid := by decide +kernel
def certificate464 : RatCutBinCertificate := ⟨⟨retention464,(1222518097931020301/500000000000000000),(6713316315302437/100000000000000000),(88093019625623847/8000000000000000),(75711793260584595709/200000000000000000),(97187917572939629/100000000000000000)⟩,(993960088432333113/1000000000000000000),(103182386771411771/250000000000000000),(55504816753257287/250000000000000000),(202865039736250471/1000000000000000000)⟩
theorem valid464 : certificate464.Valid := by decide +kernel
theorem sound464 : certificate464.Sound := rat_cut_bin_certificate_sound certificate464 profilesValid464 numericValid464 valid464

def retention465 : RatCutRetentionCertificate := ⟨(77/2000),(39/1000),(788321368722148447/33324258217759276002),(780516206655592521/1000000000000000000),(13/4),(17306763858550842783/8000000000000000000),true,MergedCutProfiles.Batch076.profile3067,![MergedCutProfiles.Batch076.profile3067,MergedCutProfiles.Batch076.profile3068,MergedCutProfiles.Batch076.profile3069,MergedCutProfiles.Batch076.profile3070,MergedCutProfiles.Batch076.profile3071,MergedCutProfiles.Batch076.profile3072,MergedCutProfiles.Batch076.profile3073,MergedCutProfiles.Batch076.profile3074,MergedCutProfiles.Batch076.profile3075,MergedCutProfiles.Batch076.profile3076,MergedCutProfiles.Batch076.profile3077,MergedCutProfiles.Batch076.profile3078,MergedCutProfiles.Batch076.profile3079,MergedCutProfiles.Batch077.profile3080,MergedCutProfiles.Batch077.profile3081,MergedCutProfiles.Batch077.profile3082]⟩
theorem profilesValid465 : retention465.ProfilesValid := by
  change ∀ j : Fin 16, (retention465.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch076.valid3067
  · exact MergedCutProfiles.Batch076.valid3068
  · exact MergedCutProfiles.Batch076.valid3069
  · exact MergedCutProfiles.Batch076.valid3070
  · exact MergedCutProfiles.Batch076.valid3071
  · exact MergedCutProfiles.Batch076.valid3072
  · exact MergedCutProfiles.Batch076.valid3073
  · exact MergedCutProfiles.Batch076.valid3074
  · exact MergedCutProfiles.Batch076.valid3075
  · exact MergedCutProfiles.Batch076.valid3076
  · exact MergedCutProfiles.Batch076.valid3077
  · exact MergedCutProfiles.Batch076.valid3078
  · exact MergedCutProfiles.Batch076.valid3079
  · exact MergedCutProfiles.Batch077.valid3080
  · exact MergedCutProfiles.Batch077.valid3081
  · exact MergedCutProfiles.Batch077.valid3082
theorem numericValid465 : retention465.NumericValid := by decide +kernel
def certificate465 : RatCutBinCertificate := ⟨⟨retention465,(256600747103535091/125000000000000000),(69043717129131353/1000000000000000000),(693446761838081229/62500000000000000),(185362666901472325183/500000000000000000),(2121825782393521111/1000000000000000000)⟩,(198966502880292769/200000000000000000),(408213522428965981/1000000000000000000),(226040442339887663/1000000000000000000),(116655271574564047/1000000000000000000)⟩
theorem valid465 : certificate465.Valid := by decide +kernel
theorem sound465 : certificate465.Sound := rat_cut_bin_certificate_sound certificate465 profilesValid465 numericValid465 valid465

def retention466 : RatCutRetentionCertificate := ⟨(77/2000),(39/1000),(444150125032005271/16662129108879638001),(788321368722148447/1000000000000000000),(13/4),(551799957875433156331/256000000000000000000),true,MergedCutProfiles.Batch077.profile3083,![MergedCutProfiles.Batch077.profile3083,MergedCutProfiles.Batch077.profile3084,MergedCutProfiles.Batch077.profile3085,MergedCutProfiles.Batch077.profile3086,MergedCutProfiles.Batch077.profile3087,MergedCutProfiles.Batch077.profile3088,MergedCutProfiles.Batch077.profile3089,MergedCutProfiles.Batch076.profile3075,MergedCutProfiles.Batch077.profile3090,MergedCutProfiles.Batch077.profile3091,MergedCutProfiles.Batch077.profile3092,MergedCutProfiles.Batch077.profile3093,MergedCutProfiles.Batch077.profile3094,MergedCutProfiles.Batch077.profile3095,MergedCutProfiles.Batch077.profile3096,MergedCutProfiles.Batch077.profile3097]⟩
theorem profilesValid466 : retention466.ProfilesValid := by
  change ∀ j : Fin 16, (retention466.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch077.valid3083
  · exact MergedCutProfiles.Batch077.valid3084
  · exact MergedCutProfiles.Batch077.valid3085
  · exact MergedCutProfiles.Batch077.valid3086
  · exact MergedCutProfiles.Batch077.valid3087
  · exact MergedCutProfiles.Batch077.valid3088
  · exact MergedCutProfiles.Batch077.valid3089
  · exact MergedCutProfiles.Batch076.valid3075
  · exact MergedCutProfiles.Batch077.valid3090
  · exact MergedCutProfiles.Batch077.valid3091
  · exact MergedCutProfiles.Batch077.valid3092
  · exact MergedCutProfiles.Batch077.valid3093
  · exact MergedCutProfiles.Batch077.valid3094
  · exact MergedCutProfiles.Batch077.valid3095
  · exact MergedCutProfiles.Batch077.valid3096
  · exact MergedCutProfiles.Batch077.valid3097
theorem numericValid466 : retention466.NumericValid := by decide +kernel
def certificate466 : RatCutBinCertificate := ⟨⟨retention466,(256600747103535091/125000000000000000),(69043717129131353/1000000000000000000),(693446761838081229/62500000000000000),(185362666901472325183/500000000000000000),(2113948915704765307/1000000000000000000)⟩,(198966502880292769/200000000000000000),(101960038025655919/250000000000000000),(28296890975872497/125000000000000000),(29179852862659991/250000000000000000)⟩
theorem valid466 : certificate466.Valid := by decide +kernel
theorem sound466 : certificate466.Sound := rat_cut_bin_certificate_sound certificate466 profilesValid466 numericValid466 valid466

def retention467 : RatCutRetentionCertificate := ⟨(77/2000),(39/1000),(463653128500000000/16662129108879638001),(444150125032005271/500000000000000000),(29/10),(85509556565901246013/40000000000000000000),true,MergedCutProfiles.Batch077.profile3098,![MergedCutProfiles.Batch077.profile3098,MergedCutProfiles.Batch077.profile3099,MergedCutProfiles.Batch077.profile3100,MergedCutProfiles.Batch077.profile3101,MergedCutProfiles.Batch077.profile3102,MergedCutProfiles.Batch077.profile3103,MergedCutProfiles.Batch077.profile3104,MergedCutProfiles.Batch077.profile3105,MergedCutProfiles.Batch077.profile3106,MergedCutProfiles.Batch077.profile3107,MergedCutProfiles.Batch076.profile3079,MergedCutProfiles.Batch077.profile3108,MergedCutProfiles.Batch077.profile3109,MergedCutProfiles.Batch077.profile3110,MergedCutProfiles.Batch077.profile3111,MergedCutProfiles.Batch077.profile3112]⟩
theorem profilesValid467 : retention467.ProfilesValid := by
  change ∀ j : Fin 16, (retention467.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch077.valid3098
  · exact MergedCutProfiles.Batch077.valid3099
  · exact MergedCutProfiles.Batch077.valid3100
  · exact MergedCutProfiles.Batch077.valid3101
  · exact MergedCutProfiles.Batch077.valid3102
  · exact MergedCutProfiles.Batch077.valid3103
  · exact MergedCutProfiles.Batch077.valid3104
  · exact MergedCutProfiles.Batch077.valid3105
  · exact MergedCutProfiles.Batch077.valid3106
  · exact MergedCutProfiles.Batch077.valid3107
  · exact MergedCutProfiles.Batch076.valid3079
  · exact MergedCutProfiles.Batch077.valid3108
  · exact MergedCutProfiles.Batch077.valid3109
  · exact MergedCutProfiles.Batch077.valid3110
  · exact MergedCutProfiles.Batch077.valid3111
  · exact MergedCutProfiles.Batch077.valid3112
theorem numericValid467 : retention467.NumericValid := by decide +kernel
def certificate467 : RatCutBinCertificate := ⟨⟨retention467,(256600747103535091/125000000000000000),(69043717129131353/1000000000000000000),(693446761838081229/62500000000000000),(185362666901472325183/500000000000000000),(210069060811342999/100000000000000000)⟩,(198966502880292769/200000000000000000),(38895766264036553/100000000000000000),(243753664084346767/1000000000000000000),(273967555409101/2000000000000000)⟩
theorem valid467 : certificate467.Valid := by decide +kernel
theorem sound467 : certificate467.Sound := rat_cut_bin_certificate_sound certificate467 profilesValid467 numericValid467 valid467

def certificates : List RatCutBinCertificate := [certificate456,certificate457,certificate458,certificate459,certificate460,certificate461,certificate462,certificate463,certificate464,certificate465,certificate466,certificate467]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound456,List.forall_mem_cons.mpr ⟨sound457,List.forall_mem_cons.mpr ⟨sound458,List.forall_mem_cons.mpr ⟨sound459,List.forall_mem_cons.mpr ⟨sound460,List.forall_mem_cons.mpr ⟨sound461,List.forall_mem_cons.mpr ⟨sound462,List.forall_mem_cons.mpr ⟨sound463,List.forall_mem_cons.mpr ⟨sound464,List.forall_mem_cons.mpr ⟨sound465,List.forall_mem_cons.mpr ⟨sound466,List.forall_mem_cons.mpr ⟨sound467,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch038
