import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch076
import Cycle12.MergedCutProfiles.Batch077
import Cycle12.MergedCutProfiles.Batch078
import Cycle12.MergedCutProfiles.Batch079

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch039

def retention468 : RatCutRetentionCertificate := ⟨(77/2000),(39/1000),(471474307613427217/16662129108879638001),(927306257/1000000000),(14/5),(8534440314356480207/4000000000000000000),true,MergedCutProfiles.Batch077.profile3113,![MergedCutProfiles.Batch077.profile3113,MergedCutProfiles.Batch077.profile3114,MergedCutProfiles.Batch077.profile3115,MergedCutProfiles.Batch077.profile3116,MergedCutProfiles.Batch076.profile3072,MergedCutProfiles.Batch077.profile3117,MergedCutProfiles.Batch077.profile3118,MergedCutProfiles.Batch077.profile3119,MergedCutProfiles.Batch078.profile3120,MergedCutProfiles.Batch076.profile3078,MergedCutProfiles.Batch078.profile3121,MergedCutProfiles.Batch078.profile3122,MergedCutProfiles.Batch078.profile3123,MergedCutProfiles.Batch078.profile3124,MergedCutProfiles.Batch078.profile3125,MergedCutProfiles.Batch078.profile3126]⟩
theorem profilesValid468 : retention468.ProfilesValid := by
  change ∀ j : Fin 16, (retention468.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch077.valid3113
  · exact MergedCutProfiles.Batch077.valid3114
  · exact MergedCutProfiles.Batch077.valid3115
  · exact MergedCutProfiles.Batch077.valid3116
  · exact MergedCutProfiles.Batch076.valid3072
  · exact MergedCutProfiles.Batch077.valid3117
  · exact MergedCutProfiles.Batch077.valid3118
  · exact MergedCutProfiles.Batch077.valid3119
  · exact MergedCutProfiles.Batch078.valid3120
  · exact MergedCutProfiles.Batch076.valid3078
  · exact MergedCutProfiles.Batch078.valid3121
  · exact MergedCutProfiles.Batch078.valid3122
  · exact MergedCutProfiles.Batch078.valid3123
  · exact MergedCutProfiles.Batch078.valid3124
  · exact MergedCutProfiles.Batch078.valid3125
  · exact MergedCutProfiles.Batch078.valid3126
theorem numericValid468 : retention468.NumericValid := by decide +kernel
def certificate468 : RatCutBinCertificate := ⟨⟨retention468,(256600747103535091/125000000000000000),(69043717129131353/1000000000000000000),(693446761838081229/62500000000000000),(185362666901472325183/500000000000000000),(131114957540823037/62500000000000000)⟩,(198966502880292769/200000000000000000),(19118010110817203/50000000000000000),(12501970598060219/50000000000000000),(72254137456984681/500000000000000000)⟩
theorem valid468 : certificate468.Valid := by decide +kernel
theorem sound468 : certificate468.Sound := rat_cut_bin_certificate_sound certificate468 profilesValid468 numericValid468 valid468

def retention469 : RatCutRetentionCertificate := ⟨(77/2000),(39/1000),(184280234912563829/5554043036293212667),(471474307613427217/500000000000000000),(14/5),(1357816023398416031509/640000000000000000000),true,MergedCutProfiles.Batch078.profile3127,![MergedCutProfiles.Batch078.profile3127,MergedCutProfiles.Batch078.profile3128,MergedCutProfiles.Batch078.profile3129,MergedCutProfiles.Batch077.profile3087,MergedCutProfiles.Batch076.profile3073,MergedCutProfiles.Batch078.profile3130,MergedCutProfiles.Batch078.profile3131,MergedCutProfiles.Batch078.profile3132,MergedCutProfiles.Batch078.profile3133,MergedCutProfiles.Batch077.profile3080,MergedCutProfiles.Batch078.profile3134,MergedCutProfiles.Batch077.profile3096,MergedCutProfiles.Batch078.profile3135,MergedCutProfiles.Batch078.profile3136,MergedCutProfiles.Batch078.profile3137,MergedCutProfiles.Batch078.profile3138]⟩
theorem profilesValid469 : retention469.ProfilesValid := by
  change ∀ j : Fin 16, (retention469.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch078.valid3127
  · exact MergedCutProfiles.Batch078.valid3128
  · exact MergedCutProfiles.Batch078.valid3129
  · exact MergedCutProfiles.Batch077.valid3087
  · exact MergedCutProfiles.Batch076.valid3073
  · exact MergedCutProfiles.Batch078.valid3130
  · exact MergedCutProfiles.Batch078.valid3131
  · exact MergedCutProfiles.Batch078.valid3132
  · exact MergedCutProfiles.Batch078.valid3133
  · exact MergedCutProfiles.Batch077.valid3080
  · exact MergedCutProfiles.Batch078.valid3134
  · exact MergedCutProfiles.Batch077.valid3096
  · exact MergedCutProfiles.Batch078.valid3135
  · exact MergedCutProfiles.Batch078.valid3136
  · exact MergedCutProfiles.Batch078.valid3137
  · exact MergedCutProfiles.Batch078.valid3138
theorem numericValid469 : retention469.NumericValid := by decide +kernel
def certificate469 : RatCutBinCertificate := ⟨⟨retention469,(256600747103535091/125000000000000000),(69043717129131353/1000000000000000000),(693446761838081229/62500000000000000),(185362666901472325183/500000000000000000),(2085816821184098243/1000000000000000000)⟩,(198966502880292769/200000000000000000),(47732057094160551/125000000000000000),(50104801343416483/200000000000000000),(144680094428121507/1000000000000000000)⟩
theorem valid469 : certificate469.Valid := by decide +kernel
theorem sound469 : certificate469.Sound := rat_cut_bin_certificate_sound certificate469 profilesValid469 numericValid469 valid469

def retention470 : RatCutRetentionCertificate := ⟨(77/2000),(39/1000),(1422756312843416623/16662129108879638001),(552840704737691487/500000000000000000),(49/20),(1240555417543833629727/640000000000000000000),true,MergedCutProfiles.Batch077.profile3115,![MergedCutProfiles.Batch077.profile3115,MergedCutProfiles.Batch078.profile3139,MergedCutProfiles.Batch078.profile3140,MergedCutProfiles.Batch078.profile3141,MergedCutProfiles.Batch077.profile3097,MergedCutProfiles.Batch078.profile3142,MergedCutProfiles.Batch078.profile3143,MergedCutProfiles.Batch078.profile3144,MergedCutProfiles.Batch078.profile3145,MergedCutProfiles.Batch078.profile3146,MergedCutProfiles.Batch078.profile3147,MergedCutProfiles.Batch078.profile3148,MergedCutProfiles.Batch078.profile3149,MergedCutProfiles.Batch078.profile3150,MergedCutProfiles.Batch078.profile3151,MergedCutProfiles.Batch078.profile3152]⟩
theorem profilesValid470 : retention470.ProfilesValid := by
  change ∀ j : Fin 16, (retention470.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch077.valid3115
  · exact MergedCutProfiles.Batch078.valid3139
  · exact MergedCutProfiles.Batch078.valid3140
  · exact MergedCutProfiles.Batch078.valid3141
  · exact MergedCutProfiles.Batch077.valid3097
  · exact MergedCutProfiles.Batch078.valid3142
  · exact MergedCutProfiles.Batch078.valid3143
  · exact MergedCutProfiles.Batch078.valid3144
  · exact MergedCutProfiles.Batch078.valid3145
  · exact MergedCutProfiles.Batch078.valid3146
  · exact MergedCutProfiles.Batch078.valid3147
  · exact MergedCutProfiles.Batch078.valid3148
  · exact MergedCutProfiles.Batch078.valid3149
  · exact MergedCutProfiles.Batch078.valid3150
  · exact MergedCutProfiles.Batch078.valid3151
  · exact MergedCutProfiles.Batch078.valid3152
theorem numericValid470 : retention470.NumericValid := by decide +kernel
def certificate470 : RatCutBinCertificate := ⟨⟨retention470,(256600747103535091/125000000000000000),(69043717129131353/1000000000000000000),(693446761838081229/62500000000000000),(185362666901472325183/500000000000000000),(953534259957989451/500000000000000000)⟩,(198966502880292769/200000000000000000),(1224403503067773/3125000000000000),(120535827505902121/500000000000000000),(144890717828571911/1000000000000000000)⟩
theorem valid470 : certificate470.Valid := by decide +kernel
theorem sound470 : certificate470.Sound := rat_cut_bin_certificate_sound certificate470 profilesValid470 numericValid470 valid470

def retention471 : RatCutRetentionCertificate := ⟨(77/2000),(39/1000),(11806385723753745625/33324258217759276002),(1422756312843416623/500000000000000000),(13/10),(91214172003070361283321339004844669121/71137815642170831150000000000000000000),false,MergedCutProfiles.Batch078.profile3153,(fun _ => MergedCutProfiles.Batch078.profile3153)⟩
theorem profilesValid471 : retention471.ProfilesValid := by
  exact MergedCutProfiles.Batch078.valid3153
theorem numericValid471 : retention471.NumericValid := by decide +kernel
def certificate471 : RatCutBinCertificate := ⟨⟨retention471,(256600747103535091/125000000000000000),(69043717129131353/1000000000000000000),(693446761838081229/62500000000000000),(185362666901472325183/500000000000000000),(1265610282570198389/1000000000000000000)⟩,(198966502880292769/200000000000000000),(226225807325028731/500000000000000000),(47180078062895169/250000000000000000),(144607496794223197/1000000000000000000)⟩
theorem valid471 : certificate471.Valid := by decide +kernel
theorem sound471 : certificate471.Sound := rat_cut_bin_certificate_sound certificate471 profilesValid471 numericValid471 valid471

def retention472 : RatCutRetentionCertificate := ⟨(77/2000),(39/1000),(8116539999008916205/16662129108879638001),(18890217158005993/1600000000000000),(21/20),(773206018815968126560490721893607064151/755608686320239720000000000000000000000),false,MergedCutProfiles.Batch078.profile3154,(fun _ => MergedCutProfiles.Batch078.profile3154)⟩
theorem profilesValid472 : retention472.ProfilesValid := by
  exact MergedCutProfiles.Batch078.valid3154
theorem numericValid472 : retention472.NumericValid := by decide +kernel
def certificate472 : RatCutBinCertificate := ⟨⟨retention472,(256600747103535091/125000000000000000),(69043717129131353/1000000000000000000),(693446761838081229/62500000000000000),(185362666901472325183/500000000000000000),(15779307434487517/15625000000000000)⟩,(198966502880292769/200000000000000000),(241821945146345369/500000000000000000),(82516999557547469/500000000000000000),(73253211504356321/500000000000000000)⟩
theorem valid472 : certificate472.Valid := by decide +kernel
theorem sound472 : certificate472.Sound := rat_cut_bin_certificate_sound certificate472 profilesValid472 numericValid472 valid472

def retention473 : RatCutRetentionCertificate := ⟨(77/2000),(39/1000),(16559364905977990843/33324258217759276002),(1623307999801783241/100000000000000000),(21/20),(261571877906135082109008894257680998551/259729279968285318560000000000000000000),false,MergedCutProfiles.Batch078.profile3155,(fun _ => MergedCutProfiles.Batch078.profile3155)⟩
theorem profilesValid473 : retention473.ProfilesValid := by
  exact MergedCutProfiles.Batch078.valid3155
theorem numericValid473 : retention473.NumericValid := by decide +kernel
def certificate473 : RatCutBinCertificate := ⟨⟨retention473,(256600747103535091/125000000000000000),(69043717129131353/1000000000000000000),(693446761838081229/62500000000000000),(185362666901472325183/500000000000000000),(198736216652994937/200000000000000000)⟩,(198966502880292769/200000000000000000),(96837577460411721/200000000000000000),(164639143707267051/1000000000000000000),(29365231613794267/200000000000000000)⟩
theorem valid473 : certificate473.Valid := by decide +kernel
theorem sound473 : certificate473.Sound := rat_cut_bin_certificate_sound certificate473 profilesValid473 numericValid473 valid473

def retention474 : RatCutRetentionCertificate := ⟨(77/2000),(39/1000),(1/2),(16559364905977990843/1000000000000000000),(21/20),(26522871313675377606482613102685875941631/26494983849564785348800000000000000000000),false,MergedCutProfiles.Batch078.profile3156,(fun _ => MergedCutProfiles.Batch078.profile3156)⟩
theorem profilesValid474 : retention474.ProfilesValid := by
  exact MergedCutProfiles.Batch078.valid3156
theorem numericValid474 : retention474.NumericValid := by decide +kernel
def certificate474 : RatCutBinCertificate := ⟨⟨retention474,(256600747103535091/125000000000000000),(69043717129131353/1000000000000000000),(693446761838081229/62500000000000000),(185362666901472325183/500000000000000000),(493819670287050401/500000000000000000)⟩,(198966502880292769/200000000000000000),(486761838717376379/1000000000000000000),(81389569737696617/500000000000000000),(1444802274511879/10000000000000000)⟩
theorem valid474 : certificate474.Valid := by decide +kernel
theorem sound474 : certificate474.Sound := rat_cut_bin_certificate_sound certificate474 profilesValid474 numericValid474 valid474

def retention475 : RatCutRetentionCertificate := ⟨(77/2000),(39/1000),(4816930621440726499/11108086072586425334),(3771431162707975121/1000000000000000000),(6/5),(424620072516387558968769434386436714159/377143116270797512100000000000000000000),false,MergedCutProfiles.Batch078.profile3157,(fun _ => MergedCutProfiles.Batch078.profile3157)⟩
theorem profilesValid475 : retention475.ProfilesValid := by
  exact MergedCutProfiles.Batch078.valid3157
theorem numericValid475 : retention475.NumericValid := by decide +kernel
def certificate475 : RatCutBinCertificate := ⟨⟨retention475,(306138928728535091/125000000000000000),(69043717129131353/1000000000000000000),(693446761838081229/62500000000000000),(185362666901472325183/500000000000000000),(22151928268553091/20000000000000000)⟩,(993834460363187229/1000000000000000000),(360513650999677201/1000000000000000000),(135838419504212767/500000000000000000),(5172127713162859/25000000000000000)⟩
theorem valid475 : certificate475.Valid := by decide +kernel
theorem sound475 : certificate475.Sound := rat_cut_bin_certificate_sound certificate475 profilesValid475 numericValid475 valid475

def retention476 : RatCutRetentionCertificate := ⟨(77/2000),(39/1000),(16446349117725119441/33324258217759276002),(14450791864322179497/1000000000000000000),1,(768151185451775616856956345904128489/770708899430516239840000000000000000),false,MergedCutProfiles.Batch078.profile3158,(fun _ => MergedCutProfiles.Batch078.profile3158)⟩
theorem profilesValid476 : retention476.ProfilesValid := by
  exact MergedCutProfiles.Batch078.valid3158
theorem numericValid476 : retention476.NumericValid := by decide +kernel
def certificate476 : RatCutBinCertificate := ⟨⟨retention476,(306138928728535091/125000000000000000),(69043717129131353/1000000000000000000),(693446761838081229/62500000000000000),(185362666901472325183/500000000000000000),(245360159709242551/250000000000000000)⟩,(993834460363187229/1000000000000000000),(406854588079963393/1000000000000000000),(227260219795808863/1000000000000000000),(207530906821843771/1000000000000000000)⟩
theorem valid476 : certificate476.Valid := by decide +kernel
theorem sound476 : certificate476.Sound := rat_cut_bin_certificate_sound certificate476 profilesValid476 numericValid476 valid476

def retention477 : RatCutRetentionCertificate := ⟨(77/2000),(39/1000),(2768468768150395106/5554043036293212667),(16446349117725119441/1000000000000000000),1,(65078291173315377076887966011995271323/65785396470900477764000000000000000000),false,MergedCutProfiles.Batch078.profile3159,(fun _ => MergedCutProfiles.Batch078.profile3159)⟩
theorem profilesValid477 : retention477.ProfilesValid := by
  exact MergedCutProfiles.Batch078.valid3159
theorem numericValid477 : retention477.NumericValid := by decide +kernel
def certificate477 : RatCutBinCertificate := ⟨⟨retention477,(306138928728535091/125000000000000000),(69043717129131353/1000000000000000000),(693446761838081229/62500000000000000),(185362666901472325183/500000000000000000),(30437832723960819/31250000000000000)⟩,(993834460363187229/1000000000000000000),(5124477181030659/12500000000000000),(224481072809559157/1000000000000000000),(102557534807780077/500000000000000000)⟩
theorem valid477 : certificate477.Valid := by decide +kernel
theorem sound477 : certificate477.Sound := rat_cut_bin_certificate_sound certificate477 profilesValid477 numericValid477 valid477

def retention478 : RatCutRetentionCertificate := ⟨(77/2000),(39/1000),(1/2),(4152703152225592659/250000000000000000),1,(13108075666334910912081816213493319083/13288650087121896508800000000000000000),false,MergedCutProfiles.Batch078.profile3156,(fun _ => MergedCutProfiles.Batch078.profile3156)⟩
theorem profilesValid478 : retention478.ProfilesValid := by
  exact MergedCutProfiles.Batch078.valid3156
theorem numericValid478 : retention478.NumericValid := by decide +kernel
def certificate478 : RatCutBinCertificate := ⟨⟨retention478,(306138928728535091/125000000000000000),(69043717129131353/1000000000000000000),(693446761838081229/62500000000000000),(185362666901472325183/500000000000000000),(485585347599346027/500000000000000000)⟩,(993834460363187229/1000000000000000000),(102789249308345843/250000000000000000),(111706934718122623/500000000000000000),(203690666740698903/1000000000000000000)⟩
theorem valid478 : certificate478.Valid := by decide +kernel
theorem sound478 : certificate478.Sound := rat_cut_bin_certificate_sound certificate478 profilesValid478 numericValid478 valid478

def retention479 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(790834396180964278/32399124674329550227),(783004352654420077/1000000000000000000),(13/4),(17297734959119316617/8000000000000000000),true,MergedCutProfiles.Batch079.profile3160,![MergedCutProfiles.Batch079.profile3160,MergedCutProfiles.Batch079.profile3161,MergedCutProfiles.Batch079.profile3162,MergedCutProfiles.Batch079.profile3163,MergedCutProfiles.Batch079.profile3164,MergedCutProfiles.Batch079.profile3165,MergedCutProfiles.Batch079.profile3166,MergedCutProfiles.Batch079.profile3167,MergedCutProfiles.Batch079.profile3168,MergedCutProfiles.Batch079.profile3169,MergedCutProfiles.Batch079.profile3170,MergedCutProfiles.Batch079.profile3171,MergedCutProfiles.Batch079.profile3172,MergedCutProfiles.Batch079.profile3173,MergedCutProfiles.Batch079.profile3174,MergedCutProfiles.Batch079.profile3175]⟩
theorem profilesValid479 : retention479.ProfilesValid := by
  change ∀ j : Fin 16, (retention479.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch079.valid3160
  · exact MergedCutProfiles.Batch079.valid3161
  · exact MergedCutProfiles.Batch079.valid3162
  · exact MergedCutProfiles.Batch079.valid3163
  · exact MergedCutProfiles.Batch079.valid3164
  · exact MergedCutProfiles.Batch079.valid3165
  · exact MergedCutProfiles.Batch079.valid3166
  · exact MergedCutProfiles.Batch079.valid3167
  · exact MergedCutProfiles.Batch079.valid3168
  · exact MergedCutProfiles.Batch079.valid3169
  · exact MergedCutProfiles.Batch079.valid3170
  · exact MergedCutProfiles.Batch079.valid3171
  · exact MergedCutProfiles.Batch079.valid3172
  · exact MergedCutProfiles.Batch079.valid3173
  · exact MergedCutProfiles.Batch079.valid3174
  · exact MergedCutProfiles.Batch079.valid3175
theorem numericValid479 : retention479.NumericValid := by decide +kernel
def certificate479 : RatCutBinCertificate := ⟨⟨retention479,(205916410838747817/100000000000000000),(70986334890534179/1000000000000000000),(11179644401673740689/1000000000000000000),(14527252830750459517/40000000000000000),(21197202449182043/10000000000000000)⟩,(994719567412799441/1000000000000000000),(406270330269288913/1000000000000000000),(227786042555068441/1000000000000000000),(11752422608216751/100000000000000000)⟩
theorem valid479 : certificate479.Valid := by decide +kernel
theorem sound479 : certificate479.Sound := rat_cut_bin_certificate_sound certificate479 profilesValid479 numericValid479 valid479

def certificates : List RatCutBinCertificate := [certificate468,certificate469,certificate470,certificate471,certificate472,certificate473,certificate474,certificate475,certificate476,certificate477,certificate478,certificate479]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound468,List.forall_mem_cons.mpr ⟨sound469,List.forall_mem_cons.mpr ⟨sound470,List.forall_mem_cons.mpr ⟨sound471,List.forall_mem_cons.mpr ⟨sound472,List.forall_mem_cons.mpr ⟨sound473,List.forall_mem_cons.mpr ⟨sound474,List.forall_mem_cons.mpr ⟨sound475,List.forall_mem_cons.mpr ⟨sound476,List.forall_mem_cons.mpr ⟨sound477,List.forall_mem_cons.mpr ⟨sound478,List.forall_mem_cons.mpr ⟨sound479,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch039
