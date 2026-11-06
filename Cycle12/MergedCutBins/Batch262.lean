import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch366
import Cycle12.MergedCutProfiles.Batch367
import Cycle12.MergedCutProfiles.Batch482
import Cycle12.MergedCutProfiles.Batch483
import Cycle12.MergedCutProfiles.Batch484

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch262

def retention3144 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(28460045949223173041/57638080845721486782),(18926019003869354171/500000000000000000),1,(30500424843732508550372257608746734083/30281630406190966673600000000000000000),false,MergedCutProfiles.Batch482.profile19307,(fun _ => MergedCutProfiles.Batch482.profile19307)⟩
theorem profilesValid3144 : retention3144.ProfilesValid := by
  exact MergedCutProfiles.Batch482.valid19307
theorem numericValid3144 : retention3144.NumericValid := by decide +kernel
def certificate3144 : RatCutBinCertificate := ⟨⟨retention3144,(509465894602006859/250000000000000000),(19858540071699249/200000000000000000),(6138646236888365959/500000000000000000),(355794286259728427773/250000000000000000),(990744050686320713/1000000000000000000)⟩,(998703306766094507/1000000000000000000),(234440736353669363/500000000000000000),(175985081740998061/1000000000000000000),(169685256084441107/1000000000000000000)⟩
theorem valid3144 : certificate3144.Valid := by decide +kernel
theorem sound3144 : certificate3144.Sound := rat_cut_bin_certificate_sound certificate3144 profilesValid3144 numericValid3144 valid3144

def retention3145 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(57489292817430809543/115276161691442973564),(28460045949223173041/500000000000000000),1,(227609488687888603993231302134287208527/227680367593785384328000000000000000000),false,MergedCutProfiles.Batch482.profile19308,(fun _ => MergedCutProfiles.Batch482.profile19308)⟩
theorem profilesValid3145 : retention3145.ProfilesValid := by
  exact MergedCutProfiles.Batch482.valid19308
theorem numericValid3145 : retention3145.NumericValid := by decide +kernel
def certificate3145 : RatCutBinCertificate := ⟨⟨retention3145,(509465894602006859/250000000000000000),(19858540071699249/200000000000000000),(6138646236888365959/500000000000000000),(355794286259728427773/250000000000000000),(122900929138914267/125000000000000000)⟩,(998703306766094507/1000000000000000000),(468744195833945499/1000000000000000000),(88044537686936113/500000000000000000),(169969319591332291/1000000000000000000)⟩
theorem valid3145 : certificate3145.Valid := by decide +kernel
theorem sound3145 : certificate3145.Sound := rat_cut_bin_certificate_sound certificate3145 profilesValid3145 numericValid3145 valid3145

def retention3146 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(1/2),(57489292817430809543/1000000000000000000),1,(45861247471193208334864815127198455471/45991434253944647634400000000000000000),false,MergedCutProfiles.Batch366.profile14641,(fun _ => MergedCutProfiles.Batch366.profile14641)⟩
theorem profilesValid3146 : retention3146.ProfilesValid := by
  exact MergedCutProfiles.Batch366.valid14641
theorem numericValid3146 : retention3146.NumericValid := by decide +kernel
def certificate3146 : RatCutBinCertificate := ⟨⟨retention3146,(509465894602006859/250000000000000000),(19858540071699249/200000000000000000),(6138646236888365959/500000000000000000),(355794286259728427773/250000000000000000),(196137613514407299/200000000000000000)⟩,(998703306766094507/1000000000000000000),(14683589429516987/31250000000000000),(87616870069972353/500000000000000000),(168745958414567383/1000000000000000000)⟩
theorem valid3146 : certificate3146.Valid := by decide +kernel
theorem sound3146 : certificate3146.Sound := rat_cut_bin_certificate_sound certificate3146 profilesValid3146 numericValid3146 valid3146

def retention3147 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(7519430366992671061/16468023098777567652),(10091016912222790751/1000000000000000000),1,(66824782051654752658910325706721427/63068855701392442193750000000000000),false,MergedCutProfiles.Batch482.profile19309,(fun _ => MergedCutProfiles.Batch482.profile19309)⟩
theorem profilesValid3147 : retention3147.ProfilesValid := by
  exact MergedCutProfiles.Batch482.valid19309
theorem numericValid3147 : retention3147.NumericValid := by decide +kernel
def certificate3147 : RatCutBinCertificate := ⟨⟨retention3147,(541160525352006859/250000000000000000),(19858540071699249/200000000000000000),(6138646236888365959/500000000000000000),(355794286259728427773/250000000000000000),(521023054636731391/500000000000000000)⟩,(499311312974451847/500000000000000000),(120431163747642359/1000000000000000000),(155651358707519621/250000000000000000),(587207161501398743/1000000000000000000)⟩
theorem valid3147 : certificate3147.Valid := by decide +kernel
theorem sound3147 : certificate3147.Sound := rat_cut_bin_certificate_sound certificate3147 profilesValid3147 numericValid3147 valid3147

def retention3148 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(4749771597317500321/9606346807620247797),(52636012568948697427/1000000000000000000),1,(828855109767466757503045576046036457/822437696389823397296875000000000000),false,MergedCutProfiles.Batch482.profile19310,(fun _ => MergedCutProfiles.Batch482.profile19310)⟩
theorem profilesValid3148 : retention3148.ProfilesValid := by
  exact MergedCutProfiles.Batch482.valid19310
theorem numericValid3148 : retention3148.NumericValid := by decide +kernel
def certificate3148 : RatCutBinCertificate := ⟨⟨retention3148,(541160525352006859/250000000000000000),(19858540071699249/200000000000000000),(6138646236888365959/500000000000000000),(355794286259728427773/250000000000000000),(990296333972492231/1000000000000000000)⟩,(499311312974451847/500000000000000000),(126724518018857907/1000000000000000000),(609735333341520171/1000000000000000000),(591843317979541851/1000000000000000000)⟩
theorem valid3148 : certificate3148.Valid := by decide +kernel
theorem sound3148 : certificate3148.Sound := rat_cut_bin_certificate_sound certificate3148 profilesValid3148 numericValid3148 valid3148

def retention3149 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(913765583483938157/1829780344308618628),(14249314791952500963/250000000000000000),1,(14225832264463025457872292409284273227/14249314791952500963000000000000000000),false,MergedCutProfiles.Batch482.profile19311,(fun _ => MergedCutProfiles.Batch482.profile19311)⟩
theorem profilesValid3149 : retention3149.ProfilesValid := by
  exact MergedCutProfiles.Batch482.valid19311
theorem numericValid3149 : retention3149.NumericValid := by decide +kernel
def certificate3149 : RatCutBinCertificate := ⟨⟨retention3149,(541160525352006859/250000000000000000),(19858540071699249/200000000000000000),(6138646236888365959/500000000000000000),(355794286259728427773/250000000000000000),(245211360620205371/250000000000000000)⟩,(499311312974451847/500000000000000000),(15993195791007591/125000000000000000),(607269997900900343/1000000000000000000),(584746957871640609/1000000000000000000)⟩
theorem valid3149 : certificate3149.Valid := by decide +kernel
theorem sound3149 : certificate3149.Sound := rat_cut_bin_certificate_sound certificate3149 profilesValid3149 numericValid3149 valid3149

def retention3150 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(1/2),(57567231759488103891/1000000000000000000),1,(5102632678056466452393567974571178183/5117087267510053679200000000000000000),false,MergedCutProfiles.Batch366.profile14641,(fun _ => MergedCutProfiles.Batch366.profile14641)⟩
theorem profilesValid3150 : retention3150.ProfilesValid := by
  exact MergedCutProfiles.Batch366.valid14641
theorem numericValid3150 : retention3150.NumericValid := by decide +kernel
def certificate3150 : RatCutBinCertificate := ⟨⟨retention3150,(541160525352006859/250000000000000000),(19858540071699249/200000000000000000),(6138646236888365959/500000000000000000),(355794286259728427773/250000000000000000),(122458581200915943/125000000000000000)⟩,(499311312974451847/500000000000000000),(8006203530449241/62500000000000000),(303480206845529031/500000000000000000),(583857254438762479/1000000000000000000)⟩
theorem valid3150 : certificate3150.Valid := by decide +kernel
theorem sound3150 : certificate3150.Sound := rat_cut_bin_certificate_sound certificate3150 profilesValid3150 numericValid3150 valid3150

def retention3151 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(760530716683639785/109806300649514491154),(753000709587762163/1000000000000000000),(18/5),(184157034088341328551/80000000000000000000),true,MergedCutProfiles.Batch482.profile19312,![MergedCutProfiles.Batch482.profile19312,MergedCutProfiles.Batch482.profile19313,MergedCutProfiles.Batch482.profile19314,MergedCutProfiles.Batch482.profile19315,MergedCutProfiles.Batch482.profile19316,MergedCutProfiles.Batch482.profile19317,MergedCutProfiles.Batch482.profile19318,MergedCutProfiles.Batch366.profile14647,MergedCutProfiles.Batch482.profile19319,MergedCutProfiles.Batch366.profile14679,MergedCutProfiles.Batch483.profile19320,MergedCutProfiles.Batch483.profile19321,MergedCutProfiles.Batch483.profile19322,MergedCutProfiles.Batch367.profile14705,MergedCutProfiles.Batch483.profile19323,MergedCutProfiles.Batch483.profile19324]⟩
theorem profilesValid3151 : retention3151.ProfilesValid := by
  change ∀ j : Fin 16, (retention3151.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch482.valid19312
  · exact MergedCutProfiles.Batch482.valid19313
  · exact MergedCutProfiles.Batch482.valid19314
  · exact MergedCutProfiles.Batch482.valid19315
  · exact MergedCutProfiles.Batch482.valid19316
  · exact MergedCutProfiles.Batch482.valid19317
  · exact MergedCutProfiles.Batch482.valid19318
  · exact MergedCutProfiles.Batch366.valid14647
  · exact MergedCutProfiles.Batch482.valid19319
  · exact MergedCutProfiles.Batch366.valid14679
  · exact MergedCutProfiles.Batch483.valid19320
  · exact MergedCutProfiles.Batch483.valid19321
  · exact MergedCutProfiles.Batch483.valid19322
  · exact MergedCutProfiles.Batch367.valid14705
  · exact MergedCutProfiles.Batch483.valid19323
  · exact MergedCutProfiles.Batch483.valid19324
theorem numericValid3151 : retention3151.NumericValid := by decide +kernel
def certificate3151 : RatCutBinCertificate := ⟨⟨retention3151,(409656174908065579/200000000000000000),(6511012982960937/62500000000000000),(194938560381505529/15625000000000000),(1377644565834100502187/1000000000000000000),(2240389270134115493/1000000000000000000)⟩,(249665157596448029/250000000000000000),(441537586280029057/1000000000000000000),(24688568117412407/125000000000000000),(99808036268420427/1000000000000000000)⟩
theorem valid3151 : certificate3151.Valid := by decide +kernel
theorem sound3151 : certificate3151.Sound := rat_cut_bin_certificate_sound certificate3151 profilesValid3151 numericValid3151 valid3151

def retention3152 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(985082213511171525/109806300649514491154),(152106143336727957/200000000000000000),(71/20),(584704687471587996053/256000000000000000000),true,MergedCutProfiles.Batch483.profile19325,![MergedCutProfiles.Batch483.profile19325,MergedCutProfiles.Batch483.profile19326,MergedCutProfiles.Batch483.profile19327,MergedCutProfiles.Batch483.profile19328,MergedCutProfiles.Batch483.profile19329,MergedCutProfiles.Batch483.profile19330,MergedCutProfiles.Batch483.profile19331,MergedCutProfiles.Batch483.profile19332,MergedCutProfiles.Batch483.profile19333,MergedCutProfiles.Batch483.profile19322,MergedCutProfiles.Batch483.profile19334,MergedCutProfiles.Batch366.profile14665,MergedCutProfiles.Batch483.profile19335,MergedCutProfiles.Batch483.profile19336,MergedCutProfiles.Batch367.profile14713,MergedCutProfiles.Batch483.profile19337]⟩
theorem profilesValid3152 : retention3152.ProfilesValid := by
  change ∀ j : Fin 16, (retention3152.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch483.valid19325
  · exact MergedCutProfiles.Batch483.valid19326
  · exact MergedCutProfiles.Batch483.valid19327
  · exact MergedCutProfiles.Batch483.valid19328
  · exact MergedCutProfiles.Batch483.valid19329
  · exact MergedCutProfiles.Batch483.valid19330
  · exact MergedCutProfiles.Batch483.valid19331
  · exact MergedCutProfiles.Batch483.valid19332
  · exact MergedCutProfiles.Batch483.valid19333
  · exact MergedCutProfiles.Batch483.valid19322
  · exact MergedCutProfiles.Batch483.valid19334
  · exact MergedCutProfiles.Batch366.valid14665
  · exact MergedCutProfiles.Batch483.valid19335
  · exact MergedCutProfiles.Batch483.valid19336
  · exact MergedCutProfiles.Batch367.valid14713
  · exact MergedCutProfiles.Batch483.valid19337
theorem numericValid3152 : retention3152.NumericValid := by decide +kernel
def certificate3152 : RatCutBinCertificate := ⟨⟨retention3152,(409656174908065579/200000000000000000),(6511012982960937/62500000000000000),(194938560381505529/15625000000000000),(1377644565834100502187/1000000000000000000),(111164210614123351/50000000000000000)⟩,(249665157596448029/250000000000000000),(110632963492783531/250000000000000000),(19669686914299281/100000000000000000),(199668265707157/2000000000000000)⟩
theorem valid3152 : certificate3152.Valid := by decide +kernel
theorem sound3152 : certificate3152.Sound := rat_cut_bin_certificate_sound certificate3152 profilesValid3152 numericValid3152 valid3152

def retention3153 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(558812667500000000/54903150324757245577),(39403288540446861/40000000000000000),(57/20),(579025699335399862329/256000000000000000000),true,MergedCutProfiles.Batch483.profile19338,![MergedCutProfiles.Batch483.profile19338,MergedCutProfiles.Batch482.profile19314,MergedCutProfiles.Batch483.profile19339,MergedCutProfiles.Batch483.profile19340,MergedCutProfiles.Batch483.profile19341,MergedCutProfiles.Batch483.profile19342,MergedCutProfiles.Batch367.profile14693,MergedCutProfiles.Batch483.profile19343,MergedCutProfiles.Batch483.profile19344,MergedCutProfiles.Batch483.profile19345,MergedCutProfiles.Batch366.profile14650,MergedCutProfiles.Batch483.profile19346,MergedCutProfiles.Batch483.profile19347,MergedCutProfiles.Batch483.profile19337,MergedCutProfiles.Batch483.profile19348,MergedCutProfiles.Batch483.profile19349]⟩
theorem profilesValid3153 : retention3153.ProfilesValid := by
  change ∀ j : Fin 16, (retention3153.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch483.valid19338
  · exact MergedCutProfiles.Batch482.valid19314
  · exact MergedCutProfiles.Batch483.valid19339
  · exact MergedCutProfiles.Batch483.valid19340
  · exact MergedCutProfiles.Batch483.valid19341
  · exact MergedCutProfiles.Batch483.valid19342
  · exact MergedCutProfiles.Batch367.valid14693
  · exact MergedCutProfiles.Batch483.valid19343
  · exact MergedCutProfiles.Batch483.valid19344
  · exact MergedCutProfiles.Batch483.valid19345
  · exact MergedCutProfiles.Batch366.valid14650
  · exact MergedCutProfiles.Batch483.valid19346
  · exact MergedCutProfiles.Batch483.valid19347
  · exact MergedCutProfiles.Batch483.valid19337
  · exact MergedCutProfiles.Batch483.valid19348
  · exact MergedCutProfiles.Batch483.valid19349
theorem numericValid3153 : retention3153.NumericValid := by decide +kernel
def certificate3153 : RatCutBinCertificate := ⟨⟨retention3153,(409656174908065579/200000000000000000),(6511012982960937/62500000000000000),(194938560381505529/15625000000000000),(1377644565834100502187/1000000000000000000),(55326834346960119/25000000000000000)⟩,(249665157596448029/250000000000000000),(15581994324110887/40000000000000000),(121597473160396619/500000000000000000),(147698260508781339/1000000000000000000)⟩
theorem valid3153 : certificate3153.Valid := by decide +kernel
theorem sound3153 : certificate3153.Sound := rat_cut_bin_certificate_sound certificate3153 profilesValid3153 numericValid3153 valid3153

def retention3154 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(740659857061293868/54903150324757245577),(223525067/200000000),(13/5),(17922249373139982169/8000000000000000000),true,MergedCutProfiles.Batch483.profile19350,![MergedCutProfiles.Batch483.profile19350,MergedCutProfiles.Batch483.profile19351,MergedCutProfiles.Batch483.profile19340,MergedCutProfiles.Batch483.profile19330,MergedCutProfiles.Batch483.profile19352,MergedCutProfiles.Batch483.profile19333,MergedCutProfiles.Batch367.profile14694,MergedCutProfiles.Batch483.profile19353,MergedCutProfiles.Batch483.profile19346,MergedCutProfiles.Batch483.profile19354,MergedCutProfiles.Batch366.profile14652,MergedCutProfiles.Batch483.profile19349,MergedCutProfiles.Batch483.profile19355,MergedCutProfiles.Batch367.profile14698,MergedCutProfiles.Batch483.profile19356,MergedCutProfiles.Batch483.profile19357]⟩
theorem profilesValid3154 : retention3154.ProfilesValid := by
  change ∀ j : Fin 16, (retention3154.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch483.valid19350
  · exact MergedCutProfiles.Batch483.valid19351
  · exact MergedCutProfiles.Batch483.valid19340
  · exact MergedCutProfiles.Batch483.valid19330
  · exact MergedCutProfiles.Batch483.valid19352
  · exact MergedCutProfiles.Batch483.valid19333
  · exact MergedCutProfiles.Batch367.valid14694
  · exact MergedCutProfiles.Batch483.valid19353
  · exact MergedCutProfiles.Batch483.valid19346
  · exact MergedCutProfiles.Batch483.valid19354
  · exact MergedCutProfiles.Batch366.valid14652
  · exact MergedCutProfiles.Batch483.valid19349
  · exact MergedCutProfiles.Batch483.valid19355
  · exact MergedCutProfiles.Batch367.valid14698
  · exact MergedCutProfiles.Batch483.valid19356
  · exact MergedCutProfiles.Batch483.valid19357
theorem numericValid3154 : retention3154.NumericValid := by decide +kernel
def certificate3154 : RatCutBinCertificate := ⟨⟨retention3154,(409656174908065579/200000000000000000),(6511012982960937/62500000000000000),(194938560381505529/15625000000000000),(1377644565834100502187/1000000000000000000),(1097905696125597561/500000000000000000)⟩,(249665157596448029/250000000000000000),(18516873912865427/50000000000000000),(65447008132981609/250000000000000000),(6841512082957487/40000000000000000)⟩
theorem valid3154 : certificate3154.Valid := by decide +kernel
theorem sound3154 : certificate3154.Sound := rat_cut_bin_certificate_sound certificate3154 profilesValid3154 numericValid3154 valid3154

def retention3155 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(5311911318884656478/54903150324757245577),(185164964265323467/125000000000000000),(21/10),(306109495727527031181/160000000000000000000),true,MergedCutProfiles.Batch367.profile14705,![MergedCutProfiles.Batch367.profile14705,MergedCutProfiles.Batch483.profile19358,MergedCutProfiles.Batch367.profile14707,MergedCutProfiles.Batch367.profile14708,MergedCutProfiles.Batch483.profile19359,MergedCutProfiles.Batch484.profile19360,MergedCutProfiles.Batch484.profile19361,MergedCutProfiles.Batch484.profile19362,MergedCutProfiles.Batch484.profile19363,MergedCutProfiles.Batch484.profile19364,MergedCutProfiles.Batch484.profile19365,MergedCutProfiles.Batch484.profile19366,MergedCutProfiles.Batch484.profile19367,MergedCutProfiles.Batch484.profile19368,MergedCutProfiles.Batch484.profile19369,MergedCutProfiles.Batch484.profile19370]⟩
theorem profilesValid3155 : retention3155.ProfilesValid := by
  change ∀ j : Fin 16, (retention3155.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch367.valid14705
  · exact MergedCutProfiles.Batch483.valid19358
  · exact MergedCutProfiles.Batch367.valid14707
  · exact MergedCutProfiles.Batch367.valid14708
  · exact MergedCutProfiles.Batch483.valid19359
  · exact MergedCutProfiles.Batch484.valid19360
  · exact MergedCutProfiles.Batch484.valid19361
  · exact MergedCutProfiles.Batch484.valid19362
  · exact MergedCutProfiles.Batch484.valid19363
  · exact MergedCutProfiles.Batch484.valid19364
  · exact MergedCutProfiles.Batch484.valid19365
  · exact MergedCutProfiles.Batch484.valid19366
  · exact MergedCutProfiles.Batch484.valid19367
  · exact MergedCutProfiles.Batch484.valid19368
  · exact MergedCutProfiles.Batch484.valid19369
  · exact MergedCutProfiles.Batch484.valid19370
theorem numericValid3155 : retention3155.NumericValid := by decide +kernel
def certificate3155 : RatCutBinCertificate := ⟨⟨retention3155,(409656174908065579/200000000000000000),(6511012982960937/62500000000000000),(194938560381505529/15625000000000000),(1377644565834100502187/1000000000000000000),(234658313892098637/125000000000000000)⟩,(249665157596448029/250000000000000000),(192817765417100441/500000000000000000),(246904735837767649/1000000000000000000),(34236883685067047/200000000000000000)⟩
theorem valid3155 : certificate3155.Valid := by decide +kernel
theorem sound3155 : certificate3155.Sound := rat_cut_bin_certificate_sound certificate3155 profilesValid3155 numericValid3155 valid3155

def certificates : List RatCutBinCertificate := [certificate3144,certificate3145,certificate3146,certificate3147,certificate3148,certificate3149,certificate3150,certificate3151,certificate3152,certificate3153,certificate3154,certificate3155]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3144,List.forall_mem_cons.mpr ⟨sound3145,List.forall_mem_cons.mpr ⟨sound3146,List.forall_mem_cons.mpr ⟨sound3147,List.forall_mem_cons.mpr ⟨sound3148,List.forall_mem_cons.mpr ⟨sound3149,List.forall_mem_cons.mpr ⟨sound3150,List.forall_mem_cons.mpr ⟨sound3151,List.forall_mem_cons.mpr ⟨sound3152,List.forall_mem_cons.mpr ⟨sound3153,List.forall_mem_cons.mpr ⟨sound3154,List.forall_mem_cons.mpr ⟨sound3155,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch262
