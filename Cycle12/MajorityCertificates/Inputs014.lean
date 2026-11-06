import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch014

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs014

def inputs280 : RatMajorityInputs := ⟨(1776612648514964853191423/5000000000000000000000),(55305396268903/12500000000000),(252124703376467977/250000000000000000),(2847781243932851/15625000000000000),(55305396268903/25000000000000),(27364459341633897/250000000000000000),25⟩
theorem inputs_valid280 : inputs280.Valid := by decide +kernel
def envelope280 : RatMajorityEnvelope := ⟨140,0,inputs280,(2271974151/1945240000),(348674885350933607/500000000000000000)⟩
theorem envelope_sound280 : envelope280.Sound := by
  apply rat_majority_inputs_envelopes inputs280 inputs_valid280
  · norm_num [envelope280]
  · intro rho hr0 hr1
    have hh := Batch014.bound560 rho hr0 hr1
    norm_num [Batch014.certificate560,envelope280,inputs280,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch014.bound561 rho hr0 hr1
    norm_num [Batch014.certificate561,envelope280,inputs280,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs281 : RatMajorityInputs := ⟨(1776612648514964853191423/5000000000000000000000),(25214230496279/5000000000000),(252124703376467977/250000000000000000),(15136176487749271/125000000000000000),(25214230496279/10000000000000),(80345190165633571/1000000000000000000),26⟩
theorem inputs_valid281 : inputs281.Valid := by decide +kernel
def envelope281 : RatMajorityEnvelope := ⟨140,1,inputs281,1,(108651037840991079/200000000000000000)⟩
theorem envelope_sound281 : envelope281.Sound := by
  apply rat_majority_inputs_envelopes inputs281 inputs_valid281
  · norm_num [envelope281]
  · intro rho hr0 hr1
    have hh := Batch014.bound562 rho hr0 hr1
    norm_num [Batch014.certificate562,envelope281,inputs281,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch014.bound563 rho hr0 hr1
    norm_num [Batch014.certificate563,envelope281,inputs281,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs282 : RatMajorityInputs := ⟨(35445515674249122836832387/100000000000000000000000),(3543612096321/800000000000),(1008519748273701313/1000000000000000000),(22707838511003857/125000000000000000),(3543612096321/1600000000000),(109179980612679899/1000000000000000000),25⟩
theorem inputs_valid282 : inputs282.Valid := by decide +kernel
def envelope282 : RatMajorityEnvelope := ⟨141,0,inputs282,(9462007/8104125),(696935170085942903/1000000000000000000)⟩
theorem envelope_sound282 : envelope282.Sound := by
  apply rat_majority_inputs_envelopes inputs282 inputs_valid282
  · norm_num [envelope282]
  · intro rho hr0 hr1
    have hh := Batch014.bound564 rho hr0 hr1
    norm_num [Batch014.certificate564,envelope282,inputs282,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch014.bound565 rho hr0 hr1
    norm_num [Batch014.certificate565,envelope282,inputs282,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs283 : RatMajorityInputs := ⟨(35445515674249122836832387/100000000000000000000000),(100875992010201/20000000000000),(1008519748273701313/1000000000000000000),(24202234067185133/200000000000000000),(100875992010201/40000000000000),(40153447337630253/500000000000000000),26⟩
theorem inputs_valid283 : inputs283.Valid := by decide +kernel
def envelope283 : RatMajorityEnvelope := ⟨141,1,inputs283,1,(543256912610338729/1000000000000000000)⟩
theorem envelope_sound283 : envelope283.Sound := by
  apply rat_majority_inputs_envelopes inputs283 inputs_valid283
  · norm_num [envelope283]
  · intro rho hr0 hr1
    have hh := Batch014.bound566 rho hr0 hr1
    norm_num [Batch014.certificate566,envelope283,inputs283,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch014.bound567 rho hr0 hr1
    norm_num [Batch014.certificate567,envelope283,inputs283,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs284 : RatMajorityInputs := ⟨(4419916916756168023575281/12500000000000000000000),(44137528009659/10000000000000),(1008540651010050701/1000000000000000000),(5734811228922611/31250000000000000),(44137528009659/20000000000000),(110043845133585961/1000000000000000000),25⟩
theorem inputs_valid284 : inputs284.Valid := by decide +kernel
def envelope284 : RatMajorityEnvelope := ⟨142,0,inputs284,(162160387/138910000),(139391386603653449/200000000000000000)⟩
theorem envelope_sound284 : envelope284.Sound := by
  apply rat_majority_inputs_envelopes inputs284 inputs_valid284
  · norm_num [envelope284]
  · intro rho hr0 hr1
    have hh := Batch014.bound568 rho hr0 hr1
    norm_num [Batch014.certificate568,envelope284,inputs284,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch014.bound569 rho hr0 hr1
    norm_num [Batch014.certificate569,envelope284,inputs284,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs285 : RatMajorityInputs := ⟨(4419916916756168023575281/12500000000000000000000),(252265794920587/50000000000000),(1008540651010050701/1000000000000000000),(120886839987059959/1000000000000000000),(252265794920587/100000000000000),(40123016580639269/500000000000000000),26⟩
theorem inputs_valid285 : inputs285.Valid := by decide +kernel
def envelope285 : RatMajorityEnvelope := ⟨142,1,inputs285,1,(67906742002830693/125000000000000000)⟩
theorem envelope_sound285 : envelope285.Sound := by
  apply rat_majority_inputs_envelopes inputs285 inputs_valid285
  · norm_num [envelope285]
  · intro rho hr0 hr1
    have hh := Batch014.bound570 rho hr0 hr1
    norm_num [Batch014.certificate570,envelope285,inputs285,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch014.bound571 rho hr0 hr1
    norm_num [Batch014.certificate571,envelope285,inputs285,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs286 : RatMajorityInputs := ⟨(35273708025161403872463591/100000000000000000000000),(443649786420531/100000000000000),(1008561521440750483/1000000000000000000),(180847698411186909/1000000000000000000),(443649786420531/200000000000000),(2719986433918611/25000000000000000),25⟩
theorem inputs_valid286 : inputs286.Valid := by decide +kernel
def envelope286 : RatMajorityEnvelope := ⟨143,0,inputs286,(1134381907/972245000),(69617132500834241/100000000000000000)⟩
theorem envelope_sound286 : envelope286.Sound := by
  apply rat_majority_inputs_envelopes inputs286 inputs_valid286
  · norm_num [envelope286]
  · intro rho hr0 hr1
    have hh := Batch014.bound572 rho hr0 hr1
    norm_num [Batch014.certificate572,envelope286,inputs286,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch014.bound573 rho hr0 hr1
    norm_num [Batch014.certificate573,envelope286,inputs286,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs287 : RatMajorityInputs := ⟨(35273708025161403872463591/100000000000000000000000),(50489695345943/10000000000000),(1008561521440750483/1000000000000000000),(120587723527028103/1000000000000000000),(50489695345943/20000000000000),(80099572075758019/1000000000000000000),27⟩
theorem inputs_valid287 : inputs287.Valid := by decide +kernel
def envelope287 : RatMajorityEnvelope := ⟨143,1,inputs287,1,(271616591619311811/500000000000000000)⟩
theorem envelope_sound287 : envelope287.Sound := by
  apply rat_majority_inputs_envelopes inputs287 inputs_valid287
  · norm_num [envelope287]
  · intro rho hr0 hr1
    have hh := Batch014.bound574 rho hr0 hr1
    norm_num [Batch014.certificate574,envelope287,inputs287,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch014.bound575 rho hr0 hr1
    norm_num [Batch014.certificate575,envelope287,inputs287,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs288 : RatMajorityInputs := ⟨(4398578732667205647069729/12500000000000000000000),(55617842528013/12500000000000),(201716471858396247/200000000000000000),(179346822501041237/1000000000000000000),(55617842528013/25000000000000),(108098362645099089/1000000000000000000),25⟩
theorem inputs_valid288 : inputs288.Valid := by decide +kernel
def envelope288 : RatMajorityEnvelope := ⟨144,0,inputs288,(188952733/162020000),(34778159961783693/50000000000000000)⟩
theorem envelope_sound288 : envelope288.Sound := by
  apply rat_majority_inputs_envelopes inputs288 inputs_valid288
  · norm_num [envelope288]
  · intro rho hr0 hr1
    have hh := Batch014.bound576 rho hr0 hr1
    norm_num [Batch014.certificate576,envelope288,inputs288,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch014.bound577 rho hr0 hr1
    norm_num [Batch014.certificate577,envelope288,inputs288,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs289 : RatMajorityInputs := ⟨(4398578732667205647069729/12500000000000000000000),(63134280686793/12500000000000),(201716471858396247/200000000000000000),(120442815434491681/1000000000000000000),(63134280686793/25000000000000),(20007149614350869/250000000000000000),27⟩
theorem inputs_valid289 : inputs289.Valid := by decide +kernel
def envelope289 : RatMajorityEnvelope := ⟨144,1,inputs289,1,(271614053843481461/500000000000000000)⟩
theorem envelope_sound289 : envelope289.Sound := by
  apply rat_majority_inputs_envelopes inputs289 inputs_valid289
  · norm_num [envelope289]
  · intro rho hr0 hr1
    have hh := Batch014.bound578 rho hr0 hr1
    norm_num [Batch014.certificate578,envelope289,inputs289,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch014.bound579 rho hr0 hr1
    norm_num [Batch014.certificate579,envelope289,inputs289,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs290 : RatMajorityInputs := ⟨(1097008674117075882549/3125000000000000000),(55557359487/12500000000),(504301559869757873/500000000000000000),(22488406092791707/125000000000000000),(55557359487/25000000000),(54180101982310429/500000000000000000),26⟩
theorem inputs_valid290 : inputs290.Valid := by decide +kernel
def envelope290 : RatMajorityEnvelope := ⟨145,0,inputs290,(6996131/6000000),(695436975695481491/1000000000000000000)⟩
theorem envelope_sound290 : envelope290.Sound := by
  apply rat_majority_inputs_envelopes inputs290 inputs_valid290
  · norm_num [envelope290]
  · intro rho hr0 hr1
    have hh := Batch014.bound580 rho hr0 hr1
    norm_num [Batch014.certificate580,envelope290,inputs290,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch014.bound581 rho hr0 hr1
    norm_num [Batch014.certificate581,envelope290,inputs290,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs291 : RatMajorityInputs := ⟨(1097008674117075882549/3125000000000000000),(631564398621/125000000000),(504301559869757873/500000000000000000),(60149038821125433/500000000000000000),(631564398621/250000000000),(79957695175498979/1000000000000000000),27⟩
theorem inputs_valid291 : inputs291.Valid := by decide +kernel
def envelope291 : RatMajorityEnvelope := ⟨145,1,inputs291,1,(108644604479267031/200000000000000000)⟩
theorem envelope_sound291 : envelope291.Sound := by
  apply rat_majority_inputs_envelopes inputs291 inputs_valid291
  · norm_num [envelope291]
  · intro rho hr0 hr1
    have hh := Batch014.bound582 rho hr0 hr1
    norm_num [Batch014.certificate582,envelope291,inputs291,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch014.bound583 rho hr0 hr1
    norm_num [Batch014.certificate583,envelope291,inputs291,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs292 : RatMajorityInputs := ⟨(11206491450054001966969/32000000000000000000),(142195968293/32000000000),(100862389149774643/100000000000000000),(5625598983083301/31250000000000000),(142195968293/64000000000),(10841248681632939/100000000000000000),25⟩
theorem inputs_valid292 : inputs292.Valid := by decide +kernel
def envelope292 : RatMajorityEnvelope := ⟨146,0,inputs292,(1132951183/971875000),(69520201003090247/100000000000000000)⟩
theorem envelope_sound292 : envelope292.Sound := by
  apply rat_majority_inputs_envelopes inputs292 inputs_valid292
  · norm_num [envelope292]
  · intro rho hr0 hr1
    have hh := Batch014.bound584 rho hr0 hr1
    norm_num [Batch014.certificate584,envelope292,inputs292,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch014.bound585 rho hr0 hr1
    norm_num [Batch014.certificate585,envelope292,inputs292,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs293 : RatMajorityInputs := ⟨(11206491450054001966969/32000000000000000000),(808682667221/160000000000),(100862389149774643/100000000000000000),(30038806808278107/250000000000000000),(808682667221/320000000000),(19971925907178177/250000000000000000),26⟩
theorem inputs_valid293 : inputs293.Valid := by decide +kernel
def envelope293 : RatMajorityEnvelope := ⟨146,1,inputs293,1,(135804535668866737/250000000000000000)⟩
theorem envelope_sound293 : envelope293.Sound := by
  apply rat_majority_inputs_envelopes inputs293 inputs_valid293
  · norm_num [envelope293]
  · intro rho hr0 hr1
    have hh := Batch014.bound586 rho hr0 hr1
    norm_num [Batch014.certificate586,envelope293,inputs293,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch014.bound587 rho hr0 hr1
    norm_num [Batch014.certificate587,envelope293,inputs293,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs294 : RatMajorityInputs := ⟨(4367126433493986323892377/12500000000000000000000),(89238445960889/20000000000000),(504322292539563367/500000000000000000),(35581303016182499/200000000000000000),(89238445960889/40000000000000),(21485025788436339/200000000000000000),26⟩
theorem inputs_valid294 : inputs294.Valid := by decide +kernel
def envelope294 : RatMajorityEnvelope := ⟨147,0,inputs294,(5866069/5035000),(138881576284516671/200000000000000000)⟩
theorem envelope_sound294 : envelope294.Sound := by
  apply rat_majority_inputs_envelopes inputs294 inputs_valid294
  · norm_num [envelope294]
  · intro rho hr0 hr1
    have hh := Batch014.bound588 rho hr0 hr1
    norm_num [Batch014.certificate588,envelope294,inputs294,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch014.bound589 rho hr0 hr1
    norm_num [Batch014.certificate589,envelope294,inputs294,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs295 : RatMajorityInputs := ⟨(4367126433493986323892377/12500000000000000000000),(505543556816499/100000000000000),(504322292539563367/500000000000000000),(60029988129122649/500000000000000000),(505543556816499/200000000000000),(79841026980256209/1000000000000000000),26⟩
theorem inputs_valid295 : inputs295.Valid := by decide +kernel
def envelope295 : RatMajorityEnvelope := ⟨147,1,inputs295,1,(543218064017740693/1000000000000000000)⟩
theorem envelope_sound295 : envelope295.Sound := by
  apply rat_majority_inputs_envelopes inputs295 inputs_valid295
  · norm_num [envelope295]
  · intro rho hr0 hr1
    have hh := Batch014.bound590 rho hr0 hr1
    norm_num [Batch014.certificate590,envelope295,inputs295,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch014.bound591 rho hr0 hr1
    norm_num [Batch014.certificate591,envelope295,inputs295,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs296 : RatMajorityInputs := ⟨(6970854064869206572371843/20000000000000000000000),(445581896630787/100000000000000),(63041577797654527/62500000000000000),(44652204288580277/250000000000000000),(445581896630787/200000000000000),(53876727628938737/500000000000000000),25⟩
theorem inputs_valid296 : inputs296.Valid := by decide +kernel
def envelope296 : RatMajorityEnvelope := ⟨148,0,inputs296,(141479456/121454375),(694319723902860211/1000000000000000000)⟩
theorem envelope_sound296 : envelope296.Sound := by
  apply rat_majority_inputs_envelopes inputs296 inputs_valid296
  · norm_num [envelope296]
  · intro rho hr0 hr1
    have hh := Batch014.bound592 rho hr0 hr1
    norm_num [Batch014.certificate592,envelope296,inputs296,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch014.bound593 rho hr0 hr1
    norm_num [Batch014.certificate593,envelope296,inputs296,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs297 : RatMajorityInputs := ⟨(6970854064869206572371843/20000000000000000000000),(506002528624439/100000000000000),(63041577797654527/62500000000000000),(59843310159378159/500000000000000000),(506002528624439/200000000000000),(62232822776201/781250000000000),26⟩
theorem inputs_valid297 : inputs297.Valid := by decide +kernel
def envelope297 : RatMajorityEnvelope := ⟨148,1,inputs297,1,(67898722563572523/125000000000000000)⟩
theorem envelope_sound297 : envelope297.Sound := by
  apply rat_majority_inputs_envelopes inputs297 inputs_valid297
  · norm_num [envelope297]
  · intro rho hr0 hr1
    have hh := Batch014.bound594 rho hr0 hr1
    norm_num [Batch014.certificate594,envelope297,inputs297,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch014.bound595 rho hr0 hr1
    norm_num [Batch014.certificate595,envelope297,inputs297,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs298 : RatMajorityInputs := ⟨(135829053184275062591001/390625000000000000000),(1737999754491/390625000000),(201737165054414713/200000000000000000),(11210246609209629/62500000000000000),(1737999754491/781250000000),(108106363881730781/1000000000000000000),25⟩
theorem inputs_valid298 : inputs298.Valid := by decide +kernel
def envelope298 : RatMajorityEnvelope := ⟨149,0,inputs298,(2263058477/1943040000),(694239671716377411/1000000000000000000)⟩
theorem envelope_sound298 : envelope298.Sound := by
  apply rat_majority_inputs_envelopes inputs298 inputs_valid298
  · norm_num [envelope298]
  · intro rho hr0 hr1
    have hh := Batch014.bound596 rho hr0 hr1
    norm_num [Batch014.certificate596,envelope298,inputs298,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch014.bound597 rho hr0 hr1
    norm_num [Batch014.certificate597,envelope298,inputs298,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs299 : RatMajorityInputs := ⟨(135829053184275062591001/390625000000000000000),(123580523451/24414062500),(201737165054414713/200000000000000000),(59768902907645257/500000000000000000),(123580523451/48828125000),(15917008369540251/200000000000000000),27⟩
theorem inputs_valid299 : inputs299.Valid := by decide +kernel
def envelope299 : RatMajorityEnvelope := ⟨149,1,inputs299,1,(543184242693662291/1000000000000000000)⟩
theorem envelope_sound299 : envelope299.Sound := by
  apply rat_majority_inputs_envelopes inputs299 inputs_valid299
  · norm_num [envelope299]
  · intro rho hr0 hr1
    have hh := Batch014.bound598 rho hr0 hr1
    norm_num [Batch014.certificate598,envelope299,inputs299,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch014.bound599 rho hr0 hr1
    norm_num [Batch014.certificate599,envelope299,inputs299,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope280,envelope281,envelope282,envelope283,envelope284,envelope285,envelope286,envelope287,envelope288,envelope289,envelope290,envelope291,envelope292,envelope293,envelope294,envelope295,envelope296,envelope297,envelope298,envelope299]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound280
  · exact envelope_sound281
  · exact envelope_sound282
  · exact envelope_sound283
  · exact envelope_sound284
  · exact envelope_sound285
  · exact envelope_sound286
  · exact envelope_sound287
  · exact envelope_sound288
  · exact envelope_sound289
  · exact envelope_sound290
  · exact envelope_sound291
  · exact envelope_sound292
  · exact envelope_sound293
  · exact envelope_sound294
  · exact envelope_sound295
  · exact envelope_sound296
  · exact envelope_sound297
  · exact envelope_sound298
  · exact envelope_sound299

end Cycle12.MajorityCertificates.Inputs014
