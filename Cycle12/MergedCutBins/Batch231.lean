import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch001
import Cycle12.MergedCutProfiles.Batch002
import Cycle12.MergedCutProfiles.Batch003
import Cycle12.MergedCutProfiles.Batch307
import Cycle12.MergedCutProfiles.Batch440
import Cycle12.MergedCutProfiles.Batch441

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch231

def retention2772 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(1/2),(2310517734743707239/250000000000000000),(21/20),(229615052338521698222354413173732056651/231051773474370723900000000000000000000),false,MergedCutProfiles.Batch307.profile12294,(fun _ => MergedCutProfiles.Batch307.profile12294)⟩
theorem profilesValid2772 : retention2772.ProfilesValid := by
  exact MergedCutProfiles.Batch307.valid12294
theorem numericValid2772 : retention2772.NumericValid := by decide +kernel
def certificate2772 : RatCutBinCertificate := ⟨⟨retention2772,(2375668480937083231/1000000000000000000),(123364672097640231/500000000000000000),(4573138638309731967/250000000000000000),(13572511252097274473/40000000000000000),(960134219422298161/1000000000000000000)⟩,(994685652049364679/1000000000000000000),(353880536770253841/1000000000000000000),(278504610903398873/1000000000000000000),(231420497968238189/1000000000000000000)⟩
theorem valid2772 : certificate2772.Valid := by decide +kernel
theorem sound2772 : certificate2772.Sound := rat_cut_bin_certificate_sound certificate2772 profilesValid2772 numericValid2772 valid2772

def retention2773 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(1/2),64,1,(10216831075443792460644374972913285751/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch307.profile12294,(fun _ => MergedCutProfiles.Batch307.profile12294)⟩
theorem profilesValid2773 : retention2773.ProfilesValid := by
  exact MergedCutProfiles.Batch307.valid12294
theorem numericValid2773 : retention2773.NumericValid := by decide +kernel
def certificate2773 : RatCutBinCertificate := ⟨⟨retention2773,(2375668480937083231/1000000000000000000),(123364672097640231/500000000000000000),(4573138638309731967/250000000000000000),(13572511252097274473/40000000000000000),(965694111209321259/1000000000000000000)⟩,(994685652049364679/1000000000000000000),(334377496947853733/1000000000000000000),(74827015543416539/250000000000000000),(141607116693952139/500000000000000000)⟩
theorem valid2773 : certificate2773.Valid := by decide +kernel
theorem sound2773 : certificate2773.Sound := rat_cut_bin_certificate_sound certificate2773 profilesValid2773 numericValid2773 valid2773

def retention2774 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(4202259407671122396/9244737841268092559),(1156566038511704029/250000000000000000),(21/20),(487253411622009617253055754607923279999/462626415404681611600000000000000000000),false,MergedCutProfiles.Batch440.profile17636,(fun _ => MergedCutProfiles.Batch440.profile17636)⟩
theorem profilesValid2774 : retention2774.ProfilesValid := by
  exact MergedCutProfiles.Batch440.valid17636
theorem numericValid2774 : retention2774.NumericValid := by decide +kernel
def certificate2774 : RatCutBinCertificate := ⟨⟨retention2774,(2612463527937083231/1000000000000000000),(123364672097640231/500000000000000000),(4573138638309731967/250000000000000000),(13572511252097274473/40000000000000000),(1016228811993335449/1000000000000000000)⟩,(994154953942964871/1000000000000000000),(222837210962392021/1000000000000000000),(442445702530912427/1000000000000000000),(1108623465472011/3125000000000000)⟩
theorem valid2774 : certificate2774.Valid := by decide +kernel
theorem sound2774 : certificate2774.Sound := rat_cut_bin_certificate_sound certificate2774 profilesValid2774 numericValid2774 valid2774

def retention2775 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(9100889556770717665/18489475682536185118),(1050564851917780599/125000000000000000),1,(33163551515443767446436476764331683127/33618075261368979168000000000000000000),false,MergedCutProfiles.Batch440.profile17637,(fun _ => MergedCutProfiles.Batch440.profile17637)⟩
theorem profilesValid2775 : retention2775.ProfilesValid := by
  exact MergedCutProfiles.Batch440.valid17637
theorem numericValid2775 : retention2775.NumericValid := by decide +kernel
def certificate2775 : RatCutBinCertificate := ⟨⟨retention2775,(2612463527937083231/1000000000000000000),(123364672097640231/500000000000000000),(4573138638309731967/250000000000000000),(13572511252097274473/40000000000000000),(95123991433294021/100000000000000000)⟩,(994154953942964871/1000000000000000000),(119030746477360109/500000000000000000),(134448464412213/320000000000000),(89197469240325829/250000000000000000)⟩
theorem valid2775 : certificate2775.Valid := by decide +kernel
theorem sound2775 : certificate2775.Sound := rat_cut_bin_certificate_sound certificate2775 profilesValid2775 numericValid2775 valid2775

def retention2776 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(4595949226169212421/9244737841268092559),(1820177911354143533/200000000000000000),1,(1114298375119964190004691863471964073/1137611194596339708125000000000000000),false,MergedCutProfiles.Batch440.profile17638,(fun _ => MergedCutProfiles.Batch440.profile17638)⟩
theorem profilesValid2776 : retention2776.ProfilesValid := by
  exact MergedCutProfiles.Batch440.valid17638
theorem numericValid2776 : retention2776.NumericValid := by decide +kernel
def certificate2776 : RatCutBinCertificate := ⟨⟨retention2776,(2612463527937083231/1000000000000000000),(123364672097640231/500000000000000000),(4573138638309731967/250000000000000000),(13572511252097274473/40000000000000000),(944267583671814801/1000000000000000000)⟩,(994154953942964871/1000000000000000000),(239819303426310413/1000000000000000000),(417640067173979467/1000000000000000000),(355073984331855809/1000000000000000000)⟩
theorem valid2776 : certificate2776.Valid := by decide +kernel
theorem sound2776 : certificate2776.Sound := rat_cut_bin_certificate_sound certificate2776 profilesValid2776 numericValid2776 valid2776

def retention2777 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(1/2),(4595949226169212421/500000000000000000),1,(7165037500615789893883905624381282779/7353518761870739873600000000000000000),false,MergedCutProfiles.Batch307.profile12294,(fun _ => MergedCutProfiles.Batch307.profile12294)⟩
theorem profilesValid2777 : retention2777.ProfilesValid := by
  exact MergedCutProfiles.Batch307.valid12294
theorem numericValid2777 : retention2777.NumericValid := by decide +kernel
def certificate2777 : RatCutBinCertificate := ⟨⟨retention2777,(2612463527937083231/1000000000000000000),(123364672097640231/500000000000000000),(4573138638309731967/250000000000000000),(13572511252097274473/40000000000000000),(187825791303713637/200000000000000000)⟩,(994154953942964871/1000000000000000000),(241131521493813651/1000000000000000000),(415773567490718381/1000000000000000000),(44008818261325817/125000000000000000)⟩
theorem valid2777 : certificate2777.Valid := by decide +kernel
theorem sound2777 : certificate2777.Sound := rat_cut_bin_certificate_sound certificate2777 profilesValid2777 numericValid2777 valid2777

def retention2778 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(93146146721749780/2679143532738708719727),(572908247735206181/1000000000000000000),4,(5056364120065447324383060101253025647/2291632990940824724000000000000000000),true,MergedCutProfiles.Batch440.profile17639,![MergedCutProfiles.Batch440.profile17639,MergedCutProfiles.Batch307.profile12298,MergedCutProfiles.Batch441.profile17640,MergedCutProfiles.Batch001.profile71,MergedCutProfiles.Batch001.profile71,MergedCutProfiles.Batch307.profile12299,MergedCutProfiles.Batch307.profile12299,MergedCutProfiles.Batch441.profile17641,MergedCutProfiles.Batch001.profile72,MergedCutProfiles.Batch001.profile72,MergedCutProfiles.Batch307.profile12300,MergedCutProfiles.Batch307.profile12300,MergedCutProfiles.Batch307.profile12300,MergedCutProfiles.Batch001.profile73,MergedCutProfiles.Batch001.profile73,MergedCutProfiles.Batch001.profile74]⟩
theorem profilesValid2778 : retention2778.ProfilesValid := by
  change ∀ j : Fin 16, (retention2778.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch440.valid17639
  · exact MergedCutProfiles.Batch307.valid12298
  · exact MergedCutProfiles.Batch441.valid17640
  · exact MergedCutProfiles.Batch001.valid71
  · exact MergedCutProfiles.Batch001.valid71
  · exact MergedCutProfiles.Batch307.valid12299
  · exact MergedCutProfiles.Batch307.valid12299
  · exact MergedCutProfiles.Batch441.valid17641
  · exact MergedCutProfiles.Batch001.valid72
  · exact MergedCutProfiles.Batch001.valid72
  · exact MergedCutProfiles.Batch307.valid12300
  · exact MergedCutProfiles.Batch307.valid12300
  · exact MergedCutProfiles.Batch307.valid12300
  · exact MergedCutProfiles.Batch001.valid73
  · exact MergedCutProfiles.Batch001.valid73
  · exact MergedCutProfiles.Batch001.valid74
theorem numericValid2778 : retention2778.NumericValid := by decide +kernel
def certificate2778 : RatCutBinCertificate := ⟨⟨retention2778,(71433378637781447/40000000000000000),(637434242080419/1000000000000000000),(6917663836391420737/1000000000000000000),(130298704196336693278041/1000000000000000000),(551446907113044807/250000000000000000)⟩,(62499143700170907/62500000000000000),(292775521204838013/500000000000000000),(25265228068012679/250000000000000000),(701868615941549/15625000000000000)⟩
theorem valid2778 : certificate2778.Valid := by decide +kernel
theorem sound2778 : certificate2778.Sound := rat_cut_bin_certificate_sound certificate2778 profilesValid2778 numericValid2778 valid2778

def retention2779 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(1326378314000000000/18754004729170961038089),(32601151352612423/50000000000000000),4,(6091590180049097444409285748261720839/2608092108208993840000000000000000000),true,MergedCutProfiles.Batch307.profile12298,![MergedCutProfiles.Batch307.profile12298,MergedCutProfiles.Batch001.profile71,MergedCutProfiles.Batch307.profile12299,MergedCutProfiles.Batch441.profile17641,MergedCutProfiles.Batch001.profile72,MergedCutProfiles.Batch307.profile12300,MergedCutProfiles.Batch001.profile73,MergedCutProfiles.Batch001.profile74,MergedCutProfiles.Batch001.profile74,MergedCutProfiles.Batch002.profile86,MergedCutProfiles.Batch001.profile75,MergedCutProfiles.Batch001.profile75,MergedCutProfiles.Batch001.profile76,MergedCutProfiles.Batch001.profile77,MergedCutProfiles.Batch001.profile77,MergedCutProfiles.Batch307.profile12301]⟩
theorem profilesValid2779 : retention2779.ProfilesValid := by
  change ∀ j : Fin 16, (retention2779.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch307.valid12298
  · exact MergedCutProfiles.Batch001.valid71
  · exact MergedCutProfiles.Batch307.valid12299
  · exact MergedCutProfiles.Batch441.valid17641
  · exact MergedCutProfiles.Batch001.valid72
  · exact MergedCutProfiles.Batch307.valid12300
  · exact MergedCutProfiles.Batch001.valid73
  · exact MergedCutProfiles.Batch001.valid74
  · exact MergedCutProfiles.Batch001.valid74
  · exact MergedCutProfiles.Batch002.valid86
  · exact MergedCutProfiles.Batch001.valid75
  · exact MergedCutProfiles.Batch001.valid75
  · exact MergedCutProfiles.Batch001.valid76
  · exact MergedCutProfiles.Batch001.valid77
  · exact MergedCutProfiles.Batch001.valid77
  · exact MergedCutProfiles.Batch307.valid12301
theorem numericValid2779 : retention2779.NumericValid := by decide +kernel
def certificate2779 : RatCutBinCertificate := ⟨⟨retention2779,(71433378637781447/40000000000000000),(637434242080419/1000000000000000000),(6917663836391420737/1000000000000000000),(130298704196336693278041/1000000000000000000),(466998342471287927/200000000000000000)⟩,(62499143700170907/62500000000000000),(506728144382494319/1000000000000000000),(7440392091039023/50000000000000000),(35489181772502669/500000000000000000)⟩
theorem valid2779 : certificate2779.Valid := by decide +kernel
theorem sound2779 : certificate2779.Sound := rat_cut_bin_certificate_sound certificate2779 profilesValid2779 numericValid2779 valid2779

def retention2780 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(1340581023321521066/2679143532738708719727),(663189157/500000000),(12/5),(37452153939616501629/16000000000000000000),true,MergedCutProfiles.Batch001.profile73,![MergedCutProfiles.Batch001.profile73,MergedCutProfiles.Batch001.profile77,MergedCutProfiles.Batch001.profile79,MergedCutProfiles.Batch002.profile82,MergedCutProfiles.Batch002.profile85,MergedCutProfiles.Batch002.profile88,MergedCutProfiles.Batch002.profile89,MergedCutProfiles.Batch441.profile17642,MergedCutProfiles.Batch002.profile92,MergedCutProfiles.Batch002.profile97,MergedCutProfiles.Batch002.profile94,MergedCutProfiles.Batch002.profile98,MergedCutProfiles.Batch307.profile12304,MergedCutProfiles.Batch002.profile99,MergedCutProfiles.Batch002.profile100,MergedCutProfiles.Batch441.profile17643]⟩
theorem profilesValid2780 : retention2780.ProfilesValid := by
  change ∀ j : Fin 16, (retention2780.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch001.valid73
  · exact MergedCutProfiles.Batch001.valid77
  · exact MergedCutProfiles.Batch001.valid79
  · exact MergedCutProfiles.Batch002.valid82
  · exact MergedCutProfiles.Batch002.valid85
  · exact MergedCutProfiles.Batch002.valid88
  · exact MergedCutProfiles.Batch002.valid89
  · exact MergedCutProfiles.Batch441.valid17642
  · exact MergedCutProfiles.Batch002.valid92
  · exact MergedCutProfiles.Batch002.valid97
  · exact MergedCutProfiles.Batch002.valid94
  · exact MergedCutProfiles.Batch002.valid98
  · exact MergedCutProfiles.Batch307.valid12304
  · exact MergedCutProfiles.Batch002.valid99
  · exact MergedCutProfiles.Batch002.valid100
  · exact MergedCutProfiles.Batch441.valid17643
theorem numericValid2780 : retention2780.NumericValid := by decide +kernel
def certificate2780 : RatCutBinCertificate := ⟨⟨retention2780,(71433378637781447/40000000000000000),(637434242080419/1000000000000000000),(6917663836391420737/1000000000000000000),(130298704196336693278041/1000000000000000000),(2340364683720670173/1000000000000000000)⟩,(62499143700170907/62500000000000000),(2617537212248407/7812500000000000),(59715582660207633/200000000000000000),(222879105646354977/1000000000000000000)⟩
theorem valid2780 : certificate2780.Valid := by decide +kernel
theorem sound2780 : certificate2780.Sound := rat_cut_bin_certificate_sound certificate2780 profilesValid2780 numericValid2780 valid2780

def retention2781 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(64000000000000000000/18754004729170961038089),(4692033581625323731/500000000000000000),(21/20),(8414056654039322771432126017064016550119/3753626865300258984800000000000000000000),false,MergedCutProfiles.Batch441.profile17644,(fun _ => MergedCutProfiles.Batch441.profile17644)⟩
theorem profilesValid2781 : retention2781.ProfilesValid := by
  exact MergedCutProfiles.Batch441.valid17644
theorem numericValid2781 : retention2781.NumericValid := by decide +kernel
def certificate2781 : RatCutBinCertificate := ⟨⟨retention2781,(71433378637781447/40000000000000000),(637434242080419/1000000000000000000),(6917663836391420737/1000000000000000000),(130298704196336693278041/1000000000000000000),(70043989994076081/31250000000000000)⟩,(62499143700170907/62500000000000000),(101008669834920539/500000000000000000),(94918655300116041/200000000000000000),(33307541951555991/40000000000000000)⟩
theorem valid2781 : certificate2781.Valid := by decide +kernel
theorem sound2781 : certificate2781.Sound := rat_cut_bin_certificate_sound certificate2781 profilesValid2781 numericValid2781 valid2781

def retention2782 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(1/2),64,1,(15960555614684130987744105293091422311/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch003.profile124,(fun _ => MergedCutProfiles.Batch003.profile124)⟩
theorem profilesValid2782 : retention2782.ProfilesValid := by
  exact MergedCutProfiles.Batch003.valid124
theorem numericValid2782 : retention2782.NumericValid := by decide +kernel
def certificate2782 : RatCutBinCertificate := ⟨⟨retention2782,(71433378637781447/40000000000000000),(637434242080419/1000000000000000000),(6917663836391420737/1000000000000000000),(130298704196336693278041/1000000000000000000),(124671271078012251/125000000000000000)⟩,(62499143700170907/62500000000000000),(203666012943537449/500000000000000000),(113415578047394047/500000000000000000),(222760030066895411/1000000000000000000)⟩
theorem valid2782 : certificate2782.Valid := by decide +kernel
theorem sound2782 : certificate2782.Sound := rat_cut_bin_certificate_sound certificate2782 profilesValid2782 numericValid2782 valid2782

def retention2783 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(64000000000000000000/18754004729170961038089),(7250213697956392521/1000000000000000000),1,(12449294429917194064283690624362702183/5800170958365114016800000000000000000),false,MergedCutProfiles.Batch441.profile17644,(fun _ => MergedCutProfiles.Batch441.profile17644)⟩
theorem profilesValid2783 : retention2783.ProfilesValid := by
  exact MergedCutProfiles.Batch441.valid17644
theorem numericValid2783 : retention2783.NumericValid := by decide +kernel
def certificate2783 : RatCutBinCertificate := ⟨⟨retention2783,(77319636757781447/40000000000000000),(637434242080419/1000000000000000000),(6917663836391420737/1000000000000000000),(130298704196336693278041/1000000000000000000),(1073094345780801279/500000000000000000)⟩,(249996292557175341/250000000000000000),(7129525791027703/100000000000000000),(183393184889087149/250000000000000000),(1214768415657634149/1000000000000000000)⟩
theorem valid2783 : certificate2783.Valid := by decide +kernel
theorem sound2783 : certificate2783.Sound := rat_cut_bin_certificate_sound certificate2783 profilesValid2783 numericValid2783 valid2783

def certificates : List RatCutBinCertificate := [certificate2772,certificate2773,certificate2774,certificate2775,certificate2776,certificate2777,certificate2778,certificate2779,certificate2780,certificate2781,certificate2782,certificate2783]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2772,List.forall_mem_cons.mpr ⟨sound2773,List.forall_mem_cons.mpr ⟨sound2774,List.forall_mem_cons.mpr ⟨sound2775,List.forall_mem_cons.mpr ⟨sound2776,List.forall_mem_cons.mpr ⟨sound2777,List.forall_mem_cons.mpr ⟨sound2778,List.forall_mem_cons.mpr ⟨sound2779,List.forall_mem_cons.mpr ⟨sound2780,List.forall_mem_cons.mpr ⟨sound2781,List.forall_mem_cons.mpr ⟨sound2782,List.forall_mem_cons.mpr ⟨sound2783,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch231
