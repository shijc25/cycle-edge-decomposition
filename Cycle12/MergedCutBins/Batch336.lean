import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch368
import Cycle12.MergedCutProfiles.Batch369
import Cycle12.MergedCutProfiles.Batch370
import Cycle12.MergedCutProfiles.Batch484
import Cycle12.MergedCutProfiles.Batch485
import Cycle12.MergedCutProfiles.Batch608
import Cycle12.MergedCutProfiles.Batch609

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch336

def retention4032 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(14417147302057446697/109806300649514491154),(354395744869940311/200000000000000000),2,(1616462649385063638180753779205925673/885989362174850777500000000000000000),false,MergedCutProfiles.Batch608.profile24333,(fun _ => MergedCutProfiles.Batch608.profile24333)⟩
theorem profilesValid4032 : retention4032.ProfilesValid := by
  exact MergedCutProfiles.Batch608.valid24333
theorem numericValid4032 : retention4032.NumericValid := by decide +kernel
def certificate4032 : RatCutBinCertificate := ⟨⟨retention4032,(959300363692540987/500000000000000000),(6511012982960937/62500000000000000),(2495228950263818199/200000000000000000),(5510612223659443130943/1000000000000000000),(1792430922732350161/1000000000000000000)⟩,(99968639464525333/100000000000000000),(237782271536308833/500000000000000000),(21371340278943959/125000000000000000),(6112754816859373/50000000000000000)⟩
theorem valid4032 : certificate4032.Valid := by decide +kernel
theorem sound4032 : certificate4032.Sound := rat_cut_bin_certificate_sound certificate4032 profilesValid4032 numericValid4032 valid4032

def retention4033 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(8000000000000000000/54903150324757245577),(14417147302057446697/250000000000000000),1,(199525935944153773197129287993969819/112633963297323802320312500000000000),false,MergedCutProfiles.Batch608.profile24334,(fun _ => MergedCutProfiles.Batch608.profile24334)⟩
theorem profilesValid4033 : retention4033.ProfilesValid := by
  exact MergedCutProfiles.Batch608.valid24334
theorem numericValid4033 : retention4033.NumericValid := by decide +kernel
def certificate4033 : RatCutBinCertificate := ⟨⟨retention4033,(959300363692540987/500000000000000000),(6511012982960937/62500000000000000),(2495228950263818199/200000000000000000),(5510612223659443130943/1000000000000000000),(14043472569709679/8000000000000000)⟩,(99968639464525333/100000000000000000),(151767108077419247/500000000000000000),(334552866202461049/1000000000000000000),(569755950831359769/1000000000000000000)⟩
theorem valid4033 : certificate4033.Valid := by decide +kernel
theorem sound4033 : certificate4033.Sound := rat_cut_bin_certificate_sound certificate4033 profilesValid4033 numericValid4033 valid4033

def retention4034 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(1/2),64,1,(3990468797864115059147722484285061679/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch368.profile14746,(fun _ => MergedCutProfiles.Batch368.profile14746)⟩
theorem profilesValid4034 : retention4034.ProfilesValid := by
  exact MergedCutProfiles.Batch368.valid14746
theorem numericValid4034 : retention4034.NumericValid := by decide +kernel
def certificate4034 : RatCutBinCertificate := ⟨⟨retention4034,(959300363692540987/500000000000000000),(6511012982960937/62500000000000000),(2495228950263818199/200000000000000000),(5510612223659443130943/1000000000000000000),(39263872691722587/40000000000000000)⟩,(99968639464525333/100000000000000000),(108360590625841069/200000000000000000),(12615152573191339/100000000000000000),(121920766903932971/1000000000000000000)⟩
theorem valid4034 : certificate4034.Valid := by decide +kernel
theorem sound4034 : certificate4034.Sound := rat_cut_bin_certificate_sound certificate4034 profilesValid4034 numericValid4034 valid4034

def retention4035 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(8000000000000000000/54903150324757245577),(6210106206462073057/250000000000000000),1,(85058787654136111080712231833550979/48516454737984945757812500000000000),false,MergedCutProfiles.Batch608.profile24334,(fun _ => MergedCutProfiles.Batch608.profile24334)⟩
theorem profilesValid4035 : retention4035.ProfilesValid := by
  exact MergedCutProfiles.Batch608.valid24334
theorem numericValid4035 : retention4035.NumericValid := by decide +kernel
def certificate4035 : RatCutBinCertificate := ⟨⟨retention4035,(925774533692540987/500000000000000000),(6511012982960937/62500000000000000),(2495228950263818199/200000000000000000),(5510612223659443130943/1000000000000000000),(868867059478776707/500000000000000000)⟩,(499848677478261117/500000000000000000),(8157280879399249/250000000000000000),(418323341837573647/500000000000000000),(339597765093414659/250000000000000000)⟩
theorem valid4035 : certificate4035.Valid := by decide +kernel
theorem sound4035 : certificate4035.Sound := rat_cut_bin_certificate_sound certificate4035 profilesValid4035 numericValid4035 valid4035

def retention4036 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(1/2),64,1,(3990468797864115059147722484285061679/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch368.profile14746,(fun _ => MergedCutProfiles.Batch368.profile14746)⟩
theorem profilesValid4036 : retention4036.ProfilesValid := by
  exact MergedCutProfiles.Batch368.valid14746
theorem numericValid4036 : retention4036.NumericValid := by decide +kernel
def certificate4036 : RatCutBinCertificate := ⟨⟨retention4036,(925774533692540987/500000000000000000),(6511012982960937/62500000000000000),(2495228950263818199/200000000000000000),(5510612223659443130943/1000000000000000000),(491078350482058403/500000000000000000)⟩,(499848677478261117/500000000000000000),(11546170005773889/200000000000000000),(767945929307160061/1000000000000000000),(742616309570157201/1000000000000000000)⟩
theorem valid4036 : certificate4036.Valid := by decide +kernel
theorem sound4036 : certificate4036.Sound := rat_cut_bin_certificate_sound certificate4036 profilesValid4036 numericValid4036 valid4036

def retention4037 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(629219313155481551/418748044271657088761),(622989418965823317/1000000000000000000),4,(589851035679107640117/256000000000000000000),true,MergedCutProfiles.Batch608.profile24335,![MergedCutProfiles.Batch608.profile24335,MergedCutProfiles.Batch608.profile24336,MergedCutProfiles.Batch608.profile24337,MergedCutProfiles.Batch608.profile24338,MergedCutProfiles.Batch484.profile19376,MergedCutProfiles.Batch608.profile24339,MergedCutProfiles.Batch484.profile19388,MergedCutProfiles.Batch608.profile24340,MergedCutProfiles.Batch608.profile24341,MergedCutProfiles.Batch484.profile19377,MergedCutProfiles.Batch608.profile24342,MergedCutProfiles.Batch608.profile24343,MergedCutProfiles.Batch368.profile14749,MergedCutProfiles.Batch484.profile19389,MergedCutProfiles.Batch484.profile19378,MergedCutProfiles.Batch369.profile14781]⟩
theorem profilesValid4037 : retention4037.ProfilesValid := by
  change ∀ j : Fin 16, (retention4037.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch608.valid24335
  · exact MergedCutProfiles.Batch608.valid24336
  · exact MergedCutProfiles.Batch608.valid24337
  · exact MergedCutProfiles.Batch608.valid24338
  · exact MergedCutProfiles.Batch484.valid19376
  · exact MergedCutProfiles.Batch608.valid24339
  · exact MergedCutProfiles.Batch484.valid19388
  · exact MergedCutProfiles.Batch608.valid24340
  · exact MergedCutProfiles.Batch608.valid24341
  · exact MergedCutProfiles.Batch484.valid19377
  · exact MergedCutProfiles.Batch608.valid24342
  · exact MergedCutProfiles.Batch608.valid24343
  · exact MergedCutProfiles.Batch368.valid14749
  · exact MergedCutProfiles.Batch484.valid19389
  · exact MergedCutProfiles.Batch484.valid19378
  · exact MergedCutProfiles.Batch369.valid14781
theorem numericValid4037 : retention4037.NumericValid := by decide +kernel
def certificate4037 : RatCutBinCertificate := ⟨⟨retention4037,(240325241856841151/125000000000000000),(13651068898300767/125000000000000000),(12679903510959588819/1000000000000000000),(5339694884310694289539/1000000000000000000),(1118934839894645621/500000000000000000)⟩,(62479839938327331/62500000000000000),(324895000874708963/500000000000000000),(1752040050724749/25000000000000000),(3200715613548761/100000000000000000)⟩
theorem valid4037 : certificate4037.Valid := by decide +kernel
theorem sound4037 : certificate4037.Sound := rat_cut_bin_certificate_sound certificate4037 profilesValid4037 numericValid4037 valid4037

def retention4038 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(1097975930000000000/418748044271657088761),(629219313155481551/1000000000000000000),4,(147403570338812120711/64000000000000000000),true,MergedCutProfiles.Batch608.profile24344,![MergedCutProfiles.Batch608.profile24344,MergedCutProfiles.Batch608.profile24345,MergedCutProfiles.Batch608.profile24346,MergedCutProfiles.Batch484.profile19388,MergedCutProfiles.Batch608.profile24347,MergedCutProfiles.Batch608.profile24348,MergedCutProfiles.Batch608.profile24349,MergedCutProfiles.Batch484.profile19389,MergedCutProfiles.Batch608.profile24350,MergedCutProfiles.Batch608.profile24351,MergedCutProfiles.Batch608.profile24352,MergedCutProfiles.Batch484.profile19390,MergedCutProfiles.Batch485.profile19401,MergedCutProfiles.Batch484.profile19379,MergedCutProfiles.Batch368.profile14750,MergedCutProfiles.Batch484.profile19391]⟩
theorem profilesValid4038 : retention4038.ProfilesValid := by
  change ∀ j : Fin 16, (retention4038.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch608.valid24344
  · exact MergedCutProfiles.Batch608.valid24345
  · exact MergedCutProfiles.Batch608.valid24346
  · exact MergedCutProfiles.Batch484.valid19388
  · exact MergedCutProfiles.Batch608.valid24347
  · exact MergedCutProfiles.Batch608.valid24348
  · exact MergedCutProfiles.Batch608.valid24349
  · exact MergedCutProfiles.Batch484.valid19389
  · exact MergedCutProfiles.Batch608.valid24350
  · exact MergedCutProfiles.Batch608.valid24351
  · exact MergedCutProfiles.Batch608.valid24352
  · exact MergedCutProfiles.Batch484.valid19390
  · exact MergedCutProfiles.Batch485.valid19401
  · exact MergedCutProfiles.Batch484.valid19379
  · exact MergedCutProfiles.Batch368.valid14750
  · exact MergedCutProfiles.Batch484.valid19391
theorem numericValid4038 : retention4038.NumericValid := by decide +kernel
def certificate4038 : RatCutBinCertificate := ⟨⟨retention4038,(240325241856841151/125000000000000000),(13651068898300767/125000000000000000),(12679903510959588819/1000000000000000000),(5339694884310694289539/1000000000000000000),(447388972718804101/200000000000000000)⟩,(62479839938327331/62500000000000000),(32296736650953061/50000000000000000),(71755091186476457/1000000000000000000),(32819975243289781/1000000000000000000)⟩
theorem valid4038 : certificate4038.Valid := by decide +kernel
theorem sound4038 : certificate4038.Sound := rat_cut_bin_certificate_sound certificate4038 profilesValid4038 numericValid4038 valid4038

def retention4039 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(1098497255341470213/418748044271657088761),(109797593/100000000),(57/20),(189587228271016801/80000000000000000),true,MergedCutProfiles.Batch608.profile24344,![MergedCutProfiles.Batch608.profile24344,MergedCutProfiles.Batch608.profile24345,MergedCutProfiles.Batch608.profile24346,MergedCutProfiles.Batch484.profile19388,MergedCutProfiles.Batch608.profile24347,MergedCutProfiles.Batch608.profile24348,MergedCutProfiles.Batch608.profile24349,MergedCutProfiles.Batch484.profile19389,MergedCutProfiles.Batch608.profile24350,MergedCutProfiles.Batch608.profile24351,MergedCutProfiles.Batch608.profile24352,MergedCutProfiles.Batch484.profile19390,MergedCutProfiles.Batch485.profile19401,MergedCutProfiles.Batch484.profile19379,MergedCutProfiles.Batch368.profile14750,MergedCutProfiles.Batch484.profile19391]⟩
theorem profilesValid4039 : retention4039.ProfilesValid := by
  change ∀ j : Fin 16, (retention4039.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch608.valid24344
  · exact MergedCutProfiles.Batch608.valid24345
  · exact MergedCutProfiles.Batch608.valid24346
  · exact MergedCutProfiles.Batch484.valid19388
  · exact MergedCutProfiles.Batch608.valid24347
  · exact MergedCutProfiles.Batch608.valid24348
  · exact MergedCutProfiles.Batch608.valid24349
  · exact MergedCutProfiles.Batch484.valid19389
  · exact MergedCutProfiles.Batch608.valid24350
  · exact MergedCutProfiles.Batch608.valid24351
  · exact MergedCutProfiles.Batch608.valid24352
  · exact MergedCutProfiles.Batch484.valid19390
  · exact MergedCutProfiles.Batch485.valid19401
  · exact MergedCutProfiles.Batch484.valid19379
  · exact MergedCutProfiles.Batch368.valid14750
  · exact MergedCutProfiles.Batch484.valid19391
theorem numericValid4039 : retention4039.NumericValid := by decide +kernel
def certificate4039 : RatCutBinCertificate := ⟨⟨retention4039,(240325241856841151/125000000000000000),(13651068898300767/125000000000000000),(12679903510959588819/1000000000000000000),(5339694884310694289539/1000000000000000000),(2322647333330257361/1000000000000000000)⟩,(62479839938327331/62500000000000000),(90507159045194049/200000000000000000),(23581694916053417/125000000000000000),(24386511746358843/200000000000000000)⟩
theorem valid4039 : certificate4039.Valid := by decide +kernel
theorem sound4039 : certificate4039.Sound := rat_cut_bin_certificate_sound certificate4039 profilesValid4039 numericValid4039 valid4039

def retention4040 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(1131782820675572104/418748044271657088761),(1098497255341470213/1000000000000000000),(14/5),(3020240323619804638321/1280000000000000000000),true,MergedCutProfiles.Batch608.profile24344,![MergedCutProfiles.Batch608.profile24344,MergedCutProfiles.Batch608.profile24345,MergedCutProfiles.Batch608.profile24353,MergedCutProfiles.Batch608.profile24354,MergedCutProfiles.Batch608.profile24341,MergedCutProfiles.Batch608.profile24342,MergedCutProfiles.Batch608.profile24355,MergedCutProfiles.Batch608.profile24356,MergedCutProfiles.Batch369.profile14781,MergedCutProfiles.Batch608.profile24357,MergedCutProfiles.Batch369.profile14796,MergedCutProfiles.Batch608.profile24358,MergedCutProfiles.Batch608.profile24359,MergedCutProfiles.Batch609.profile24360,MergedCutProfiles.Batch609.profile24361,MergedCutProfiles.Batch609.profile24362]⟩
theorem profilesValid4040 : retention4040.ProfilesValid := by
  change ∀ j : Fin 16, (retention4040.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch608.valid24344
  · exact MergedCutProfiles.Batch608.valid24345
  · exact MergedCutProfiles.Batch608.valid24353
  · exact MergedCutProfiles.Batch608.valid24354
  · exact MergedCutProfiles.Batch608.valid24341
  · exact MergedCutProfiles.Batch608.valid24342
  · exact MergedCutProfiles.Batch608.valid24355
  · exact MergedCutProfiles.Batch608.valid24356
  · exact MergedCutProfiles.Batch369.valid14781
  · exact MergedCutProfiles.Batch608.valid24357
  · exact MergedCutProfiles.Batch369.valid14796
  · exact MergedCutProfiles.Batch608.valid24358
  · exact MergedCutProfiles.Batch608.valid24359
  · exact MergedCutProfiles.Batch609.valid24360
  · exact MergedCutProfiles.Batch609.valid24361
  · exact MergedCutProfiles.Batch609.valid24362
theorem numericValid4040 : retention4040.NumericValid := by decide +kernel
def certificate4040 : RatCutBinCertificate := ⟨⟨retention4040,(240325241856841151/125000000000000000),(13651068898300767/125000000000000000),(12679903510959588819/1000000000000000000),(5339694884310694289539/1000000000000000000),(2313197675225895467/1000000000000000000)⟩,(62479839938327331/62500000000000000),(9085519833821027/20000000000000000),(93638566805173287/500000000000000000),(121913916660647391/1000000000000000000)⟩
theorem valid4040 : certificate4040.Valid := by decide +kernel
theorem sound4040 : certificate4040.Sound := rat_cut_bin_certificate_sound certificate4040 profilesValid4040 numericValid4040 valid4040

def retention4041 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(2771320395312026886/418748044271657088761),(141472852584446513/125000000000000000),(11/4),(3712972284480878431/1600000000000000000),true,MergedCutProfiles.Batch609.profile24363,![MergedCutProfiles.Batch609.profile24363,MergedCutProfiles.Batch608.profile24347,MergedCutProfiles.Batch609.profile24364,MergedCutProfiles.Batch609.profile24365,MergedCutProfiles.Batch609.profile24366,MergedCutProfiles.Batch609.profile24367,MergedCutProfiles.Batch609.profile24368,MergedCutProfiles.Batch484.profile19392,MergedCutProfiles.Batch368.profile14751,MergedCutProfiles.Batch609.profile24369,MergedCutProfiles.Batch369.profile14783,MergedCutProfiles.Batch485.profile19404,MergedCutProfiles.Batch609.profile24370,MergedCutProfiles.Batch609.profile24371,MergedCutProfiles.Batch609.profile24372,MergedCutProfiles.Batch609.profile24373]⟩
theorem profilesValid4041 : retention4041.ProfilesValid := by
  change ∀ j : Fin 16, (retention4041.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch609.valid24363
  · exact MergedCutProfiles.Batch608.valid24347
  · exact MergedCutProfiles.Batch609.valid24364
  · exact MergedCutProfiles.Batch609.valid24365
  · exact MergedCutProfiles.Batch609.valid24366
  · exact MergedCutProfiles.Batch609.valid24367
  · exact MergedCutProfiles.Batch609.valid24368
  · exact MergedCutProfiles.Batch484.valid19392
  · exact MergedCutProfiles.Batch368.valid14751
  · exact MergedCutProfiles.Batch609.valid24369
  · exact MergedCutProfiles.Batch369.valid14783
  · exact MergedCutProfiles.Batch485.valid19404
  · exact MergedCutProfiles.Batch609.valid24370
  · exact MergedCutProfiles.Batch609.valid24371
  · exact MergedCutProfiles.Batch609.valid24372
  · exact MergedCutProfiles.Batch609.valid24373
theorem numericValid4041 : retention4041.NumericValid := by decide +kernel
def certificate4041 : RatCutBinCertificate := ⟨⟨retention4041,(240325241856841151/125000000000000000),(13651068898300767/125000000000000000),(12679903510959588819/1000000000000000000),(5339694884310694289539/1000000000000000000),(2275070551574476917/1000000000000000000)⟩,(62479839938327331/62500000000000000),(455058341599063941/1000000000000000000),(186660499597141903/1000000000000000000),(60975322007484009/500000000000000000)⟩
theorem valid4041 : certificate4041.Valid := by decide +kernel
theorem sound4041 : certificate4041.Sound := rat_cut_bin_certificate_sound certificate4041 profilesValid4041 numericValid4041 valid4041

def retention4042 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(64000000000000000000/418748044271657088761),(1385660197656013443/500000000000000000),(31/20),(1952676702582664232488992449205584235911/1108528158124810754400000000000000000000),false,MergedCutProfiles.Batch609.profile24374,(fun _ => MergedCutProfiles.Batch609.profile24374)⟩
theorem profilesValid4042 : retention4042.ProfilesValid := by
  exact MergedCutProfiles.Batch609.valid24374
theorem numericValid4042 : retention4042.NumericValid := by decide +kernel
def certificate4042 : RatCutBinCertificate := ⟨⟨retention4042,(240325241856841151/125000000000000000),(13651068898300767/125000000000000000),(12679903510959588819/1000000000000000000),(5339694884310694289539/1000000000000000000),(1735837592185480421/1000000000000000000)⟩,(62479839938327331/62500000000000000),(105406479400671463/250000000000000000),(26780216163996867/125000000000000000),(23780404498218451/125000000000000000)⟩
theorem valid4042 : certificate4042.Valid := by decide +kernel
theorem sound4042 : certificate4042.Sound := rat_cut_bin_certificate_sound certificate4042 profilesValid4042 numericValid4042 valid4042

def retention4043 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(1/2),64,1,(15961943206562927268838532628520865151/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch370.profile14826,(fun _ => MergedCutProfiles.Batch370.profile14826)⟩
theorem profilesValid4043 : retention4043.ProfilesValid := by
  exact MergedCutProfiles.Batch370.valid14826
theorem numericValid4043 : retention4043.NumericValid := by decide +kernel
def certificate4043 : RatCutBinCertificate := ⟨⟨retention4043,(240325241856841151/125000000000000000),(13651068898300767/125000000000000000),(12679903510959588819/1000000000000000000),(5339694884310694289539/1000000000000000000),(981062598938665501/1000000000000000000)⟩,(62479839938327331/62500000000000000),(541753360868946203/1000000000000000000),(630909603707249/5000000000000000),(121883669457956373/1000000000000000000)⟩
theorem valid4043 : certificate4043.Valid := by decide +kernel
theorem sound4043 : certificate4043.Sound := rat_cut_bin_certificate_sound certificate4043 profilesValid4043 numericValid4043 valid4043

def certificates : List RatCutBinCertificate := [certificate4032,certificate4033,certificate4034,certificate4035,certificate4036,certificate4037,certificate4038,certificate4039,certificate4040,certificate4041,certificate4042,certificate4043]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4032,List.forall_mem_cons.mpr ⟨sound4033,List.forall_mem_cons.mpr ⟨sound4034,List.forall_mem_cons.mpr ⟨sound4035,List.forall_mem_cons.mpr ⟨sound4036,List.forall_mem_cons.mpr ⟨sound4037,List.forall_mem_cons.mpr ⟨sound4038,List.forall_mem_cons.mpr ⟨sound4039,List.forall_mem_cons.mpr ⟨sound4040,List.forall_mem_cons.mpr ⟨sound4041,List.forall_mem_cons.mpr ⟨sound4042,List.forall_mem_cons.mpr ⟨sound4043,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch336
