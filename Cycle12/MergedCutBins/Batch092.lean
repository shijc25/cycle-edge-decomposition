import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch184
import Cycle12.MergedCutProfiles.Batch185
import Cycle12.MergedCutProfiles.Batch186

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch092

def retention1104 : RatCutRetentionCertificate := ⟨(43/800),(27/500),(1/2),64,1,(638498291519787926911919493121367679/640000000000000000000000000000000000),false,MergedCutProfiles.Batch184.profile7374,(fun _ => MergedCutProfiles.Batch184.profile7374)⟩
theorem profilesValid1104 : retention1104.ProfilesValid := by
  exact MergedCutProfiles.Batch184.valid7374
theorem numericValid1104 : retention1104.NumericValid := by decide +kernel
def certificate1104 : RatCutBinCertificate := ⟨⟨retention1104,(1113526092303454291/500000000000000000),(142705547327693923/1000000000000000000),(2839015555850207423/200000000000000000),(227180872034970018037/1000000000000000000),(24381610595896119/25000000000000000)⟩,(495784529389865187/500000000000000000),(110031293729019889/250000000000000000),(49666356120045387/250000000000000000),(94609705778666773/500000000000000000)⟩
theorem valid1104 : certificate1104.Valid := by decide +kernel
theorem sound1104 : certificate1104.Sound := rat_cut_bin_certificate_sound certificate1104 profilesValid1104 numericValid1104 valid1104

def retention1105 : RatCutRetentionCertificate := ⟨(43/800),(27/500),(7318249566689341053/15980719681828407898),(1823396241416605989/500000000000000000),(6/5),(24560803630746245210724519106426805261/22792453017707574862500000000000000000),false,MergedCutProfiles.Batch184.profile7375,(fun _ => MergedCutProfiles.Batch184.profile7375)⟩
theorem profilesValid1105 : retention1105.ProfilesValid := by
  exact MergedCutProfiles.Batch184.valid7375
theorem numericValid1105 : retention1105.NumericValid := by decide +kernel
def certificate1105 : RatCutBinCertificate := ⟨⟨retention1105,(1288732865803454291/500000000000000000),(142705547327693923/1000000000000000000),(2839015555850207423/200000000000000000),(227180872034970018037/1000000000000000000),(1046486410202162871/1000000000000000000)⟩,(495120186009186389/500000000000000000),(193440614838553249/500000000000000000),(30714980121844377/125000000000000000),(176763910328261857/1000000000000000000)⟩
theorem valid1105 : certificate1105.Valid := by decide +kernel
theorem sound1105 : certificate1105.Sound := rat_cut_bin_certificate_sound certificate1105 profilesValid1105 numericValid1105 valid1105

def retention1106 : RatCutRetentionCertificate := ⟨(43/800),(27/500),(3962307808374672268/7990359840914203949),(7318249566689341053/1000000000000000000),(21/20),(11658308208588881166477360938626165429391/11709199306702945684800000000000000000000),false,MergedCutProfiles.Batch184.profile7376,(fun _ => MergedCutProfiles.Batch184.profile7376)⟩
theorem profilesValid1106 : retention1106.ProfilesValid := by
  exact MergedCutProfiles.Batch184.valid7376
theorem numericValid1106 : retention1106.NumericValid := by decide +kernel
def certificate1106 : RatCutBinCertificate := ⟨⟨retention1106,(1288732865803454291/500000000000000000),(142705547327693923/1000000000000000000),(2839015555850207423/200000000000000000),(227180872034970018037/1000000000000000000),(968444237166118269/1000000000000000000)⟩,(495120186009186389/500000000000000000),(418058091195958629/1000000000000000000),(108669046282023979/500000000000000000),(177123555261484381/1000000000000000000)⟩
theorem valid1106 : certificate1106.Valid := by decide +kernel
theorem sound1106 : certificate1106.Sound := rat_cut_bin_certificate_sound certificate1106 profilesValid1106 numericValid1106 valid1106

def retention1107 : RatCutRetentionCertificate := ⟨(43/800),(27/500),(1/2),(990576952093668067/125000000000000000),(21/20),(196136613680427084389180717056810014311/198115390418733613400000000000000000000),false,MergedCutProfiles.Batch184.profile7374,(fun _ => MergedCutProfiles.Batch184.profile7374)⟩
theorem profilesValid1107 : retention1107.ProfilesValid := by
  exact MergedCutProfiles.Batch184.valid7374
theorem numericValid1107 : retention1107.NumericValid := by decide +kernel
def certificate1107 : RatCutBinCertificate := ⟨⟨retention1107,(1288732865803454291/500000000000000000),(142705547327693923/1000000000000000000),(2839015555850207423/200000000000000000),(227180872034970018037/1000000000000000000),(962802655443589177/1000000000000000000)⟩,(495120186009186389/500000000000000000),(420507719759934589/1000000000000000000),(107604452834265693/500000000000000000),(87958799867575539/500000000000000000)⟩
theorem valid1107 : certificate1107.Valid := by decide +kernel
theorem sound1107 : certificate1107.Sound := rat_cut_bin_certificate_sound certificate1107 profilesValid1107 numericValid1107 valid1107

def retention1108 : RatCutRetentionCertificate := ⟨(27/500),(217/4000),(929813600737952941/15810502367943446988),(850165604274620639/1000000000000000000),(57/20),(2595877459541932285591/1280000000000000000000),true,MergedCutProfiles.Batch184.profile7377,![MergedCutProfiles.Batch184.profile7377,MergedCutProfiles.Batch184.profile7378,MergedCutProfiles.Batch184.profile7379,MergedCutProfiles.Batch184.profile7380,MergedCutProfiles.Batch184.profile7381,MergedCutProfiles.Batch184.profile7382,MergedCutProfiles.Batch184.profile7383,MergedCutProfiles.Batch184.profile7384,MergedCutProfiles.Batch184.profile7385,MergedCutProfiles.Batch184.profile7386,MergedCutProfiles.Batch184.profile7387,MergedCutProfiles.Batch184.profile7388,MergedCutProfiles.Batch184.profile7389,MergedCutProfiles.Batch184.profile7390,MergedCutProfiles.Batch184.profile7391,MergedCutProfiles.Batch184.profile7392]⟩
theorem profilesValid1108 : retention1108.ProfilesValid := by
  change ∀ j : Fin 16, (retention1108.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch184.valid7377
  · exact MergedCutProfiles.Batch184.valid7378
  · exact MergedCutProfiles.Batch184.valid7379
  · exact MergedCutProfiles.Batch184.valid7380
  · exact MergedCutProfiles.Batch184.valid7381
  · exact MergedCutProfiles.Batch184.valid7382
  · exact MergedCutProfiles.Batch184.valid7383
  · exact MergedCutProfiles.Batch184.valid7384
  · exact MergedCutProfiles.Batch184.valid7385
  · exact MergedCutProfiles.Batch184.valid7386
  · exact MergedCutProfiles.Batch184.valid7387
  · exact MergedCutProfiles.Batch184.valid7388
  · exact MergedCutProfiles.Batch184.valid7389
  · exact MergedCutProfiles.Batch184.valid7390
  · exact MergedCutProfiles.Batch184.valid7391
  · exact MergedCutProfiles.Batch184.valid7392
theorem numericValid1108 : retention1108.NumericValid := by decide +kernel
def certificate1108 : RatCutBinCertificate := ⟨⟨retention1108,(1115141502066766229/500000000000000000),(5769223604251667/40000000000000000),(14256515711461654539/1000000000000000000),(225734409531058096999/1000000000000000000),(1963706704359940141/1000000000000000000)⟩,(39660699087471147/40000000000000000),(181855478872307433/500000000000000000),(268429380109107071/1000000000000000000),(5701905483668229/40000000000000000)⟩
theorem valid1108 : certificate1108.Valid := by decide +kernel
theorem sound1108 : certificate1108.Sound := rat_cut_bin_certificate_sound certificate1108 profilesValid1108 numericValid1108 valid1108

def retention1109 : RatCutRetentionCertificate := ⟨(27/500),(217/4000),(371056864973653181/3952625591985861747),(929813600737952941/1000000000000000000),(13/5),(613656918277938173769/320000000000000000000),true,MergedCutProfiles.Batch184.profile7393,![MergedCutProfiles.Batch184.profile7393,MergedCutProfiles.Batch184.profile7394,MergedCutProfiles.Batch184.profile7395,MergedCutProfiles.Batch184.profile7396,MergedCutProfiles.Batch184.profile7397,MergedCutProfiles.Batch184.profile7398,MergedCutProfiles.Batch184.profile7399,MergedCutProfiles.Batch185.profile7400,MergedCutProfiles.Batch185.profile7401,MergedCutProfiles.Batch184.profile7392,MergedCutProfiles.Batch185.profile7402,MergedCutProfiles.Batch185.profile7403,MergedCutProfiles.Batch185.profile7404,MergedCutProfiles.Batch185.profile7405,MergedCutProfiles.Batch185.profile7406,MergedCutProfiles.Batch185.profile7407]⟩
theorem profilesValid1109 : retention1109.ProfilesValid := by
  change ∀ j : Fin 16, (retention1109.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch184.valid7393
  · exact MergedCutProfiles.Batch184.valid7394
  · exact MergedCutProfiles.Batch184.valid7395
  · exact MergedCutProfiles.Batch184.valid7396
  · exact MergedCutProfiles.Batch184.valid7397
  · exact MergedCutProfiles.Batch184.valid7398
  · exact MergedCutProfiles.Batch184.valid7399
  · exact MergedCutProfiles.Batch185.valid7400
  · exact MergedCutProfiles.Batch185.valid7401
  · exact MergedCutProfiles.Batch184.valid7392
  · exact MergedCutProfiles.Batch185.valid7402
  · exact MergedCutProfiles.Batch185.valid7403
  · exact MergedCutProfiles.Batch185.valid7404
  · exact MergedCutProfiles.Batch185.valid7405
  · exact MergedCutProfiles.Batch185.valid7406
  · exact MergedCutProfiles.Batch185.valid7407
theorem numericValid1109 : retention1109.NumericValid := by decide +kernel
def certificate1109 : RatCutBinCertificate := ⟨⟨retention1109,(1115141502066766229/500000000000000000),(5769223604251667/40000000000000000),(14256515711461654539/1000000000000000000),(225734409531058096999/1000000000000000000),(1858997603698075991/1000000000000000000)⟩,(39660699087471147/40000000000000000),(92715839915734821/250000000000000000),(65316518903181937/250000000000000000),(142711049730772039/1000000000000000000)⟩
theorem valid1109 : certificate1109.Valid := by decide +kernel
theorem sound1109 : certificate1109.Sound := rat_cut_bin_certificate_sound certificate1109 profilesValid1109 numericValid1109 valid1109

def retention1110 : RatCutRetentionCertificate := ⟨(27/500),(217/4000),(1003639739882533016/3952625591985861747),(371056864973653181/250000000000000000),(9/5),(482204314925497122489/320000000000000000000),true,MergedCutProfiles.Batch185.profile7408,![MergedCutProfiles.Batch185.profile7408,MergedCutProfiles.Batch185.profile7409,MergedCutProfiles.Batch185.profile7410,MergedCutProfiles.Batch185.profile7411,MergedCutProfiles.Batch185.profile7412,MergedCutProfiles.Batch185.profile7413,MergedCutProfiles.Batch185.profile7414,MergedCutProfiles.Batch185.profile7415,MergedCutProfiles.Batch185.profile7416,MergedCutProfiles.Batch185.profile7417,MergedCutProfiles.Batch185.profile7418,MergedCutProfiles.Batch185.profile7419,MergedCutProfiles.Batch185.profile7420,MergedCutProfiles.Batch185.profile7421,MergedCutProfiles.Batch185.profile7422,MergedCutProfiles.Batch185.profile7423]⟩
theorem profilesValid1110 : retention1110.ProfilesValid := by
  change ∀ j : Fin 16, (retention1110.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch185.valid7408
  · exact MergedCutProfiles.Batch185.valid7409
  · exact MergedCutProfiles.Batch185.valid7410
  · exact MergedCutProfiles.Batch185.valid7411
  · exact MergedCutProfiles.Batch185.valid7412
  · exact MergedCutProfiles.Batch185.valid7413
  · exact MergedCutProfiles.Batch185.valid7414
  · exact MergedCutProfiles.Batch185.valid7415
  · exact MergedCutProfiles.Batch185.valid7416
  · exact MergedCutProfiles.Batch185.valid7417
  · exact MergedCutProfiles.Batch185.valid7418
  · exact MergedCutProfiles.Batch185.valid7419
  · exact MergedCutProfiles.Batch185.valid7420
  · exact MergedCutProfiles.Batch185.valid7421
  · exact MergedCutProfiles.Batch185.valid7422
  · exact MergedCutProfiles.Batch185.valid7423
theorem numericValid1110 : retention1110.NumericValid := by decide +kernel
def certificate1110 : RatCutBinCertificate := ⟨⟨retention1110,(1115141502066766229/500000000000000000),(5769223604251667/40000000000000000),(14256515711461654539/1000000000000000000),(225734409531058096999/1000000000000000000),(1466264705570963093/1000000000000000000)⟩,(39660699087471147/40000000000000000),(100698475899954563/250000000000000000),(230932179134250703/1000000000000000000),(5709124698086979/40000000000000000)⟩
theorem valid1110 : certificate1110.Valid := by decide +kernel
theorem sound1110 : certificate1110.Sound := rat_cut_bin_certificate_sound certificate1110 profilesValid1110 numericValid1110 valid1110

def retention1111 : RatCutRetentionCertificate := ⟨(27/500),(217/4000),(3504328225666399369/7905251183971723494),(125454967485316627/31250000000000000),(21/20),(42961401013037298243/40000000000000000000),true,MergedCutProfiles.Batch185.profile7424,![MergedCutProfiles.Batch185.profile7424,MergedCutProfiles.Batch185.profile7425,MergedCutProfiles.Batch185.profile7426,MergedCutProfiles.Batch185.profile7427,MergedCutProfiles.Batch185.profile7428,MergedCutProfiles.Batch185.profile7429,MergedCutProfiles.Batch185.profile7430,MergedCutProfiles.Batch185.profile7431,MergedCutProfiles.Batch185.profile7432,MergedCutProfiles.Batch185.profile7433,MergedCutProfiles.Batch185.profile7434,MergedCutProfiles.Batch185.profile7435,MergedCutProfiles.Batch185.profile7436,MergedCutProfiles.Batch185.profile7437,MergedCutProfiles.Batch185.profile7438,MergedCutProfiles.Batch185.profile7439]⟩
theorem profilesValid1111 : retention1111.ProfilesValid := by
  change ∀ j : Fin 16, (retention1111.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch185.valid7424
  · exact MergedCutProfiles.Batch185.valid7425
  · exact MergedCutProfiles.Batch185.valid7426
  · exact MergedCutProfiles.Batch185.valid7427
  · exact MergedCutProfiles.Batch185.valid7428
  · exact MergedCutProfiles.Batch185.valid7429
  · exact MergedCutProfiles.Batch185.valid7430
  · exact MergedCutProfiles.Batch185.valid7431
  · exact MergedCutProfiles.Batch185.valid7432
  · exact MergedCutProfiles.Batch185.valid7433
  · exact MergedCutProfiles.Batch185.valid7434
  · exact MergedCutProfiles.Batch185.valid7435
  · exact MergedCutProfiles.Batch185.valid7436
  · exact MergedCutProfiles.Batch185.valid7437
  · exact MergedCutProfiles.Batch185.valid7438
  · exact MergedCutProfiles.Batch185.valid7439
theorem numericValid1111 : retention1111.NumericValid := by decide +kernel
def certificate1111 : RatCutBinCertificate := ⟨⟨retention1111,(1115141502066766229/500000000000000000),(5769223604251667/40000000000000000),(14256515711461654539/1000000000000000000),(225734409531058096999/1000000000000000000),(1050339896117502149/1000000000000000000)⟩,(39660699087471147/40000000000000000),(18513287706473621/40000000000000000),(90302998049955709/500000000000000000),(144633885168985431/1000000000000000000)⟩
theorem valid1111 : certificate1111.Valid := by decide +kernel
theorem sound1111 : certificate1111.Sound := rat_cut_bin_certificate_sound certificate1111 profilesValid1111 numericValid1111 valid1111

def retention1112 : RatCutRetentionCertificate := ⟨(27/500),(217/4000),(7741916985548186371/15810502367943446988),(3504328225666399369/500000000000000000),(21/20),(2820828133393852403617548239436868032239/2803462580533119495200000000000000000000),false,MergedCutProfiles.Batch186.profile7440,(fun _ => MergedCutProfiles.Batch186.profile7440)⟩
theorem profilesValid1112 : retention1112.ProfilesValid := by
  exact MergedCutProfiles.Batch186.valid7440
theorem numericValid1112 : retention1112.NumericValid := by decide +kernel
def certificate1112 : RatCutBinCertificate := ⟨⟨retention1112,(1115141502066766229/500000000000000000),(5769223604251667/40000000000000000),(14256515711461654539/1000000000000000000),(225734409531058096999/1000000000000000000),(982500727945240453/1000000000000000000)⟩,(39660699087471147/40000000000000000),(234072198959429669/500000000000000000),(44135980489377411/250000000000000000),(14522699723791957/100000000000000000)⟩
theorem valid1112 : certificate1112.Valid := by decide +kernel
theorem sound1112 : certificate1112.Sound := rat_cut_bin_certificate_sound certificate1112 profilesValid1112 numericValid1112 valid1112

def retention1113 : RatCutRetentionCertificate := ⟨(27/500),(217/4000),(7819336155403668235/15810502367943446988),(7741916985548186371/1000000000000000000),(21/20),(12385054069629277383638845381956159491759/12387067176877098193600000000000000000000),false,MergedCutProfiles.Batch186.profile7441,(fun _ => MergedCutProfiles.Batch186.profile7441)⟩
theorem profilesValid1113 : retention1113.ProfilesValid := by
  exact MergedCutProfiles.Batch186.valid7441
theorem numericValid1113 : retention1113.NumericValid := by decide +kernel
def certificate1113 : RatCutBinCertificate := ⟨⟨retention1113,(1115141502066766229/500000000000000000),(5769223604251667/40000000000000000),(14256515711461654539/1000000000000000000),(225734409531058096999/1000000000000000000),(195228816573280759/200000000000000000)⟩,(39660699087471147/40000000000000000),(467787150803070073/1000000000000000000),(11050949958058433/62500000000000000),(146174971003269281/1000000000000000000)⟩
theorem valid1113 : certificate1113.Valid := by decide +kernel
theorem sound1113 : certificate1113.Sound := rat_cut_bin_certificate_sound certificate1113 profilesValid1113 numericValid1113 valid1113

def retention1114 : RatCutRetentionCertificate := ⟨(27/500),(217/4000),(3948764758478852459/7905251183971723494),(1563867231080733647/200000000000000000),(21/20),(495729951392397401937922949852037389639/500437513945834767040000000000000000000),false,MergedCutProfiles.Batch186.profile7442,(fun _ => MergedCutProfiles.Batch186.profile7442)⟩
theorem profilesValid1114 : retention1114.ProfilesValid := by
  exact MergedCutProfiles.Batch186.valid7442
theorem numericValid1114 : retention1114.NumericValid := by decide +kernel
def certificate1114 : RatCutBinCertificate := ⟨⟨retention1114,(1115141502066766229/500000000000000000),(5769223604251667/40000000000000000),(14256515711461654539/1000000000000000000),(225734409531058096999/1000000000000000000),(966899724349974243/1000000000000000000)⟩,(39660699087471147/40000000000000000),(471934189651657017/1000000000000000000),(6947314741493809/40000000000000000),(285016436570667/2000000000000000)⟩
theorem valid1114 : certificate1114.Valid := by decide +kernel
theorem sound1114 : certificate1114.Sound := rat_cut_bin_certificate_sound certificate1114 profilesValid1114 numericValid1114 valid1114

def retention1115 : RatCutRetentionCertificate := ⟨(27/500),(217/4000),(1/2),(3948764758478852459/500000000000000000),(21/20),(3127174154314527152571994374326746966799/3159011806783081967200000000000000000000),false,MergedCutProfiles.Batch186.profile7443,(fun _ => MergedCutProfiles.Batch186.profile7443)⟩
theorem profilesValid1115 : retention1115.ProfilesValid := by
  exact MergedCutProfiles.Batch186.valid7443
theorem numericValid1115 : retention1115.NumericValid := by decide +kernel
def certificate1115 : RatCutBinCertificate := ⟨⟨retention1115,(1115141502066766229/500000000000000000),(5769223604251667/40000000000000000),(14256515711461654539/1000000000000000000),(225734409531058096999/1000000000000000000),(966228278241754337/1000000000000000000)⟩,(39660699087471147/40000000000000000),(471939749441974361/1000000000000000000),(173678693661413337/1000000000000000000),(142558765421589219/1000000000000000000)⟩
theorem valid1115 : certificate1115.Valid := by decide +kernel
theorem sound1115 : certificate1115.Sound := rat_cut_bin_certificate_sound certificate1115 profilesValid1115 numericValid1115 valid1115

def certificates : List RatCutBinCertificate := [certificate1104,certificate1105,certificate1106,certificate1107,certificate1108,certificate1109,certificate1110,certificate1111,certificate1112,certificate1113,certificate1114,certificate1115]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1104,List.forall_mem_cons.mpr ⟨sound1105,List.forall_mem_cons.mpr ⟨sound1106,List.forall_mem_cons.mpr ⟨sound1107,List.forall_mem_cons.mpr ⟨sound1108,List.forall_mem_cons.mpr ⟨sound1109,List.forall_mem_cons.mpr ⟨sound1110,List.forall_mem_cons.mpr ⟨sound1111,List.forall_mem_cons.mpr ⟨sound1112,List.forall_mem_cons.mpr ⟨sound1113,List.forall_mem_cons.mpr ⟨sound1114,List.forall_mem_cons.mpr ⟨sound1115,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch092
