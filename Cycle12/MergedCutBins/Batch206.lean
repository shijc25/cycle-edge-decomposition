import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch384
import Cycle12.MergedCutProfiles.Batch385
import Cycle12.MergedCutProfiles.Batch386

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch206

def retention2472 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(7891591448964295531/15980719681828407898),(3572077395257037269/250000000000000000),1,(2846144566445442059874442819458875891/2857661916205629815200000000000000000),false,MergedCutProfiles.Batch384.profile15390,(fun _ => MergedCutProfiles.Batch384.profile15390)⟩
theorem profilesValid2472 : retention2472.ProfilesValid := by
  exact MergedCutProfiles.Batch384.valid15390
theorem numericValid2472 : retention2472.NumericValid := by decide +kernel
def certificate2472 : RatCutBinCertificate := ⟨⟨retention2472,(2458777814303454291/1000000000000000000),(142705547327693923/1000000000000000000),(7007928973391192469/500000000000000000),(450599157594054054609/1000000000000000000),(970934516557484619/1000000000000000000)⟩,(248821436070388231/250000000000000000),(6116365438492181/25000000000000000),(102699244251544539/250000000000000000),(371655294987466531/1000000000000000000)⟩
theorem valid2472 : certificate2472.Valid := by decide +kernel
theorem sound2472 : certificate2472.Sound := rat_cut_bin_certificate_sound certificate2472 profilesValid2472 numericValid2472 valid2472

def retention2473 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(15941014726907876973/31961439363656815796),(7891591448964295531/500000000000000000),1,(155951808589395188575143726476596369/157831828979285910620000000000000000),false,MergedCutProfiles.Batch384.profile15391,(fun _ => MergedCutProfiles.Batch384.profile15391)⟩
theorem profilesValid2473 : retention2473.ProfilesValid := by
  exact MergedCutProfiles.Batch384.valid15391
theorem numericValid2473 : retention2473.NumericValid := by decide +kernel
def certificate2473 : RatCutBinCertificate := ⟨⟨retention2473,(2458777814303454291/1000000000000000000),(142705547327693923/1000000000000000000),(7007928973391192469/500000000000000000),(450599157594054054609/1000000000000000000),(38522134711109031/40000000000000000)⟩,(248821436070388231/250000000000000000),(123328374497350787/500000000000000000),(407991157812693281/1000000000000000000),(1842596462980619/5000000000000000)⟩
theorem valid2473 : certificate2473.Valid := by decide +kernel
theorem sound2473 : certificate2473.Sound := rat_cut_bin_certificate_sound certificate2473 profilesValid2473 numericValid2473 valid2473

def retention2474 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(1/2),(15941014726907876973/1000000000000000000),1,(5238408713750507855867411860505206131/5313671575635958991000000000000000000),false,MergedCutProfiles.Batch384.profile15388,(fun _ => MergedCutProfiles.Batch384.profile15388)⟩
theorem profilesValid2474 : retention2474.ProfilesValid := by
  exact MergedCutProfiles.Batch384.valid15388
theorem numericValid2474 : retention2474.NumericValid := by decide +kernel
def certificate2474 : RatCutBinCertificate := ⟨⟨retention2474,(2458777814303454291/1000000000000000000),(142705547327693923/1000000000000000000),(7007928973391192469/500000000000000000),(450599157594054054609/1000000000000000000),(960800910979489511/1000000000000000000)⟩,(248821436070388231/250000000000000000),(247234999561239423/1000000000000000000),(203591887490199767/500000000000000000),(45898536995430739/125000000000000000)⟩
theorem valid2474 : certificate2474.Valid := by decide +kernel
theorem sound2474 : certificate2474.Sound := rat_cut_bin_certificate_sound certificate2474 profilesValid2474 numericValid2474 valid2474

def retention2475 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(440357372015008373/15314307777793637652),(87199479606932351/100000000000000000),(29/10),(17137372953807667823/8000000000000000000),true,MergedCutProfiles.Batch384.profile15392,![MergedCutProfiles.Batch384.profile15392,MergedCutProfiles.Batch384.profile15393,MergedCutProfiles.Batch384.profile15394,MergedCutProfiles.Batch384.profile15395,MergedCutProfiles.Batch384.profile15396,MergedCutProfiles.Batch384.profile15397,MergedCutProfiles.Batch384.profile15398,MergedCutProfiles.Batch384.profile15399,MergedCutProfiles.Batch385.profile15400,MergedCutProfiles.Batch385.profile15401,MergedCutProfiles.Batch385.profile15402,MergedCutProfiles.Batch385.profile15403,MergedCutProfiles.Batch385.profile15404,MergedCutProfiles.Batch385.profile15405,MergedCutProfiles.Batch385.profile15406,MergedCutProfiles.Batch385.profile15407]⟩
theorem profilesValid2475 : retention2475.ProfilesValid := by
  change ∀ j : Fin 16, (retention2475.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch384.valid15392
  · exact MergedCutProfiles.Batch384.valid15393
  · exact MergedCutProfiles.Batch384.valid15394
  · exact MergedCutProfiles.Batch384.valid15395
  · exact MergedCutProfiles.Batch384.valid15396
  · exact MergedCutProfiles.Batch384.valid15397
  · exact MergedCutProfiles.Batch384.valid15398
  · exact MergedCutProfiles.Batch384.valid15399
  · exact MergedCutProfiles.Batch385.valid15400
  · exact MergedCutProfiles.Batch385.valid15401
  · exact MergedCutProfiles.Batch385.valid15402
  · exact MergedCutProfiles.Batch385.valid15403
  · exact MergedCutProfiles.Batch385.valid15404
  · exact MergedCutProfiles.Batch385.valid15405
  · exact MergedCutProfiles.Batch385.valid15406
  · exact MergedCutProfiles.Batch385.valid15407
theorem numericValid2475 : retention2475.NumericValid := by decide +kernel
def certificate2475 : RatCutBinCertificate := ⟨⟨retention2475,(1102648119346584823/500000000000000000),(14887102204219317/100000000000000000),(285189018766043241/20000000000000000),(27458151097991125517/62500000000000000),(2075394067386061349/1000000000000000000)⟩,(995693522260839989/1000000000000000000),(33894256032295781/100000000000000000),(147169601669127307/500000000000000000),(40835470041918701/250000000000000000)⟩
theorem valid2475 : certificate2475.Valid := by decide +kernel
theorem sound2475 : certificate2475.Sound := rat_cut_bin_certificate_sound certificate2475 profilesValid2475 numericValid2475 valid2475

def retention2476 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(123320421500000000/3828576944448409413),(440357372015008373/500000000000000000),(57/20),(1327505909617939719/625000000000000000),true,MergedCutProfiles.Batch385.profile15408,![MergedCutProfiles.Batch385.profile15408,MergedCutProfiles.Batch385.profile15409,MergedCutProfiles.Batch385.profile15410,MergedCutProfiles.Batch385.profile15411,MergedCutProfiles.Batch385.profile15412,MergedCutProfiles.Batch385.profile15413,MergedCutProfiles.Batch385.profile15414,MergedCutProfiles.Batch385.profile15415,MergedCutProfiles.Batch385.profile15416,MergedCutProfiles.Batch385.profile15417,MergedCutProfiles.Batch385.profile15418,MergedCutProfiles.Batch385.profile15419,MergedCutProfiles.Batch385.profile15420,MergedCutProfiles.Batch385.profile15421,MergedCutProfiles.Batch385.profile15422,MergedCutProfiles.Batch385.profile15423]⟩
theorem profilesValid2476 : retention2476.ProfilesValid := by
  change ∀ j : Fin 16, (retention2476.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch385.valid15408
  · exact MergedCutProfiles.Batch385.valid15409
  · exact MergedCutProfiles.Batch385.valid15410
  · exact MergedCutProfiles.Batch385.valid15411
  · exact MergedCutProfiles.Batch385.valid15412
  · exact MergedCutProfiles.Batch385.valid15413
  · exact MergedCutProfiles.Batch385.valid15414
  · exact MergedCutProfiles.Batch385.valid15415
  · exact MergedCutProfiles.Batch385.valid15416
  · exact MergedCutProfiles.Batch385.valid15417
  · exact MergedCutProfiles.Batch385.valid15418
  · exact MergedCutProfiles.Batch385.valid15419
  · exact MergedCutProfiles.Batch385.valid15420
  · exact MergedCutProfiles.Batch385.valid15421
  · exact MergedCutProfiles.Batch385.valid15422
  · exact MergedCutProfiles.Batch385.valid15423
theorem numericValid2476 : retention2476.NumericValid := by decide +kernel
def certificate2476 : RatCutBinCertificate := ⟨⟨retention2476,(1102648119346584823/500000000000000000),(14887102204219317/100000000000000000),(285189018766043241/20000000000000000),(27458151097991125517/62500000000000000),(1029191587487374649/500000000000000000)⟩,(995693522260839989/1000000000000000000),(85069314758014461/250000000000000000),(292898075249146431/1000000000000000000),(32686815164323363/200000000000000000)⟩
theorem valid2476 : certificate2476.Valid := by decide +kernel
theorem sound2476 : certificate2476.Sound := rat_cut_bin_certificate_sound certificate2476 profilesValid2476 numericValid2476 valid2476

def retention2477 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(45224406345323209/1276192314816136471),(246640843/250000000),(53/20),(3390726009683178417/1600000000000000000),true,MergedCutProfiles.Batch385.profile15424,![MergedCutProfiles.Batch385.profile15424,MergedCutProfiles.Batch385.profile15425,MergedCutProfiles.Batch385.profile15426,MergedCutProfiles.Batch385.profile15427,MergedCutProfiles.Batch385.profile15428,MergedCutProfiles.Batch385.profile15429,MergedCutProfiles.Batch385.profile15430,MergedCutProfiles.Batch385.profile15431,MergedCutProfiles.Batch385.profile15432,MergedCutProfiles.Batch385.profile15418,MergedCutProfiles.Batch385.profile15433,MergedCutProfiles.Batch385.profile15434,MergedCutProfiles.Batch385.profile15407,MergedCutProfiles.Batch385.profile15435,MergedCutProfiles.Batch385.profile15436,MergedCutProfiles.Batch385.profile15437]⟩
theorem profilesValid2477 : retention2477.ProfilesValid := by
  change ∀ j : Fin 16, (retention2477.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch385.valid15424
  · exact MergedCutProfiles.Batch385.valid15425
  · exact MergedCutProfiles.Batch385.valid15426
  · exact MergedCutProfiles.Batch385.valid15427
  · exact MergedCutProfiles.Batch385.valid15428
  · exact MergedCutProfiles.Batch385.valid15429
  · exact MergedCutProfiles.Batch385.valid15430
  · exact MergedCutProfiles.Batch385.valid15431
  · exact MergedCutProfiles.Batch385.valid15432
  · exact MergedCutProfiles.Batch385.valid15418
  · exact MergedCutProfiles.Batch385.valid15433
  · exact MergedCutProfiles.Batch385.valid15434
  · exact MergedCutProfiles.Batch385.valid15407
  · exact MergedCutProfiles.Batch385.valid15435
  · exact MergedCutProfiles.Batch385.valid15436
  · exact MergedCutProfiles.Batch385.valid15437
theorem numericValid2477 : retention2477.NumericValid := by decide +kernel
def certificate2477 : RatCutBinCertificate := ⟨⟨retention2477,(1102648119346584823/500000000000000000),(14887102204219317/100000000000000000),(285189018766043241/20000000000000000),(27458151097991125517/62500000000000000),(1029091578714680451/500000000000000000)⟩,(995693522260839989/1000000000000000000),(20285991006843259/62500000000000000),(310187887712529449/1000000000000000000),(92396871797688583/500000000000000000)⟩
theorem valid2477 : certificate2477.Valid := by decide +kernel
theorem sound2477 : certificate2477.Sound := rat_cut_bin_certificate_sound certificate2477 profilesValid2477 numericValid2477 valid2477

def retention2478 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(528513601430391913/7657153888896818826),(135673219035969627/125000000000000000),(49/20),(80109773808485860971/40000000000000000000),true,MergedCutProfiles.Batch385.profile15438,![MergedCutProfiles.Batch385.profile15438,MergedCutProfiles.Batch385.profile15439,MergedCutProfiles.Batch386.profile15440,MergedCutProfiles.Batch386.profile15441,MergedCutProfiles.Batch385.profile15403,MergedCutProfiles.Batch386.profile15442,MergedCutProfiles.Batch385.profile15422,MergedCutProfiles.Batch386.profile15443,MergedCutProfiles.Batch386.profile15444,MergedCutProfiles.Batch386.profile15445,MergedCutProfiles.Batch386.profile15446,MergedCutProfiles.Batch386.profile15447,MergedCutProfiles.Batch386.profile15448,MergedCutProfiles.Batch386.profile15449,MergedCutProfiles.Batch386.profile15450,MergedCutProfiles.Batch386.profile15451]⟩
theorem profilesValid2478 : retention2478.ProfilesValid := by
  change ∀ j : Fin 16, (retention2478.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch385.valid15438
  · exact MergedCutProfiles.Batch385.valid15439
  · exact MergedCutProfiles.Batch386.valid15440
  · exact MergedCutProfiles.Batch386.valid15441
  · exact MergedCutProfiles.Batch385.valid15403
  · exact MergedCutProfiles.Batch386.valid15442
  · exact MergedCutProfiles.Batch385.valid15422
  · exact MergedCutProfiles.Batch386.valid15443
  · exact MergedCutProfiles.Batch386.valid15444
  · exact MergedCutProfiles.Batch386.valid15445
  · exact MergedCutProfiles.Batch386.valid15446
  · exact MergedCutProfiles.Batch386.valid15447
  · exact MergedCutProfiles.Batch386.valid15448
  · exact MergedCutProfiles.Batch386.valid15449
  · exact MergedCutProfiles.Batch386.valid15450
  · exact MergedCutProfiles.Batch386.valid15451
theorem numericValid2478 : retention2478.NumericValid := by decide +kernel
def certificate2478 : RatCutBinCertificate := ⟨⟨retention2478,(1102648119346584823/500000000000000000),(14887102204219317/100000000000000000),(285189018766043241/20000000000000000),(27458151097991125517/62500000000000000),(15570633583732717/8000000000000000)⟩,(995693522260839989/1000000000000000000),(330624017556445021/1000000000000000000),(75860024638404209/250000000000000000),(184669496837424977/1000000000000000000)⟩
theorem valid2478 : certificate2478.Valid := by decide +kernel
theorem sound2478 : certificate2478.Sound := rat_cut_bin_certificate_sound certificate2478 profilesValid2478 numericValid2478 valid2478

def retention2479 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(1433106984971274687/5104769259264545884),(528513601430391913/250000000000000000),(31/20),(306666388774200892752187768654620127111/211405440572156765200000000000000000000),false,MergedCutProfiles.Batch386.profile15452,(fun _ => MergedCutProfiles.Batch386.profile15452)⟩
theorem profilesValid2479 : retention2479.ProfilesValid := by
  exact MergedCutProfiles.Batch386.valid15452
theorem numericValid2479 : retention2479.NumericValid := by decide +kernel
def certificate2479 : RatCutBinCertificate := ⟨⟨retention2479,(1102648119346584823/500000000000000000),(14887102204219317/100000000000000000),(285189018766043241/20000000000000000),(27458151097991125517/62500000000000000),(282983495598599287/200000000000000000)⟩,(995693522260839989/1000000000000000000),(46321414285518239/125000000000000000),(65388962375112303/250000000000000000),(37163726746766903/200000000000000000)⟩
theorem valid2479 : certificate2479.Valid := by decide +kernel
theorem sound2479 : certificate2479.Sound := rat_cut_bin_certificate_sound certificate2479 profilesValid2479 numericValid2479 valid2479

def retention2480 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(1214175394538521959/2552384629632272942),(4299320954913824061/500000000000000000),(21/20),(3574330087402614152714800056270107075039/3439456763931059248800000000000000000000),false,MergedCutProfiles.Batch386.profile15453,(fun _ => MergedCutProfiles.Batch386.profile15453)⟩
theorem profilesValid2480 : retention2480.ProfilesValid := by
  exact MergedCutProfiles.Batch386.valid15453
theorem numericValid2480 : retention2480.NumericValid := by decide +kernel
def certificate2480 : RatCutBinCertificate := ⟨⟨retention2480,(1102648119346584823/500000000000000000),(14887102204219317/100000000000000000),(285189018766043241/20000000000000000),(27458151097991125517/62500000000000000),(1015037806983780387/1000000000000000000)⟩,(995693522260839989/1000000000000000000),(211567212795751689/500000000000000000),(212941653538676693/1000000000000000000),(11568300092007277/62500000000000000)⟩
theorem valid2480 : certificate2480.Valid := by decide +kernel
theorem sound2480 : certificate2480.Sound := rat_cut_bin_certificate_sound certificate2480 profilesValid2480 numericValid2480 valid2480

def retention2481 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(5053903137600472201/10209538518529091768),(3642526183615565877/250000000000000000),1,(3620679918312820522965956868537308387/3642526183615565877000000000000000000),false,MergedCutProfiles.Batch386.profile15454,(fun _ => MergedCutProfiles.Batch386.profile15454)⟩
theorem profilesValid2481 : retention2481.ProfilesValid := by
  exact MergedCutProfiles.Batch386.valid15454
theorem numericValid2481 : retention2481.NumericValid := by decide +kernel
def certificate2481 : RatCutBinCertificate := ⟨⟨retention2481,(1102648119346584823/500000000000000000),(14887102204219317/100000000000000000),(285189018766043241/20000000000000000),(27458151097991125517/62500000000000000),(48548912440769781/50000000000000000)⟩,(995693522260839989/1000000000000000000),(85857077674778367/200000000000000000),(207696031733710793/1000000000000000000),(94111226666969567/500000000000000000)⟩
theorem valid2481 : certificate2481.Valid := by decide +kernel
theorem sound2481 : certificate2481.Sound := rat_cut_bin_certificate_sound certificate2481 profilesValid2481 numericValid2481 valid2481

def retention2482 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(7656663253464715385/15314307777793637652),(15161709412801416603/1000000000000000000),1,(19914287196941626127605263752711592369/20215612550401888804000000000000000000),false,MergedCutProfiles.Batch386.profile15455,(fun _ => MergedCutProfiles.Batch386.profile15455)⟩
theorem profilesValid2482 : retention2482.ProfilesValid := by
  exact MergedCutProfiles.Batch386.valid15455
theorem numericValid2482 : retention2482.NumericValid := by decide +kernel
def certificate2482 : RatCutBinCertificate := ⟨⟨retention2482,(1102648119346584823/500000000000000000),(14887102204219317/100000000000000000),(285189018766043241/20000000000000000),(27458151097991125517/62500000000000000),(192414050478664261/200000000000000000)⟩,(995693522260839989/1000000000000000000),(432520236802904693/1000000000000000000),(204972746479250161/1000000000000000000),(92301596059146843/500000000000000000)⟩
theorem valid2482 : certificate2482.Valid := by decide +kernel
theorem sound2482 : certificate2482.Sound := rat_cut_bin_certificate_sound certificate2482 profilesValid2482 numericValid2482 valid2482

def retention2483 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(1/2),(1531332650692943077/100000000000000000),1,(394099725825933526678205195202339/400021590385095334400000000000000),false,MergedCutProfiles.Batch386.profile15456,(fun _ => MergedCutProfiles.Batch386.profile15456)⟩
theorem profilesValid2483 : retention2483.ProfilesValid := by
  exact MergedCutProfiles.Batch386.valid15456
theorem numericValid2483 : retention2483.NumericValid := by decide +kernel
def certificate2483 : RatCutBinCertificate := ⟨⟨retention2483,(1102648119346584823/500000000000000000),(14887102204219317/100000000000000000),(285189018766043241/20000000000000000),(27458151097991125517/62500000000000000),(481085985675420589/500000000000000000)⟩,(995693522260839989/1000000000000000000),(108073522455538441/250000000000000000),(205162341776697553/1000000000000000000),(36980368398158337/200000000000000000)⟩
theorem valid2483 : certificate2483.Valid := by decide +kernel
theorem sound2483 : certificate2483.Sound := rat_cut_bin_certificate_sound certificate2483 profilesValid2483 numericValid2483 valid2483

def certificates : List RatCutBinCertificate := [certificate2472,certificate2473,certificate2474,certificate2475,certificate2476,certificate2477,certificate2478,certificate2479,certificate2480,certificate2481,certificate2482,certificate2483]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2472,List.forall_mem_cons.mpr ⟨sound2473,List.forall_mem_cons.mpr ⟨sound2474,List.forall_mem_cons.mpr ⟨sound2475,List.forall_mem_cons.mpr ⟨sound2476,List.forall_mem_cons.mpr ⟨sound2477,List.forall_mem_cons.mpr ⟨sound2478,List.forall_mem_cons.mpr ⟨sound2479,List.forall_mem_cons.mpr ⟨sound2480,List.forall_mem_cons.mpr ⟨sound2481,List.forall_mem_cons.mpr ⟨sound2482,List.forall_mem_cons.mpr ⟨sound2483,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch206
