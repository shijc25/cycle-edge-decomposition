import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch008
import Cycle12.MergedCutProfiles.Batch009
import Cycle12.MergedCutProfiles.Batch010
import Cycle12.MergedCutProfiles.Batch310
import Cycle12.MergedCutProfiles.Batch444
import Cycle12.MergedCutProfiles.Batch445
import Cycle12.MergedCutProfiles.Batch563
import Cycle12.MergedCutProfiles.Batch564
import Cycle12.MergedCutProfiles.Batch645

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch363

def retention4356 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(628526757440289961/72471107720699531725569),(568997074186175471/1000000000000000000),4,(1564813094024738972716588039127957/711246342732719338750000000000000),true,MergedCutProfiles.Batch645.profile25810,![MergedCutProfiles.Batch645.profile25810,MergedCutProfiles.Batch645.profile25811,MergedCutProfiles.Batch645.profile25811,MergedCutProfiles.Batch563.profile22555,MergedCutProfiles.Batch563.profile22555,MergedCutProfiles.Batch563.profile22555,MergedCutProfiles.Batch563.profile22555,MergedCutProfiles.Batch563.profile22556,MergedCutProfiles.Batch563.profile22556,MergedCutProfiles.Batch563.profile22556,MergedCutProfiles.Batch563.profile22557,MergedCutProfiles.Batch563.profile22557,MergedCutProfiles.Batch563.profile22557,MergedCutProfiles.Batch563.profile22557,MergedCutProfiles.Batch563.profile22557,MergedCutProfiles.Batch444.profile17794]⟩
theorem profilesValid4356 : retention4356.ProfilesValid := by
  change ∀ j : Fin 16, (retention4356.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch645.valid25810
  · exact MergedCutProfiles.Batch645.valid25811
  · exact MergedCutProfiles.Batch645.valid25811
  · exact MergedCutProfiles.Batch563.valid22555
  · exact MergedCutProfiles.Batch563.valid22555
  · exact MergedCutProfiles.Batch563.valid22555
  · exact MergedCutProfiles.Batch563.valid22555
  · exact MergedCutProfiles.Batch563.valid22556
  · exact MergedCutProfiles.Batch563.valid22556
  · exact MergedCutProfiles.Batch563.valid22556
  · exact MergedCutProfiles.Batch563.valid22557
  · exact MergedCutProfiles.Batch563.valid22557
  · exact MergedCutProfiles.Batch563.valid22557
  · exact MergedCutProfiles.Batch563.valid22557
  · exact MergedCutProfiles.Batch563.valid22557
  · exact MergedCutProfiles.Batch444.valid17794
theorem numericValid4356 : retention4356.NumericValid := by decide +kernel
def certificate4356 : RatCutBinCertificate := ⟨⟨retention4356,(184222838560238723/100000000000000000),(3278736788116277/1000000000000000000),(7343162248714555013/1000000000000000000),(534550273825938603099079/1000000000000000000),(2196809786820206303/1000000000000000000)⟩,(999996562584594017/1000000000000000000),(11664687415311361/20000000000000000),(12788173511401747/125000000000000000),(2263192230005087/50000000000000000)⟩
theorem valid4356 : certificate4356.Valid := by decide +kernel
theorem sound4356 : certificate4356.Sound := rat_cut_bin_certificate_sound certificate4356 profilesValid4356 numericValid4356 valid4356

def retention4357 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(1281261215000000000/72471107720699531725569),(628526757440289961/1000000000000000000),4,(232344821953527004314045171716774343/100564281190446393760000000000000000),true,MergedCutProfiles.Batch645.profile25811,![MergedCutProfiles.Batch645.profile25811,MergedCutProfiles.Batch563.profile22555,MergedCutProfiles.Batch563.profile22555,MergedCutProfiles.Batch563.profile22556,MergedCutProfiles.Batch563.profile22556,MergedCutProfiles.Batch563.profile22557,MergedCutProfiles.Batch563.profile22557,MergedCutProfiles.Batch444.profile17794,MergedCutProfiles.Batch444.profile17794,MergedCutProfiles.Batch444.profile17794,MergedCutProfiles.Batch563.profile22558,MergedCutProfiles.Batch563.profile22558,MergedCutProfiles.Batch563.profile22558,MergedCutProfiles.Batch563.profile22559,MergedCutProfiles.Batch563.profile22559,MergedCutProfiles.Batch563.profile22559]⟩
theorem profilesValid4357 : retention4357.ProfilesValid := by
  change ∀ j : Fin 16, (retention4357.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch645.valid25811
  · exact MergedCutProfiles.Batch563.valid22555
  · exact MergedCutProfiles.Batch563.valid22555
  · exact MergedCutProfiles.Batch563.valid22556
  · exact MergedCutProfiles.Batch563.valid22556
  · exact MergedCutProfiles.Batch563.valid22557
  · exact MergedCutProfiles.Batch563.valid22557
  · exact MergedCutProfiles.Batch444.valid17794
  · exact MergedCutProfiles.Batch444.valid17794
  · exact MergedCutProfiles.Batch444.valid17794
  · exact MergedCutProfiles.Batch563.valid22558
  · exact MergedCutProfiles.Batch563.valid22558
  · exact MergedCutProfiles.Batch563.valid22558
  · exact MergedCutProfiles.Batch563.valid22559
  · exact MergedCutProfiles.Batch563.valid22559
  · exact MergedCutProfiles.Batch563.valid22559
theorem numericValid4357 : retention4357.NumericValid := by decide +kernel
def certificate4357 : RatCutBinCertificate := ⟨⟨retention4357,(184222838560238723/100000000000000000),(3278736788116277/1000000000000000000),(7343162248714555013/1000000000000000000),(534550273825938603099079/1000000000000000000),(2307120770012272163/1000000000000000000)⟩,(999996562584594017/1000000000000000000),(259635790055622073/500000000000000000),(5617402208976159/40000000000000000),(32942360688320827/500000000000000000)⟩
theorem valid4357 : certificate4357.Valid := by decide +kernel
theorem sound4357 : certificate4357.Sound := rat_cut_bin_certificate_sound certificate4357 profilesValid4357 numericValid4357 valid4357

def retention4358 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(1472962796477515174/24157035906899843908523),(256252243/200000000),(5/2),(12157289655563722311909455237836870711/5125044860000000000000000000000000000),true,MergedCutProfiles.Batch563.profile22555,![MergedCutProfiles.Batch563.profile22555,MergedCutProfiles.Batch563.profile22557,MergedCutProfiles.Batch444.profile17794,MergedCutProfiles.Batch563.profile22558,MergedCutProfiles.Batch563.profile22559,MergedCutProfiles.Batch444.profile17795,MergedCutProfiles.Batch310.profile12413,MergedCutProfiles.Batch444.profile17796,MergedCutProfiles.Batch444.profile17796,MergedCutProfiles.Batch564.profile22560,MergedCutProfiles.Batch444.profile17797,MergedCutProfiles.Batch444.profile17797,MergedCutProfiles.Batch008.profile356,MergedCutProfiles.Batch008.profile356,MergedCutProfiles.Batch310.profile12420,MergedCutProfiles.Batch310.profile12420]⟩
theorem profilesValid4358 : retention4358.ProfilesValid := by
  change ∀ j : Fin 16, (retention4358.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch563.valid22555
  · exact MergedCutProfiles.Batch563.valid22557
  · exact MergedCutProfiles.Batch444.valid17794
  · exact MergedCutProfiles.Batch563.valid22558
  · exact MergedCutProfiles.Batch563.valid22559
  · exact MergedCutProfiles.Batch444.valid17795
  · exact MergedCutProfiles.Batch310.valid12413
  · exact MergedCutProfiles.Batch444.valid17796
  · exact MergedCutProfiles.Batch444.valid17796
  · exact MergedCutProfiles.Batch564.valid22560
  · exact MergedCutProfiles.Batch444.valid17797
  · exact MergedCutProfiles.Batch444.valid17797
  · exact MergedCutProfiles.Batch008.valid356
  · exact MergedCutProfiles.Batch008.valid356
  · exact MergedCutProfiles.Batch310.valid12420
  · exact MergedCutProfiles.Batch310.valid12420
theorem numericValid4358 : retention4358.NumericValid := by decide +kernel
def certificate4358 : RatCutBinCertificate := ⟨⟨retention4358,(184222838560238723/100000000000000000),(3278736788116277/1000000000000000000),(7343162248714555013/1000000000000000000),(534550273825938603099079/1000000000000000000),(296259614837129293/125000000000000000)⟩,(999996562584594017/1000000000000000000),(167236963343163511/500000000000000000),(59840492581124671/200000000000000000),(218872718584333641/1000000000000000000)⟩
theorem valid4358 : certificate4358.Valid := by decide +kernel
theorem sound4358 : certificate4358.Sound := rat_cut_bin_certificate_sound certificate4358 profilesValid4358 numericValid4358 valid4358

def retention4359 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(64000000000000000000/72471107720699531725569),(2209444194716272761/500000000000000000),(5/4),(32442494776394307535281378295799095531/14140442846184145670400000000000000000),true,MergedCutProfiles.Batch310.profile12420,![MergedCutProfiles.Batch310.profile12420,MergedCutProfiles.Batch009.profile372,MergedCutProfiles.Batch310.profile12421,MergedCutProfiles.Batch009.profile373,MergedCutProfiles.Batch310.profile12422,MergedCutProfiles.Batch009.profile374,MergedCutProfiles.Batch310.profile12423,MergedCutProfiles.Batch009.profile375,MergedCutProfiles.Batch445.profile17804,MergedCutProfiles.Batch009.profile376,MergedCutProfiles.Batch310.profile12424,MergedCutProfiles.Batch009.profile377,MergedCutProfiles.Batch645.profile25812,MergedCutProfiles.Batch645.profile25813,MergedCutProfiles.Batch564.profile22561,MergedCutProfiles.Batch009.profile378]⟩
theorem profilesValid4359 : retention4359.ProfilesValid := by
  change ∀ j : Fin 16, (retention4359.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch310.valid12420
  · exact MergedCutProfiles.Batch009.valid372
  · exact MergedCutProfiles.Batch310.valid12421
  · exact MergedCutProfiles.Batch009.valid373
  · exact MergedCutProfiles.Batch310.valid12422
  · exact MergedCutProfiles.Batch009.valid374
  · exact MergedCutProfiles.Batch310.valid12423
  · exact MergedCutProfiles.Batch009.valid375
  · exact MergedCutProfiles.Batch445.valid17804
  · exact MergedCutProfiles.Batch009.valid376
  · exact MergedCutProfiles.Batch310.valid12424
  · exact MergedCutProfiles.Batch009.valid377
  · exact MergedCutProfiles.Batch645.valid25812
  · exact MergedCutProfiles.Batch645.valid25813
  · exact MergedCutProfiles.Batch564.valid22561
  · exact MergedCutProfiles.Batch009.valid378
theorem numericValid4359 : retention4359.NumericValid := by decide +kernel
def certificate4359 : RatCutBinCertificate := ⟨⟨retention4359,(184222838560238723/100000000000000000),(3278736788116277/1000000000000000000),(7343162248714555013/1000000000000000000),(534550273825938603099079/1000000000000000000),(2293277229631074341/1000000000000000000)⟩,(999996562584594017/1000000000000000000),(224841347116793261/1000000000000000000),(27465880460763597/62500000000000000),(605212658753439631/1000000000000000000)⟩
theorem valid4359 : certificate4359.Valid := by decide +kernel
theorem sound4359 : certificate4359.Sound := rat_cut_bin_certificate_sound certificate4359 profilesValid4359 numericValid4359 valid4359

def retention4360 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(1/2),64,1,(249383750761872694322254949188936071/250000000000000000000000000000000000),false,MergedCutProfiles.Batch010.profile416,(fun _ => MergedCutProfiles.Batch010.profile416)⟩
theorem profilesValid4360 : retention4360.ProfilesValid := by
  exact MergedCutProfiles.Batch010.valid416
theorem numericValid4360 : retention4360.NumericValid := by decide +kernel
def certificate4360 : RatCutBinCertificate := ⟨⟨retention4360,(184222838560238723/100000000000000000),(3278736788116277/1000000000000000000),(7343162248714555013/1000000000000000000),(534550273825938603099079/1000000000000000000),(124589055543651279/125000000000000000)⟩,(999996562584594017/1000000000000000000),(411632772994745877/1000000000000000000),(222991298459684667/1000000000000000000),(109424577772553051/500000000000000000)⟩
theorem valid4360 : certificate4360.Valid := by decide +kernel
theorem sound4360 : certificate4360.Sound := rat_cut_bin_certificate_sound certificate4360 profilesValid4360 numericValid4360 valid4360

def retention4361 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(64000000000000000000/72471107720699531725569),(1964451296601608453/125000000000000000),1,(144199248614514299634928881267061363279/62862441491251470496000000000000000000),false,MergedCutProfiles.Batch645.profile25814,(fun _ => MergedCutProfiles.Batch645.profile25814)⟩
theorem profilesValid4361 : retention4361.ProfilesValid := by
  exact MergedCutProfiles.Batch645.valid25814
theorem numericValid4361 : retention4361.NumericValid := by decide +kernel
def certificate4361 : RatCutBinCertificate := ⟨⟨retention4361,(177900575360238723/100000000000000000),(3278736788116277/1000000000000000000),(7343162248714555013/1000000000000000000),(534550273825938603099079/1000000000000000000),(2293091259149581981/1000000000000000000)⟩,(999996680551754229/1000000000000000000),(6177953604578769/200000000000000000),(841673894479044109/1000000000000000000),(1684273282636177591/1000000000000000000)⟩
theorem valid4361 : certificate4361.Valid := by decide +kernel
theorem sound4361 : certificate4361.Sound := rat_cut_bin_certificate_sound certificate4361 profilesValid4361 numericValid4361 valid4361

def retention4362 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(1/2),64,1,(249383750761872694322254949188936071/250000000000000000000000000000000000),false,MergedCutProfiles.Batch010.profile416,(fun _ => MergedCutProfiles.Batch010.profile416)⟩
theorem profilesValid4362 : retention4362.ProfilesValid := by
  exact MergedCutProfiles.Batch010.valid416
theorem numericValid4362 : retention4362.NumericValid := by decide +kernel
def certificate4362 : RatCutBinCertificate := ⟨⟨retention4362,(177900575360238723/100000000000000000),(3278736788116277/1000000000000000000),(7343162248714555013/1000000000000000000),(534550273825938603099079/1000000000000000000),(498370336691102153/500000000000000000)⟩,(999996680551754229/1000000000000000000),(71064680053740431/1000000000000000000),(367071086336625351/500000000000000000),(720525398248029429/1000000000000000000)⟩
theorem valid4362 : certificate4362.Valid := by decide +kernel
theorem sound4362 : certificate4362.Sound := rat_cut_bin_certificate_sound certificate4362 profilesValid4362 numericValid4362 valid4362

def retention4363 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(685701169627522939/72471107720699531725569),(27156481965446453/40000000000000000),4,(1609917444797781535598407812863863179/678912049136161325000000000000000000),false,MergedCutProfiles.Batch645.profile25815,(fun _ => MergedCutProfiles.Batch645.profile25815)⟩
theorem profilesValid4363 : retention4363.ProfilesValid := by
  exact MergedCutProfiles.Batch645.valid25815
theorem numericValid4363 : retention4363.NumericValid := by decide +kernel
def certificate4363 : RatCutBinCertificate := ⟨⟨retention4363,(175022849860238723/100000000000000000),(3278736788116277/1000000000000000000),(7343162248714555013/1000000000000000000),(534550273825938603099079/1000000000000000000),(2368193671857862043/1000000000000000000)⟩,(499998367123628799/500000000000000000),(739829242218943291/1000000000000000000),(37233667079873439/1000000000000000000),(9049179747385497/500000000000000000)⟩
theorem valid4363 : certificate4363.Valid := by decide +kernel
theorem sound4363 : certificate4363.Sound := rat_cut_bin_certificate_sound certificate4363 profilesValid4363 numericValid4363 valid4363

def retention4364 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(1544249259679559539/24157035906899843908523),(685701169627522939/1000000000000000000),4,(325253096679586095131136378336808007/137140233925504587800000000000000000),false,MergedCutProfiles.Batch645.profile25816,(fun _ => MergedCutProfiles.Batch645.profile25816)⟩
theorem profilesValid4364 : retention4364.ProfilesValid := by
  exact MergedCutProfiles.Batch645.valid25816
theorem numericValid4364 : retention4364.NumericValid := by decide +kernel
def certificate4364 : RatCutBinCertificate := ⟨⟨retention4364,(175022849860238723/100000000000000000),(3278736788116277/1000000000000000000),(7343162248714555013/1000000000000000000),(534550273825938603099079/1000000000000000000),(1184278302844288801/500000000000000000)⟩,(499998367123628799/500000000000000000),(737321901138747413/1000000000000000000),(1519738899689953/40000000000000000),(740112010970103/40000000000000000)⟩
theorem valid4364 : certificate4364.Valid := by decide +kernel
theorem sound4364 : certificate4364.Sound := rat_cut_bin_certificate_sound certificate4364 profilesValid4364 numericValid4364 valid4364

def retention4365 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(1/40),(4632747779038678617/1000000000000000000),(7/5),(41830631271108663410054622489072293811/19303115745994494237500000000000000000),false,MergedCutProfiles.Batch645.profile25817,(fun _ => MergedCutProfiles.Batch645.profile25817)⟩
theorem profilesValid4365 : retention4365.ProfilesValid := by
  exact MergedCutProfiles.Batch645.valid25817
theorem numericValid4365 : retention4365.NumericValid := by decide +kernel
def certificate4365 : RatCutBinCertificate := ⟨⟨retention4365,(175022849860238723/100000000000000000),(3278736788116277/1000000000000000000),(7343162248714555013/1000000000000000000),(534550273825938603099079/1000000000000000000),(541486576669725943/250000000000000000)⟩,(499998367123628799/500000000000000000),(583250057215213969/1000000000000000000),(51148465350298243/500000000000000000),(63891383387475897/500000000000000000)⟩
theorem valid4365 : certificate4365.Valid := by decide +kernel
theorem sound4365 : certificate4365.Sound := rat_cut_bin_certificate_sound certificate4365 profilesValid4365 numericValid4365 valid4365

def retention4366 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(789013691369288826/58438407163718057272441),(573852896848046577/1000000000000000000),4,(84590082160635121310168003739051693/38256859789869771800000000000000000),true,MergedCutProfiles.Batch645.profile25818,![MergedCutProfiles.Batch645.profile25818,MergedCutProfiles.Batch645.profile25819,MergedCutProfiles.Batch645.profile25820,MergedCutProfiles.Batch645.profile25820,MergedCutProfiles.Batch645.profile25821,MergedCutProfiles.Batch645.profile25821,MergedCutProfiles.Batch645.profile25821,MergedCutProfiles.Batch645.profile25822,MergedCutProfiles.Batch645.profile25822,MergedCutProfiles.Batch645.profile25822,MergedCutProfiles.Batch645.profile25823,MergedCutProfiles.Batch645.profile25823,MergedCutProfiles.Batch645.profile25823,MergedCutProfiles.Batch445.profile17817,MergedCutProfiles.Batch445.profile17817,MergedCutProfiles.Batch445.profile17817]⟩
theorem profilesValid4366 : retention4366.ProfilesValid := by
  change ∀ j : Fin 16, (retention4366.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch645.valid25818
  · exact MergedCutProfiles.Batch645.valid25819
  · exact MergedCutProfiles.Batch645.valid25820
  · exact MergedCutProfiles.Batch645.valid25820
  · exact MergedCutProfiles.Batch645.valid25821
  · exact MergedCutProfiles.Batch645.valid25821
  · exact MergedCutProfiles.Batch645.valid25821
  · exact MergedCutProfiles.Batch645.valid25822
  · exact MergedCutProfiles.Batch645.valid25822
  · exact MergedCutProfiles.Batch645.valid25822
  · exact MergedCutProfiles.Batch645.valid25823
  · exact MergedCutProfiles.Batch645.valid25823
  · exact MergedCutProfiles.Batch645.valid25823
  · exact MergedCutProfiles.Batch445.valid17817
  · exact MergedCutProfiles.Batch445.valid17817
  · exact MergedCutProfiles.Batch445.valid17817
theorem numericValid4366 : retention4366.NumericValid := by decide +kernel
def certificate4366 : RatCutBinCertificate := ⟨⟨retention4366,(920098431516911947/500000000000000000),(4061079806220747/1000000000000000000),(7433116774958187683/1000000000000000000),(218167913631906075246811/500000000000000000),(2207087310951715617/1000000000000000000)⟩,(999995796441060671/1000000000000000000),(115175679041863787/200000000000000000),(13289758118512003/125000000000000000),(1182359493191423/25000000000000000)⟩
theorem valid4366 : certificate4366.Valid := by decide +kernel
theorem sound4366 : certificate4366.Sound := rat_cut_bin_certificate_sound certificate4366 profilesValid4366 numericValid4366 valid4366

def retention4367 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(1295794958000000000/58438407163718057272441),(394506845684644413/500000000000000000),(73/20),(1529870453965125871733/640000000000000000000),true,MergedCutProfiles.Batch645.profile25819,![MergedCutProfiles.Batch645.profile25819,MergedCutProfiles.Batch645.profile25820,MergedCutProfiles.Batch645.profile25821,MergedCutProfiles.Batch645.profile25821,MergedCutProfiles.Batch645.profile25822,MergedCutProfiles.Batch645.profile25822,MergedCutProfiles.Batch645.profile25823,MergedCutProfiles.Batch645.profile25823,MergedCutProfiles.Batch445.profile17817,MergedCutProfiles.Batch445.profile17817,MergedCutProfiles.Batch445.profile17817,MergedCutProfiles.Batch645.profile25824,MergedCutProfiles.Batch645.profile25824,MergedCutProfiles.Batch645.profile25825,MergedCutProfiles.Batch645.profile25825,MergedCutProfiles.Batch645.profile25825]⟩
theorem profilesValid4367 : retention4367.ProfilesValid := by
  change ∀ j : Fin 16, (retention4367.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch645.valid25819
  · exact MergedCutProfiles.Batch645.valid25820
  · exact MergedCutProfiles.Batch645.valid25821
  · exact MergedCutProfiles.Batch645.valid25821
  · exact MergedCutProfiles.Batch645.valid25822
  · exact MergedCutProfiles.Batch645.valid25822
  · exact MergedCutProfiles.Batch645.valid25823
  · exact MergedCutProfiles.Batch645.valid25823
  · exact MergedCutProfiles.Batch445.valid17817
  · exact MergedCutProfiles.Batch445.valid17817
  · exact MergedCutProfiles.Batch445.valid17817
  · exact MergedCutProfiles.Batch645.valid25824
  · exact MergedCutProfiles.Batch645.valid25824
  · exact MergedCutProfiles.Batch645.valid25825
  · exact MergedCutProfiles.Batch645.valid25825
  · exact MergedCutProfiles.Batch645.valid25825
theorem numericValid4367 : retention4367.NumericValid := by decide +kernel
def certificate4367 : RatCutBinCertificate := ⟨⟨retention4367,(920098431516911947/500000000000000000),(4061079806220747/1000000000000000000),(7433116774958187683/1000000000000000000),(218167913631906075246811/500000000000000000),(2386752908331047939/1000000000000000000)⟩,(999995796441060671/1000000000000000000),(433323953611065563/1000000000000000000),(102149944522169993/500000000000000000),(108871813236251909/1000000000000000000)⟩
theorem valid4367 : certificate4367.Valid := by decide +kernel
theorem sound4367 : certificate4367.Sound := rat_cut_bin_certificate_sound certificate4367 profilesValid4367 numericValid4367 valid4367

def certificates : List RatCutBinCertificate := [certificate4356,certificate4357,certificate4358,certificate4359,certificate4360,certificate4361,certificate4362,certificate4363,certificate4364,certificate4365,certificate4366,certificate4367]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4356,List.forall_mem_cons.mpr ⟨sound4357,List.forall_mem_cons.mpr ⟨sound4358,List.forall_mem_cons.mpr ⟨sound4359,List.forall_mem_cons.mpr ⟨sound4360,List.forall_mem_cons.mpr ⟨sound4361,List.forall_mem_cons.mpr ⟨sound4362,List.forall_mem_cons.mpr ⟨sound4363,List.forall_mem_cons.mpr ⟨sound4364,List.forall_mem_cons.mpr ⟨sound4365,List.forall_mem_cons.mpr ⟨sound4366,List.forall_mem_cons.mpr ⟨sound4367,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch363
