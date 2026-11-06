import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch373
import Cycle12.MergedCutProfiles.Batch374
import Cycle12.MergedCutProfiles.Batch375
import Cycle12.MergedCutProfiles.Batch376
import Cycle12.MergedCutProfiles.Batch377
import Cycle12.MergedCutProfiles.Batch378
import Cycle12.MergedCutProfiles.Batch610
import Cycle12.MergedCutProfiles.Batch611
import Cycle12.MergedCutProfiles.Batch612

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch338

def retention4056 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(1182178771719029793/381551060284943935990),(219406449/200000000),(14/5),(37715940335506393461/16000000000000000000),true,MergedCutProfiles.Batch610.profile24432,![MergedCutProfiles.Batch610.profile24432,MergedCutProfiles.Batch610.profile24433,MergedCutProfiles.Batch610.profile24434,MergedCutProfiles.Batch610.profile24435,MergedCutProfiles.Batch610.profile24411,MergedCutProfiles.Batch610.profile24413,MergedCutProfiles.Batch373.profile14921,MergedCutProfiles.Batch373.profile14937,MergedCutProfiles.Batch610.profile24436,MergedCutProfiles.Batch610.profile24437,MergedCutProfiles.Batch610.profile24438,MergedCutProfiles.Batch610.profile24428,MergedCutProfiles.Batch610.profile24429,MergedCutProfiles.Batch610.profile24430,MergedCutProfiles.Batch610.profile24439,MergedCutProfiles.Batch611.profile24440]⟩
theorem profilesValid4056 : retention4056.ProfilesValid := by
  change ∀ j : Fin 16, (retention4056.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch610.valid24432
  · exact MergedCutProfiles.Batch610.valid24433
  · exact MergedCutProfiles.Batch610.valid24434
  · exact MergedCutProfiles.Batch610.valid24435
  · exact MergedCutProfiles.Batch610.valid24411
  · exact MergedCutProfiles.Batch610.valid24413
  · exact MergedCutProfiles.Batch373.valid14921
  · exact MergedCutProfiles.Batch373.valid14937
  · exact MergedCutProfiles.Batch610.valid24436
  · exact MergedCutProfiles.Batch610.valid24437
  · exact MergedCutProfiles.Batch610.valid24438
  · exact MergedCutProfiles.Batch610.valid24428
  · exact MergedCutProfiles.Batch610.valid24429
  · exact MergedCutProfiles.Batch610.valid24430
  · exact MergedCutProfiles.Batch610.valid24439
  · exact MergedCutProfiles.Batch611.valid24440
theorem numericValid4056 : retention4056.NumericValid := by decide +kernel
def certificate4056 : RatCutBinCertificate := ⟨⟨retention4056,(485887555299514563/250000000000000000),(59865971199444307/500000000000000000),(3275756374603509871/250000000000000000),(5028094937505649710709/1000000000000000000),(2307518887622841443/1000000000000000000)⟩,(199931532780840767/200000000000000000),(448301132508772391/1000000000000000000),(192031011489198543/1000000000000000000),(15591050881188287/125000000000000000)⟩
theorem valid4056 : certificate4056.Valid := by decide +kernel
theorem sound4056 : certificate4056.Sound := rat_cut_bin_certificate_sound certificate4056 profilesValid4056 numericValid4056 valid4056

def retention4057 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(6044890758826945061/381551060284943935990),(1182178771719029793/1000000000000000000),(53/20),(721833534262757124343/320000000000000000000),true,MergedCutProfiles.Batch611.profile24441,![MergedCutProfiles.Batch611.profile24441,MergedCutProfiles.Batch610.profile24426,MergedCutProfiles.Batch611.profile24442,MergedCutProfiles.Batch611.profile24443,MergedCutProfiles.Batch373.profile14954,MergedCutProfiles.Batch611.profile24444,MergedCutProfiles.Batch611.profile24445,MergedCutProfiles.Batch611.profile24446,MergedCutProfiles.Batch611.profile24447,MergedCutProfiles.Batch373.profile14957,MergedCutProfiles.Batch611.profile24448,MergedCutProfiles.Batch611.profile24449,MergedCutProfiles.Batch611.profile24450,MergedCutProfiles.Batch611.profile24451,MergedCutProfiles.Batch374.profile14960,MergedCutProfiles.Batch611.profile24452]⟩
theorem profilesValid4057 : retention4057.ProfilesValid := by
  change ∀ j : Fin 16, (retention4057.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch611.valid24441
  · exact MergedCutProfiles.Batch610.valid24426
  · exact MergedCutProfiles.Batch611.valid24442
  · exact MergedCutProfiles.Batch611.valid24443
  · exact MergedCutProfiles.Batch373.valid14954
  · exact MergedCutProfiles.Batch611.valid24444
  · exact MergedCutProfiles.Batch611.valid24445
  · exact MergedCutProfiles.Batch611.valid24446
  · exact MergedCutProfiles.Batch611.valid24447
  · exact MergedCutProfiles.Batch373.valid14957
  · exact MergedCutProfiles.Batch611.valid24448
  · exact MergedCutProfiles.Batch611.valid24449
  · exact MergedCutProfiles.Batch611.valid24450
  · exact MergedCutProfiles.Batch611.valid24451
  · exact MergedCutProfiles.Batch374.valid14960
  · exact MergedCutProfiles.Batch611.valid24452
theorem numericValid4057 : retention4057.NumericValid := by decide +kernel
def certificate4057 : RatCutBinCertificate := ⟨⟨retention4057,(485887555299514563/250000000000000000),(59865971199444307/500000000000000000),(3275756374603509871/250000000000000000),(5028094937505649710709/1000000000000000000),(2208666385303624017/1000000000000000000)⟩,(199931532780840767/200000000000000000),(451495415119049073/1000000000000000000),(94739826292847011/500000000000000000),(62343987097027979/500000000000000000)⟩
theorem valid4057 : certificate4057.Valid := by decide +kernel
theorem sound4057 : certificate4057.Sound := rat_cut_bin_certificate_sound certificate4057 profilesValid4057 numericValid4057 valid4057

def retention4058 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(6400000000000000000/38155106028494393599),(6044890758826945061/1000000000000000000),(23/20),(16451548660138071523319512663299596014111/9671825214123112097600000000000000000000),false,MergedCutProfiles.Batch611.profile24453,(fun _ => MergedCutProfiles.Batch611.profile24453)⟩
theorem profilesValid4058 : retention4058.ProfilesValid := by
  exact MergedCutProfiles.Batch611.valid24453
theorem numericValid4058 : retention4058.NumericValid := by decide +kernel
def certificate4058 : RatCutBinCertificate := ⟨⟨retention4058,(485887555299514563/250000000000000000),(59865971199444307/500000000000000000),(3275756374603509871/250000000000000000),(5028094937505649710709/1000000000000000000),(1680552971789315717/1000000000000000000)⟩,(199931532780840767/200000000000000000),(363583057707776989/1000000000000000000),(134279372824766391/500000000000000000),(162084012924584091/500000000000000000)⟩
theorem valid4058 : certificate4058.Valid := by decide +kernel
theorem sound4058 : certificate4058.Sound := rat_cut_bin_certificate_sound certificate4058 profilesValid4058 numericValid4058 valid4058

def retention4059 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(1/2),64,1,(15962085016107493154417226112293942951/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch375.profile15016,(fun _ => MergedCutProfiles.Batch375.profile15016)⟩
theorem profilesValid4059 : retention4059.ProfilesValid := by
  exact MergedCutProfiles.Batch375.valid15016
theorem numericValid4059 : retention4059.NumericValid := by decide +kernel
def certificate4059 : RatCutBinCertificate := ⟨⟨retention4059,(485887555299514563/250000000000000000),(59865971199444307/500000000000000000),(3275756374603509871/250000000000000000),(5028094937505649710709/1000000000000000000),(195974132961987673/200000000000000000)⟩,(199931532780840767/200000000000000000),(268404321203222051/500000000000000000),(64617695480158759/500000000000000000),(12468125337536737/100000000000000000)⟩
theorem valid4059 : certificate4059.Valid := by decide +kernel
theorem sound4059 : certificate4059.Sound := rat_cut_bin_certificate_sound certificate4059 profilesValid4059 numericValid4059 valid4059

def retention4060 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(6400000000000000000/38155106028494393599),(12553391283835167719/500000000000000000),1,(133314639235428253519537099140309747/78458695523969798243750000000000000),false,MergedCutProfiles.Batch611.profile24453,(fun _ => MergedCutProfiles.Batch611.profile24453)⟩
theorem profilesValid4060 : retention4060.ProfilesValid := by
  exact MergedCutProfiles.Batch611.valid24453
theorem numericValid4060 : retention4060.NumericValid := by decide +kernel
def certificate4060 : RatCutBinCertificate := ⟨⟨retention4060,(465649350799514563/250000000000000000),(59865971199444307/500000000000000000),(3275756374603509871/250000000000000000),(5028094937505649710709/1000000000000000000),(841074890490991811/500000000000000000)⟩,(499835961751413967/500000000000000000),(825961922415613/25000000000000000),(835468840228443029/1000000000000000000),(164586599669334167/125000000000000000)⟩
theorem valid4060 : certificate4060.Valid := by decide +kernel
theorem sound4060 : certificate4060.Sound := rat_cut_bin_certificate_sound certificate4060 profilesValid4060 numericValid4060 valid4060

def retention4061 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(1/2),64,1,(15962085016107493154417226112293942951/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch375.profile15016,(fun _ => MergedCutProfiles.Batch375.profile15016)⟩
theorem profilesValid4061 : retention4061.ProfilesValid := by
  exact MergedCutProfiles.Batch375.valid15016
theorem numericValid4061 : retention4061.NumericValid := by decide +kernel
def certificate4061 : RatCutBinCertificate := ⟨⟨retention4061,(465649350799514563/250000000000000000),(59865971199444307/500000000000000000),(3275756374603509871/250000000000000000),(5028094937505649710709/1000000000000000000),(49030519514198869/50000000000000000)⟩,(499835961751413967/500000000000000000),(14168641089847357/250000000000000000),(770699564937796697/1000000000000000000),(29764170879423907/40000000000000000)⟩
theorem valid4061 : certificate4061.Valid := by decide +kernel
theorem sound4061 : certificate4061.Sound := rat_cut_bin_certificate_sound certificate4061 profilesValid4061 numericValid4061 valid4061

def retention4062 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(130417437065274691/72926787324172208592),(645630876560765797/1000000000000000000),4,(149445167271439811437/64000000000000000000),true,MergedCutProfiles.Batch611.profile24454,![MergedCutProfiles.Batch611.profile24454,MergedCutProfiles.Batch611.profile24455,MergedCutProfiles.Batch611.profile24456,MergedCutProfiles.Batch611.profile24457,MergedCutProfiles.Batch611.profile24458,MergedCutProfiles.Batch611.profile24459,MergedCutProfiles.Batch611.profile24460,MergedCutProfiles.Batch611.profile24461,MergedCutProfiles.Batch611.profile24462,MergedCutProfiles.Batch611.profile24463,MergedCutProfiles.Batch611.profile24464,MergedCutProfiles.Batch611.profile24465,MergedCutProfiles.Batch611.profile24466,MergedCutProfiles.Batch611.profile24467,MergedCutProfiles.Batch611.profile24468,MergedCutProfiles.Batch611.profile24469]⟩
theorem profilesValid4062 : retention4062.ProfilesValid := by
  change ∀ j : Fin 16, (retention4062.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch611.valid24454
  · exact MergedCutProfiles.Batch611.valid24455
  · exact MergedCutProfiles.Batch611.valid24456
  · exact MergedCutProfiles.Batch611.valid24457
  · exact MergedCutProfiles.Batch611.valid24458
  · exact MergedCutProfiles.Batch611.valid24459
  · exact MergedCutProfiles.Batch611.valid24460
  · exact MergedCutProfiles.Batch611.valid24461
  · exact MergedCutProfiles.Batch611.valid24462
  · exact MergedCutProfiles.Batch611.valid24463
  · exact MergedCutProfiles.Batch611.valid24464
  · exact MergedCutProfiles.Batch611.valid24465
  · exact MergedCutProfiles.Batch611.valid24466
  · exact MergedCutProfiles.Batch611.valid24467
  · exact MergedCutProfiles.Batch611.valid24468
  · exact MergedCutProfiles.Batch611.valid24469
theorem numericValid4062 : retention4062.NumericValid := by decide +kernel
def certificate4062 : RatCutBinCertificate := ⟨⟨retention4062,(1952474893493732891/1000000000000000000),(31307344283847009/250000000000000000),(6661371946043031087/500000000000000000),(4885916049529217336309/1000000000000000000),(282708692802358193/125000000000000000)⟩,(999648216704368521/1000000000000000000),(611838432314111759/1000000000000000000),(87573280358826691/1000000000000000000),(40604475451094897/1000000000000000000)⟩
theorem valid4062 : certificate4062.Valid := by decide +kernel
theorem sound4062 : certificate4062.Sound := rat_cut_bin_certificate_sound certificate4062 profilesValid4062 numericValid4062 valid4062

def retention4063 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(13859285937500000/4557924207760763037),(130417437065274691/200000000000000000),4,(596494826750576884679/256000000000000000000),true,MergedCutProfiles.Batch611.profile24470,![MergedCutProfiles.Batch611.profile24470,MergedCutProfiles.Batch611.profile24471,MergedCutProfiles.Batch611.profile24458,MergedCutProfiles.Batch611.profile24472,MergedCutProfiles.Batch611.profile24473,MergedCutProfiles.Batch611.profile24474,MergedCutProfiles.Batch611.profile24475,MergedCutProfiles.Batch611.profile24476,MergedCutProfiles.Batch376.profile15051,MergedCutProfiles.Batch611.profile24477,MergedCutProfiles.Batch611.profile24478,MergedCutProfiles.Batch377.profile15080,MergedCutProfiles.Batch611.profile24479,MergedCutProfiles.Batch612.profile24480,MergedCutProfiles.Batch612.profile24481,MergedCutProfiles.Batch612.profile24482]⟩
theorem profilesValid4063 : retention4063.ProfilesValid := by
  change ∀ j : Fin 16, (retention4063.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch611.valid24470
  · exact MergedCutProfiles.Batch611.valid24471
  · exact MergedCutProfiles.Batch611.valid24458
  · exact MergedCutProfiles.Batch611.valid24472
  · exact MergedCutProfiles.Batch611.valid24473
  · exact MergedCutProfiles.Batch611.valid24474
  · exact MergedCutProfiles.Batch611.valid24475
  · exact MergedCutProfiles.Batch611.valid24476
  · exact MergedCutProfiles.Batch376.valid15051
  · exact MergedCutProfiles.Batch611.valid24477
  · exact MergedCutProfiles.Batch611.valid24478
  · exact MergedCutProfiles.Batch377.valid15080
  · exact MergedCutProfiles.Batch611.valid24479
  · exact MergedCutProfiles.Batch612.valid24480
  · exact MergedCutProfiles.Batch612.valid24481
  · exact MergedCutProfiles.Batch612.valid24482
theorem numericValid4063 : retention4063.NumericValid := by decide +kernel
def certificate4063 : RatCutBinCertificate := ⟨⟨retention4063,(1952474893493732891/1000000000000000000),(31307344283847009/250000000000000000),(6661371946043031087/500000000000000000),(4885916049529217336309/1000000000000000000),(1128323364005333849/500000000000000000)⟩,(999648216704368521/1000000000000000000),(152346752412707861/250000000000000000),(22195637505363101/250000000000000000),(20581615668376439/500000000000000000)⟩
theorem valid4063 : certificate4063.Valid := by decide +kernel
theorem sound4063 : certificate4063.Sound := rat_cut_bin_certificate_sound certificate4063 profilesValid4063 numericValid4063 valid4063

def retention4064 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(10689542041571713/2209902646187036624),(8869943/8000000),(14/5),(9376907292436009641/4000000000000000000),true,MergedCutProfiles.Batch612.profile24483,![MergedCutProfiles.Batch612.profile24483,MergedCutProfiles.Batch612.profile24484,MergedCutProfiles.Batch611.profile24461,MergedCutProfiles.Batch611.profile24464,MergedCutProfiles.Batch611.profile24476,MergedCutProfiles.Batch612.profile24485,MergedCutProfiles.Batch612.profile24486,MergedCutProfiles.Batch612.profile24487,MergedCutProfiles.Batch612.profile24488,MergedCutProfiles.Batch612.profile24482,MergedCutProfiles.Batch612.profile24489,MergedCutProfiles.Batch612.profile24490,MergedCutProfiles.Batch612.profile24491,MergedCutProfiles.Batch612.profile24492,MergedCutProfiles.Batch612.profile24493,MergedCutProfiles.Batch375.profile15038]⟩
theorem profilesValid4064 : retention4064.ProfilesValid := by
  change ∀ j : Fin 16, (retention4064.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch612.valid24483
  · exact MergedCutProfiles.Batch612.valid24484
  · exact MergedCutProfiles.Batch611.valid24461
  · exact MergedCutProfiles.Batch611.valid24464
  · exact MergedCutProfiles.Batch611.valid24476
  · exact MergedCutProfiles.Batch612.valid24485
  · exact MergedCutProfiles.Batch612.valid24486
  · exact MergedCutProfiles.Batch612.valid24487
  · exact MergedCutProfiles.Batch612.valid24488
  · exact MergedCutProfiles.Batch612.valid24482
  · exact MergedCutProfiles.Batch612.valid24489
  · exact MergedCutProfiles.Batch612.valid24490
  · exact MergedCutProfiles.Batch612.valid24491
  · exact MergedCutProfiles.Batch612.valid24492
  · exact MergedCutProfiles.Batch612.valid24493
  · exact MergedCutProfiles.Batch375.valid15038
theorem numericValid4064 : retention4064.NumericValid := by decide +kernel
def certificate4064 : RatCutBinCertificate := ⟨⟨retention4064,(1952474893493732891/1000000000000000000),(31307344283847009/250000000000000000),(6661371946043031087/500000000000000000),(4885916049529217336309/1000000000000000000),(229283907151754041/100000000000000000)⟩,(999648216704368521/1000000000000000000),(111297911194216469/250000000000000000),(97268250157695287/500000000000000000),(31499962620426017/250000000000000000)⟩
theorem valid4064 : certificate4064.Valid := by decide +kernel
theorem sound4064 : certificate4064.Sound := rat_cut_bin_certificate_sound certificate4064 profilesValid4064 numericValid4064 valid4064

def retention4065 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(12238322572785149897/91158484155215260740),(352754887371866529/200000000000000000),2,(12833585972836134338373005720937798239/7055097747437330580000000000000000000),false,MergedCutProfiles.Batch612.profile24494,(fun _ => MergedCutProfiles.Batch612.profile24494)⟩
theorem profilesValid4065 : retention4065.ProfilesValid := by
  exact MergedCutProfiles.Batch612.valid24494
theorem numericValid4065 : retention4065.NumericValid := by decide +kernel
def certificate4065 : RatCutBinCertificate := ⟨⟨retention4065,(1952474893493732891/1000000000000000000),(31307344283847009/250000000000000000),(6661371946043031087/500000000000000000),(4885916049529217336309/1000000000000000000),(222793246972740499/125000000000000000)⟩,(999648216704368521/1000000000000000000),(467248513888814487/1000000000000000000),(88612365878600949/500000000000000000),(31508467353228159/250000000000000000)⟩
theorem valid4065 : certificate4065.Valid := by decide +kernel
theorem sound4065 : certificate4065.Sound := rat_cut_bin_certificate_sound certificate4065 profilesValid4065 numericValid4065 valid4065

def retention4066 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(800000000000000000/4557924207760763037),(12238322572785149897/250000000000000000),1,(66364006344727485548518084567133741763/39162632232912479670400000000000000000),false,MergedCutProfiles.Batch612.profile24495,(fun _ => MergedCutProfiles.Batch612.profile24495)⟩
theorem profilesValid4066 : retention4066.ProfilesValid := by
  exact MergedCutProfiles.Batch612.valid24495
theorem numericValid4066 : retention4066.NumericValid := by decide +kernel
def certificate4066 : RatCutBinCertificate := ⟨⟨retention4066,(1952474893493732891/1000000000000000000),(31307344283847009/250000000000000000),(6661371946043031087/500000000000000000),(4885916049529217336309/1000000000000000000),(209527761028712943/125000000000000000)⟩,(999648216704368521/1000000000000000000),(156936002959007773/500000000000000000),(12896267972907123/40000000000000000),(13058671213128693/25000000000000000)⟩
theorem valid4066 : certificate4066.Valid := by decide +kernel
theorem sound4066 : certificate4066.Sound := rat_cut_bin_certificate_sound certificate4066 profilesValid4066 numericValid4066 valid4066

def retention4067 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(1/2),64,1,(63848635416822846544693585750381821951/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch378.profile15126,(fun _ => MergedCutProfiles.Batch378.profile15126)⟩
theorem profilesValid4067 : retention4067.ProfilesValid := by
  exact MergedCutProfiles.Batch378.valid15126
theorem numericValid4067 : retention4067.NumericValid := by decide +kernel
def certificate4067 : RatCutBinCertificate := ⟨⟨retention4067,(1952474893493732891/1000000000000000000),(31307344283847009/250000000000000000),(6661371946043031087/500000000000000000),(4885916049529217336309/1000000000000000000),(979282304132273863/1000000000000000000)⟩,(999648216704368521/1000000000000000000),(106899569457666953/200000000000000000),(65338973797592627/500000000000000000),(125997210806241771/1000000000000000000)⟩
theorem valid4067 : certificate4067.Valid := by decide +kernel
theorem sound4067 : certificate4067.Sound := rat_cut_bin_certificate_sound certificate4067 profilesValid4067 numericValid4067 valid4067

def certificates : List RatCutBinCertificate := [certificate4056,certificate4057,certificate4058,certificate4059,certificate4060,certificate4061,certificate4062,certificate4063,certificate4064,certificate4065,certificate4066,certificate4067]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4056,List.forall_mem_cons.mpr ⟨sound4057,List.forall_mem_cons.mpr ⟨sound4058,List.forall_mem_cons.mpr ⟨sound4059,List.forall_mem_cons.mpr ⟨sound4060,List.forall_mem_cons.mpr ⟨sound4061,List.forall_mem_cons.mpr ⟨sound4062,List.forall_mem_cons.mpr ⟨sound4063,List.forall_mem_cons.mpr ⟨sound4064,List.forall_mem_cons.mpr ⟨sound4065,List.forall_mem_cons.mpr ⟨sound4066,List.forall_mem_cons.mpr ⟨sound4067,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch338
