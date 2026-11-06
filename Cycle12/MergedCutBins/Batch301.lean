import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch434
import Cycle12.MergedCutProfiles.Batch435
import Cycle12.MergedCutProfiles.Batch436
import Cycle12.MergedCutProfiles.Batch555
import Cycle12.MergedCutProfiles.Batch556
import Cycle12.MergedCutProfiles.Batch557

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch301

def retention3612 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(22378163716858186537/48800942647576952518),(2109938636003019641/250000000000000000),1,(7091709772108855204064475314542959203/6751803635209662851200000000000000000),false,MergedCutProfiles.Batch555.profile22204,(fun _ => MergedCutProfiles.Batch555.profile22204)⟩
theorem profilesValid3612 : retention3612.ProfilesValid := by
  exact MergedCutProfiles.Batch555.valid22204
theorem numericValid3612 : retention3612.NumericValid := by decide +kernel
def certificate3612 : RatCutBinCertificate := ⟨⟨retention3612,(585977416613854579/250000000000000000),(233579791654726571/1000000000000000000),(17766695161368751747/1000000000000000000),(217451032822346997693/250000000000000000),(509763256669968553/500000000000000000)⟩,(99792189240401269/100000000000000000),(11674863099450347/100000000000000000),(315132998980604551/500000000000000000),(71504839078785667/125000000000000000)⟩
theorem valid3612 : certificate3612.Valid := by decide +kernel
theorem sound3612 : certificate3612.Sound := rat_cut_bin_certificate_sound certificate3612 profilesValid3612 numericValid3612 valid3612

def retention3613 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(24232344640442888135/48800942647576952518),(22378163716858186537/1000000000000000000),1,(1394702024703517929909694096067742709/1398635232303636658562500000000000000),false,MergedCutProfiles.Batch555.profile22205,(fun _ => MergedCutProfiles.Batch555.profile22205)⟩
theorem profilesValid3613 : retention3613.ProfilesValid := by
  exact MergedCutProfiles.Batch555.valid22205
theorem numericValid3613 : retention3613.NumericValid := by decide +kernel
def certificate3613 : RatCutBinCertificate := ⟨⟨retention3613,(585977416613854579/250000000000000000),(233579791654726571/1000000000000000000),(17766695161368751747/1000000000000000000),(217451032822346997693/250000000000000000),(120796491980675749/125000000000000000)⟩,(99792189240401269/100000000000000000),(61585151782635391/500000000000000000),(616969840477454811/1000000000000000000),(570318649526138389/1000000000000000000)⟩
theorem valid3613 : certificate3613.Valid := by decide +kernel
theorem sound3613 : certificate3613.Sound := rat_cut_bin_certificate_sound certificate3613 profilesValid3613 numericValid3613 valid3613

def retention3614 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(1/2),(4846468928088577627/200000000000000000),1,(24021408143716347546465850600676174001/24232344640442888135000000000000000000),false,MergedCutProfiles.Batch434.profile17377,(fun _ => MergedCutProfiles.Batch434.profile17377)⟩
theorem profilesValid3614 : retention3614.ProfilesValid := by
  exact MergedCutProfiles.Batch434.valid17377
theorem numericValid3614 : retention3614.NumericValid := by decide +kernel
def certificate3614 : RatCutBinCertificate := ⟨⟨retention3614,(585977416613854579/250000000000000000),(233579791654726571/1000000000000000000),(17766695161368751747/1000000000000000000),(217451032822346997693/250000000000000000),(120059923720406139/125000000000000000)⟩,(99792189240401269/100000000000000000),(3872686063192641/31250000000000000),(615424401482949469/1000000000000000000),(567353067200591921/1000000000000000000)⟩
theorem valid3614 : certificate3614.Valid := by decide +kernel
theorem sound3614 : certificate3614.Sound := rat_cut_bin_certificate_sound certificate3614 profilesValid3614 numericValid3614 valid3614

def retention3615 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(962286977314442554/47921503563055897243),(952759383479646093/1000000000000000000),(11/4),(563849502085787661777/256000000000000000000),true,MergedCutProfiles.Batch555.profile22206,![MergedCutProfiles.Batch555.profile22206,MergedCutProfiles.Batch555.profile22207,MergedCutProfiles.Batch555.profile22208,MergedCutProfiles.Batch555.profile22209,MergedCutProfiles.Batch555.profile22210,MergedCutProfiles.Batch555.profile22211,MergedCutProfiles.Batch555.profile22212,MergedCutProfiles.Batch555.profile22213,MergedCutProfiles.Batch555.profile22214,MergedCutProfiles.Batch555.profile22215,MergedCutProfiles.Batch555.profile22216,MergedCutProfiles.Batch555.profile22217,MergedCutProfiles.Batch555.profile22218,MergedCutProfiles.Batch555.profile22219,MergedCutProfiles.Batch555.profile22220,MergedCutProfiles.Batch555.profile22221]⟩
theorem profilesValid3615 : retention3615.ProfilesValid := by
  change ∀ j : Fin 16, (retention3615.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch555.valid22206
  · exact MergedCutProfiles.Batch555.valid22207
  · exact MergedCutProfiles.Batch555.valid22208
  · exact MergedCutProfiles.Batch555.valid22209
  · exact MergedCutProfiles.Batch555.valid22210
  · exact MergedCutProfiles.Batch555.valid22211
  · exact MergedCutProfiles.Batch555.valid22212
  · exact MergedCutProfiles.Batch555.valid22213
  · exact MergedCutProfiles.Batch555.valid22214
  · exact MergedCutProfiles.Batch555.valid22215
  · exact MergedCutProfiles.Batch555.valid22216
  · exact MergedCutProfiles.Batch555.valid22217
  · exact MergedCutProfiles.Batch555.valid22218
  · exact MergedCutProfiles.Batch555.valid22219
  · exact MergedCutProfiles.Batch555.valid22220
  · exact MergedCutProfiles.Batch555.valid22221
theorem numericValid3615 : retention3615.NumericValid := by decide +kernel
def certificate3615 : RatCutBinCertificate := ⟨⟨retention3615,(2295491748774205273/1000000000000000000),(11895173549139047/50000000000000000),(8970110022628371949/500000000000000000),(431240624310649139377/500000000000000000),(264852189281084943/125000000000000000)⟩,(498979445306957719/500000000000000000),(274526542880009013/1000000000000000000),(92636472829453919/250000000000000000),(220077149298795667/1000000000000000000)⟩
theorem valid3615 : certificate3615.Valid := by decide +kernel
theorem sound3615 : certificate3615.Sound := rat_cut_bin_certificate_sound certificate3615 profilesValid3615 numericValid3615 valid3615

def retention3616 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(1104321179000000000/47921503563055897243),(481143488657221277/500000000000000000),(27/10),(87306489635067609003/40000000000000000000),true,MergedCutProfiles.Batch555.profile22222,![MergedCutProfiles.Batch555.profile22222,MergedCutProfiles.Batch555.profile22223,MergedCutProfiles.Batch555.profile22224,MergedCutProfiles.Batch435.profile17429,MergedCutProfiles.Batch555.profile22225,MergedCutProfiles.Batch555.profile22226,MergedCutProfiles.Batch555.profile22213,MergedCutProfiles.Batch435.profile17430,MergedCutProfiles.Batch555.profile22227,MergedCutProfiles.Batch555.profile22228,MergedCutProfiles.Batch434.profile17385,MergedCutProfiles.Batch435.profile17431,MergedCutProfiles.Batch555.profile22220,MergedCutProfiles.Batch555.profile22221,MergedCutProfiles.Batch555.profile22229,MergedCutProfiles.Batch435.profile17432]⟩
theorem profilesValid3616 : retention3616.ProfilesValid := by
  change ∀ j : Fin 16, (retention3616.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch555.valid22222
  · exact MergedCutProfiles.Batch555.valid22223
  · exact MergedCutProfiles.Batch555.valid22224
  · exact MergedCutProfiles.Batch435.valid17429
  · exact MergedCutProfiles.Batch555.valid22225
  · exact MergedCutProfiles.Batch555.valid22226
  · exact MergedCutProfiles.Batch555.valid22213
  · exact MergedCutProfiles.Batch435.valid17430
  · exact MergedCutProfiles.Batch555.valid22227
  · exact MergedCutProfiles.Batch555.valid22228
  · exact MergedCutProfiles.Batch434.valid17385
  · exact MergedCutProfiles.Batch435.valid17431
  · exact MergedCutProfiles.Batch555.valid22220
  · exact MergedCutProfiles.Batch555.valid22221
  · exact MergedCutProfiles.Batch555.valid22229
  · exact MergedCutProfiles.Batch435.valid17432
theorem numericValid3616 : retention3616.NumericValid := by decide +kernel
def certificate3616 : RatCutBinCertificate := ⟨⟨retention3616,(2295491748774205273/1000000000000000000),(11895173549139047/50000000000000000),(8970110022628371949/500000000000000000),(431240624310649139377/500000000000000000),(2100464739230004033/1000000000000000000)⟩,(498979445306957719/500000000000000000),(68938155174585893/250000000000000000),(368965085463877929/1000000000000000000),(220350756737770713/1000000000000000000)⟩
theorem valid3616 : certificate3616.Valid := by decide +kernel
theorem sound3616 : certificate3616.Sound := rat_cut_bin_certificate_sound certificate3616 profilesValid3616 numericValid3616 valid3616

def retention3617 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(159597900974128837/6845929080436556749),(1104321179/1000000000),(12/5),(34685722226388269977/16000000000000000000),true,MergedCutProfiles.Batch555.profile22230,![MergedCutProfiles.Batch555.profile22230,MergedCutProfiles.Batch555.profile22231,MergedCutProfiles.Batch555.profile22232,MergedCutProfiles.Batch555.profile22233,MergedCutProfiles.Batch555.profile22234,MergedCutProfiles.Batch555.profile22212,MergedCutProfiles.Batch555.profile22235,MergedCutProfiles.Batch555.profile22236,MergedCutProfiles.Batch555.profile22237,MergedCutProfiles.Batch555.profile22238,MergedCutProfiles.Batch435.profile17401,MergedCutProfiles.Batch435.profile17417,MergedCutProfiles.Batch555.profile22239,MergedCutProfiles.Batch556.profile22240,MergedCutProfiles.Batch556.profile22241,MergedCutProfiles.Batch556.profile22242]⟩
theorem profilesValid3617 : retention3617.ProfilesValid := by
  change ∀ j : Fin 16, (retention3617.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch555.valid22230
  · exact MergedCutProfiles.Batch555.valid22231
  · exact MergedCutProfiles.Batch555.valid22232
  · exact MergedCutProfiles.Batch555.valid22233
  · exact MergedCutProfiles.Batch555.valid22234
  · exact MergedCutProfiles.Batch555.valid22212
  · exact MergedCutProfiles.Batch555.valid22235
  · exact MergedCutProfiles.Batch555.valid22236
  · exact MergedCutProfiles.Batch555.valid22237
  · exact MergedCutProfiles.Batch555.valid22238
  · exact MergedCutProfiles.Batch435.valid17401
  · exact MergedCutProfiles.Batch435.valid17417
  · exact MergedCutProfiles.Batch555.valid22239
  · exact MergedCutProfiles.Batch556.valid22240
  · exact MergedCutProfiles.Batch556.valid22241
  · exact MergedCutProfiles.Batch556.valid22242
theorem numericValid3617 : retention3617.NumericValid := by decide +kernel
def certificate3617 : RatCutBinCertificate := ⟨⟨retention3617,(2295491748774205273/1000000000000000000),(11895173549139047/50000000000000000),(8970110022628371949/500000000000000000),(431240624310649139377/500000000000000000),(2094793345988294299/1000000000000000000)⟩,(498979445306957719/500000000000000000),(261376842786678839/1000000000000000000),(387846372667057577/1000000000000000000),(25403544962339947/100000000000000000)⟩
theorem valid3617 : certificate3617.Valid := by decide +kernel
theorem sound3617 : certificate3617.Sound := rat_cut_bin_certificate_sound certificate3617 profilesValid3617 numericValid3617 valid3617

def retention3618 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(1297017458612251801/47921503563055897243),(1117185306818901859/1000000000000000000),(12/5),(172716047617004699967/80000000000000000000),true,MergedCutProfiles.Batch556.profile22243,![MergedCutProfiles.Batch556.profile22243,MergedCutProfiles.Batch556.profile22244,MergedCutProfiles.Batch555.profile22209,MergedCutProfiles.Batch556.profile22245,MergedCutProfiles.Batch556.profile22246,MergedCutProfiles.Batch555.profile22235,MergedCutProfiles.Batch556.profile22247,MergedCutProfiles.Batch556.profile22248,MergedCutProfiles.Batch556.profile22249,MergedCutProfiles.Batch556.profile22250,MergedCutProfiles.Batch556.profile22251,MergedCutProfiles.Batch556.profile22252,MergedCutProfiles.Batch556.profile22253,MergedCutProfiles.Batch556.profile22254,MergedCutProfiles.Batch434.profile17388,MergedCutProfiles.Batch556.profile22255]⟩
theorem profilesValid3618 : retention3618.ProfilesValid := by
  change ∀ j : Fin 16, (retention3618.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch556.valid22243
  · exact MergedCutProfiles.Batch556.valid22244
  · exact MergedCutProfiles.Batch555.valid22209
  · exact MergedCutProfiles.Batch556.valid22245
  · exact MergedCutProfiles.Batch556.valid22246
  · exact MergedCutProfiles.Batch555.valid22235
  · exact MergedCutProfiles.Batch556.valid22247
  · exact MergedCutProfiles.Batch556.valid22248
  · exact MergedCutProfiles.Batch556.valid22249
  · exact MergedCutProfiles.Batch556.valid22250
  · exact MergedCutProfiles.Batch556.valid22251
  · exact MergedCutProfiles.Batch556.valid22252
  · exact MergedCutProfiles.Batch556.valid22253
  · exact MergedCutProfiles.Batch556.valid22254
  · exact MergedCutProfiles.Batch434.valid17388
  · exact MergedCutProfiles.Batch556.valid22255
theorem numericValid3618 : retention3618.NumericValid := by decide +kernel
def certificate3618 : RatCutBinCertificate := ⟨⟨retention3618,(2295491748774205273/1000000000000000000),(11895173549139047/50000000000000000),(8970110022628371949/500000000000000000),(431240624310649139377/500000000000000000),(2085886389602280687/1000000000000000000)⟩,(498979445306957719/500000000000000000),(261308173105062043/1000000000000000000),(48492301227253229/125000000000000000),(254005187018016447/1000000000000000000)⟩
theorem valid3618 : certificate3618.Valid := by decide +kernel
theorem sound3618 : certificate3618.Sound := rat_cut_bin_certificate_sound certificate3618 profilesValid3618 numericValid3618 valid3618

def retention3619 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(3798867888065799728/47921503563055897243),(1297017458612251801/1000000000000000000),(43/20),(633412658678078541531/320000000000000000000),true,MergedCutProfiles.Batch556.profile22256,![MergedCutProfiles.Batch556.profile22256,MergedCutProfiles.Batch556.profile22257,MergedCutProfiles.Batch556.profile22258,MergedCutProfiles.Batch556.profile22259,MergedCutProfiles.Batch556.profile22260,MergedCutProfiles.Batch556.profile22261,MergedCutProfiles.Batch556.profile22262,MergedCutProfiles.Batch556.profile22263,MergedCutProfiles.Batch556.profile22264,MergedCutProfiles.Batch556.profile22265,MergedCutProfiles.Batch556.profile22266,MergedCutProfiles.Batch556.profile22267,MergedCutProfiles.Batch556.profile22268,MergedCutProfiles.Batch556.profile22269,MergedCutProfiles.Batch556.profile22270,MergedCutProfiles.Batch556.profile22271]⟩
theorem profilesValid3619 : retention3619.ProfilesValid := by
  change ∀ j : Fin 16, (retention3619.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch556.valid22256
  · exact MergedCutProfiles.Batch556.valid22257
  · exact MergedCutProfiles.Batch556.valid22258
  · exact MergedCutProfiles.Batch556.valid22259
  · exact MergedCutProfiles.Batch556.valid22260
  · exact MergedCutProfiles.Batch556.valid22261
  · exact MergedCutProfiles.Batch556.valid22262
  · exact MergedCutProfiles.Batch556.valid22263
  · exact MergedCutProfiles.Batch556.valid22264
  · exact MergedCutProfiles.Batch556.valid22265
  · exact MergedCutProfiles.Batch556.valid22266
  · exact MergedCutProfiles.Batch556.valid22267
  · exact MergedCutProfiles.Batch556.valid22268
  · exact MergedCutProfiles.Batch556.valid22269
  · exact MergedCutProfiles.Batch556.valid22270
  · exact MergedCutProfiles.Batch556.valid22271
theorem numericValid3619 : retention3619.NumericValid := by decide +kernel
def certificate3619 : RatCutBinCertificate := ⟨⟨retention3619,(2295491748774205273/1000000000000000000),(11895173549139047/50000000000000000),(8970110022628371949/500000000000000000),(431240624310649139377/500000000000000000),(1913961466683234873/1000000000000000000)⟩,(498979445306957719/500000000000000000),(269412170189612289/1000000000000000000),(377198798359235061/1000000000000000000),(63478382529925913/250000000000000000)⟩
theorem valid3619 : certificate3619.Valid := by decide +kernel
theorem sound3619 : certificate3619.Sound := rat_cut_bin_certificate_sound certificate3619 profilesValid3619 numericValid3619 valid3619

def retention3620 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(2562656875222757418/6845929080436556749),(237429243004112483/62500000000000000),(23/20),(98417013768067685761/80000000000000000000),true,MergedCutProfiles.Batch556.profile22272,![MergedCutProfiles.Batch556.profile22272,MergedCutProfiles.Batch556.profile22273,MergedCutProfiles.Batch556.profile22274,MergedCutProfiles.Batch556.profile22275,MergedCutProfiles.Batch436.profile17451,MergedCutProfiles.Batch556.profile22276,MergedCutProfiles.Batch556.profile22277,MergedCutProfiles.Batch556.profile22278,MergedCutProfiles.Batch556.profile22279,MergedCutProfiles.Batch436.profile17458,MergedCutProfiles.Batch436.profile17469,MergedCutProfiles.Batch557.profile22280,MergedCutProfiles.Batch557.profile22281,MergedCutProfiles.Batch557.profile22282,MergedCutProfiles.Batch557.profile22283,MergedCutProfiles.Batch557.profile22284]⟩
theorem profilesValid3620 : retention3620.ProfilesValid := by
  change ∀ j : Fin 16, (retention3620.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch556.valid22272
  · exact MergedCutProfiles.Batch556.valid22273
  · exact MergedCutProfiles.Batch556.valid22274
  · exact MergedCutProfiles.Batch556.valid22275
  · exact MergedCutProfiles.Batch436.valid17451
  · exact MergedCutProfiles.Batch556.valid22276
  · exact MergedCutProfiles.Batch556.valid22277
  · exact MergedCutProfiles.Batch556.valid22278
  · exact MergedCutProfiles.Batch556.valid22279
  · exact MergedCutProfiles.Batch436.valid17458
  · exact MergedCutProfiles.Batch436.valid17469
  · exact MergedCutProfiles.Batch557.valid22280
  · exact MergedCutProfiles.Batch557.valid22281
  · exact MergedCutProfiles.Batch557.valid22282
  · exact MergedCutProfiles.Batch557.valid22283
  · exact MergedCutProfiles.Batch557.valid22284
theorem numericValid3620 : retention3620.NumericValid := by decide +kernel
def certificate3620 : RatCutBinCertificate := ⟨⟨retention3620,(2295491748774205273/1000000000000000000),(11895173549139047/50000000000000000),(8970110022628371949/500000000000000000),(431240624310649139377/500000000000000000),(29880103282257821/25000000000000000)⟩,(498979445306957719/500000000000000000),(330737923101610847/1000000000000000000),(30331408202625861/100000000000000000),(254067374271934109/1000000000000000000)⟩
theorem valid3620 : certificate3620.Valid := by decide +kernel
theorem sound3620 : certificate3620.Sound := rat_cut_bin_certificate_sound certificate3620 profilesValid3620 numericValid3620 valid3620

def retention3621 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(23467433330139297621/47921503563055897243),(8969299063279650963/500000000000000000),1,(14461955842679078344385197273630464883/14350878501247441540800000000000000000),false,MergedCutProfiles.Batch557.profile22285,(fun _ => MergedCutProfiles.Batch557.profile22285)⟩
theorem profilesValid3621 : retention3621.ProfilesValid := by
  exact MergedCutProfiles.Batch557.valid22285
theorem numericValid3621 : retention3621.NumericValid := by decide +kernel
def certificate3621 : RatCutBinCertificate := ⟨⟨retention3621,(2295491748774205273/1000000000000000000),(11895173549139047/50000000000000000),(8970110022628371949/500000000000000000),(431240624310649139377/500000000000000000),(977299351942538789/1000000000000000000)⟩,(498979445306957719/500000000000000000),(354161602656817123/1000000000000000000),(278212793906703279/1000000000000000000),(257303623863919889/1000000000000000000)⟩
theorem valid3621 : certificate3621.Valid := by decide +kernel
theorem sound3621 : certificate3621.Sound := rat_cut_bin_certificate_sound certificate3621 profilesValid3621 numericValid3621 valid3621

def retention3622 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(23939128740075097504/47921503563055897243),(23467433330139297621/1000000000000000000),1,(193967326475292128418919900370076867/195561944417827480175000000000000000),false,MergedCutProfiles.Batch557.profile22286,(fun _ => MergedCutProfiles.Batch557.profile22286)⟩
theorem profilesValid3622 : retention3622.ProfilesValid := by
  exact MergedCutProfiles.Batch557.valid22286
theorem numericValid3622 : retention3622.NumericValid := by decide +kernel
def certificate3622 : RatCutBinCertificate := ⟨⟨retention3622,(2295491748774205273/1000000000000000000),(11895173549139047/50000000000000000),(8970110022628371949/500000000000000000),(431240624310649139377/500000000000000000),(480702662438836663/500000000000000000)⟩,(498979445306957719/500000000000000000),(89194725330237003/250000000000000000),(275506051691131677/1000000000000000000),(15869657315021837/62500000000000000)⟩
theorem valid3622 : certificate3622.Valid := by decide +kernel
theorem sound3622 : certificate3622.Sound := rat_cut_bin_certificate_sound certificate3622 profilesValid3622 numericValid3622 valid3622

def retention3623 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(1/2),(748097773127346797/31250000000000000),1,(3796446616222771536851493038468278687/3830260598412015600640000000000000000),false,MergedCutProfiles.Batch436.profile17478,(fun _ => MergedCutProfiles.Batch436.profile17478)⟩
theorem profilesValid3623 : retention3623.ProfilesValid := by
  exact MergedCutProfiles.Batch436.valid17478
theorem numericValid3623 : retention3623.NumericValid := by decide +kernel
def certificate3623 : RatCutBinCertificate := ⟨⟨retention3623,(2295491748774205273/1000000000000000000),(11895173549139047/50000000000000000),(8970110022628371949/500000000000000000),(431240624310649139377/500000000000000000),(960731246530625431/1000000000000000000)⟩,(498979445306957719/500000000000000000),(356822093430967183/1000000000000000000),(55092308948848421/200000000000000000),(126949767914965093/500000000000000000)⟩
theorem valid3623 : certificate3623.Valid := by decide +kernel
theorem sound3623 : certificate3623.Sound := rat_cut_bin_certificate_sound certificate3623 profilesValid3623 numericValid3623 valid3623

def certificates : List RatCutBinCertificate := [certificate3612,certificate3613,certificate3614,certificate3615,certificate3616,certificate3617,certificate3618,certificate3619,certificate3620,certificate3621,certificate3622,certificate3623]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3612,List.forall_mem_cons.mpr ⟨sound3613,List.forall_mem_cons.mpr ⟨sound3614,List.forall_mem_cons.mpr ⟨sound3615,List.forall_mem_cons.mpr ⟨sound3616,List.forall_mem_cons.mpr ⟨sound3617,List.forall_mem_cons.mpr ⟨sound3618,List.forall_mem_cons.mpr ⟨sound3619,List.forall_mem_cons.mpr ⟨sound3620,List.forall_mem_cons.mpr ⟨sound3621,List.forall_mem_cons.mpr ⟨sound3622,List.forall_mem_cons.mpr ⟨sound3623,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch301
