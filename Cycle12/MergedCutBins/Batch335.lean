import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch364
import Cycle12.MergedCutProfiles.Batch365
import Cycle12.MergedCutProfiles.Batch366
import Cycle12.MergedCutProfiles.Batch367
import Cycle12.MergedCutProfiles.Batch481
import Cycle12.MergedCutProfiles.Batch482
import Cycle12.MergedCutProfiles.Batch483
import Cycle12.MergedCutProfiles.Batch606
import Cycle12.MergedCutProfiles.Batch607
import Cycle12.MergedCutProfiles.Batch608

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch335

def retention4020 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(12800000000000000000/96902946267737970119),(12310945329504740971/500000000000000000),1,(2200691677614838857576447352065371877/1231094532950474097100000000000000000),false,MergedCutProfiles.Batch606.profile24276,(fun _ => MergedCutProfiles.Batch606.profile24276)⟩
theorem profilesValid4020 : retention4020.ProfilesValid := by
  exact MergedCutProfiles.Batch606.valid24276
theorem numericValid4020 : retention4020.NumericValid := by decide +kernel
def certificate4020 : RatCutBinCertificate := ⟨⟨retention4020,(1844598573734127217/1000000000000000000),(11819389720817643/125000000000000000),(12083395261939574679/1000000000000000000),(1177409762622282378903/200000000000000000),(35463102626197243/20000000000000000)⟩,(99971484784480177/100000000000000000),(32430766127617957/1000000000000000000),(209304536622640257/250000000000000000),(1384386728250669943/1000000000000000000)⟩
theorem valid4020 : certificate4020.Valid := by decide +kernel
theorem sound4020 : certificate4020.Sound := rat_cut_bin_certificate_sound certificate4020 profilesValid4020 numericValid4020 valid4020

def retention4021 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(1/2),64,1,(249402263071399035807503415845231079/250000000000000000000000000000000000),false,MergedCutProfiles.Batch364.profile14563,(fun _ => MergedCutProfiles.Batch364.profile14563)⟩
theorem profilesValid4021 : retention4021.ProfilesValid := by
  exact MergedCutProfiles.Batch364.valid14563
theorem numericValid4021 : retention4021.NumericValid := by decide +kernel
def certificate4021 : RatCutBinCertificate := ⟨⟨retention4021,(1844598573734127217/1000000000000000000),(11819389720817643/125000000000000000),(12083395261939574679/1000000000000000000),(1177409762622282378903/200000000000000000),(122896834446985183/125000000000000000)⟩,(99971484784480177/100000000000000000),(4679109891663/80000000000000),(153195373622493099/200000000000000000),(741481443920733409/1000000000000000000)⟩
theorem valid4021 : certificate4021.Valid := by decide +kernel
theorem sound4021 : certificate4021.Sound := rat_cut_bin_certificate_sound certificate4021 profilesValid4021 numericValid4021 valid4021

def retention4022 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(634128533231041744/461104646765771894257),(121877011262149901/200000000000000000),4,(5563368339632469534854073363017456799/2437540225242998020000000000000000000),true,MergedCutProfiles.Batch606.profile24277,![MergedCutProfiles.Batch606.profile24277,MergedCutProfiles.Batch606.profile24278,MergedCutProfiles.Batch606.profile24279,MergedCutProfiles.Batch607.profile24280,MergedCutProfiles.Batch607.profile24281,MergedCutProfiles.Batch607.profile24282,MergedCutProfiles.Batch481.profile19271,MergedCutProfiles.Batch607.profile24283,MergedCutProfiles.Batch607.profile24284,MergedCutProfiles.Batch607.profile24285,MergedCutProfiles.Batch607.profile24286,MergedCutProfiles.Batch607.profile24287,MergedCutProfiles.Batch607.profile24288,MergedCutProfiles.Batch481.profile19243,MergedCutProfiles.Batch364.profile14583,MergedCutProfiles.Batch607.profile24289]⟩
theorem profilesValid4022 : retention4022.ProfilesValid := by
  change ∀ j : Fin 16, (retention4022.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch606.valid24277
  · exact MergedCutProfiles.Batch606.valid24278
  · exact MergedCutProfiles.Batch606.valid24279
  · exact MergedCutProfiles.Batch607.valid24280
  · exact MergedCutProfiles.Batch607.valid24281
  · exact MergedCutProfiles.Batch607.valid24282
  · exact MergedCutProfiles.Batch481.valid19271
  · exact MergedCutProfiles.Batch607.valid24283
  · exact MergedCutProfiles.Batch607.valid24284
  · exact MergedCutProfiles.Batch607.valid24285
  · exact MergedCutProfiles.Batch607.valid24286
  · exact MergedCutProfiles.Batch607.valid24287
  · exact MergedCutProfiles.Batch607.valid24288
  · exact MergedCutProfiles.Batch481.valid19243
  · exact MergedCutProfiles.Batch364.valid14583
  · exact MergedCutProfiles.Batch607.valid24289
theorem numericValid4022 : retention4022.NumericValid := by decide +kernel
def certificate4022 : RatCutBinCertificate := ⟨⟨retention4022,(1909556891102006859/1000000000000000000),(19858540071699249/200000000000000000),(1534670280267979769/125000000000000000),(569274093020212457171/100000000000000000),(2220595541713936777/1000000000000000000)⟩,(999696270488175699/1000000000000000000),(673200025955339599/1000000000000000000),(30203060760622381/500000000000000000),(13651823304101449/500000000000000000)⟩
theorem valid4022 : certificate4022.Valid := by decide +kernel
theorem sound4022 : certificate4022.Sound := rat_cut_bin_certificate_sound certificate4022 profilesValid4022 numericValid4022 valid4022

def retention4023 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(1127867185000000000/461104646765771894257),(39633033326940109/62500000000000000),4,(18470012210700366703/8000000000000000000),true,MergedCutProfiles.Batch607.profile24290,![MergedCutProfiles.Batch607.profile24290,MergedCutProfiles.Batch607.profile24291,MergedCutProfiles.Batch607.profile24292,MergedCutProfiles.Batch481.profile19271,MergedCutProfiles.Batch607.profile24284,MergedCutProfiles.Batch607.profile24286,MergedCutProfiles.Batch481.profile19258,MergedCutProfiles.Batch481.profile19243,MergedCutProfiles.Batch607.profile24289,MergedCutProfiles.Batch607.profile24293,MergedCutProfiles.Batch365.profile14612,MergedCutProfiles.Batch607.profile24294,MergedCutProfiles.Batch607.profile24295,MergedCutProfiles.Batch481.profile19260,MergedCutProfiles.Batch607.profile24296,MergedCutProfiles.Batch481.profile19246]⟩
theorem profilesValid4023 : retention4023.ProfilesValid := by
  change ∀ j : Fin 16, (retention4023.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch607.valid24290
  · exact MergedCutProfiles.Batch607.valid24291
  · exact MergedCutProfiles.Batch607.valid24292
  · exact MergedCutProfiles.Batch481.valid19271
  · exact MergedCutProfiles.Batch607.valid24284
  · exact MergedCutProfiles.Batch607.valid24286
  · exact MergedCutProfiles.Batch481.valid19258
  · exact MergedCutProfiles.Batch481.valid19243
  · exact MergedCutProfiles.Batch607.valid24289
  · exact MergedCutProfiles.Batch607.valid24293
  · exact MergedCutProfiles.Batch365.valid14612
  · exact MergedCutProfiles.Batch607.valid24294
  · exact MergedCutProfiles.Batch607.valid24295
  · exact MergedCutProfiles.Batch481.valid19260
  · exact MergedCutProfiles.Batch607.valid24296
  · exact MergedCutProfiles.Batch481.valid19246
theorem numericValid4023 : retention4023.NumericValid := by decide +kernel
def certificate4023 : RatCutBinCertificate := ⟨⟨retention4023,(1909556891102006859/1000000000000000000),(19858540071699249/200000000000000000),(1534670280267979769/125000000000000000),(569274093020212457171/100000000000000000),(1123488613264940373/500000000000000000)⟩,(999696270488175699/1000000000000000000),(648457063709117879/1000000000000000000),(70657607754013651/1000000000000000000),(32483158494272853/1000000000000000000)⟩
theorem valid4023 : certificate4023.Valid := by decide +kernel
theorem sound4023 : certificate4023.Sound := rat_cut_bin_certificate_sound certificate4023 profilesValid4023 numericValid4023 valid4023

def retention4024 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(2381880715400811990/461104646765771894257),(225573437/200000000),(11/4),(4661109324015576501/2000000000000000000),true,MergedCutProfiles.Batch607.profile24297,![MergedCutProfiles.Batch607.profile24297,MergedCutProfiles.Batch482.profile19284,MergedCutProfiles.Batch607.profile24298,MergedCutProfiles.Batch364.profile14583,MergedCutProfiles.Batch481.profile19244,MergedCutProfiles.Batch482.profile19285,MergedCutProfiles.Batch607.profile24299,MergedCutProfiles.Batch482.profile19286,MergedCutProfiles.Batch607.profile24300,MergedCutProfiles.Batch481.profile19248,MergedCutProfiles.Batch481.profile19276,MergedCutProfiles.Batch482.profile19287,MergedCutProfiles.Batch364.profile14599,MergedCutProfiles.Batch481.profile19251,MergedCutProfiles.Batch607.profile24301,MergedCutProfiles.Batch482.profile19289]⟩
theorem profilesValid4024 : retention4024.ProfilesValid := by
  change ∀ j : Fin 16, (retention4024.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch607.valid24297
  · exact MergedCutProfiles.Batch482.valid19284
  · exact MergedCutProfiles.Batch607.valid24298
  · exact MergedCutProfiles.Batch364.valid14583
  · exact MergedCutProfiles.Batch481.valid19244
  · exact MergedCutProfiles.Batch482.valid19285
  · exact MergedCutProfiles.Batch607.valid24299
  · exact MergedCutProfiles.Batch482.valid19286
  · exact MergedCutProfiles.Batch607.valid24300
  · exact MergedCutProfiles.Batch481.valid19248
  · exact MergedCutProfiles.Batch481.valid19276
  · exact MergedCutProfiles.Batch482.valid19287
  · exact MergedCutProfiles.Batch364.valid14599
  · exact MergedCutProfiles.Batch481.valid19251
  · exact MergedCutProfiles.Batch607.valid24301
  · exact MergedCutProfiles.Batch482.valid19289
theorem numericValid4024 : retention4024.NumericValid := by decide +kernel
def certificate4024 : RatCutBinCertificate := ⟨⟨retention4024,(1909556891102006859/1000000000000000000),(19858540071699249/200000000000000000),(1534670280267979769/125000000000000000),(569274093020212457171/100000000000000000),(286010610512401351/125000000000000000)⟩,(999696270488175699/1000000000000000000),(114630804397103567/250000000000000000),(183945683246887963/1000000000000000000),(30158449405061711/250000000000000000)⟩
theorem valid4024 : certificate4024.Valid := by decide +kernel
theorem sound4024 : certificate4024.Sound := rat_cut_bin_certificate_sound certificate4024 profilesValid4024 numericValid4024 valid4024

def retention4025 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(64000000000000000000/461104646765771894257),(238188071540081199/100000000000000000),(33/20),(22822675272800155364978739073683673797/12703363815470997280000000000000000000),false,MergedCutProfiles.Batch607.profile24302,(fun _ => MergedCutProfiles.Batch607.profile24302)⟩
theorem profilesValid4025 : retention4025.ProfilesValid := by
  exact MergedCutProfiles.Batch607.valid24302
theorem numericValid4025 : retention4025.NumericValid := by decide +kernel
def certificate4025 : RatCutBinCertificate := ⟨⟨retention4025,(1909556891102006859/1000000000000000000),(19858540071699249/200000000000000000),(1534670280267979769/125000000000000000),(569274093020212457171/100000000000000000),(885551675894207627/500000000000000000)⟩,(999696270488175699/1000000000000000000),(43662449478882651/100000000000000000),(201552332307818071/1000000000000000000),(169874901253234743/1000000000000000000)⟩
theorem valid4025 : certificate4025.Valid := by decide +kernel
theorem sound4025 : certificate4025.Sound := rat_cut_bin_certificate_sound certificate4025 profilesValid4025 numericValid4025 valid4025

def retention4026 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(1/2),64,1,(10215557807894927792817143837696186991/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch366.profile14641,(fun _ => MergedCutProfiles.Batch366.profile14641)⟩
theorem profilesValid4026 : retention4026.ProfilesValid := by
  exact MergedCutProfiles.Batch366.valid14641
theorem numericValid4026 : retention4026.NumericValid := by decide +kernel
def certificate4026 : RatCutBinCertificate := ⟨⟨retention4026,(1909556891102006859/1000000000000000000),(19858540071699249/200000000000000000),(1534670280267979769/125000000000000000),(569274093020212457171/100000000000000000),(98216959421135189/100000000000000000)⟩,(999696270488175699/1000000000000000000),(108831369794501923/200000000000000000),(124714040710828843/1000000000000000000),(120601964856653459/1000000000000000000)⟩
theorem valid4026 : certificate4026.Valid := by decide +kernel
theorem sound4026 : certificate4026.Sound := rat_cut_bin_certificate_sound certificate4026 profilesValid4026 numericValid4026 valid4026

def retention4027 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(64000000000000000000/461104646765771894257),(24841864931235642567/1000000000000000000),1,(543052513602722683298953144106600993/306689690509082007000000000000000000),false,MergedCutProfiles.Batch607.profile24302,(fun _ => MergedCutProfiles.Batch607.profile24302)⟩
theorem profilesValid4027 : retention4027.ProfilesValid := by
  exact MergedCutProfiles.Batch607.valid24302
theorem numericValid4027 : retention4027.NumericValid := by decide +kernel
def certificate4027 : RatCutBinCertificate := ⟨⟨retention4027,(1847003545102006859/1000000000000000000),(19858540071699249/200000000000000000),(1534670280267979769/125000000000000000),(569274093020212457171/100000000000000000),(351150578606592739/200000000000000000)⟩,(99970622037771079/100000000000000000),(32436701345271773/1000000000000000000),(837201040406479851/1000000000000000000),(10722446243464033/7812500000000000)⟩
theorem valid4027 : certificate4027.Valid := by decide +kernel
theorem sound4027 : certificate4027.Sound := rat_cut_bin_certificate_sound certificate4027 profilesValid4027 numericValid4027 valid4027

def retention4028 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(1/2),64,1,(10215557807894927792817143837696186991/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch366.profile14641,(fun _ => MergedCutProfiles.Batch366.profile14641)⟩
theorem profilesValid4028 : retention4028.ProfilesValid := by
  exact MergedCutProfiles.Batch366.valid14641
theorem numericValid4028 : retention4028.NumericValid := by decide +kernel
def certificate4028 : RatCutBinCertificate := ⟨⟨retention4028,(1847003545102006859/1000000000000000000),(19858540071699249/200000000000000000),(1534670280267979769/125000000000000000),(569274093020212457171/100000000000000000),(982675492156774863/1000000000000000000)⟩,(99970622037771079/100000000000000000),(57954871859489983/1000000000000000000),(153472678875474239/200000000000000000),(46402855814224613/62500000000000000)⟩
theorem valid4028 : certificate4028.Valid := by decide +kernel
theorem sound4028 : certificate4028.Sound := rat_cut_bin_certificate_sound certificate4028 profilesValid4028 numericValid4028 valid4028

def retention4029 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(155831146033856173/109806300649514491154),(154288263399857597/250000000000000000),4,(29379133629323700337/12800000000000000000),true,MergedCutProfiles.Batch607.profile24303,![MergedCutProfiles.Batch607.profile24303,MergedCutProfiles.Batch607.profile24304,MergedCutProfiles.Batch607.profile24305,MergedCutProfiles.Batch607.profile24306,MergedCutProfiles.Batch607.profile24307,MergedCutProfiles.Batch607.profile24308,MergedCutProfiles.Batch483.profile19338,MergedCutProfiles.Batch607.profile24309,MergedCutProfiles.Batch607.profile24310,MergedCutProfiles.Batch482.profile19313,MergedCutProfiles.Batch607.profile24311,MergedCutProfiles.Batch607.profile24312,MergedCutProfiles.Batch366.profile14645,MergedCutProfiles.Batch607.profile24313,MergedCutProfiles.Batch366.profile14661,MergedCutProfiles.Batch366.profile14677]⟩
theorem profilesValid4029 : retention4029.ProfilesValid := by
  change ∀ j : Fin 16, (retention4029.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch607.valid24303
  · exact MergedCutProfiles.Batch607.valid24304
  · exact MergedCutProfiles.Batch607.valid24305
  · exact MergedCutProfiles.Batch607.valid24306
  · exact MergedCutProfiles.Batch607.valid24307
  · exact MergedCutProfiles.Batch607.valid24308
  · exact MergedCutProfiles.Batch483.valid19338
  · exact MergedCutProfiles.Batch607.valid24309
  · exact MergedCutProfiles.Batch607.valid24310
  · exact MergedCutProfiles.Batch482.valid19313
  · exact MergedCutProfiles.Batch607.valid24311
  · exact MergedCutProfiles.Batch607.valid24312
  · exact MergedCutProfiles.Batch366.valid14645
  · exact MergedCutProfiles.Batch607.valid24313
  · exact MergedCutProfiles.Batch366.valid14661
  · exact MergedCutProfiles.Batch366.valid14677
theorem numericValid4029 : retention4029.NumericValid := by decide +kernel
def certificate4029 : RatCutBinCertificate := ⟨⟨retention4029,(959300363692540987/500000000000000000),(6511012982960937/62500000000000000),(2495228950263818199/200000000000000000),(5510612223659443130943/1000000000000000000),(2231162814291068309/1000000000000000000)⟩,(99968639464525333/100000000000000000),(131714366992703669/200000000000000000),(66354777862162071/1000000000000000000),(15089492124646901/500000000000000000)⟩
theorem valid4029 : certificate4029.Valid := by decide +kernel
theorem sound4029 : certificate4029.Sound := rat_cut_bin_certificate_sound certificate4029 profilesValid4029 numericValid4029 valid4029

def retention4030 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(139520305250000000/54903150324757245577),(155831146033856173/250000000000000000),4,(1144362257456125741087043773327010931/498659667308339753600000000000000000),true,MergedCutProfiles.Batch607.profile24314,![MergedCutProfiles.Batch607.profile24314,MergedCutProfiles.Batch607.profile24315,MergedCutProfiles.Batch607.profile24316,MergedCutProfiles.Batch483.profile19338,MergedCutProfiles.Batch607.profile24310,MergedCutProfiles.Batch607.profile24311,MergedCutProfiles.Batch483.profile19326,MergedCutProfiles.Batch482.profile19314,MergedCutProfiles.Batch366.profile14677,MergedCutProfiles.Batch607.profile24317,MergedCutProfiles.Batch482.profile19315,MergedCutProfiles.Batch483.profile19339,MergedCutProfiles.Batch607.profile24318,MergedCutProfiles.Batch483.profile19328,MergedCutProfiles.Batch607.profile24319,MergedCutProfiles.Batch483.profile19340]⟩
theorem profilesValid4030 : retention4030.ProfilesValid := by
  change ∀ j : Fin 16, (retention4030.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch607.valid24314
  · exact MergedCutProfiles.Batch607.valid24315
  · exact MergedCutProfiles.Batch607.valid24316
  · exact MergedCutProfiles.Batch483.valid19338
  · exact MergedCutProfiles.Batch607.valid24310
  · exact MergedCutProfiles.Batch607.valid24311
  · exact MergedCutProfiles.Batch483.valid19326
  · exact MergedCutProfiles.Batch482.valid19314
  · exact MergedCutProfiles.Batch366.valid14677
  · exact MergedCutProfiles.Batch607.valid24317
  · exact MergedCutProfiles.Batch482.valid19315
  · exact MergedCutProfiles.Batch483.valid19339
  · exact MergedCutProfiles.Batch607.valid24318
  · exact MergedCutProfiles.Batch483.valid19328
  · exact MergedCutProfiles.Batch607.valid24319
  · exact MergedCutProfiles.Batch483.valid19340
theorem numericValid4030 : retention4030.NumericValid := by decide +kernel
def certificate4030 : RatCutBinCertificate := ⟨⟨retention4030,(959300363692540987/500000000000000000),(6511012982960937/62500000000000000),(2495228950263818199/200000000000000000),(5510612223659443130943/1000000000000000000),(446158862951093467/200000000000000000)⟩,(99968639464525333/100000000000000000),(327239479652777091/500000000000000000),(68077041587472949/1000000000000000000),(15507362801245621/500000000000000000)⟩
theorem valid4030 : certificate4030.Valid := by decide +kernel
theorem sound4030 : certificate4030.Sound := rat_cut_bin_certificate_sound certificate4030 profilesValid4030 numericValid4030 valid4030

def retention4031 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(1771978724349701555/439225202598057964616),(558081221/500000000),(14/5),(2348541054148297281/1000000000000000000),true,MergedCutProfiles.Batch608.profile24320,![MergedCutProfiles.Batch608.profile24320,MergedCutProfiles.Batch608.profile24321,MergedCutProfiles.Batch608.profile24322,MergedCutProfiles.Batch608.profile24323,MergedCutProfiles.Batch607.profile24313,MergedCutProfiles.Batch608.profile24324,MergedCutProfiles.Batch608.profile24325,MergedCutProfiles.Batch367.profile14704,MergedCutProfiles.Batch608.profile24326,MergedCutProfiles.Batch608.profile24327,MergedCutProfiles.Batch608.profile24328,MergedCutProfiles.Batch482.profile19318,MergedCutProfiles.Batch608.profile24329,MergedCutProfiles.Batch608.profile24330,MergedCutProfiles.Batch608.profile24331,MergedCutProfiles.Batch608.profile24332]⟩
theorem profilesValid4031 : retention4031.ProfilesValid := by
  change ∀ j : Fin 16, (retention4031.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch608.valid24320
  · exact MergedCutProfiles.Batch608.valid24321
  · exact MergedCutProfiles.Batch608.valid24322
  · exact MergedCutProfiles.Batch608.valid24323
  · exact MergedCutProfiles.Batch607.valid24313
  · exact MergedCutProfiles.Batch608.valid24324
  · exact MergedCutProfiles.Batch608.valid24325
  · exact MergedCutProfiles.Batch367.valid14704
  · exact MergedCutProfiles.Batch608.valid24326
  · exact MergedCutProfiles.Batch608.valid24327
  · exact MergedCutProfiles.Batch608.valid24328
  · exact MergedCutProfiles.Batch482.valid19318
  · exact MergedCutProfiles.Batch608.valid24329
  · exact MergedCutProfiles.Batch608.valid24330
  · exact MergedCutProfiles.Batch608.valid24331
  · exact MergedCutProfiles.Batch608.valid24332
theorem numericValid4031 : retention4031.NumericValid := by decide +kernel
def certificate4031 : RatCutBinCertificate := ⟨⟨retention4031,(959300363692540987/500000000000000000),(6511012982960937/62500000000000000),(2495228950263818199/200000000000000000),(5510612223659443130943/1000000000000000000),(460736745194795237/200000000000000000)⟩,(99968639464525333/100000000000000000),(227058973586908793/500000000000000000),(59968596775583/320000000000000),(24401631283181933/200000000000000000)⟩
theorem valid4031 : certificate4031.Valid := by decide +kernel
theorem sound4031 : certificate4031.Sound := rat_cut_bin_certificate_sound certificate4031 profilesValid4031 numericValid4031 valid4031

def certificates : List RatCutBinCertificate := [certificate4020,certificate4021,certificate4022,certificate4023,certificate4024,certificate4025,certificate4026,certificate4027,certificate4028,certificate4029,certificate4030,certificate4031]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4020,List.forall_mem_cons.mpr ⟨sound4021,List.forall_mem_cons.mpr ⟨sound4022,List.forall_mem_cons.mpr ⟨sound4023,List.forall_mem_cons.mpr ⟨sound4024,List.forall_mem_cons.mpr ⟨sound4025,List.forall_mem_cons.mpr ⟨sound4026,List.forall_mem_cons.mpr ⟨sound4027,List.forall_mem_cons.mpr ⟨sound4028,List.forall_mem_cons.mpr ⟨sound4029,List.forall_mem_cons.mpr ⟨sound4030,List.forall_mem_cons.mpr ⟨sound4031,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch335
