import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch258
import Cycle12.MergedCutProfiles.Batch259
import Cycle12.MergedCutProfiles.Batch260

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch134

def retention1608 : RatCutRetentionCertificate := ⟨(509/8000),(51/800),(1/2),(5382613227270642337/1000000000000000000),(11/10),(2135083901971283783203104094151879730391/2153045290908256934800000000000000000000),false,MergedCutProfiles.Batch258.profile10335,(fun _ => MergedCutProfiles.Batch258.profile10335)⟩
theorem profilesValid1608 : retention1608.ProfilesValid := by
  exact MergedCutProfiles.Batch258.valid10335
theorem numericValid1608 : retention1608.NumericValid := by decide +kernel
def certificate1608 : RatCutBinCertificate := ⟨⟨retention1608,(473824445381424539/200000000000000000),(52706141081196361/250000000000000000),(16967775142051727919/1000000000000000000),(1433717631298357343/7812500000000000),(239817856898348957/250000000000000000)⟩,(247442534552934607/250000000000000000),(430893215541178129/1000000000000000000),(206339433628973843/1000000000000000000),(2423194782949663/15625000000000000)⟩
theorem valid1608 : certificate1608.Valid := by decide +kernel
theorem sound1608 : certificate1608.Sound := rat_cut_bin_certificate_sound certificate1608 profilesValid1608 numericValid1608 valid1608

def retention1609 : RatCutRetentionCertificate := ⟨(509/8000),(51/800),(1/2),64,1,(63853510510315067724084090726358240951/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch258.profile10335,(fun _ => MergedCutProfiles.Batch258.profile10335)⟩
theorem profilesValid1609 : retention1609.ProfilesValid := by
  exact MergedCutProfiles.Batch258.valid10335
theorem numericValid1609 : retention1609.NumericValid := by decide +kernel
def certificate1609 : RatCutBinCertificate := ⟨⟨retention1609,(473824445381424539/200000000000000000),(52706141081196361/250000000000000000),(16967775142051727919/1000000000000000000),(1433717631298357343/7812500000000000),(96827423550664807/100000000000000000)⟩,(247442534552934607/250000000000000000),(388957395076184893/1000000000000000000),(243753916726271677/1000000000000000000),(230100991205131353/1000000000000000000)⟩
theorem valid1609 : certificate1609.Valid := by decide +kernel
theorem sound1609 : certificate1609.Sound := rat_cut_bin_certificate_sound certificate1609 profilesValid1609 numericValid1609 valid1609

def retention1610 : RatCutRetentionCertificate := ⟨(509/8000),(51/800),(2521161708057609323/5403537305755299846),(3222321565108766203/1000000000000000000),(6/5),(42492738584808578077766421191905841647/40279019563859577537500000000000000000),false,MergedCutProfiles.Batch258.profile10336,(fun _ => MergedCutProfiles.Batch258.profile10336)⟩
theorem profilesValid1610 : retention1610.ProfilesValid := by
  exact MergedCutProfiles.Batch258.valid10336
theorem numericValid1610 : retention1610.NumericValid := by decide +kernel
def certificate1610 : RatCutBinCertificate := ⟨⟨retention1610,(536647479581424539/200000000000000000),(52706141081196361/250000000000000000),(16967775142051727919/1000000000000000000),(1433717631298357343/7812500000000000),(1014940657770992187/1000000000000000000)⟩,(494204809002432987/500000000000000000),(48449913034486683/125000000000000000),(9801545539815787/40000000000000000),(41961381722527719/250000000000000000)⟩
theorem valid1610 : certificate1610.Valid := by decide +kernel
theorem sound1610 : certificate1610.Sound := rat_cut_bin_certificate_sound certificate1610 profilesValid1610 numericValid1610 valid1610

def retention1611 : RatCutRetentionCertificate := ⟨(509/8000),(51/800),(297362661780754205/600393033972811094),(2521161708057609323/500000000000000000),(11/10),(71914667288498421026784199452503773513/72033191658788837800000000000000000000),false,MergedCutProfiles.Batch258.profile10337,(fun _ => MergedCutProfiles.Batch258.profile10337)⟩
theorem profilesValid1611 : retention1611.ProfilesValid := by
  exact MergedCutProfiles.Batch258.valid10337
theorem numericValid1611 : retention1611.NumericValid := by decide +kernel
def certificate1611 : RatCutBinCertificate := ⟨⟨retention1611,(536647479581424539/200000000000000000),(52706141081196361/250000000000000000),(16967775142051727919/1000000000000000000),(1433717631298357343/7812500000000000),(120209231384614317/125000000000000000)⟩,(494204809002432987/500000000000000000),(51133538204353619/125000000000000000),(112637753994184827/500000000000000000),(41996164669024177/250000000000000000)⟩
theorem valid1611 : certificate1611.Valid := by decide +kernel
theorem sound1611 : certificate1611.Sound := rat_cut_bin_certificate_sound certificate1611 profilesValid1611 numericValid1611 valid1611

def retention1612 : RatCutRetentionCertificate := ⟨(509/8000),(51/800),(1/2),(535252791205357569/100000000000000000),(11/10),(4245500884099420258441211960008495123/4282022329642860552000000000000000000),false,MergedCutProfiles.Batch258.profile10335,(fun _ => MergedCutProfiles.Batch258.profile10335)⟩
theorem profilesValid1612 : retention1612.ProfilesValid := by
  exact MergedCutProfiles.Batch258.valid10335
theorem numericValid1612 : retention1612.NumericValid := by decide +kernel
def certificate1612 : RatCutBinCertificate := ⟨⟨retention1612,(536647479581424539/200000000000000000),(52706141081196361/250000000000000000),(16967775142051727919/1000000000000000000),(1433717631298357343/7812500000000000),(238697671641570071/250000000000000000)⟩,(494204809002432987/500000000000000000),(20600865633079551/50000000000000000),(222650162612977511/1000000000000000000),(83156088918800921/500000000000000000)⟩
theorem valid1612 : certificate1612.Valid := by decide +kernel
theorem sound1612 : certificate1612.Sound := rat_cut_bin_certificate_sound certificate1612 profilesValid1612 numericValid1612 valid1612

def retention1613 : RatCutRetentionCertificate := ⟨(51/800),(511/8000),(350572967409917152/3585457739833142415),(174109942955663927/200000000000000000),(13/5),(486960263835462604187/256000000000000000000),true,MergedCutProfiles.Batch258.profile10338,![MergedCutProfiles.Batch258.profile10338,MergedCutProfiles.Batch258.profile10339,MergedCutProfiles.Batch258.profile10340,MergedCutProfiles.Batch258.profile10341,MergedCutProfiles.Batch258.profile10342,MergedCutProfiles.Batch258.profile10343,MergedCutProfiles.Batch258.profile10344,MergedCutProfiles.Batch258.profile10345,MergedCutProfiles.Batch258.profile10346,MergedCutProfiles.Batch258.profile10347,MergedCutProfiles.Batch258.profile10348,MergedCutProfiles.Batch258.profile10349,MergedCutProfiles.Batch258.profile10350,MergedCutProfiles.Batch258.profile10351,MergedCutProfiles.Batch258.profile10352,MergedCutProfiles.Batch258.profile10353]⟩
theorem profilesValid1613 : retention1613.ProfilesValid := by
  change ∀ j : Fin 16, (retention1613.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch258.valid10338
  · exact MergedCutProfiles.Batch258.valid10339
  · exact MergedCutProfiles.Batch258.valid10340
  · exact MergedCutProfiles.Batch258.valid10341
  · exact MergedCutProfiles.Batch258.valid10342
  · exact MergedCutProfiles.Batch258.valid10343
  · exact MergedCutProfiles.Batch258.valid10344
  · exact MergedCutProfiles.Batch258.valid10345
  · exact MergedCutProfiles.Batch258.valid10346
  · exact MergedCutProfiles.Batch258.valid10347
  · exact MergedCutProfiles.Batch258.valid10348
  · exact MergedCutProfiles.Batch258.valid10349
  · exact MergedCutProfiles.Batch258.valid10350
  · exact MergedCutProfiles.Batch258.valid10351
  · exact MergedCutProfiles.Batch258.valid10352
  · exact MergedCutProfiles.Batch258.valid10353
theorem numericValid1613 : retention1613.NumericValid := by decide +kernel
def certificate1613 : RatCutBinCertificate := ⟨⟨retention1613,(2370502591943633393/1000000000000000000),(21182226506109577/100000000000000000),(8503990036874126001/500000000000000000),(5721494197070798261/31250000000000000),(1825389704251804351/1000000000000000000)⟩,(989752926237757021/1000000000000000000),(169936027063299393/500000000000000000),(146667519036915169/500000000000000000),(31045249388852647/200000000000000000)⟩
theorem valid1613 : certificate1613.Valid := by decide +kernel
theorem sound1613 : certificate1613.Sound := rat_cut_bin_certificate_sound certificate1613 profilesValid1613 numericValid1613 valid1613

def retention1614 : RatCutRetentionCertificate := ⟨(51/800),(511/8000),(1854462198423799199/10756373219499427245),(32866215694679733/31250000000000000),(11/5),(34014529021237744329/20000000000000000000),true,MergedCutProfiles.Batch258.profile10354,![MergedCutProfiles.Batch258.profile10354,MergedCutProfiles.Batch258.profile10355,MergedCutProfiles.Batch258.profile10356,MergedCutProfiles.Batch258.profile10357,MergedCutProfiles.Batch258.profile10358,MergedCutProfiles.Batch258.profile10359,MergedCutProfiles.Batch259.profile10360,MergedCutProfiles.Batch259.profile10361,MergedCutProfiles.Batch259.profile10362,MergedCutProfiles.Batch259.profile10363,MergedCutProfiles.Batch259.profile10364,MergedCutProfiles.Batch259.profile10365,MergedCutProfiles.Batch259.profile10366,MergedCutProfiles.Batch259.profile10367,MergedCutProfiles.Batch259.profile10368,MergedCutProfiles.Batch259.profile10369]⟩
theorem profilesValid1614 : retention1614.ProfilesValid := by
  change ∀ j : Fin 16, (retention1614.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch258.valid10354
  · exact MergedCutProfiles.Batch258.valid10355
  · exact MergedCutProfiles.Batch258.valid10356
  · exact MergedCutProfiles.Batch258.valid10357
  · exact MergedCutProfiles.Batch258.valid10358
  · exact MergedCutProfiles.Batch258.valid10359
  · exact MergedCutProfiles.Batch259.valid10360
  · exact MergedCutProfiles.Batch259.valid10361
  · exact MergedCutProfiles.Batch259.valid10362
  · exact MergedCutProfiles.Batch259.valid10363
  · exact MergedCutProfiles.Batch259.valid10364
  · exact MergedCutProfiles.Batch259.valid10365
  · exact MergedCutProfiles.Batch259.valid10366
  · exact MergedCutProfiles.Batch259.valid10367
  · exact MergedCutProfiles.Batch259.valid10368
  · exact MergedCutProfiles.Batch259.valid10369
theorem numericValid1614 : retention1614.NumericValid := by decide +kernel
def certificate1614 : RatCutBinCertificate := ⟨⟨retention1614,(2370502591943633393/1000000000000000000),(21182226506109577/100000000000000000),(8503990036874126001/500000000000000000),(5721494197070798261/31250000000000000),(817871775619369689/500000000000000000)⟩,(989752926237757021/1000000000000000000),(176582128327082013/500000000000000000),(279249297918585801/1000000000000000000),(31036898312653163/200000000000000000)⟩
theorem valid1614 : certificate1614.Valid := by decide +kernel
theorem sound1614 : certificate1614.Sound := rat_cut_bin_certificate_sound certificate1614 profilesValid1614 numericValid1614 valid1614

def retention1615 : RatCutRetentionCertificate := ⟨(51/800),(511/8000),(112771721450631872/325950703621194765),(1854462198423799199/1000000000000000000),(29/20),(1659274128722645569159/1280000000000000000000),true,MergedCutProfiles.Batch259.profile10370,![MergedCutProfiles.Batch259.profile10370,MergedCutProfiles.Batch258.profile10357,MergedCutProfiles.Batch259.profile10371,MergedCutProfiles.Batch259.profile10372,MergedCutProfiles.Batch259.profile10373,MergedCutProfiles.Batch259.profile10374,MergedCutProfiles.Batch259.profile10375,MergedCutProfiles.Batch259.profile10376,MergedCutProfiles.Batch259.profile10377,MergedCutProfiles.Batch259.profile10378,MergedCutProfiles.Batch259.profile10379,MergedCutProfiles.Batch259.profile10380,MergedCutProfiles.Batch259.profile10381,MergedCutProfiles.Batch259.profile10382,MergedCutProfiles.Batch259.profile10383,MergedCutProfiles.Batch259.profile10384]⟩
theorem profilesValid1615 : retention1615.ProfilesValid := by
  change ∀ j : Fin 16, (retention1615.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch259.valid10370
  · exact MergedCutProfiles.Batch258.valid10357
  · exact MergedCutProfiles.Batch259.valid10371
  · exact MergedCutProfiles.Batch259.valid10372
  · exact MergedCutProfiles.Batch259.valid10373
  · exact MergedCutProfiles.Batch259.valid10374
  · exact MergedCutProfiles.Batch259.valid10375
  · exact MergedCutProfiles.Batch259.valid10376
  · exact MergedCutProfiles.Batch259.valid10377
  · exact MergedCutProfiles.Batch259.valid10378
  · exact MergedCutProfiles.Batch259.valid10379
  · exact MergedCutProfiles.Batch259.valid10380
  · exact MergedCutProfiles.Batch259.valid10381
  · exact MergedCutProfiles.Batch259.valid10382
  · exact MergedCutProfiles.Batch259.valid10383
  · exact MergedCutProfiles.Batch259.valid10384
theorem numericValid1615 : retention1615.NumericValid := by decide +kernel
def certificate1615 : RatCutBinCertificate := ⟨⟨retention1615,(2370502591943633393/1000000000000000000),(21182226506109577/100000000000000000),(8503990036874126001/500000000000000000),(5721494197070798261/31250000000000000),(1253481261170227897/1000000000000000000)⟩,(989752926237757021/1000000000000000000),(48748495318112969/125000000000000000),(242782187663540011/1000000000000000000),(156897265050224261/1000000000000000000)⟩
theorem valid1615 : certificate1615.Valid := by decide +kernel
theorem sound1615 : certificate1615.Sound := rat_cut_bin_certificate_sound certificate1615 profilesValid1615 numericValid1615 valid1615

def retention1616 : RatCutRetentionCertificate := ⟨(51/800),(511/8000),(1671991666812046124/3585457739833142415),(58147918872982059/15625000000000000),1,(8132481202320054423/8000000000000000000),true,MergedCutProfiles.Batch259.profile10385,![MergedCutProfiles.Batch259.profile10385,MergedCutProfiles.Batch259.profile10386,MergedCutProfiles.Batch259.profile10387,MergedCutProfiles.Batch259.profile10388,MergedCutProfiles.Batch259.profile10389,MergedCutProfiles.Batch259.profile10390,MergedCutProfiles.Batch259.profile10391,MergedCutProfiles.Batch259.profile10392,MergedCutProfiles.Batch259.profile10393,MergedCutProfiles.Batch259.profile10394,MergedCutProfiles.Batch259.profile10395,MergedCutProfiles.Batch259.profile10396,MergedCutProfiles.Batch259.profile10397,MergedCutProfiles.Batch259.profile10398,MergedCutProfiles.Batch259.profile10399,MergedCutProfiles.Batch260.profile10400]⟩
theorem profilesValid1616 : retention1616.ProfilesValid := by
  change ∀ j : Fin 16, (retention1616.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch259.valid10385
  · exact MergedCutProfiles.Batch259.valid10386
  · exact MergedCutProfiles.Batch259.valid10387
  · exact MergedCutProfiles.Batch259.valid10388
  · exact MergedCutProfiles.Batch259.valid10389
  · exact MergedCutProfiles.Batch259.valid10390
  · exact MergedCutProfiles.Batch259.valid10391
  · exact MergedCutProfiles.Batch259.valid10392
  · exact MergedCutProfiles.Batch259.valid10393
  · exact MergedCutProfiles.Batch259.valid10394
  · exact MergedCutProfiles.Batch259.valid10395
  · exact MergedCutProfiles.Batch259.valid10396
  · exact MergedCutProfiles.Batch259.valid10397
  · exact MergedCutProfiles.Batch259.valid10398
  · exact MergedCutProfiles.Batch259.valid10399
  · exact MergedCutProfiles.Batch260.valid10400
theorem numericValid1616 : retention1616.NumericValid := by decide +kernel
def certificate1616 : RatCutBinCertificate := ⟨⟨retention1616,(2370502591943633393/1000000000000000000),(21182226506109577/100000000000000000),(8503990036874126001/500000000000000000),(5721494197070798261/31250000000000000),(123378506561156851/125000000000000000)⟩,(989752926237757021/1000000000000000000),(218052059972469241/500000000000000000),(201983860437651417/1000000000000000000),(155736257480594391/1000000000000000000)⟩
theorem valid1616 : certificate1616.Valid := by decide +kernel
theorem sound1616 : certificate1616.Sound := rat_cut_bin_certificate_sound certificate1616 profilesValid1616 numericValid1616 valid1616

def retention1617 : RatCutRetentionCertificate := ⟨(51/800),(511/8000),(5324558537873820649/10756373219499427245),(1253993750109034593/250000000000000000),(11/10),(31307865138650430022247787078177566309/31349843752725864825000000000000000000),false,MergedCutProfiles.Batch260.profile10401,(fun _ => MergedCutProfiles.Batch260.profile10401)⟩
theorem profilesValid1617 : retention1617.ProfilesValid := by
  exact MergedCutProfiles.Batch260.valid10401
theorem numericValid1617 : retention1617.NumericValid := by decide +kernel
def certificate1617 : RatCutBinCertificate := ⟨⟨retention1617,(2370502591943633393/1000000000000000000),(21182226506109577/100000000000000000),(8503990036874126001/500000000000000000),(5721494197070798261/31250000000000000),(966178941495048103/1000000000000000000)⟩,(989752926237757021/1000000000000000000),(215010728643756791/500000000000000000),(103537115255197823/500000000000000000),(155135050177009553/1000000000000000000)⟩
theorem valid1617 : certificate1617.Valid := by decide +kernel
theorem sound1617 : certificate1617.Sound := rat_cut_bin_certificate_sound certificate1617 profilesValid1617 numericValid1617 valid1617

def retention1618 : RatCutRetentionCertificate := ⟨(51/800),(511/8000),(5377804123252558856/10756373219499427245),(5324558537873820649/1000000000000000000),(11/10),(2111429494771442156468338388834643842239/2129823415149528259600000000000000000000),false,MergedCutProfiles.Batch260.profile10402,(fun _ => MergedCutProfiles.Batch260.profile10402)⟩
theorem profilesValid1618 : retention1618.ProfilesValid := by
  exact MergedCutProfiles.Batch260.valid10402
theorem numericValid1618 : retention1618.NumericValid := by decide +kernel
def certificate1618 : RatCutBinCertificate := ⟨⟨retention1618,(2370502591943633393/1000000000000000000),(21182226506109577/100000000000000000),(8503990036874126001/500000000000000000),(5721494197070798261/31250000000000000),(958882014208528993/1000000000000000000)⟩,(989752926237757021/1000000000000000000),(215346437847268173/500000000000000000),(206508142031661729/1000000000000000000),(9683432605239619/62500000000000000)⟩
theorem valid1618 : certificate1618.Valid := by decide +kernel
theorem sound1618 : certificate1618.Sound := rat_cut_bin_certificate_sound certificate1618 profilesValid1618 numericValid1618 valid1618

def retention1619 : RatCutRetentionCertificate := ⟨(51/800),(511/8000),(1/2),(672225515406569857/125000000000000000),(11/10),(533278556877340932185950620635754997591/537780412325255885600000000000000000000),false,MergedCutProfiles.Batch260.profile10403,(fun _ => MergedCutProfiles.Batch260.profile10403)⟩
theorem profilesValid1619 : retention1619.ProfilesValid := by
  exact MergedCutProfiles.Batch260.valid10403
theorem numericValid1619 : retention1619.NumericValid := by decide +kernel
def certificate1619 : RatCutBinCertificate := ⟨⟨retention1619,(2370502591943633393/1000000000000000000),(21182226506109577/100000000000000000),(8503990036874126001/500000000000000000),(5721494197070798261/31250000000000000),(959147259280000289/1000000000000000000)⟩,(989752926237757021/1000000000000000000),(53769411115545963/125000000000000000),(206961310360071201/1000000000000000000),(77756578801076597/500000000000000000)⟩
theorem valid1619 : certificate1619.Valid := by decide +kernel
theorem sound1619 : certificate1619.Sound := rat_cut_bin_certificate_sound certificate1619 profilesValid1619 numericValid1619 valid1619

def certificates : List RatCutBinCertificate := [certificate1608,certificate1609,certificate1610,certificate1611,certificate1612,certificate1613,certificate1614,certificate1615,certificate1616,certificate1617,certificate1618,certificate1619]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1608,List.forall_mem_cons.mpr ⟨sound1609,List.forall_mem_cons.mpr ⟨sound1610,List.forall_mem_cons.mpr ⟨sound1611,List.forall_mem_cons.mpr ⟨sound1612,List.forall_mem_cons.mpr ⟨sound1613,List.forall_mem_cons.mpr ⟨sound1614,List.forall_mem_cons.mpr ⟨sound1615,List.forall_mem_cons.mpr ⟨sound1616,List.forall_mem_cons.mpr ⟨sound1617,List.forall_mem_cons.mpr ⟨sound1618,List.forall_mem_cons.mpr ⟨sound1619,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch134
