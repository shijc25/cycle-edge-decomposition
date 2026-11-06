import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch010
import Cycle12.MergedCutProfiles.Batch011
import Cycle12.MergedCutProfiles.Batch012
import Cycle12.MergedCutProfiles.Batch311
import Cycle12.MergedCutProfiles.Batch312
import Cycle12.MergedCutProfiles.Batch313

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch165

def retention1980 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(605904539014894011/1168768143274361145448),(145565588156558711/250000000000000000),4,(142076133821793091559/64000000000000000000),true,MergedCutProfiles.Batch311.profile12442,![MergedCutProfiles.Batch311.profile12442,MergedCutProfiles.Batch010.profile418,MergedCutProfiles.Batch311.profile12443,MergedCutProfiles.Batch010.profile419,MergedCutProfiles.Batch311.profile12444,MergedCutProfiles.Batch010.profile420,MergedCutProfiles.Batch311.profile12445,MergedCutProfiles.Batch311.profile12446,MergedCutProfiles.Batch311.profile12447,MergedCutProfiles.Batch311.profile12448,MergedCutProfiles.Batch311.profile12449,MergedCutProfiles.Batch010.profile423,MergedCutProfiles.Batch311.profile12450,MergedCutProfiles.Batch311.profile12451,MergedCutProfiles.Batch311.profile12452,MergedCutProfiles.Batch311.profile12453]⟩
theorem profilesValid1980 : retention1980.ProfilesValid := by
  change ∀ j : Fin 16, (retention1980.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch311.valid12442
  · exact MergedCutProfiles.Batch010.valid418
  · exact MergedCutProfiles.Batch311.valid12443
  · exact MergedCutProfiles.Batch010.valid419
  · exact MergedCutProfiles.Batch311.valid12444
  · exact MergedCutProfiles.Batch010.valid420
  · exact MergedCutProfiles.Batch311.valid12445
  · exact MergedCutProfiles.Batch311.valid12446
  · exact MergedCutProfiles.Batch311.valid12447
  · exact MergedCutProfiles.Batch311.valid12448
  · exact MergedCutProfiles.Batch311.valid12449
  · exact MergedCutProfiles.Batch010.valid423
  · exact MergedCutProfiles.Batch311.valid12450
  · exact MergedCutProfiles.Batch311.valid12451
  · exact MergedCutProfiles.Batch311.valid12452
  · exact MergedCutProfiles.Batch311.valid12453
theorem numericValid1980 : retention1980.NumericValid := by decide +kernel
def certificate1980 : RatCutBinCertificate := ⟨⟨retention1980,(114582081168199667/62500000000000000),(4061079806220747/1000000000000000000),(3716558024871893587/500000000000000000),(8726715693851369783053/1000000000000000000),(553983267596823507/250000000000000000)⟩,(999790608096989649/1000000000000000000),(284649322209076791/500000000000000000),(10998688995492489/100000000000000000),(49210573266518111/1000000000000000000)⟩
theorem valid1980 : certificate1980.Valid := by decide +kernel
theorem sound1980 : certificate1980.Sound := rat_cut_bin_certificate_sound certificate1980 profilesValid1980 numericValid1980 valid1980

def retention1981 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(159950879250000000/146096017909295143181),(605904539014894011/1000000000000000000),4,(577508214853220073963/256000000000000000000),true,MergedCutProfiles.Batch010.profile418,![MergedCutProfiles.Batch010.profile418,MergedCutProfiles.Batch010.profile419,MergedCutProfiles.Batch311.profile12454,MergedCutProfiles.Batch010.profile421,MergedCutProfiles.Batch010.profile422,MergedCutProfiles.Batch010.profile434,MergedCutProfiles.Batch010.profile424,MergedCutProfiles.Batch010.profile425,MergedCutProfiles.Batch311.profile12455,MergedCutProfiles.Batch010.profile435,MergedCutProfiles.Batch311.profile12456,MergedCutProfiles.Batch010.profile436,MergedCutProfiles.Batch011.profile449,MergedCutProfiles.Batch010.profile437,MergedCutProfiles.Batch311.profile12457,MergedCutProfiles.Batch010.profile438]⟩
theorem profilesValid1981 : retention1981.ProfilesValid := by
  change ∀ j : Fin 16, (retention1981.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch010.valid418
  · exact MergedCutProfiles.Batch010.valid419
  · exact MergedCutProfiles.Batch311.valid12454
  · exact MergedCutProfiles.Batch010.valid421
  · exact MergedCutProfiles.Batch010.valid422
  · exact MergedCutProfiles.Batch010.valid434
  · exact MergedCutProfiles.Batch010.valid424
  · exact MergedCutProfiles.Batch010.valid425
  · exact MergedCutProfiles.Batch311.valid12455
  · exact MergedCutProfiles.Batch010.valid435
  · exact MergedCutProfiles.Batch311.valid12456
  · exact MergedCutProfiles.Batch010.valid436
  · exact MergedCutProfiles.Batch011.valid449
  · exact MergedCutProfiles.Batch010.valid437
  · exact MergedCutProfiles.Batch311.valid12457
  · exact MergedCutProfiles.Batch010.valid438
theorem numericValid1981 : retention1981.NumericValid := by decide +kernel
def certificate1981 : RatCutBinCertificate := ⟨⟨retention1981,(114582081168199667/62500000000000000),(4061079806220747/1000000000000000000),(3716558024871893587/500000000000000000),(8726715693851369783053/1000000000000000000),(2251884943723404411/1000000000000000000)⟩,(999790608096989649/1000000000000000000),(545523188668345153/1000000000000000000),(24776862644236767/200000000000000000),(884104390369549/15625000000000000)⟩
theorem valid1981 : certificate1981.Valid := by decide +kernel
theorem sound1981 : certificate1981.Sound := rat_cut_bin_certificate_sound certificate1981 profilesValid1981 numericValid1981 valid1981

def retention1982 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(494980049486993623/292192035818590286362),(639803517/500000000),(49/20),(37104720122294149813/16000000000000000000),true,MergedCutProfiles.Batch311.profile12458,![MergedCutProfiles.Batch311.profile12458,MergedCutProfiles.Batch311.profile12454,MergedCutProfiles.Batch311.profile12448,MergedCutProfiles.Batch311.profile12450,MergedCutProfiles.Batch010.profile425,MergedCutProfiles.Batch311.profile12459,MergedCutProfiles.Batch010.profile428,MergedCutProfiles.Batch311.profile12460,MergedCutProfiles.Batch010.profile437,MergedCutProfiles.Batch010.profile433,MergedCutProfiles.Batch311.profile12461,MergedCutProfiles.Batch311.profile12462,MergedCutProfiles.Batch011.profile440,MergedCutProfiles.Batch011.profile451,MergedCutProfiles.Batch311.profile12463,MergedCutProfiles.Batch311.profile12464]⟩
theorem profilesValid1982 : retention1982.ProfilesValid := by
  change ∀ j : Fin 16, (retention1982.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch311.valid12458
  · exact MergedCutProfiles.Batch311.valid12454
  · exact MergedCutProfiles.Batch311.valid12448
  · exact MergedCutProfiles.Batch311.valid12450
  · exact MergedCutProfiles.Batch010.valid425
  · exact MergedCutProfiles.Batch311.valid12459
  · exact MergedCutProfiles.Batch010.valid428
  · exact MergedCutProfiles.Batch311.valid12460
  · exact MergedCutProfiles.Batch010.valid437
  · exact MergedCutProfiles.Batch010.valid433
  · exact MergedCutProfiles.Batch311.valid12461
  · exact MergedCutProfiles.Batch311.valid12462
  · exact MergedCutProfiles.Batch011.valid440
  · exact MergedCutProfiles.Batch011.valid451
  · exact MergedCutProfiles.Batch311.valid12463
  · exact MergedCutProfiles.Batch311.valid12464
theorem numericValid1982 : retention1982.NumericValid := by decide +kernel
def certificate1982 : RatCutBinCertificate := ⟨⟨retention1982,(114582081168199667/62500000000000000),(4061079806220747/1000000000000000000),(3716558024871893587/500000000000000000),(8726715693851369783053/1000000000000000000),(1158295506957640487/500000000000000000)⟩,(999790608096989649/1000000000000000000),(172586448512388667/500000000000000000),(143828317892515901/500000000000000000),(41783498376113947/200000000000000000)⟩
theorem valid1982 : certificate1982.Valid := by decide +kernel
theorem sound1982 : certificate1982.Sound := rat_cut_bin_certificate_sound certificate1982 profilesValid1982 numericValid1982 valid1982

def retention1983 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(8000000000000000000/146096017909295143181),(494980049486993623/250000000000000000),(37/20),(648735930290129477479/320000000000000000000),true,MergedCutProfiles.Batch311.profile12465,![MergedCutProfiles.Batch311.profile12465,MergedCutProfiles.Batch311.profile12466,MergedCutProfiles.Batch311.profile12467,MergedCutProfiles.Batch311.profile12468,MergedCutProfiles.Batch311.profile12469,MergedCutProfiles.Batch311.profile12470,MergedCutProfiles.Batch311.profile12471,MergedCutProfiles.Batch311.profile12472,MergedCutProfiles.Batch311.profile12473,MergedCutProfiles.Batch311.profile12474,MergedCutProfiles.Batch311.profile12475,MergedCutProfiles.Batch311.profile12476,MergedCutProfiles.Batch311.profile12477,MergedCutProfiles.Batch311.profile12478,MergedCutProfiles.Batch311.profile12479,MergedCutProfiles.Batch312.profile12480]⟩
theorem profilesValid1983 : retention1983.ProfilesValid := by
  change ∀ j : Fin 16, (retention1983.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch311.valid12465
  · exact MergedCutProfiles.Batch311.valid12466
  · exact MergedCutProfiles.Batch311.valid12467
  · exact MergedCutProfiles.Batch311.valid12468
  · exact MergedCutProfiles.Batch311.valid12469
  · exact MergedCutProfiles.Batch311.valid12470
  · exact MergedCutProfiles.Batch311.valid12471
  · exact MergedCutProfiles.Batch311.valid12472
  · exact MergedCutProfiles.Batch311.valid12473
  · exact MergedCutProfiles.Batch311.valid12474
  · exact MergedCutProfiles.Batch311.valid12475
  · exact MergedCutProfiles.Batch311.valid12476
  · exact MergedCutProfiles.Batch311.valid12477
  · exact MergedCutProfiles.Batch311.valid12478
  · exact MergedCutProfiles.Batch311.valid12479
  · exact MergedCutProfiles.Batch312.valid12480
theorem numericValid1983 : retention1983.NumericValid := by decide +kernel
def certificate1983 : RatCutBinCertificate := ⟨⟨retention1983,(114582081168199667/62500000000000000),(4061079806220747/1000000000000000000),(3716558024871893587/500000000000000000),(8726715693851369783053/1000000000000000000),(63295211453876539/31250000000000000)⟩,(999790608096989649/1000000000000000000),(327437856581389731/1000000000000000000),(76745234582935373/250000000000000000),(25869168919768793/100000000000000000)⟩
theorem valid1983 : certificate1983.Valid := by decide +kernel
theorem sound1983 : certificate1983.Sound := rat_cut_bin_certificate_sound certificate1983 profilesValid1983 numericValid1983 valid1983

def retention1984 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(1/2),64,1,(62345958716102427160851921466530999/62500000000000000000000000000000000),false,MergedCutProfiles.Batch011.profile461,(fun _ => MergedCutProfiles.Batch011.profile461)⟩
theorem profilesValid1984 : retention1984.ProfilesValid := by
  exact MergedCutProfiles.Batch011.valid461
theorem numericValid1984 : retention1984.NumericValid := by decide +kernel
def certificate1984 : RatCutBinCertificate := ⟨⟨retention1984,(114582081168199667/62500000000000000),(4061079806220747/1000000000000000000),(3716558024871893587/500000000000000000),(8726715693851369783053/1000000000000000000),(996533709505933219/1000000000000000000)⟩,(999790608096989649/1000000000000000000),(211563291422173801/500000000000000000),(106474199362250359/500000000000000000),(208912503945639211/1000000000000000000)⟩
theorem valid1984 : certificate1984.Valid := by decide +kernel
theorem sound1984 : certificate1984.Sound := rat_cut_bin_certificate_sound certificate1984 profilesValid1984 numericValid1984 valid1984

def retention1985 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(8000000000000000000/146096017909295143181),(2373836221299913911/500000000000000000),(23/20),(3702122505328645433177059913712669390551/1899068977039931128800000000000000000000),false,MergedCutProfiles.Batch312.profile12481,(fun _ => MergedCutProfiles.Batch312.profile12481)⟩
theorem profilesValid1985 : retention1985.ProfilesValid := by
  exact MergedCutProfiles.Batch312.valid12481
theorem numericValid1985 : retention1985.NumericValid := by decide +kernel
def certificate1985 : RatCutBinCertificate := ⟨⟨retention1985,(131587682918199667/62500000000000000),(4061079806220747/1000000000000000000),(3716558024871893587/500000000000000000),(8726715693851369783053/1000000000000000000),(60878685926549159/31250000000000000)⟩,(999759531351894069/1000000000000000000),(31957930851050237/250000000000000000),(607499419984423193/1000000000000000000),(196304964070545911/250000000000000000)⟩
theorem valid1985 : certificate1985.Valid := by decide +kernel
theorem sound1985 : certificate1985.Sound := rat_cut_bin_certificate_sound certificate1985 profilesValid1985 numericValid1985 valid1985

def retention1986 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(1/2),64,1,(62345958716102427160851921466530999/62500000000000000000000000000000000),false,MergedCutProfiles.Batch011.profile461,(fun _ => MergedCutProfiles.Batch011.profile461)⟩
theorem profilesValid1986 : retention1986.ProfilesValid := by
  exact MergedCutProfiles.Batch011.valid461
theorem numericValid1986 : retention1986.NumericValid := by decide +kernel
def certificate1986 : RatCutBinCertificate := ⟨⟨retention1986,(131587682918199667/62500000000000000),(4061079806220747/1000000000000000000),(3716558024871893587/500000000000000000),(8726715693851369783053/1000000000000000000),(996385053451810991/1000000000000000000)⟩,(999759531351894069/1000000000000000000),(124967387876622441/500000000000000000),(100857952156877689/250000000000000000),(395715349694578967/1000000000000000000)⟩
theorem valid1986 : certificate1986.Valid := by decide +kernel
theorem sound1986 : certificate1986.Sound := rat_cut_bin_certificate_sound certificate1986 profilesValid1986 numericValid1986 valid1986

def retention1987 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(295801974092141673/480784384756872143102),(58574648335077559/100000000000000000),4,(5215898813067098942952452737819456231/2342985933403102360000000000000000000),true,MergedCutProfiles.Batch312.profile12482,![MergedCutProfiles.Batch312.profile12482,MergedCutProfiles.Batch312.profile12483,MergedCutProfiles.Batch312.profile12484,MergedCutProfiles.Batch011.profile463,MergedCutProfiles.Batch312.profile12485,MergedCutProfiles.Batch011.profile464,MergedCutProfiles.Batch312.profile12486,MergedCutProfiles.Batch312.profile12487,MergedCutProfiles.Batch312.profile12488,MergedCutProfiles.Batch011.profile466,MergedCutProfiles.Batch312.profile12489,MergedCutProfiles.Batch312.profile12490,MergedCutProfiles.Batch012.profile480,MergedCutProfiles.Batch312.profile12491,MergedCutProfiles.Batch312.profile12492,MergedCutProfiles.Batch312.profile12493]⟩
theorem profilesValid1987 : retention1987.ProfilesValid := by
  change ∀ j : Fin 16, (retention1987.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch312.valid12482
  · exact MergedCutProfiles.Batch312.valid12483
  · exact MergedCutProfiles.Batch312.valid12484
  · exact MergedCutProfiles.Batch011.valid463
  · exact MergedCutProfiles.Batch312.valid12485
  · exact MergedCutProfiles.Batch011.valid464
  · exact MergedCutProfiles.Batch312.valid12486
  · exact MergedCutProfiles.Batch312.valid12487
  · exact MergedCutProfiles.Batch312.valid12488
  · exact MergedCutProfiles.Batch011.valid466
  · exact MergedCutProfiles.Batch312.valid12489
  · exact MergedCutProfiles.Batch312.valid12490
  · exact MergedCutProfiles.Batch012.valid480
  · exact MergedCutProfiles.Batch312.valid12491
  · exact MergedCutProfiles.Batch312.valid12492
  · exact MergedCutProfiles.Batch312.valid12493
theorem numericValid1987 : retention1987.NumericValid := by decide +kernel
def certificate1987 : RatCutBinCertificate := ⟨⟨retention1987,(460068900054981793/250000000000000000),(246507623072377/50000000000000000),(7524782997285624993/1000000000000000000),(908546141764463021387/125000000000000000),(2221352985288252247/1000000000000000000)⟩,(2499369595866033/2500000000000000),(564259954144905993/1000000000000000000),(112847799964352943/1000000000000000000),(50645767157743643/1000000000000000000)⟩
theorem valid1987 : certificate1987.Valid := by decide +kernel
theorem sound1987 : certificate1987.Sound := rat_cut_bin_certificate_sound certificate1987 profilesValid1987 numericValid1987 valid1987

def retention1988 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(321494476250000000/240392192378436071551),(295801974092141673/500000000000000000),4,(4459530822159961609/2000000000000000000),true,MergedCutProfiles.Batch011.profile462,![MergedCutProfiles.Batch011.profile462,MergedCutProfiles.Batch011.profile478,MergedCutProfiles.Batch312.profile12494,MergedCutProfiles.Batch011.profile479,MergedCutProfiles.Batch312.profile12495,MergedCutProfiles.Batch012.profile480,MergedCutProfiles.Batch312.profile12492,MergedCutProfiles.Batch012.profile481,MergedCutProfiles.Batch312.profile12496,MergedCutProfiles.Batch312.profile12497,MergedCutProfiles.Batch312.profile12498,MergedCutProfiles.Batch012.profile483,MergedCutProfiles.Batch312.profile12499,MergedCutProfiles.Batch011.profile476,MergedCutProfiles.Batch312.profile12500,MergedCutProfiles.Batch012.profile485]⟩
theorem profilesValid1988 : retention1988.ProfilesValid := by
  change ∀ j : Fin 16, (retention1988.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch011.valid462
  · exact MergedCutProfiles.Batch011.valid478
  · exact MergedCutProfiles.Batch312.valid12494
  · exact MergedCutProfiles.Batch011.valid479
  · exact MergedCutProfiles.Batch312.valid12495
  · exact MergedCutProfiles.Batch012.valid480
  · exact MergedCutProfiles.Batch312.valid12492
  · exact MergedCutProfiles.Batch012.valid481
  · exact MergedCutProfiles.Batch312.valid12496
  · exact MergedCutProfiles.Batch312.valid12497
  · exact MergedCutProfiles.Batch312.valid12498
  · exact MergedCutProfiles.Batch012.valid483
  · exact MergedCutProfiles.Batch312.valid12499
  · exact MergedCutProfiles.Batch011.valid476
  · exact MergedCutProfiles.Batch312.valid12500
  · exact MergedCutProfiles.Batch012.valid485
theorem numericValid1988 : retention1988.NumericValid := by decide +kernel
def certificate1988 : RatCutBinCertificate := ⟨⟨retention1988,(460068900054981793/250000000000000000),(246507623072377/50000000000000000),(7524782997285624993/1000000000000000000),(908546141764463021387/125000000000000000),(2224942498906140963/1000000000000000000)⟩,(2499369595866033/2500000000000000),(559623371997583069/1000000000000000000),(115520139882292057/1000000000000000000),(52011630078156173/1000000000000000000)⟩
theorem valid1988 : certificate1988.Valid := by decide +kernel
theorem sound1988 : certificate1988.Sound := rat_cut_bin_certificate_sound certificate1988 profilesValid1988 numericValid1988 valid1988

def retention1989 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(1468054731259782921/480784384756872143102),(257195581/200000000),(12/5),(36673700281034965127/16000000000000000000),true,MergedCutProfiles.Batch312.profile12485,![MergedCutProfiles.Batch312.profile12485,MergedCutProfiles.Batch011.profile466,MergedCutProfiles.Batch312.profile12492,MergedCutProfiles.Batch312.profile12496,MergedCutProfiles.Batch011.profile473,MergedCutProfiles.Batch012.profile484,MergedCutProfiles.Batch012.profile485,MergedCutProfiles.Batch312.profile12501,MergedCutProfiles.Batch012.profile496,MergedCutProfiles.Batch312.profile12502,MergedCutProfiles.Batch312.profile12503,MergedCutProfiles.Batch012.profile491,MergedCutProfiles.Batch012.profile492,MergedCutProfiles.Batch012.profile493,MergedCutProfiles.Batch312.profile12504,MergedCutProfiles.Batch012.profile500]⟩
theorem profilesValid1989 : retention1989.ProfilesValid := by
  change ∀ j : Fin 16, (retention1989.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch312.valid12485
  · exact MergedCutProfiles.Batch011.valid466
  · exact MergedCutProfiles.Batch312.valid12492
  · exact MergedCutProfiles.Batch312.valid12496
  · exact MergedCutProfiles.Batch011.valid473
  · exact MergedCutProfiles.Batch012.valid484
  · exact MergedCutProfiles.Batch012.valid485
  · exact MergedCutProfiles.Batch312.valid12501
  · exact MergedCutProfiles.Batch012.valid496
  · exact MergedCutProfiles.Batch312.valid12502
  · exact MergedCutProfiles.Batch312.valid12503
  · exact MergedCutProfiles.Batch012.valid491
  · exact MergedCutProfiles.Batch012.valid492
  · exact MergedCutProfiles.Batch012.valid493
  · exact MergedCutProfiles.Batch312.valid12504
  · exact MergedCutProfiles.Batch012.valid500
theorem numericValid1989 : retention1989.NumericValid := by decide +kernel
def certificate1989 : RatCutBinCertificate := ⟨⟨retention1989,(460068900054981793/250000000000000000),(246507623072377/50000000000000000),(7524782997285624993/1000000000000000000),(908546141764463021387/125000000000000000),(2289212520453862731/1000000000000000000)⟩,(2499369595866033/2500000000000000),(13934335394001227/40000000000000000),(8883857117372017/31250000000000000),(51770870976252859/250000000000000000)⟩
theorem valid1989 : certificate1989.Valid := by decide +kernel
theorem sound1989 : certificate1989.Sound := rat_cut_bin_certificate_sound certificate1989 profilesValid1989 numericValid1989 valid1989

def retention1990 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(16000000000000000000/240392192378436071551),(1468054731259782921/500000000000000000),(3/2),(253227808036241754609/128000000000000000000),true,MergedCutProfiles.Batch312.profile12505,![MergedCutProfiles.Batch312.profile12505,MergedCutProfiles.Batch312.profile12506,MergedCutProfiles.Batch312.profile12507,MergedCutProfiles.Batch312.profile12508,MergedCutProfiles.Batch312.profile12509,MergedCutProfiles.Batch312.profile12510,MergedCutProfiles.Batch312.profile12511,MergedCutProfiles.Batch312.profile12512,MergedCutProfiles.Batch312.profile12513,MergedCutProfiles.Batch312.profile12514,MergedCutProfiles.Batch312.profile12515,MergedCutProfiles.Batch312.profile12516,MergedCutProfiles.Batch312.profile12517,MergedCutProfiles.Batch312.profile12518,MergedCutProfiles.Batch312.profile12519,MergedCutProfiles.Batch313.profile12520]⟩
theorem profilesValid1990 : retention1990.ProfilesValid := by
  change ∀ j : Fin 16, (retention1990.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch312.valid12505
  · exact MergedCutProfiles.Batch312.valid12506
  · exact MergedCutProfiles.Batch312.valid12507
  · exact MergedCutProfiles.Batch312.valid12508
  · exact MergedCutProfiles.Batch312.valid12509
  · exact MergedCutProfiles.Batch312.valid12510
  · exact MergedCutProfiles.Batch312.valid12511
  · exact MergedCutProfiles.Batch312.valid12512
  · exact MergedCutProfiles.Batch312.valid12513
  · exact MergedCutProfiles.Batch312.valid12514
  · exact MergedCutProfiles.Batch312.valid12515
  · exact MergedCutProfiles.Batch312.valid12516
  · exact MergedCutProfiles.Batch312.valid12517
  · exact MergedCutProfiles.Batch312.valid12518
  · exact MergedCutProfiles.Batch312.valid12519
  · exact MergedCutProfiles.Batch313.valid12520
theorem numericValid1990 : retention1990.NumericValid := by decide +kernel
def certificate1990 : RatCutBinCertificate := ⟨⟨retention1990,(460068900054981793/250000000000000000),(246507623072377/50000000000000000),(7524782997285624993/1000000000000000000),(908546141764463021387/125000000000000000),(1976533658457809897/1000000000000000000)⟩,(2499369595866033/2500000000000000),(73754169900663561/250000000000000000),(344823279572185679/1000000000000000000),(349636120996564893/1000000000000000000)⟩
theorem valid1990 : certificate1990.Valid := by decide +kernel
theorem sound1990 : certificate1990.Sound := rat_cut_bin_certificate_sound certificate1990 profilesValid1990 numericValid1990 valid1990

def retention1991 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(1/2),64,1,(63842289268809469711650675485864946351/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch012.profile509,(fun _ => MergedCutProfiles.Batch012.profile509)⟩
theorem profilesValid1991 : retention1991.ProfilesValid := by
  exact MergedCutProfiles.Batch012.valid509
theorem numericValid1991 : retention1991.NumericValid := by decide +kernel
def certificate1991 : RatCutBinCertificate := ⟨⟨retention1991,(460068900054981793/250000000000000000),(246507623072377/50000000000000000),(7524782997285624993/1000000000000000000),(908546141764463021387/125000000000000000),(996330042114515353/1000000000000000000)⟩,(2499369595866033/2500000000000000),(42528338395637169/100000000000000000),(211098899588828281/1000000000000000000),(103523724388823299/500000000000000000)⟩
theorem valid1991 : certificate1991.Valid := by decide +kernel
theorem sound1991 : certificate1991.Sound := rat_cut_bin_certificate_sound certificate1991 profilesValid1991 numericValid1991 valid1991

def certificates : List RatCutBinCertificate := [certificate1980,certificate1981,certificate1982,certificate1983,certificate1984,certificate1985,certificate1986,certificate1987,certificate1988,certificate1989,certificate1990,certificate1991]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1980,List.forall_mem_cons.mpr ⟨sound1981,List.forall_mem_cons.mpr ⟨sound1982,List.forall_mem_cons.mpr ⟨sound1983,List.forall_mem_cons.mpr ⟨sound1984,List.forall_mem_cons.mpr ⟨sound1985,List.forall_mem_cons.mpr ⟨sound1986,List.forall_mem_cons.mpr ⟨sound1987,List.forall_mem_cons.mpr ⟨sound1988,List.forall_mem_cons.mpr ⟨sound1989,List.forall_mem_cons.mpr ⟨sound1990,List.forall_mem_cons.mpr ⟨sound1991,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch165
