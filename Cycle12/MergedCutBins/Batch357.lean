import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch435
import Cycle12.MergedCutProfiles.Batch436
import Cycle12.MergedCutProfiles.Batch437
import Cycle12.MergedCutProfiles.Batch555
import Cycle12.MergedCutProfiles.Batch556
import Cycle12.MergedCutProfiles.Batch557
import Cycle12.MergedCutProfiles.Batch641
import Cycle12.MergedCutProfiles.Batch642
import Cycle12.MergedCutProfiles.Batch643

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch357

def retention4284 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(1133685655000000000/191686014252223588973),(860920711132466143/1000000000000000000),(16/5),(186554892739455016987/80000000000000000000),true,MergedCutProfiles.Batch641.profile25651,![MergedCutProfiles.Batch641.profile25651,MergedCutProfiles.Batch641.profile25652,MergedCutProfiles.Batch641.profile25640,MergedCutProfiles.Batch555.profile22230,MergedCutProfiles.Batch641.profile25653,MergedCutProfiles.Batch641.profile25654,MergedCutProfiles.Batch641.profile25655,MergedCutProfiles.Batch641.profile25656,MergedCutProfiles.Batch641.profile25646,MergedCutProfiles.Batch641.profile25657,MergedCutProfiles.Batch641.profile25658,MergedCutProfiles.Batch641.profile25659,MergedCutProfiles.Batch641.profile25660,MergedCutProfiles.Batch641.profile25661,MergedCutProfiles.Batch641.profile25662,MergedCutProfiles.Batch641.profile25663]⟩
theorem profilesValid4284 : retention4284.ProfilesValid := by
  change ∀ j : Fin 16, (retention4284.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch641.valid25651
  · exact MergedCutProfiles.Batch641.valid25652
  · exact MergedCutProfiles.Batch641.valid25640
  · exact MergedCutProfiles.Batch555.valid22230
  · exact MergedCutProfiles.Batch641.valid25653
  · exact MergedCutProfiles.Batch641.valid25654
  · exact MergedCutProfiles.Batch641.valid25655
  · exact MergedCutProfiles.Batch641.valid25656
  · exact MergedCutProfiles.Batch641.valid25646
  · exact MergedCutProfiles.Batch641.valid25657
  · exact MergedCutProfiles.Batch641.valid25658
  · exact MergedCutProfiles.Batch641.valid25659
  · exact MergedCutProfiles.Batch641.valid25660
  · exact MergedCutProfiles.Batch641.valid25661
  · exact MergedCutProfiles.Batch641.valid25662
  · exact MergedCutProfiles.Batch641.valid25663
theorem numericValid4284 : retention4284.NumericValid := by decide +kernel
def certificate4284 : RatCutBinCertificate := ⟨⟨retention4284,(2168398067693551319/1000000000000000000),(11895173549139047/50000000000000000),(8970312836421882251/500000000000000000),(3450002997137746146889/1000000000000000000),(279990027753876427/125000000000000000)⟩,(499759109067024997/500000000000000000),(377117346579133829/1000000000000000000),(25511558184781231/100000000000000000),(142311541238750423/1000000000000000000)⟩
theorem valid4284 : certificate4284.Valid := by decide +kernel
theorem sound4284 : certificate4284.Sound := rat_cut_bin_certificate_sound certificate4284 profilesValid4284 numericValid4284 valid4284

def retention4285 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(1444357139324937853/191686014252223588973),(226737131/200000000),(13/5),(9266883967033915199/4000000000000000000),true,MergedCutProfiles.Batch641.profile25664,![MergedCutProfiles.Batch641.profile25664,MergedCutProfiles.Batch641.profile25665,MergedCutProfiles.Batch641.profile25641,MergedCutProfiles.Batch641.profile25653,MergedCutProfiles.Batch641.profile25666,MergedCutProfiles.Batch641.profile25644,MergedCutProfiles.Batch641.profile25667,MergedCutProfiles.Batch555.profile22208,MergedCutProfiles.Batch641.profile25668,MergedCutProfiles.Batch641.profile25669,MergedCutProfiles.Batch641.profile25661,MergedCutProfiles.Batch641.profile25670,MergedCutProfiles.Batch641.profile25671,MergedCutProfiles.Batch641.profile25672,MergedCutProfiles.Batch641.profile25673,MergedCutProfiles.Batch555.profile22211]⟩
theorem profilesValid4285 : retention4285.ProfilesValid := by
  change ∀ j : Fin 16, (retention4285.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch641.valid25664
  · exact MergedCutProfiles.Batch641.valid25665
  · exact MergedCutProfiles.Batch641.valid25641
  · exact MergedCutProfiles.Batch641.valid25653
  · exact MergedCutProfiles.Batch641.valid25666
  · exact MergedCutProfiles.Batch641.valid25644
  · exact MergedCutProfiles.Batch641.valid25667
  · exact MergedCutProfiles.Batch555.valid22208
  · exact MergedCutProfiles.Batch641.valid25668
  · exact MergedCutProfiles.Batch641.valid25669
  · exact MergedCutProfiles.Batch641.valid25661
  · exact MergedCutProfiles.Batch641.valid25670
  · exact MergedCutProfiles.Batch641.valid25671
  · exact MergedCutProfiles.Batch641.valid25672
  · exact MergedCutProfiles.Batch641.valid25673
  · exact MergedCutProfiles.Batch555.valid22211
theorem numericValid4285 : retention4285.NumericValid := by decide +kernel
def certificate4285 : RatCutBinCertificate := ⟨⟨retention4285,(2168398067693551319/1000000000000000000),(11895173549139047/50000000000000000),(8970312836421882251/500000000000000000),(3450002997137746146889/1000000000000000000),(448391633014136107/200000000000000000)⟩,(499759109067024997/500000000000000000),(1317951739905127/4000000000000000),(38087389926935049/125000000000000000),(101578199414774001/500000000000000000)⟩
theorem valid4285 : certificate4285.Valid := by decide +kernel
theorem sound4285 : certificate4285.Sound := rat_cut_bin_certificate_sound certificate4285 profilesValid4285 numericValid4285 valid4285

def retention4286 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(14242642142982275138/191686014252223588973),(1444357139324937853/1000000000000000000),(43/20),(2571237363752463398941/1280000000000000000000),true,MergedCutProfiles.Batch641.profile25674,![MergedCutProfiles.Batch641.profile25674,MergedCutProfiles.Batch641.profile25675,MergedCutProfiles.Batch641.profile25676,MergedCutProfiles.Batch556.profile22251,MergedCutProfiles.Batch556.profile22242,MergedCutProfiles.Batch641.profile25677,MergedCutProfiles.Batch641.profile25678,MergedCutProfiles.Batch641.profile25679,MergedCutProfiles.Batch435.profile17409,MergedCutProfiles.Batch642.profile25680,MergedCutProfiles.Batch642.profile25681,MergedCutProfiles.Batch642.profile25682,MergedCutProfiles.Batch642.profile25683,MergedCutProfiles.Batch642.profile25684,MergedCutProfiles.Batch642.profile25685,MergedCutProfiles.Batch556.profile22270]⟩
theorem profilesValid4286 : retention4286.ProfilesValid := by
  change ∀ j : Fin 16, (retention4286.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch641.valid25674
  · exact MergedCutProfiles.Batch641.valid25675
  · exact MergedCutProfiles.Batch641.valid25676
  · exact MergedCutProfiles.Batch556.valid22251
  · exact MergedCutProfiles.Batch556.valid22242
  · exact MergedCutProfiles.Batch641.valid25677
  · exact MergedCutProfiles.Batch641.valid25678
  · exact MergedCutProfiles.Batch641.valid25679
  · exact MergedCutProfiles.Batch435.valid17409
  · exact MergedCutProfiles.Batch642.valid25680
  · exact MergedCutProfiles.Batch642.valid25681
  · exact MergedCutProfiles.Batch642.valid25682
  · exact MergedCutProfiles.Batch642.valid25683
  · exact MergedCutProfiles.Batch642.valid25684
  · exact MergedCutProfiles.Batch642.valid25685
  · exact MergedCutProfiles.Batch556.valid22270
theorem numericValid4286 : retention4286.NumericValid := by decide +kernel
def certificate4286 : RatCutBinCertificate := ⟨⟨retention4286,(2168398067693551319/1000000000000000000),(11895173549139047/50000000000000000),(8970312836421882251/500000000000000000),(3450002997137746146889/1000000000000000000),(121684759827138781/62500000000000000)⟩,(499759109067024997/500000000000000000),(17122254623982489/50000000000000000),(145284252105295783/500000000000000000),(203603947209271853/1000000000000000000)⟩
theorem valid4286 : certificate4286.Valid := by decide +kernel
theorem sound4286 : certificate4286.Sound := rat_cut_bin_certificate_sound certificate4286 profilesValid4286 numericValid4286 valid4286

def retention4287 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(64000000000000000000/191686014252223588973),(7121321071491137569/500000000000000000),1,(14978120109276526155441569763825237771/11394113714385820110400000000000000000),false,MergedCutProfiles.Batch642.profile25686,(fun _ => MergedCutProfiles.Batch642.profile25686)⟩
theorem profilesValid4287 : retention4287.ProfilesValid := by
  exact MergedCutProfiles.Batch642.valid25686
theorem numericValid4287 : retention4287.NumericValid := by decide +kernel
def certificate4287 : RatCutBinCertificate := ⟨⟨retention4287,(2168398067693551319/1000000000000000000),(11895173549139047/50000000000000000),(8970312836421882251/500000000000000000),(3450002997137746146889/1000000000000000000),(1285794540467988199/1000000000000000000)⟩,(499759109067024997/500000000000000000),(334984675766328781/1000000000000000000),(298643608927549423/1000000000000000000),(352020783194034063/1000000000000000000)⟩
theorem valid4287 : certificate4287.Valid := by decide +kernel
theorem sound4287 : certificate4287.Sound := rat_cut_bin_certificate_sound certificate4287 profilesValid4287 numericValid4287 valid4287

def retention4288 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(1/2),64,1,(255418975141339024894181828804947859719/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch436.profile17478,(fun _ => MergedCutProfiles.Batch436.profile17478)⟩
theorem profilesValid4288 : retention4288.ProfilesValid := by
  exact MergedCutProfiles.Batch436.valid17478
theorem numericValid4288 : retention4288.NumericValid := by decide +kernel
def certificate4288 : RatCutBinCertificate := ⟨⟨retention4288,(2168398067693551319/1000000000000000000),(11895173549139047/50000000000000000),(8970312836421882251/500000000000000000),(3450002997137746146889/1000000000000000000),(30280502500523471/31250000000000000)⟩,(499759109067024997/500000000000000000),(423141865386434777/1000000000000000000),(212935255047831089/1000000000000000000),(203152838654175771/1000000000000000000)⟩
theorem valid4288 : certificate4288.Valid := by decide +kernel
theorem sound4288 : certificate4288.Sound := rat_cut_bin_certificate_sound certificate4288 profilesValid4288 numericValid4288 valid4288

def retention4289 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(64000000000000000000/191686014252223588973),(22481671574538696189/1000000000000000000),1,(7950775778015142568478548515128055501/5995112419876985650400000000000000000),false,MergedCutProfiles.Batch642.profile25686,(fun _ => MergedCutProfiles.Batch642.profile25686)⟩
theorem profilesValid4289 : retention4289.ProfilesValid := by
  exact MergedCutProfiles.Batch642.valid25686
theorem numericValid4289 : retention4289.NumericValid := by decide +kernel
def certificate4289 : RatCutBinCertificate := ⟨⟨retention4289,(1963475090693551319/1000000000000000000),(11895173549139047/50000000000000000),(8970312836421882251/500000000000000000),(3450002997137746146889/1000000000000000000),(1300172683536091301/1000000000000000000)⟩,(499781877326671861/500000000000000000),(38048964684473599/1000000000000000000),(821213090700478691/1000000000000000000),(100889022540510691/100000000000000000)⟩
theorem valid4289 : certificate4289.Valid := by decide +kernel
theorem sound4289 : certificate4289.Sound := rat_cut_bin_certificate_sound certificate4289 profilesValid4289 numericValid4289 valid4289

def retention4290 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(1/2),64,1,(255418975141339024894181828804947859719/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch436.profile17478,(fun _ => MergedCutProfiles.Batch436.profile17478)⟩
theorem profilesValid4290 : retention4290.ProfilesValid := by
  exact MergedCutProfiles.Batch436.valid17478
theorem numericValid4290 : retention4290.NumericValid := by decide +kernel
def certificate4290 : RatCutBinCertificate := ⟨⟨retention4290,(1963475090693551319/1000000000000000000),(11895173549139047/50000000000000000),(8970312836421882251/500000000000000000),(3450002997137746146889/1000000000000000000),(242923371172447873/250000000000000000)⟩,(499781877326671861/500000000000000000),(50911347352889929/1000000000000000000),(157185591273126433/200000000000000000),(751927408882066247/1000000000000000000)⟩
theorem valid4290 : certificate4290.Valid := by decide +kernel
theorem sound4290 : certificate4290.Sound := rat_cut_bin_certificate_sound certificate4290 profilesValid4290 numericValid4290 valid4290

def retention4291 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(860324639638174895/188250500663949540382),(106475821737397883/125000000000000000),(13/4),(4697674611250551089/2000000000000000000),true,MergedCutProfiles.Batch642.profile25687,![MergedCutProfiles.Batch642.profile25687,MergedCutProfiles.Batch642.profile25688,MergedCutProfiles.Batch642.profile25689,MergedCutProfiles.Batch642.profile25690,MergedCutProfiles.Batch642.profile25691,MergedCutProfiles.Batch642.profile25692,MergedCutProfiles.Batch642.profile25693,MergedCutProfiles.Batch642.profile25694,MergedCutProfiles.Batch557.profile22290,MergedCutProfiles.Batch642.profile25695,MergedCutProfiles.Batch642.profile25696,MergedCutProfiles.Batch642.profile25697,MergedCutProfiles.Batch642.profile25698,MergedCutProfiles.Batch642.profile25699,MergedCutProfiles.Batch642.profile25700,MergedCutProfiles.Batch557.profile22318]⟩
theorem profilesValid4291 : retention4291.ProfilesValid := by
  change ∀ j : Fin 16, (retention4291.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch642.valid25687
  · exact MergedCutProfiles.Batch642.valid25688
  · exact MergedCutProfiles.Batch642.valid25689
  · exact MergedCutProfiles.Batch642.valid25690
  · exact MergedCutProfiles.Batch642.valid25691
  · exact MergedCutProfiles.Batch642.valid25692
  · exact MergedCutProfiles.Batch642.valid25693
  · exact MergedCutProfiles.Batch642.valid25694
  · exact MergedCutProfiles.Batch557.valid22290
  · exact MergedCutProfiles.Batch642.valid25695
  · exact MergedCutProfiles.Batch642.valid25696
  · exact MergedCutProfiles.Batch642.valid25697
  · exact MergedCutProfiles.Batch642.valid25698
  · exact MergedCutProfiles.Batch642.valid25699
  · exact MergedCutProfiles.Batch642.valid25700
  · exact MergedCutProfiles.Batch557.valid22318
theorem numericValid4291 : retention4291.NumericValid := by decide +kernel
def certificate4291 : RatCutBinCertificate := ⟨⟨retention4291,(272103648983192311/125000000000000000),(121143195939341811/500000000000000000),(9058362351615182299/500000000000000000),(1710732776214571575263/500000000000000000),(2254220526457806209/1000000000000000000)⟩,(199903011976271717/200000000000000000),(92627699482875357/250000000000000000),(16350995244918859/62500000000000000),(29003544308087843/200000000000000000)⟩
theorem valid4291 : certificate4291.Valid := by decide +kernel
theorem sound4291 : certificate4291.Sound := rat_cut_bin_certificate_sound certificate4291 profilesValid4291 numericValid4291 valid4291

def retention4292 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(572716836500000000/94125250331974770191),(172064927927634979/200000000000000000),(16/5),(37299594283216247011/16000000000000000000),true,MergedCutProfiles.Batch642.profile25701,![MergedCutProfiles.Batch642.profile25701,MergedCutProfiles.Batch642.profile25702,MergedCutProfiles.Batch642.profile25690,MergedCutProfiles.Batch557.profile22316,MergedCutProfiles.Batch642.profile25703,MergedCutProfiles.Batch642.profile25694,MergedCutProfiles.Batch642.profile25704,MergedCutProfiles.Batch557.profile22317,MergedCutProfiles.Batch642.profile25697,MergedCutProfiles.Batch437.profile17498,MergedCutProfiles.Batch642.profile25705,MergedCutProfiles.Batch557.profile22318,MergedCutProfiles.Batch642.profile25706,MergedCutProfiles.Batch642.profile25707,MergedCutProfiles.Batch642.profile25708,MergedCutProfiles.Batch557.profile22319]⟩
theorem profilesValid4292 : retention4292.ProfilesValid := by
  change ∀ j : Fin 16, (retention4292.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch642.valid25701
  · exact MergedCutProfiles.Batch642.valid25702
  · exact MergedCutProfiles.Batch642.valid25690
  · exact MergedCutProfiles.Batch557.valid22316
  · exact MergedCutProfiles.Batch642.valid25703
  · exact MergedCutProfiles.Batch642.valid25694
  · exact MergedCutProfiles.Batch642.valid25704
  · exact MergedCutProfiles.Batch557.valid22317
  · exact MergedCutProfiles.Batch642.valid25697
  · exact MergedCutProfiles.Batch437.valid17498
  · exact MergedCutProfiles.Batch642.valid25705
  · exact MergedCutProfiles.Batch557.valid22318
  · exact MergedCutProfiles.Batch642.valid25706
  · exact MergedCutProfiles.Batch642.valid25707
  · exact MergedCutProfiles.Batch642.valid25708
  · exact MergedCutProfiles.Batch557.valid22319
theorem numericValid4292 : retention4292.NumericValid := by decide +kernel
def certificate4292 : RatCutBinCertificate := ⟨⟨retention4292,(272103648983192311/125000000000000000),(121143195939341811/500000000000000000),(9058362351615182299/500000000000000000),(1710732776214571575263/500000000000000000),(447612698603710167/200000000000000000)⟩,(199903011976271717/200000000000000000),(9281353054578821/25000000000000000),(260878711739105609/1000000000000000000),(72704571114570669/500000000000000000)⟩
theorem valid4292 : certificate4292.Valid := by decide +kernel
theorem sound4292 : certificate4292.Sound := rat_cut_bin_certificate_sound certificate4292 profilesValid4292 numericValid4292 valid4292

def retention4293 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(846224866068938610/94125250331974770191),(1145433673/1000000000),(13/5),(3699063518999691219/1600000000000000000),true,MergedCutProfiles.Batch642.profile25688,![MergedCutProfiles.Batch642.profile25688,MergedCutProfiles.Batch642.profile25709,MergedCutProfiles.Batch642.profile25692,MergedCutProfiles.Batch642.profile25694,MergedCutProfiles.Batch642.profile25710,MergedCutProfiles.Batch642.profile25711,MergedCutProfiles.Batch642.profile25712,MergedCutProfiles.Batch642.profile25713,MergedCutProfiles.Batch642.profile25714,MergedCutProfiles.Batch642.profile25715,MergedCutProfiles.Batch642.profile25716,MergedCutProfiles.Batch642.profile25717,MergedCutProfiles.Batch557.profile22308,MergedCutProfiles.Batch642.profile25718,MergedCutProfiles.Batch642.profile25719,MergedCutProfiles.Batch557.profile22294]⟩
theorem profilesValid4293 : retention4293.ProfilesValid := by
  change ∀ j : Fin 16, (retention4293.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch642.valid25688
  · exact MergedCutProfiles.Batch642.valid25709
  · exact MergedCutProfiles.Batch642.valid25692
  · exact MergedCutProfiles.Batch642.valid25694
  · exact MergedCutProfiles.Batch642.valid25710
  · exact MergedCutProfiles.Batch642.valid25711
  · exact MergedCutProfiles.Batch642.valid25712
  · exact MergedCutProfiles.Batch642.valid25713
  · exact MergedCutProfiles.Batch642.valid25714
  · exact MergedCutProfiles.Batch642.valid25715
  · exact MergedCutProfiles.Batch642.valid25716
  · exact MergedCutProfiles.Batch642.valid25717
  · exact MergedCutProfiles.Batch557.valid22308
  · exact MergedCutProfiles.Batch642.valid25718
  · exact MergedCutProfiles.Batch642.valid25719
  · exact MergedCutProfiles.Batch557.valid22294
theorem numericValid4293 : retention4293.NumericValid := by decide +kernel
def certificate4293 : RatCutBinCertificate := ⟨⟨retention4293,(272103648983192311/125000000000000000),(121143195939341811/500000000000000000),(9058362351615182299/500000000000000000),(1710732776214571575263/500000000000000000),(2236221412408376263/1000000000000000000)⟩,(199903011976271717/200000000000000000),(1617221547079617/5000000000000000),(31146274641728161/100000000000000000),(207735185583998259/1000000000000000000)⟩
theorem valid4293 : certificate4293.Valid := by decide +kernel
theorem sound4293 : certificate4293.Sound := rat_cut_bin_certificate_sound certificate4293 profilesValid4293 numericValid4293 valid4293

def retention4294 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(11703842300900208610/94125250331974770191),(84622486606893861/50000000000000000),(39/20),(836670195805544774384996084108154393/451319928570100592000000000000000000),false,MergedCutProfiles.Batch643.profile25720,(fun _ => MergedCutProfiles.Batch643.profile25720)⟩
theorem profilesValid4294 : retention4294.ProfilesValid := by
  exact MergedCutProfiles.Batch643.valid25720
theorem numericValid4294 : retention4294.NumericValid := by decide +kernel
def certificate4294 : RatCutBinCertificate := ⟨⟨retention4294,(272103648983192311/125000000000000000),(121143195939341811/500000000000000000),(9058362351615182299/500000000000000000),(1710732776214571575263/500000000000000000),(449264915683868241/250000000000000000)⟩,(199903011976271717/200000000000000000),(86023041084083009/250000000000000000),(288807709642256507/1000000000000000000),(2079393321366981/10000000000000000)⟩
theorem valid4294 : certificate4294.Valid := by decide +kernel
theorem sound4294 : certificate4294.Sound := rat_cut_bin_certificate_sound certificate4294 profilesValid4294 numericValid4294 valid4294

def retention4295 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(32000000000000000000/94125250331974770191),(1170384230090020861/50000000000000000),1,(307633419715828218141124195173225283/234076846018004172200000000000000000),false,MergedCutProfiles.Batch643.profile25721,(fun _ => MergedCutProfiles.Batch643.profile25721)⟩
theorem profilesValid4295 : retention4295.ProfilesValid := by
  exact MergedCutProfiles.Batch643.valid25721
theorem numericValid4295 : retention4295.NumericValid := by decide +kernel
def certificate4295 : RatCutBinCertificate := ⟨⟨retention4295,(272103648983192311/125000000000000000),(121143195939341811/500000000000000000),(9058362351615182299/500000000000000000),(1710732776214571575263/500000000000000000),(321282234041682433/250000000000000000)⟩,(199903011976271717/200000000000000000),(161269130927106323/500000000000000000),(312486391333184553/1000000000000000000),(76098945813858157/200000000000000000)⟩
theorem valid4295 : certificate4295.Valid := by decide +kernel
theorem sound4295 : certificate4295.Sound := rat_cut_bin_certificate_sound certificate4295 profilesValid4295 numericValid4295 valid4295

def certificates : List RatCutBinCertificate := [certificate4284,certificate4285,certificate4286,certificate4287,certificate4288,certificate4289,certificate4290,certificate4291,certificate4292,certificate4293,certificate4294,certificate4295]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4284,List.forall_mem_cons.mpr ⟨sound4285,List.forall_mem_cons.mpr ⟨sound4286,List.forall_mem_cons.mpr ⟨sound4287,List.forall_mem_cons.mpr ⟨sound4288,List.forall_mem_cons.mpr ⟨sound4289,List.forall_mem_cons.mpr ⟨sound4290,List.forall_mem_cons.mpr ⟨sound4291,List.forall_mem_cons.mpr ⟨sound4292,List.forall_mem_cons.mpr ⟨sound4293,List.forall_mem_cons.mpr ⟨sound4294,List.forall_mem_cons.mpr ⟨sound4295,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch357
