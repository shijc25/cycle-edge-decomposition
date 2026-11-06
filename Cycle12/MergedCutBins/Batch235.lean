import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch008
import Cycle12.MergedCutProfiles.Batch009
import Cycle12.MergedCutProfiles.Batch010
import Cycle12.MergedCutProfiles.Batch011
import Cycle12.MergedCutProfiles.Batch310
import Cycle12.MergedCutProfiles.Batch311
import Cycle12.MergedCutProfiles.Batch444
import Cycle12.MergedCutProfiles.Batch445
import Cycle12.MergedCutProfiles.Batch446

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch235

def retention2820 : RatCutRetentionCertificate := ⟨(3/400),(1/125),(1/2),64,1,(63842245492489957688683474884787466679/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch444.profile17792,(fun _ => MergedCutProfiles.Batch444.profile17792)⟩
theorem profilesValid2820 : retention2820.ProfilesValid := by
  exact MergedCutProfiles.Batch444.valid17792
theorem numericValid2820 : retention2820.NumericValid := by decide +kernel
def certificate2820 : RatCutBinCertificate := ⟨⟨retention2820,(1953702420852871401/1000000000000000000),(1291114465089419/500000000000000000),(3649407053359982287/500000000000000000),(16848798986218848632169/500000000000000000),(498421945197602671/500000000000000000)⟩,(99994215386497187/100000000000000000),(73977739170787851/500000000000000000),(568270521444589323/1000000000000000000),(278878264570067371/500000000000000000)⟩
theorem valid2820 : certificate2820.Valid := by decide +kernel
theorem sound2820 : certificate2820.Sound := rat_cut_bin_certificate_sound certificate2820 profilesValid2820 numericValid2820 valid2820

def retention2821 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(15129693303803130/86275128238928013959),(28763099350521389/50000000000000000),4,(40680389766088365265275785895982571/18408383584333688960000000000000000),true,MergedCutProfiles.Batch444.profile17794,![MergedCutProfiles.Batch444.profile17794,MergedCutProfiles.Batch444.profile17795,MergedCutProfiles.Batch444.profile17796,MergedCutProfiles.Batch444.profile17797,MergedCutProfiles.Batch310.profile12420,MergedCutProfiles.Batch444.profile17798,MergedCutProfiles.Batch444.profile17799,MergedCutProfiles.Batch445.profile17800,MergedCutProfiles.Batch008.profile357,MergedCutProfiles.Batch009.profile372,MergedCutProfiles.Batch445.profile17801,MergedCutProfiles.Batch310.profile12415,MergedCutProfiles.Batch445.profile17802,MergedCutProfiles.Batch008.profile358,MergedCutProfiles.Batch310.profile12421,MergedCutProfiles.Batch310.profile12426]⟩
theorem profilesValid2821 : retention2821.ProfilesValid := by
  change ∀ j : Fin 16, (retention2821.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch444.valid17794
  · exact MergedCutProfiles.Batch444.valid17795
  · exact MergedCutProfiles.Batch444.valid17796
  · exact MergedCutProfiles.Batch444.valid17797
  · exact MergedCutProfiles.Batch310.valid12420
  · exact MergedCutProfiles.Batch444.valid17798
  · exact MergedCutProfiles.Batch444.valid17799
  · exact MergedCutProfiles.Batch445.valid17800
  · exact MergedCutProfiles.Batch008.valid357
  · exact MergedCutProfiles.Batch009.valid372
  · exact MergedCutProfiles.Batch445.valid17801
  · exact MergedCutProfiles.Batch310.valid12415
  · exact MergedCutProfiles.Batch445.valid17802
  · exact MergedCutProfiles.Batch008.valid358
  · exact MergedCutProfiles.Batch310.valid12421
  · exact MergedCutProfiles.Batch310.valid12426
theorem numericValid2821 : retention2821.NumericValid := by decide +kernel
def certificate2821 : RatCutBinCertificate := ⟨⟨retention2821,(452391586261936147/250000000000000000),(3278736788116277/1000000000000000000),(7343162173420266947/1000000000000000000),(167046958857763097523/6250000000000000),(2206651959365015637/1000000000000000000)⟩,(19998649411250573/20000000000000000),(591861110319736011/1000000000000000000),(97717630315408139/1000000000000000000),(21739504303713813/500000000000000000)⟩
theorem valid2821 : certificate2821.Valid := by decide +kernel
theorem sound2821 : certificate2821.Sound := rat_cut_bin_certificate_sound certificate2821 profilesValid2821 numericValid2821 valid2821

def retention2822 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(216404412500000000/603925897672496097713),(31772355937986573/50000000000000000),4,(7386391122766193711/3200000000000000000),true,MergedCutProfiles.Batch444.profile17795,![MergedCutProfiles.Batch444.profile17795,MergedCutProfiles.Batch444.profile17797,MergedCutProfiles.Batch444.profile17798,MergedCutProfiles.Batch445.profile17800,MergedCutProfiles.Batch009.profile372,MergedCutProfiles.Batch310.profile12415,MergedCutProfiles.Batch008.profile358,MergedCutProfiles.Batch310.profile12426,MergedCutProfiles.Batch008.profile359,MergedCutProfiles.Batch009.profile373,MergedCutProfiles.Batch445.profile17803,MergedCutProfiles.Batch009.profile360,MergedCutProfiles.Batch310.profile12422,MergedCutProfiles.Batch009.profile361,MergedCutProfiles.Batch009.profile374,MergedCutProfiles.Batch310.profile12419]⟩
theorem profilesValid2822 : retention2822.ProfilesValid := by
  change ∀ j : Fin 16, (retention2822.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch444.valid17795
  · exact MergedCutProfiles.Batch444.valid17797
  · exact MergedCutProfiles.Batch444.valid17798
  · exact MergedCutProfiles.Batch445.valid17800
  · exact MergedCutProfiles.Batch009.valid372
  · exact MergedCutProfiles.Batch310.valid12415
  · exact MergedCutProfiles.Batch008.valid358
  · exact MergedCutProfiles.Batch310.valid12426
  · exact MergedCutProfiles.Batch008.valid359
  · exact MergedCutProfiles.Batch009.valid373
  · exact MergedCutProfiles.Batch445.valid17803
  · exact MergedCutProfiles.Batch009.valid360
  · exact MergedCutProfiles.Batch310.valid12422
  · exact MergedCutProfiles.Batch009.valid361
  · exact MergedCutProfiles.Batch009.valid374
  · exact MergedCutProfiles.Batch310.valid12419
theorem numericValid2822 : retention2822.NumericValid := by decide +kernel
def certificate2822 : RatCutBinCertificate := ⟨⟨retention2822,(452391586261936147/250000000000000000),(3278736788116277/1000000000000000000),(7343162173420266947/1000000000000000000),(167046958857763097523/6250000000000000),(1152507662775522073/500000000000000000)⟩,(19998649411250573/20000000000000000),(6623664670690979/12500000000000000),(5343293246059427/40000000000000000),(31372974298152233/500000000000000000)⟩
theorem valid2822 : certificate2822.Valid := by decide +kernel
theorem sound2822 : certificate2822.Sound := rat_cut_bin_certificate_sound certificate2822 profilesValid2822 numericValid2822 valid2822

def retention2823 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(1184556621016915875/1207851795344992195426),(51937059/40000000),(49/20),(4672946511877829879/2000000000000000000),true,MergedCutProfiles.Batch444.profile17798,![MergedCutProfiles.Batch444.profile17798,MergedCutProfiles.Batch445.profile17801,MergedCutProfiles.Batch310.profile12426,MergedCutProfiles.Batch445.profile17803,MergedCutProfiles.Batch310.profile12418,MergedCutProfiles.Batch009.profile362,MergedCutProfiles.Batch009.profile387,MergedCutProfiles.Batch445.profile17804,MergedCutProfiles.Batch009.profile376,MergedCutProfiles.Batch310.profile12424,MergedCutProfiles.Batch009.profile368,MergedCutProfiles.Batch009.profile369,MergedCutProfiles.Batch009.profile370,MergedCutProfiles.Batch009.profile371,MergedCutProfiles.Batch310.profile12427,MergedCutProfiles.Batch009.profile379]⟩
theorem profilesValid2823 : retention2823.ProfilesValid := by
  change ∀ j : Fin 16, (retention2823.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch444.valid17798
  · exact MergedCutProfiles.Batch445.valid17801
  · exact MergedCutProfiles.Batch310.valid12426
  · exact MergedCutProfiles.Batch445.valid17803
  · exact MergedCutProfiles.Batch310.valid12418
  · exact MergedCutProfiles.Batch009.valid362
  · exact MergedCutProfiles.Batch009.valid387
  · exact MergedCutProfiles.Batch445.valid17804
  · exact MergedCutProfiles.Batch009.valid376
  · exact MergedCutProfiles.Batch310.valid12424
  · exact MergedCutProfiles.Batch009.valid368
  · exact MergedCutProfiles.Batch009.valid369
  · exact MergedCutProfiles.Batch009.valid370
  · exact MergedCutProfiles.Batch009.valid371
  · exact MergedCutProfiles.Batch310.valid12427
  · exact MergedCutProfiles.Batch009.valid379
theorem numericValid2823 : retention2823.NumericValid := by decide +kernel
def certificate2823 : RatCutBinCertificate := ⟨⟨retention2823,(452391586261936147/250000000000000000),(3278736788116277/1000000000000000000),(7343162173420266947/1000000000000000000),(167046958857763097523/6250000000000000),(1167246858508082041/500000000000000000)⟩,(19998649411250573/20000000000000000),(43287272266116393/125000000000000000),(57292340688912857/200000000000000000),(210025948985868517/1000000000000000000)⟩
theorem valid2823 : certificate2823.Valid := by decide +kernel
theorem sound2823 : certificate2823.Sound := rat_cut_bin_certificate_sound certificate2823 profilesValid2823 numericValid2823 valid2823

def retention2824 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(32000000000000000000/1811777693017488293139),(28429358904405981/8000000000000000),(27/20),(27581314205658926043/12800000000000000000),true,MergedCutProfiles.Batch009.profile380,![MergedCutProfiles.Batch009.profile380,MergedCutProfiles.Batch310.profile12430,MergedCutProfiles.Batch445.profile17805,MergedCutProfiles.Batch445.profile17806,MergedCutProfiles.Batch010.profile400,MergedCutProfiles.Batch445.profile17807,MergedCutProfiles.Batch445.profile17808,MergedCutProfiles.Batch445.profile17809,MergedCutProfiles.Batch445.profile17810,MergedCutProfiles.Batch010.profile401,MergedCutProfiles.Batch445.profile17811,MergedCutProfiles.Batch445.profile17812,MergedCutProfiles.Batch445.profile17813,MergedCutProfiles.Batch445.profile17814,MergedCutProfiles.Batch010.profile402,MergedCutProfiles.Batch445.profile17815]⟩
theorem profilesValid2824 : retention2824.ProfilesValid := by
  change ∀ j : Fin 16, (retention2824.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch009.valid380
  · exact MergedCutProfiles.Batch310.valid12430
  · exact MergedCutProfiles.Batch445.valid17805
  · exact MergedCutProfiles.Batch445.valid17806
  · exact MergedCutProfiles.Batch010.valid400
  · exact MergedCutProfiles.Batch445.valid17807
  · exact MergedCutProfiles.Batch445.valid17808
  · exact MergedCutProfiles.Batch445.valid17809
  · exact MergedCutProfiles.Batch445.valid17810
  · exact MergedCutProfiles.Batch010.valid401
  · exact MergedCutProfiles.Batch445.valid17811
  · exact MergedCutProfiles.Batch445.valid17812
  · exact MergedCutProfiles.Batch445.valid17813
  · exact MergedCutProfiles.Batch445.valid17814
  · exact MergedCutProfiles.Batch010.valid402
  · exact MergedCutProfiles.Batch445.valid17815
theorem numericValid2824 : retention2824.NumericValid := by decide +kernel
def certificate2824 : RatCutBinCertificate := ⟨⟨retention2824,(452391586261936147/250000000000000000),(3278736788116277/1000000000000000000),(7343162173420266947/1000000000000000000),(167046958857763097523/6250000000000000),(2153699405986085657/1000000000000000000)⟩,(19998649411250573/20000000000000000),(64682583304065403/250000000000000000),(78281282408982453/200000000000000000),(234281491556841021/500000000000000000)⟩
theorem valid2824 : certificate2824.Valid := by decide +kernel
theorem sound2824 : certificate2824.Sound := rat_cut_bin_certificate_sound certificate2824 profilesValid2824 numericValid2824 valid2824

def retention2825 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(1/2),64,1,(249383750761872694322254949188936071/250000000000000000000000000000000000),false,MergedCutProfiles.Batch010.profile416,(fun _ => MergedCutProfiles.Batch010.profile416)⟩
theorem profilesValid2825 : retention2825.ProfilesValid := by
  exact MergedCutProfiles.Batch010.valid416
theorem numericValid2825 : retention2825.NumericValid := by decide +kernel
def certificate2825 : RatCutBinCertificate := ⟨⟨retention2825,(452391586261936147/250000000000000000),(3278736788116277/1000000000000000000),(7343162173420266947/1000000000000000000),(167046958857763097523/6250000000000000),(49836351400329451/50000000000000000)⟩,(19998649411250573/20000000000000000),(26375753799283119/62500000000000000),(213908426907001843/1000000000000000000),(104962227801623719/500000000000000000)⟩
theorem valid2825 : certificate2825.Valid := by decide +kernel
theorem sound2825 : certificate2825.Sound := rat_cut_bin_certificate_sound certificate2825 profilesValid2825 numericValid2825 valid2825

def retention2826 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(32000000000000000000/1811777693017488293139),(7712526219056567007/1000000000000000000),1,(3171100317001230605636545695132382909/1542505243811313401400000000000000000),false,MergedCutProfiles.Batch445.profile17816,(fun _ => MergedCutProfiles.Batch445.profile17816)⟩
theorem profilesValid2826 : retention2826.ProfilesValid := by
  exact MergedCutProfiles.Batch445.valid17816
theorem numericValid2826 : retention2826.NumericValid := by decide +kernel
def certificate2826 : RatCutBinCertificate := ⟨⟨retention2826,(489227460261936147/250000000000000000),(3278736788116277/1000000000000000000),(7343162173420266947/1000000000000000000),(167046958857763097523/6250000000000000),(128433620559118189/62500000000000000)⟩,(499963485996799471/500000000000000000),(71439942719834177/1000000000000000000),(183303920610811091/250000000000000000),(237925993177141923/200000000000000000)⟩
theorem valid2826 : certificate2826.Valid := by decide +kernel
theorem sound2826 : certificate2826.Sound := rat_cut_bin_certificate_sound certificate2826 profilesValid2826 numericValid2826 valid2826

def retention2827 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(1/2),64,1,(249383750761872694322254949188936071/250000000000000000000000000000000000),false,MergedCutProfiles.Batch010.profile416,(fun _ => MergedCutProfiles.Batch010.profile416)⟩
theorem profilesValid2827 : retention2827.ProfilesValid := by
  exact MergedCutProfiles.Batch010.valid416
theorem numericValid2827 : retention2827.NumericValid := by decide +kernel
def certificate2827 : RatCutBinCertificate := ⟨⟨retention2827,(489227460261936147/250000000000000000),(3278736788116277/1000000000000000000),(7343162173420266947/1000000000000000000),(167046958857763097523/6250000000000000),(199332247767394443/200000000000000000)⟩,(499963485996799471/500000000000000000),(147296435555193233/1000000000000000000),(14237860002465413/25000000000000000),(558867990834541907/1000000000000000000)⟩
theorem valid2827 : certificate2827.Valid := by decide +kernel
theorem sound2827 : certificate2827.Sound := rat_cut_bin_certificate_sound certificate2827 profilesValid2827 numericValid2827 valid2827

def retention2828 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(15136373181798826/69569532337759591991),(575515969679582439/1000000000000000000),4,(1017561733112105175205769411344309147/460412775743665951200000000000000000),true,MergedCutProfiles.Batch445.profile17817,![MergedCutProfiles.Batch445.profile17817,MergedCutProfiles.Batch445.profile17818,MergedCutProfiles.Batch445.profile17819,MergedCutProfiles.Batch445.profile17820,MergedCutProfiles.Batch010.profile418,MergedCutProfiles.Batch445.profile17821,MergedCutProfiles.Batch445.profile17822,MergedCutProfiles.Batch311.profile12458,MergedCutProfiles.Batch445.profile17823,MergedCutProfiles.Batch010.profile419,MergedCutProfiles.Batch445.profile17824,MergedCutProfiles.Batch311.profile12444,MergedCutProfiles.Batch011.profile447,MergedCutProfiles.Batch010.profile420,MergedCutProfiles.Batch311.profile12454,MergedCutProfiles.Batch311.profile12445]⟩
theorem profilesValid2828 : retention2828.ProfilesValid := by
  change ∀ j : Fin 16, (retention2828.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch445.valid17817
  · exact MergedCutProfiles.Batch445.valid17818
  · exact MergedCutProfiles.Batch445.valid17819
  · exact MergedCutProfiles.Batch445.valid17820
  · exact MergedCutProfiles.Batch010.valid418
  · exact MergedCutProfiles.Batch445.valid17821
  · exact MergedCutProfiles.Batch445.valid17822
  · exact MergedCutProfiles.Batch311.valid12458
  · exact MergedCutProfiles.Batch445.valid17823
  · exact MergedCutProfiles.Batch010.valid419
  · exact MergedCutProfiles.Batch445.valid17824
  · exact MergedCutProfiles.Batch311.valid12444
  · exact MergedCutProfiles.Batch011.valid447
  · exact MergedCutProfiles.Batch010.valid420
  · exact MergedCutProfiles.Batch311.valid12454
  · exact MergedCutProfiles.Batch311.valid12445
theorem numericValid2828 : retention2828.NumericValid := by decide +kernel
def certificate2828 : RatCutBinCertificate := ⟨⟨retention2828,(1813578092676477869/1000000000000000000),(4061079806220747/1000000000000000000),(1858279164791913287/250000000000000000),(10908395511668070660349/500000000000000000),(2206144118950218883/1000000000000000000)⟩,(499958572451413639/500000000000000000),(297274726199868179/500000000000000000),(19262747247818353/200000000000000000),(5356158624588601/125000000000000000)⟩
theorem valid2828 : certificate2828.Valid := by decide +kernel
theorem sound2828 : certificate2828.Sound := rat_cut_bin_certificate_sound certificate2828 profilesValid2828 numericValid2828 valid2828

def retention2829 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(649450337500000000/1460960179092951431811),(158931918408887673/250000000000000000),4,(36921479685538836863/16000000000000000000),true,MergedCutProfiles.Batch445.profile17818,![MergedCutProfiles.Batch445.profile17818,MergedCutProfiles.Batch445.profile17820,MergedCutProfiles.Batch445.profile17821,MergedCutProfiles.Batch311.profile12458,MergedCutProfiles.Batch445.profile17825,MergedCutProfiles.Batch311.profile12444,MergedCutProfiles.Batch010.profile420,MergedCutProfiles.Batch311.profile12445,MergedCutProfiles.Batch311.profile12446,MergedCutProfiles.Batch311.profile12447,MergedCutProfiles.Batch445.profile17826,MergedCutProfiles.Batch010.profile422,MergedCutProfiles.Batch311.profile12449,MergedCutProfiles.Batch010.profile423,MergedCutProfiles.Batch010.profile434,MergedCutProfiles.Batch311.profile12451]⟩
theorem profilesValid2829 : retention2829.ProfilesValid := by
  change ∀ j : Fin 16, (retention2829.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch445.valid17818
  · exact MergedCutProfiles.Batch445.valid17820
  · exact MergedCutProfiles.Batch445.valid17821
  · exact MergedCutProfiles.Batch311.valid12458
  · exact MergedCutProfiles.Batch445.valid17825
  · exact MergedCutProfiles.Batch311.valid12444
  · exact MergedCutProfiles.Batch010.valid420
  · exact MergedCutProfiles.Batch311.valid12445
  · exact MergedCutProfiles.Batch311.valid12446
  · exact MergedCutProfiles.Batch311.valid12447
  · exact MergedCutProfiles.Batch445.valid17826
  · exact MergedCutProfiles.Batch010.valid422
  · exact MergedCutProfiles.Batch311.valid12449
  · exact MergedCutProfiles.Batch010.valid423
  · exact MergedCutProfiles.Batch010.valid434
  · exact MergedCutProfiles.Batch311.valid12451
theorem numericValid2829 : retention2829.NumericValid := by decide +kernel
def certificate2829 : RatCutBinCertificate := ⟨⟨retention2829,(1813578092676477869/1000000000000000000),(4061079806220747/1000000000000000000),(1858279164791913287/250000000000000000),(10908395511668070660349/500000000000000000),(1151814544944553851/500000000000000000)⟩,(499958572451413639/500000000000000000),(106514375235339457/200000000000000000),(131887902057883747/1000000000000000000),(15480900459078359/250000000000000000)⟩
theorem valid2829 : certificate2829.Valid := by decide +kernel
theorem sound2829 : certificate2829.Sound := rat_cut_bin_certificate_sound certificate2829 profilesValid2829 numericValid2829 valid2829

def retention2830 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(2234757393074050967/1460960179092951431811),(51956027/40000000),(49/20),(37240826460353012181/16000000000000000000),true,MergedCutProfiles.Batch311.profile12443,![MergedCutProfiles.Batch311.profile12443,MergedCutProfiles.Batch010.profile420,MergedCutProfiles.Batch311.profile12447,MergedCutProfiles.Batch010.profile423,MergedCutProfiles.Batch010.profile424,MergedCutProfiles.Batch010.profile426,MergedCutProfiles.Batch010.profile427,MergedCutProfiles.Batch311.profile12456,MergedCutProfiles.Batch010.profile430,MergedCutProfiles.Batch010.profile437,MergedCutProfiles.Batch010.profile433,MergedCutProfiles.Batch311.profile12461,MergedCutProfiles.Batch311.profile12462,MergedCutProfiles.Batch445.profile17827,MergedCutProfiles.Batch445.profile17828,MergedCutProfiles.Batch445.profile17829]⟩
theorem profilesValid2830 : retention2830.ProfilesValid := by
  change ∀ j : Fin 16, (retention2830.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch311.valid12443
  · exact MergedCutProfiles.Batch010.valid420
  · exact MergedCutProfiles.Batch311.valid12447
  · exact MergedCutProfiles.Batch010.valid423
  · exact MergedCutProfiles.Batch010.valid424
  · exact MergedCutProfiles.Batch010.valid426
  · exact MergedCutProfiles.Batch010.valid427
  · exact MergedCutProfiles.Batch311.valid12456
  · exact MergedCutProfiles.Batch010.valid430
  · exact MergedCutProfiles.Batch010.valid437
  · exact MergedCutProfiles.Batch010.valid433
  · exact MergedCutProfiles.Batch311.valid12461
  · exact MergedCutProfiles.Batch311.valid12462
  · exact MergedCutProfiles.Batch445.valid17827
  · exact MergedCutProfiles.Batch445.valid17828
  · exact MergedCutProfiles.Batch445.valid17829
theorem numericValid2830 : retention2830.NumericValid := by decide +kernel
def certificate2830 : RatCutBinCertificate := ⟨⟨retention2830,(1813578092676477869/1000000000000000000),(4061079806220747/1000000000000000000),(1858279164791913287/250000000000000000),(10908395511668070660349/500000000000000000),(1162562038576406207/500000000000000000)⟩,(499958572451413639/500000000000000000),(174818622023525421/500000000000000000),(56587480336104383/200000000000000000),(206814508660817241/1000000000000000000)⟩
theorem valid2830 : certificate2830.Valid := by decide +kernel
theorem sound2830 : certificate2830.Sound := rat_cut_bin_certificate_sound certificate2830 profilesValid2830 numericValid2830 valid2830

def retention2831 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(32000000000000000000/1460960179092951431811),(2234757393074050967/500000000000000000),(5/4),(152490657839188122699782283885552505079/71512236578369630944000000000000000000),true,MergedCutProfiles.Batch011.profile440,![MergedCutProfiles.Batch011.profile440,MergedCutProfiles.Batch011.profile457,MergedCutProfiles.Batch445.profile17830,MergedCutProfiles.Batch445.profile17831,MergedCutProfiles.Batch311.profile12466,MergedCutProfiles.Batch445.profile17832,MergedCutProfiles.Batch445.profile17833,MergedCutProfiles.Batch445.profile17834,MergedCutProfiles.Batch445.profile17835,MergedCutProfiles.Batch311.profile12468,MergedCutProfiles.Batch445.profile17836,MergedCutProfiles.Batch445.profile17837,MergedCutProfiles.Batch445.profile17838,MergedCutProfiles.Batch445.profile17839,MergedCutProfiles.Batch311.profile12470,MergedCutProfiles.Batch446.profile17840]⟩
theorem profilesValid2831 : retention2831.ProfilesValid := by
  change ∀ j : Fin 16, (retention2831.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch011.valid440
  · exact MergedCutProfiles.Batch011.valid457
  · exact MergedCutProfiles.Batch445.valid17830
  · exact MergedCutProfiles.Batch445.valid17831
  · exact MergedCutProfiles.Batch311.valid12466
  · exact MergedCutProfiles.Batch445.valid17832
  · exact MergedCutProfiles.Batch445.valid17833
  · exact MergedCutProfiles.Batch445.valid17834
  · exact MergedCutProfiles.Batch445.valid17835
  · exact MergedCutProfiles.Batch311.valid12468
  · exact MergedCutProfiles.Batch445.valid17836
  · exact MergedCutProfiles.Batch445.valid17837
  · exact MergedCutProfiles.Batch445.valid17838
  · exact MergedCutProfiles.Batch445.valid17839
  · exact MergedCutProfiles.Batch311.valid12470
  · exact MergedCutProfiles.Batch446.valid17840
theorem numericValid2831 : retention2831.NumericValid := by decide +kernel
def certificate2831 : RatCutBinCertificate := ⟨⟨retention2831,(1813578092676477869/1000000000000000000),(4061079806220747/1000000000000000000),(1858279164791913287/250000000000000000),(10908395511668070660349/500000000000000000),(532783244425759273/250000000000000000)⟩,(499958572451413639/500000000000000000),(249391928031926623/1000000000000000000),(101045975319892777/250000000000000000),(527930159309310851/1000000000000000000)⟩
theorem valid2831 : certificate2831.Valid := by decide +kernel
theorem sound2831 : certificate2831.Sound := rat_cut_bin_certificate_sound certificate2831 profilesValid2831 numericValid2831 valid2831

def certificates : List RatCutBinCertificate := [certificate2820,certificate2821,certificate2822,certificate2823,certificate2824,certificate2825,certificate2826,certificate2827,certificate2828,certificate2829,certificate2830,certificate2831]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2820,List.forall_mem_cons.mpr ⟨sound2821,List.forall_mem_cons.mpr ⟨sound2822,List.forall_mem_cons.mpr ⟨sound2823,List.forall_mem_cons.mpr ⟨sound2824,List.forall_mem_cons.mpr ⟨sound2825,List.forall_mem_cons.mpr ⟨sound2826,List.forall_mem_cons.mpr ⟨sound2827,List.forall_mem_cons.mpr ⟨sound2828,List.forall_mem_cons.mpr ⟨sound2829,List.forall_mem_cons.mpr ⟨sound2830,List.forall_mem_cons.mpr ⟨sound2831,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch235
