import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch008
import Cycle12.MergedCutProfiles.Batch009
import Cycle12.MergedCutProfiles.Batch010
import Cycle12.MergedCutProfiles.Batch310
import Cycle12.MergedCutProfiles.Batch444
import Cycle12.MergedCutProfiles.Batch445
import Cycle12.MergedCutProfiles.Batch563
import Cycle12.MergedCutProfiles.Batch564

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch308

def retention3696 : RatCutRetentionCertificate := ⟨(3/400),(1/125),(32000000000000000000/9213199537152868385809),(10146447812434543091/1000000000000000000),(21/20),(36591357877648979495254133507463289278759/16234316499895268945600000000000000000000),false,MergedCutProfiles.Batch563.profile22554,(fun _ => MergedCutProfiles.Batch563.profile22554)⟩
theorem profilesValid3696 : retention3696.ProfilesValid := by
  exact MergedCutProfiles.Batch563.valid22554
theorem numericValid3696 : retention3696.NumericValid := by decide +kernel
def certificate3696 : RatCutBinCertificate := ⟨⟨retention3696,(1795108273963217851/1000000000000000000),(1291114465089419/500000000000000000),(3649407075351135127/500000000000000000),(67395196350995630792803/500000000000000000),(2253284403304266713/1000000000000000000)⟩,(499993356200043421/500000000000000000),(103745487976364149/500000000000000000),(93189588740251427/200000000000000000),(832261383673852427/1000000000000000000)⟩
theorem valid3696 : certificate3696.Valid := by decide +kernel
theorem sound3696 : certificate3696.Sound := rat_cut_bin_certificate_sound certificate3696 profilesValid3696 numericValid3696 valid3696

def retention3697 : RatCutRetentionCertificate := ⟨(3/400),(1/125),(1/2),64,1,(63842245492489957688683474884787466679/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch444.profile17792,(fun _ => MergedCutProfiles.Batch444.profile17792)⟩
theorem profilesValid3697 : retention3697.ProfilesValid := by
  exact MergedCutProfiles.Batch444.valid17792
theorem numericValid3697 : retention3697.NumericValid := by decide +kernel
def certificate3697 : RatCutBinCertificate := ⟨⟨retention3697,(1795108273963217851/1000000000000000000),(1291114465089419/500000000000000000),(3649407075351135127/500000000000000000),(67395196350995630792803/500000000000000000),(996899999020641349/1000000000000000000)⟩,(499993356200043421/500000000000000000),(424849909432694057/1000000000000000000),(105734866322740931/500000000000000000),(207577999251903173/1000000000000000000)⟩
theorem valid3697 : certificate3697.Valid := by decide +kernel
theorem sound3697 : certificate3697.Sound := rat_cut_bin_certificate_sound certificate3697 profilesValid3697 numericValid3697 valid3697

def retention3698 : RatCutRetentionCertificate := ⟨(3/400),(1/125),(32000000000000000000/9213199537152868385809),(15663657362314665921/1000000000000000000),1,(35231593985582168335851680657726301917/15663657362314665921000000000000000000),false,MergedCutProfiles.Batch563.profile22554,(fun _ => MergedCutProfiles.Batch563.profile22554)⟩
theorem profilesValid3698 : retention3698.ProfilesValid := by
  exact MergedCutProfiles.Batch563.valid22554
theorem numericValid3698 : retention3698.NumericValid := by decide +kernel
def certificate3698 : RatCutBinCertificate := ⟨⟨retention3698,(1761980206963217851/1000000000000000000),(1291114465089419/500000000000000000),(3649407075351135127/500000000000000000),(67395196350995630792803/500000000000000000),(224863382615682079/100000000000000000)⟩,(62499184851118329/62500000000000000),(33087497846556361/1000000000000000000),(835327925657221219/1000000000000000000),(1642524775649757799/1000000000000000000)⟩
theorem valid3698 : certificate3698.Valid := by decide +kernel
theorem sound3698 : certificate3698.Sound := rat_cut_bin_certificate_sound certificate3698 profilesValid3698 numericValid3698 valid3698

def retention3699 : RatCutRetentionCertificate := ⟨(3/400),(1/125),(1/2),64,1,(63842245492489957688683474884787466679/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch444.profile17792,(fun _ => MergedCutProfiles.Batch444.profile17792)⟩
theorem profilesValid3699 : retention3699.ProfilesValid := by
  exact MergedCutProfiles.Batch444.valid17792
theorem numericValid3699 : retention3699.NumericValid := by decide +kernel
def certificate3699 : RatCutBinCertificate := ⟨⟨retention3699,(1761980206963217851/1000000000000000000),(1291114465089419/500000000000000000),(3649407075351135127/500000000000000000),(67395196350995630792803/500000000000000000),(99691171931537247/100000000000000000)⟩,(62499184851118329/62500000000000000),(597057215310923/8000000000000000),(725387582180363457/1000000000000000000),(356023250101301173/500000000000000000)⟩
theorem valid3699 : certificate3699.Valid := by decide +kernel
theorem sound3699 : certificate3699.Sound := rat_cut_bin_certificate_sound certificate3699 profilesValid3699 numericValid3699 valid3699

def retention3700 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(587808512458561684/14494221544139906345113),(35657571941267751/62500000000000000),4,(275265344565685947/125000000000000000),true,MergedCutProfiles.Batch563.profile22555,![MergedCutProfiles.Batch563.profile22555,MergedCutProfiles.Batch563.profile22556,MergedCutProfiles.Batch563.profile22557,MergedCutProfiles.Batch444.profile17794,MergedCutProfiles.Batch563.profile22558,MergedCutProfiles.Batch563.profile22558,MergedCutProfiles.Batch563.profile22559,MergedCutProfiles.Batch444.profile17795,MergedCutProfiles.Batch444.profile17795,MergedCutProfiles.Batch310.profile12413,MergedCutProfiles.Batch310.profile12413,MergedCutProfiles.Batch444.profile17796,MergedCutProfiles.Batch444.profile17796,MergedCutProfiles.Batch564.profile22560,MergedCutProfiles.Batch564.profile22560,MergedCutProfiles.Batch444.profile17797]⟩
theorem profilesValid3700 : retention3700.ProfilesValid := by
  change ∀ j : Fin 16, (retention3700.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch563.valid22555
  · exact MergedCutProfiles.Batch563.valid22556
  · exact MergedCutProfiles.Batch563.valid22557
  · exact MergedCutProfiles.Batch444.valid17794
  · exact MergedCutProfiles.Batch563.valid22558
  · exact MergedCutProfiles.Batch563.valid22558
  · exact MergedCutProfiles.Batch563.valid22559
  · exact MergedCutProfiles.Batch444.valid17795
  · exact MergedCutProfiles.Batch444.valid17795
  · exact MergedCutProfiles.Batch310.valid12413
  · exact MergedCutProfiles.Batch310.valid12413
  · exact MergedCutProfiles.Batch444.valid17796
  · exact MergedCutProfiles.Batch444.valid17796
  · exact MergedCutProfiles.Batch564.valid22560
  · exact MergedCutProfiles.Batch564.valid22560
  · exact MergedCutProfiles.Batch444.valid17797
theorem numericValid3700 : retention3700.NumericValid := by decide +kernel
def certificate3700 : RatCutBinCertificate := ⟨⟨retention3700,(1757296264011936147/1000000000000000000),(3278736788116277/1000000000000000000),(3671581122092787641/500000000000000000),(53455027349624857676131/500000000000000000),(2198984211144482449/1000000000000000000)⟩,(249995901324243803/250000000000000000),(623946297636627627/1000000000000000000),(255449575169219/3125000000000000),(7242744769014617/200000000000000000)⟩
theorem valid3700 : certificate3700.Valid := by decide +kernel
theorem sound3700 : certificate3700.Sound := rat_cut_bin_certificate_sound certificate3700 profilesValid3700 numericValid3700 valid3700

def retention3701 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(1284102601000000000/14494221544139906345113),(146952128114640421/250000000000000000),4,(1683334005851776041275631292627091/752394895946958955520000000000000),true,MergedCutProfiles.Batch563.profile22556,![MergedCutProfiles.Batch563.profile22556,MergedCutProfiles.Batch444.profile17794,MergedCutProfiles.Batch563.profile22559,MergedCutProfiles.Batch444.profile17795,MergedCutProfiles.Batch310.profile12413,MergedCutProfiles.Batch444.profile17796,MergedCutProfiles.Batch564.profile22560,MergedCutProfiles.Batch444.profile17797,MergedCutProfiles.Batch008.profile356,MergedCutProfiles.Batch310.profile12420,MergedCutProfiles.Batch310.profile12420,MergedCutProfiles.Batch444.profile17798,MergedCutProfiles.Batch444.profile17799,MergedCutProfiles.Batch310.profile12414,MergedCutProfiles.Batch310.profile12414,MergedCutProfiles.Batch445.profile17800]⟩
theorem profilesValid3701 : retention3701.ProfilesValid := by
  change ∀ j : Fin 16, (retention3701.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch563.valid22556
  · exact MergedCutProfiles.Batch444.valid17794
  · exact MergedCutProfiles.Batch563.valid22559
  · exact MergedCutProfiles.Batch444.valid17795
  · exact MergedCutProfiles.Batch310.valid12413
  · exact MergedCutProfiles.Batch444.valid17796
  · exact MergedCutProfiles.Batch564.valid22560
  · exact MergedCutProfiles.Batch444.valid17797
  · exact MergedCutProfiles.Batch008.valid356
  · exact MergedCutProfiles.Batch310.valid12420
  · exact MergedCutProfiles.Batch310.valid12420
  · exact MergedCutProfiles.Batch444.valid17798
  · exact MergedCutProfiles.Batch444.valid17799
  · exact MergedCutProfiles.Batch310.valid12414
  · exact MergedCutProfiles.Batch310.valid12414
  · exact MergedCutProfiles.Batch445.valid17800
theorem numericValid3701 : retention3701.NumericValid := by decide +kernel
def certificate3701 : RatCutBinCertificate := ⟨⟨retention3701,(1757296264011936147/1000000000000000000),(3278736788116277/1000000000000000000),(3671581122092787641/500000000000000000),(53455027349624857676131/500000000000000000),(2234162657644936371/1000000000000000000)⟩,(249995901324243803/250000000000000000),(150407534869080923/250000000000000000),(23168530067760017/250000000000000000),(41825510014727409/1000000000000000000)⟩
theorem valid3701 : certificate3701.Valid := by decide +kernel
theorem sound3701 : certificate3701.Sound := rat_cut_bin_certificate_sound certificate3701 profilesValid3701 numericValid3701 valid3701

def retention3702 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(2667378744292602434/14494221544139906345113),(1284102601/1000000000),(5/2),(759551131917601826537591659814759871/321025650250000000000000000000000000),true,MergedCutProfiles.Batch444.profile17794,![MergedCutProfiles.Batch444.profile17794,MergedCutProfiles.Batch444.profile17795,MergedCutProfiles.Batch564.profile22560,MergedCutProfiles.Batch444.profile17797,MergedCutProfiles.Batch310.profile12420,MergedCutProfiles.Batch444.profile17799,MergedCutProfiles.Batch310.profile12414,MergedCutProfiles.Batch445.profile17800,MergedCutProfiles.Batch008.profile357,MergedCutProfiles.Batch009.profile372,MergedCutProfiles.Batch310.profile12415,MergedCutProfiles.Batch445.profile17802,MergedCutProfiles.Batch008.profile358,MergedCutProfiles.Batch008.profile358,MergedCutProfiles.Batch310.profile12421,MergedCutProfiles.Batch310.profile12426]⟩
theorem profilesValid3702 : retention3702.ProfilesValid := by
  change ∀ j : Fin 16, (retention3702.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch444.valid17794
  · exact MergedCutProfiles.Batch444.valid17795
  · exact MergedCutProfiles.Batch564.valid22560
  · exact MergedCutProfiles.Batch444.valid17797
  · exact MergedCutProfiles.Batch310.valid12420
  · exact MergedCutProfiles.Batch444.valid17799
  · exact MergedCutProfiles.Batch310.valid12414
  · exact MergedCutProfiles.Batch445.valid17800
  · exact MergedCutProfiles.Batch008.valid357
  · exact MergedCutProfiles.Batch009.valid372
  · exact MergedCutProfiles.Batch310.valid12415
  · exact MergedCutProfiles.Batch445.valid17802
  · exact MergedCutProfiles.Batch008.valid358
  · exact MergedCutProfiles.Batch008.valid358
  · exact MergedCutProfiles.Batch310.valid12421
  · exact MergedCutProfiles.Batch310.valid12426
theorem numericValid3702 : retention3702.NumericValid := by decide +kernel
def certificate3702 : RatCutBinCertificate := ⟨⟨retention3702,(1757296264011936147/1000000000000000000),(3278736788116277/1000000000000000000),(3671581122092787641/500000000000000000),(53455027349624857676131/500000000000000000),(1182026125243692121/500000000000000000)⟩,(249995901324243803/250000000000000000),(357315550137007083/1000000000000000000),(274953436849873693/1000000000000000000),(25104705670708039/125000000000000000)⟩
theorem valid3702 : certificate3702.Valid := by decide +kernel
theorem sound3702 : certificate3702.Sound := rat_cut_bin_certificate_sound certificate3702 profilesValid3702 numericValid3702 valid3702

def retention3703 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(64000000000000000000/14494221544139906345113),(1333689372146301217/500000000000000000),(8/5),(364558180493978799753/160000000000000000000),true,MergedCutProfiles.Batch310.profile12422,![MergedCutProfiles.Batch310.profile12422,MergedCutProfiles.Batch009.profile376,MergedCutProfiles.Batch564.profile22561,MergedCutProfiles.Batch009.profile380,MergedCutProfiles.Batch564.profile22562,MergedCutProfiles.Batch009.profile385,MergedCutProfiles.Batch564.profile22563,MergedCutProfiles.Batch310.profile12430,MergedCutProfiles.Batch564.profile22564,MergedCutProfiles.Batch009.profile396,MergedCutProfiles.Batch564.profile22565,MergedCutProfiles.Batch445.profile17805,MergedCutProfiles.Batch564.profile22566,MergedCutProfiles.Batch564.profile22567,MergedCutProfiles.Batch564.profile22568,MergedCutProfiles.Batch445.profile17806]⟩
theorem profilesValid3703 : retention3703.ProfilesValid := by
  change ∀ j : Fin 16, (retention3703.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch310.valid12422
  · exact MergedCutProfiles.Batch009.valid376
  · exact MergedCutProfiles.Batch564.valid22561
  · exact MergedCutProfiles.Batch009.valid380
  · exact MergedCutProfiles.Batch564.valid22562
  · exact MergedCutProfiles.Batch009.valid385
  · exact MergedCutProfiles.Batch564.valid22563
  · exact MergedCutProfiles.Batch310.valid12430
  · exact MergedCutProfiles.Batch564.valid22564
  · exact MergedCutProfiles.Batch009.valid396
  · exact MergedCutProfiles.Batch564.valid22565
  · exact MergedCutProfiles.Batch445.valid17805
  · exact MergedCutProfiles.Batch564.valid22566
  · exact MergedCutProfiles.Batch564.valid22567
  · exact MergedCutProfiles.Batch564.valid22568
  · exact MergedCutProfiles.Batch445.valid17806
theorem numericValid3703 : retention3703.NumericValid := by decide +kernel
def certificate3703 : RatCutBinCertificate := ⟨⟨retention3703,(1757296264011936147/1000000000000000000),(3278736788116277/1000000000000000000),(3671581122092787641/500000000000000000),(53455027349624857676131/500000000000000000),(1138616604971407621/500000000000000000)⟩,(249995901324243803/250000000000000000),(54984946634110787/200000000000000000),(370031902452512847/1000000000000000000),(394938147433195627/1000000000000000000)⟩
theorem valid3703 : certificate3703.Valid := by decide +kernel
theorem sound3703 : certificate3703.Sound := rat_cut_bin_certificate_sound certificate3703 profilesValid3703 numericValid3703 valid3703

def retention3704 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(1/2),64,1,(249383750761872694322254949188936071/250000000000000000000000000000000000),false,MergedCutProfiles.Batch010.profile416,(fun _ => MergedCutProfiles.Batch010.profile416)⟩
theorem profilesValid3704 : retention3704.ProfilesValid := by
  exact MergedCutProfiles.Batch010.valid416
theorem numericValid3704 : retention3704.NumericValid := by decide +kernel
def certificate3704 : RatCutBinCertificate := ⟨⟨retention3704,(1757296264011936147/1000000000000000000),(3278736788116277/1000000000000000000),(3671581122092787641/500000000000000000),(53455027349624857676131/500000000000000000),(996750366712407973/1000000000000000000)⟩,(249995901324243803/250000000000000000),(21648239852726967/50000000000000000),(40920076834185217/200000000000000000),(200804756687994829/1000000000000000000)⟩
theorem valid3704 : certificate3704.Valid := by decide +kernel
theorem sound3704 : certificate3704.Sound := rat_cut_bin_certificate_sound certificate3704 profilesValid3704 numericValid3704 valid3704

def retention3705 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(64000000000000000000/14494221544139906345113),(31734968662029149/2000000000000000),1,(35532538910949670291948037912635218271/15867484331014574500000000000000000000),false,MergedCutProfiles.Batch564.profile22569,(fun _ => MergedCutProfiles.Batch564.profile22569)⟩
theorem profilesValid3705 : retention3705.ProfilesValid := by
  exact MergedCutProfiles.Batch564.valid22569
theorem numericValid3705 : retention3705.NumericValid := by decide +kernel
def certificate3705 : RatCutBinCertificate := ⟨⟨retention3705,(1762615322011936147/1000000000000000000),(3278736788116277/1000000000000000000),(3671581122092787641/500000000000000000),(53455027349624857676131/500000000000000000),(2238543317919016653/1000000000000000000)⟩,(499991777836399349/500000000000000000),(33047291724765673/1000000000000000000),(835443499189577279/1000000000000000000),(25608264384234997/15625000000000000)⟩
theorem valid3705 : certificate3705.Valid := by decide +kernel
theorem sound3705 : certificate3705.Sound := rat_cut_bin_certificate_sound certificate3705 profilesValid3705 numericValid3705 valid3705

def retention3706 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(1/2),64,1,(249383750761872694322254949188936071/250000000000000000000000000000000000),false,MergedCutProfiles.Batch010.profile416,(fun _ => MergedCutProfiles.Batch010.profile416)⟩
theorem profilesValid3706 : retention3706.ProfilesValid := by
  exact MergedCutProfiles.Batch010.valid416
theorem numericValid3706 : retention3706.NumericValid := by decide +kernel
def certificate3706 : RatCutBinCertificate := ⟨⟨retention3706,(1762615322011936147/1000000000000000000),(3278736788116277/1000000000000000000),(3671581122092787641/500000000000000000),(53455027349624857676131/500000000000000000),(498373995871127997/500000000000000000)⟩,(499991777836399349/500000000000000000),(74219155371946967/1000000000000000000),(726395027584701899/1000000000000000000),(71291766095589949/100000000000000000)⟩
theorem valid3706 : certificate3706.Valid := by decide +kernel
theorem sound3706 : certificate3706.Sound := rat_cut_bin_certificate_sound certificate3706 profilesValid3706 numericValid3706 valid3706

def retention3707 : RatCutRetentionCertificate := ⟨(9/1000),(19/2000),(705311820298049794/12979510417461775966967),(572311289295840601/1000000000000000000),4,(1010083293268808854105935584881179251/457849031436672480800000000000000000),true,MergedCutProfiles.Batch564.profile22570,![MergedCutProfiles.Batch564.profile22570,MergedCutProfiles.Batch564.profile22571,MergedCutProfiles.Batch564.profile22572,MergedCutProfiles.Batch564.profile22573,MergedCutProfiles.Batch564.profile22574,MergedCutProfiles.Batch564.profile22575,MergedCutProfiles.Batch564.profile22575,MergedCutProfiles.Batch564.profile22576,MergedCutProfiles.Batch564.profile22577,MergedCutProfiles.Batch564.profile22577,MergedCutProfiles.Batch564.profile22578,MergedCutProfiles.Batch564.profile22579,MergedCutProfiles.Batch564.profile22579,MergedCutProfiles.Batch564.profile22580,MergedCutProfiles.Batch564.profile22580,MergedCutProfiles.Batch564.profile22581]⟩
theorem profilesValid3707 : retention3707.ProfilesValid := by
  change ∀ j : Fin 16, (retention3707.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch564.valid22570
  · exact MergedCutProfiles.Batch564.valid22571
  · exact MergedCutProfiles.Batch564.valid22572
  · exact MergedCutProfiles.Batch564.valid22573
  · exact MergedCutProfiles.Batch564.valid22574
  · exact MergedCutProfiles.Batch564.valid22575
  · exact MergedCutProfiles.Batch564.valid22575
  · exact MergedCutProfiles.Batch564.valid22576
  · exact MergedCutProfiles.Batch564.valid22577
  · exact MergedCutProfiles.Batch564.valid22577
  · exact MergedCutProfiles.Batch564.valid22578
  · exact MergedCutProfiles.Batch564.valid22579
  · exact MergedCutProfiles.Batch564.valid22579
  · exact MergedCutProfiles.Batch564.valid22580
  · exact MergedCutProfiles.Batch564.valid22580
  · exact MergedCutProfiles.Batch564.valid22581
theorem numericValid3707 : retention3707.NumericValid := by decide +kernel
def certificate3707 : RatCutBinCertificate := ⟨⟨retention3707,(221054140063555913/125000000000000000),(3659123537247033/1000000000000000000),(7433116769339109203/1000000000000000000),(48347460048084572699147/500000000000000000),(17208336193633319/7812500000000000)⟩,(999981771172697331/1000000000000000000),(310603044114974373/500000000000000000),(83042422028453619/1000000000000000000),(1151905414506251/31250000000000000)⟩
theorem valid3707 : certificate3707.Valid := by decide +kernel
theorem sound3707 : certificate3707.Sound := rat_cut_bin_certificate_sound certificate3707 profilesValid3707 numericValid3707 valid3707

def certificates : List RatCutBinCertificate := [certificate3696,certificate3697,certificate3698,certificate3699,certificate3700,certificate3701,certificate3702,certificate3703,certificate3704,certificate3705,certificate3706,certificate3707]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3696,List.forall_mem_cons.mpr ⟨sound3697,List.forall_mem_cons.mpr ⟨sound3698,List.forall_mem_cons.mpr ⟨sound3699,List.forall_mem_cons.mpr ⟨sound3700,List.forall_mem_cons.mpr ⟨sound3701,List.forall_mem_cons.mpr ⟨sound3702,List.forall_mem_cons.mpr ⟨sound3703,List.forall_mem_cons.mpr ⟨sound3704,List.forall_mem_cons.mpr ⟨sound3705,List.forall_mem_cons.mpr ⟨sound3706,List.forall_mem_cons.mpr ⟨sound3707,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch308
