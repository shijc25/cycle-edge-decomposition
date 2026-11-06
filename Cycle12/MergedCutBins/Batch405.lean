import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch359
import Cycle12.MergedCutProfiles.Batch360
import Cycle12.MergedCutProfiles.Batch361
import Cycle12.MergedCutProfiles.Batch478
import Cycle12.MergedCutProfiles.Batch479
import Cycle12.MergedCutProfiles.Batch605
import Cycle12.MergedCutProfiles.Batch683
import Cycle12.MergedCutProfiles.Batch684

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch405

def retention4860 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(933057668365485569/447097425390821400744),(224319469669009731/250000000000000000),(18/5),(53746142869017036199110577145700584519/22431946966900973100000000000000000000),false,MergedCutProfiles.Batch683.profile27347,(fun _ => MergedCutProfiles.Batch683.profile27347)⟩
theorem profilesValid4860 : retention4860.ProfilesValid := by
  exact MergedCutProfiles.Batch683.valid27347
theorem numericValid4860 : retention4860.NumericValid := by decide +kernel
def certificate4860 : RatCutBinCertificate := ⟨⟨retention4860,(1850071288829828149/1000000000000000000),(21376650541548341/250000000000000000),(11709299178050645457/1000000000000000000),(31583197446211058204217/1000000000000000000),(1173663997717641337/500000000000000000)⟩,(999946177981697597/1000000000000000000),(806865916651303401/1000000000000000000),(3996490600661507/200000000000000000),(2710069351005193/250000000000000000)⟩
theorem valid4860 : certificate4860.Valid := by decide +kernel
theorem sound4860 : certificate4860.Sound := rat_cut_bin_certificate_sound certificate4860 profilesValid4860 numericValid4860 valid4860

def retention4861 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(1/40),(2799173005096456707/500000000000000000),(27/20),(4931142756068482041003874116739329327719/2239338404077165365600000000000000000000),false,MergedCutProfiles.Batch683.profile27348,(fun _ => MergedCutProfiles.Batch683.profile27348)⟩
theorem profilesValid4861 : retention4861.ProfilesValid := by
  exact MergedCutProfiles.Batch683.valid27348
theorem numericValid4861 : retention4861.NumericValid := by decide +kernel
def certificate4861 : RatCutBinCertificate := ⟨⟨retention4861,(1850071288829828149/1000000000000000000),(21376650541548341/250000000000000000),(11709299178050645457/1000000000000000000),(31583197446211058204217/1000000000000000000),(68244213113105919/31250000000000000)⟩,(999946177981697597/1000000000000000000),(358059412352402737/500000000000000000),(5595316659108299/125000000000000000),(59640301276916753/1000000000000000000)⟩
theorem valid4861 : certificate4861.Valid := by decide +kernel
theorem sound4861 : certificate4861.Sound := rat_cut_bin_certificate_sound certificate4861 profilesValid4861 numericValid4861 valid4861

def retention4862 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(290315085467565361/1273996802739327013414),(557974181682358421/1000000000000000000),4,(558868990474891272829/256000000000000000000),true,MergedCutProfiles.Batch683.profile27349,![MergedCutProfiles.Batch683.profile27349,MergedCutProfiles.Batch683.profile27350,MergedCutProfiles.Batch683.profile27351,MergedCutProfiles.Batch683.profile27352,MergedCutProfiles.Batch605.profile24212,MergedCutProfiles.Batch683.profile27353,MergedCutProfiles.Batch683.profile27354,MergedCutProfiles.Batch683.profile27355,MergedCutProfiles.Batch605.profile24226,MergedCutProfiles.Batch605.profile24213,MergedCutProfiles.Batch683.profile27356,MergedCutProfiles.Batch683.profile27357,MergedCutProfiles.Batch683.profile27358,MergedCutProfiles.Batch683.profile27359,MergedCutProfiles.Batch684.profile27360,MergedCutProfiles.Batch605.profile24214]⟩
theorem profilesValid4862 : retention4862.ProfilesValid := by
  change ∀ j : Fin 16, (retention4862.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch683.valid27349
  · exact MergedCutProfiles.Batch683.valid27350
  · exact MergedCutProfiles.Batch683.valid27351
  · exact MergedCutProfiles.Batch683.valid27352
  · exact MergedCutProfiles.Batch605.valid24212
  · exact MergedCutProfiles.Batch683.valid27353
  · exact MergedCutProfiles.Batch683.valid27354
  · exact MergedCutProfiles.Batch683.valid27355
  · exact MergedCutProfiles.Batch605.valid24226
  · exact MergedCutProfiles.Batch605.valid24213
  · exact MergedCutProfiles.Batch683.valid27356
  · exact MergedCutProfiles.Batch683.valid27357
  · exact MergedCutProfiles.Batch683.valid27358
  · exact MergedCutProfiles.Batch683.valid27359
  · exact MergedCutProfiles.Batch684.valid27360
  · exact MergedCutProfiles.Batch605.valid24214
theorem numericValid4862 : retention4862.NumericValid := by decide +kernel
def certificate4862 : RatCutBinCertificate := ⟨⟨retention4862,(937592676331560059/500000000000000000),(5622540848385301/62500000000000000),(2973523243523444443/250000000000000000),(3809134603006935974091/125000000000000000),(2126350262284188047/1000000000000000000)⟩,(999943725615245363/1000000000000000000),(791137447030679781/1000000000000000000),(23512053309039659/1000000000000000000),(10093746761505543/1000000000000000000)⟩
theorem valid4862 : certificate4862.Valid := by decide +kernel
theorem sound4862 : certificate4862.Sound := rat_cut_bin_certificate_sound certificate4862 profilesValid4862 numericValid4862 valid4862

def retention4863 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(284460887000000000/636998401369663506707),(290315085467565361/500000000000000000),4,(5189855669800720923180765186031654519/2322520683740522888000000000000000000),true,MergedCutProfiles.Batch683.profile27350,![MergedCutProfiles.Batch683.profile27350,MergedCutProfiles.Batch683.profile27352,MergedCutProfiles.Batch683.profile27353,MergedCutProfiles.Batch683.profile27355,MergedCutProfiles.Batch605.profile24213,MergedCutProfiles.Batch683.profile27357,MergedCutProfiles.Batch683.profile27359,MergedCutProfiles.Batch605.profile24214,MergedCutProfiles.Batch684.profile27361,MergedCutProfiles.Batch605.profile24234,MergedCutProfiles.Batch605.profile24215,MergedCutProfiles.Batch684.profile27362,MergedCutProfiles.Batch605.profile24216,MergedCutProfiles.Batch684.profile27363,MergedCutProfiles.Batch605.profile24228,MergedCutProfiles.Batch605.profile24217]⟩
theorem profilesValid4863 : retention4863.ProfilesValid := by
  change ∀ j : Fin 16, (retention4863.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch683.valid27350
  · exact MergedCutProfiles.Batch683.valid27352
  · exact MergedCutProfiles.Batch683.valid27353
  · exact MergedCutProfiles.Batch683.valid27355
  · exact MergedCutProfiles.Batch605.valid24213
  · exact MergedCutProfiles.Batch683.valid27357
  · exact MergedCutProfiles.Batch683.valid27359
  · exact MergedCutProfiles.Batch605.valid24214
  · exact MergedCutProfiles.Batch684.valid27361
  · exact MergedCutProfiles.Batch605.valid24234
  · exact MergedCutProfiles.Batch605.valid24215
  · exact MergedCutProfiles.Batch684.valid27362
  · exact MergedCutProfiles.Batch605.valid24216
  · exact MergedCutProfiles.Batch684.valid27363
  · exact MergedCutProfiles.Batch605.valid24228
  · exact MergedCutProfiles.Batch605.valid24217
theorem numericValid4863 : retention4863.NumericValid := by decide +kernel
def certificate4863 : RatCutBinCertificate := ⟨⟨retention4863,(937592676331560059/500000000000000000),(5622540848385301/62500000000000000),(2973523243523444443/250000000000000000),(3809134603006935974091/125000000000000000),(1088923575918724193/500000000000000000)⟩,(999943725615245363/1000000000000000000),(375925631877590289/500000000000000000),(16854076587301773/500000000000000000),(3716610643733511/250000000000000000)⟩
theorem valid4863 : certificate4863.Valid := by decide +kernel
theorem sound4863 : certificate4863.Sound := rat_cut_bin_certificate_sound certificate4863 profilesValid4863 numericValid4863 valid4863

def retention4864 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(5340303660467452053/2547993605478654026828),(284460887/250000000),(14/5),(4749027424272121543/2000000000000000000),true,MergedCutProfiles.Batch605.profile24226,![MergedCutProfiles.Batch605.profile24226,MergedCutProfiles.Batch605.profile24227,MergedCutProfiles.Batch684.profile27363,MergedCutProfiles.Batch605.profile24218,MergedCutProfiles.Batch605.profile24220,MergedCutProfiles.Batch684.profile27364,MergedCutProfiles.Batch684.profile27365,MergedCutProfiles.Batch605.profile24223,MergedCutProfiles.Batch605.profile24225,MergedCutProfiles.Batch479.profile19171,MergedCutProfiles.Batch360.profile14414,MergedCutProfiles.Batch684.profile27366,MergedCutProfiles.Batch684.profile27367,MergedCutProfiles.Batch478.profile19135,MergedCutProfiles.Batch359.profile14370,MergedCutProfiles.Batch605.profile24237]⟩
theorem profilesValid4864 : retention4864.ProfilesValid := by
  change ∀ j : Fin 16, (retention4864.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch605.valid24226
  · exact MergedCutProfiles.Batch605.valid24227
  · exact MergedCutProfiles.Batch684.valid27363
  · exact MergedCutProfiles.Batch605.valid24218
  · exact MergedCutProfiles.Batch605.valid24220
  · exact MergedCutProfiles.Batch684.valid27364
  · exact MergedCutProfiles.Batch684.valid27365
  · exact MergedCutProfiles.Batch605.valid24223
  · exact MergedCutProfiles.Batch605.valid24225
  · exact MergedCutProfiles.Batch479.valid19171
  · exact MergedCutProfiles.Batch360.valid14414
  · exact MergedCutProfiles.Batch684.valid27366
  · exact MergedCutProfiles.Batch684.valid27367
  · exact MergedCutProfiles.Batch478.valid19135
  · exact MergedCutProfiles.Batch359.valid14370
  · exact MergedCutProfiles.Batch605.valid24237
theorem numericValid4864 : retention4864.NumericValid := by decide +kernel
def certificate4864 : RatCutBinCertificate := ⟨⟨retention4864,(937592676331560059/500000000000000000),(5622540848385301/62500000000000000),(2973523243523444443/250000000000000000),(3809134603006935974091/125000000000000000),(1167400757817505459/500000000000000000)⟩,(999943725615245363/1000000000000000000),(469796471464109961/1000000000000000000),(87646476801804441/500000000000000000),(28960237221410611/250000000000000000)⟩
theorem valid4864 : certificate4864.Valid := by decide +kernel
theorem sound4864 : certificate4864.Sound := rat_cut_bin_certificate_sound certificate4864 profilesValid4864 numericValid4864 valid4864

def retention4865 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(16000000000000000000/636998401369663506707),(5340303660467452053/1000000000000000000),(6/5),(1149347202502822333847640889614170250431/534030366046745205300000000000000000000),true,MergedCutProfiles.Batch684.profile27366,![MergedCutProfiles.Batch684.profile27366,MergedCutProfiles.Batch684.profile27368,MergedCutProfiles.Batch478.profile19141,MergedCutProfiles.Batch684.profile27369,MergedCutProfiles.Batch359.profile14376,MergedCutProfiles.Batch479.profile19175,MergedCutProfiles.Batch684.profile27370,MergedCutProfiles.Batch359.profile14394,MergedCutProfiles.Batch684.profile27371,MergedCutProfiles.Batch359.profile14384,MergedCutProfiles.Batch684.profile27372,MergedCutProfiles.Batch684.profile27373,MergedCutProfiles.Batch684.profile27374,MergedCutProfiles.Batch684.profile27375,MergedCutProfiles.Batch684.profile27376,MergedCutProfiles.Batch684.profile27377]⟩
theorem profilesValid4865 : retention4865.ProfilesValid := by
  change ∀ j : Fin 16, (retention4865.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch684.valid27366
  · exact MergedCutProfiles.Batch684.valid27368
  · exact MergedCutProfiles.Batch478.valid19141
  · exact MergedCutProfiles.Batch684.valid27369
  · exact MergedCutProfiles.Batch359.valid14376
  · exact MergedCutProfiles.Batch479.valid19175
  · exact MergedCutProfiles.Batch684.valid27370
  · exact MergedCutProfiles.Batch359.valid14394
  · exact MergedCutProfiles.Batch684.valid27371
  · exact MergedCutProfiles.Batch359.valid14384
  · exact MergedCutProfiles.Batch684.valid27372
  · exact MergedCutProfiles.Batch684.valid27373
  · exact MergedCutProfiles.Batch684.valid27374
  · exact MergedCutProfiles.Batch684.valid27375
  · exact MergedCutProfiles.Batch684.valid27376
  · exact MergedCutProfiles.Batch684.valid27377
theorem numericValid4865 : retention4865.NumericValid := by decide +kernel
def certificate4865 : RatCutBinCertificate := ⟨⟨retention4865,(937592676331560059/500000000000000000),(5622540848385301/62500000000000000),(2973523243523444443/250000000000000000),(3809134603006935974091/125000000000000000),(533798423550112483/250000000000000000)⟩,(999943725615245363/1000000000000000000),(61225396905765131/200000000000000000),(41434257711902487/125000000000000000),(230799532693129087/500000000000000000)⟩
theorem valid4865 : certificate4865.Valid := by decide +kernel
theorem sound4865 : certificate4865.Sound := rat_cut_bin_certificate_sound certificate4865 profilesValid4865 numericValid4865 valid4865

def retention4866 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(1/2),64,1,(408619070903733134070802307191487799/409600000000000000000000000000000000),false,MergedCutProfiles.Batch361.profile14446,(fun _ => MergedCutProfiles.Batch361.profile14446)⟩
theorem profilesValid4866 : retention4866.ProfilesValid := by
  exact MergedCutProfiles.Batch361.valid14446
theorem numericValid4866 : retention4866.NumericValid := by decide +kernel
def certificate4866 : RatCutBinCertificate := ⟨⟨retention4866,(937592676331560059/500000000000000000),(5622540848385301/62500000000000000),(2973523243523444443/250000000000000000),(3809134603006935974091/125000000000000000),(122927779842442303/125000000000000000)⟩,(999943725615245363/1000000000000000000),(138202060572020097/250000000000000000),(119517928562591159/1000000000000000000),(4630051156683813/40000000000000000)⟩
theorem valid4866 : certificate4866.Valid := by decide +kernel
theorem sound4866 : certificate4866.Sound := rat_cut_bin_certificate_sound certificate4866 profilesValid4866 numericValid4866 valid4866

def retention4867 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(16000000000000000000/636998401369663506707),(16796095536033341597/500000000000000000),1,(58295382248612865468432876340710522843/26873752857653346555200000000000000000),false,MergedCutProfiles.Batch684.profile27378,(fun _ => MergedCutProfiles.Batch684.profile27378)⟩
theorem profilesValid4867 : retention4867.ProfilesValid := by
  exact MergedCutProfiles.Batch684.valid27378
theorem numericValid4867 : retention4867.NumericValid := by decide +kernel
def certificate4867 : RatCutBinCertificate := ⟨⟨retention4867,(871301117831560059/500000000000000000),(5622540848385301/62500000000000000),(2973523243523444443/250000000000000000),(3809134603006935974091/125000000000000000),(1078025519802586769/500000000000000000)⟩,(499973852229577629/500000000000000000),(10037603304874349/500000000000000000),(174754565759065543/200000000000000000),(354036520070237981/200000000000000000)⟩
theorem valid4867 : certificate4867.Valid := by decide +kernel
theorem sound4867 : certificate4867.Sound := rat_cut_bin_certificate_sound certificate4867 profilesValid4867 numericValid4867 valid4867

def retention4868 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(1/2),64,1,(408619070903733134070802307191487799/409600000000000000000000000000000000),false,MergedCutProfiles.Batch361.profile14446,(fun _ => MergedCutProfiles.Batch361.profile14446)⟩
theorem profilesValid4868 : retention4868.ProfilesValid := by
  exact MergedCutProfiles.Batch361.valid14446
theorem numericValid4868 : retention4868.NumericValid := by decide +kernel
def certificate4868 : RatCutBinCertificate := ⟨⟨retention4868,(871301117831560059/500000000000000000),(5622540848385301/62500000000000000),(2973523243523444443/250000000000000000),(3809134603006935974091/125000000000000000),(984425027639403991/1000000000000000000)⟩,(499973852229577629/500000000000000000),(10991992499679723/250000000000000000),(402373391219200211/500000000000000000),(48760668912180087/62500000000000000)⟩
theorem valid4868 : certificate4868.Valid := by decide +kernel
theorem sound4868 : certificate4868.Sound := rat_cut_bin_certificate_sound certificate4868 profilesValid4868 numericValid4868 valid4868

def retention4869 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(703230805667800191/2547993605478654026828),(139253624884712909/200000000000000000),4,(66870775599661802622293268412583923/27850724976942581800000000000000000),false,MergedCutProfiles.Batch684.profile27379,(fun _ => MergedCutProfiles.Batch684.profile27379)⟩
theorem profilesValid4869 : retention4869.ProfilesValid := by
  exact MergedCutProfiles.Batch684.valid27379
theorem numericValid4869 : retention4869.NumericValid := by decide +kernel
def certificate4869 : RatCutBinCertificate := ⟨⟨retention4869,(931736723831560059/500000000000000000),(5622540848385301/62500000000000000),(2973523243523444443/250000000000000000),(3809134603006935974091/125000000000000000),(1172332579995963749/500000000000000000)⟩,(999944077091803931/1000000000000000000),(425695665442640537/500000000000000000),(363560325215237/31250000000000000),(2816666306753499/500000000000000000)⟩
theorem valid4869 : certificate4869.Valid := by decide +kernel
theorem sound4869 : certificate4869.Sound := rat_cut_bin_certificate_sound certificate4869 profilesValid4869 numericValid4869 valid4869

def retention4870 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(892916519871419333/2547993605478654026828),(703230805667800191/1000000000000000000),4,(338114207509346492469688237596655183/140646161133560038200000000000000000),false,MergedCutProfiles.Batch684.profile27380,(fun _ => MergedCutProfiles.Batch684.profile27380)⟩
theorem profilesValid4870 : retention4870.ProfilesValid := by
  exact MergedCutProfiles.Batch684.valid27380
theorem numericValid4870 : retention4870.NumericValid := by decide +kernel
def certificate4870 : RatCutBinCertificate := ⟨⟨retention4870,(931736723831560059/500000000000000000),(5622540848385301/62500000000000000),(2973523243523444443/250000000000000000),(3809134603006935974091/125000000000000000),(293453569981542853/125000000000000000)⟩,(999944077091803931/1000000000000000000),(106025345385517993/125000000000000000),(3038224080669327/250000000000000000),(1180187349151313/200000000000000000)⟩
theorem valid4870 : certificate4870.Valid := by decide +kernel
theorem sound4870 : certificate4870.Sound := rat_cut_bin_certificate_sound certificate4870 profilesValid4870 numericValid4870 valid4870

def retention4871 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(1325185800414161113/636998401369663506707),(892916519871419333/1000000000000000000),(18/5),(214048263808011883091461991397010980959/89291651987141933300000000000000000000),false,MergedCutProfiles.Batch684.profile27381,(fun _ => MergedCutProfiles.Batch684.profile27381)⟩
theorem profilesValid4871 : retention4871.ProfilesValid := by
  exact MergedCutProfiles.Batch684.valid27381
theorem numericValid4871 : retention4871.NumericValid := by decide +kernel
def certificate4871 : RatCutBinCertificate := ⟨⟨retention4871,(931736723831560059/500000000000000000),(5622540848385301/62500000000000000),(2973523243523444443/250000000000000000),(3809134603006935974091/125000000000000000),(146652593543592933/62500000000000000)⟩,(999944077091803931/1000000000000000000),(50231474245522721/62500000000000000),(516682170978597/25000000000000000),(5599528578113993/500000000000000000)⟩
theorem valid4871 : certificate4871.Valid := by decide +kernel
theorem sound4871 : certificate4871.Sound := rat_cut_bin_certificate_sound certificate4871 profilesValid4871 numericValid4871 valid4871

def certificates : List RatCutBinCertificate := [certificate4860,certificate4861,certificate4862,certificate4863,certificate4864,certificate4865,certificate4866,certificate4867,certificate4868,certificate4869,certificate4870,certificate4871]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4860,List.forall_mem_cons.mpr ⟨sound4861,List.forall_mem_cons.mpr ⟨sound4862,List.forall_mem_cons.mpr ⟨sound4863,List.forall_mem_cons.mpr ⟨sound4864,List.forall_mem_cons.mpr ⟨sound4865,List.forall_mem_cons.mpr ⟨sound4866,List.forall_mem_cons.mpr ⟨sound4867,List.forall_mem_cons.mpr ⟨sound4868,List.forall_mem_cons.mpr ⟨sound4869,List.forall_mem_cons.mpr ⟨sound4870,List.forall_mem_cons.mpr ⟨sound4871,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch405
