import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch354
import Cycle12.MergedCutProfiles.Batch355
import Cycle12.MergedCutProfiles.Batch356
import Cycle12.MergedCutProfiles.Batch357
import Cycle12.MergedCutProfiles.Batch475
import Cycle12.MergedCutProfiles.Batch603
import Cycle12.MergedCutProfiles.Batch604
import Cycle12.MergedCutProfiles.Batch681
import Cycle12.MergedCutProfiles.Batch682

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch403

def retention4836 : RatCutRetentionCertificate := ⟨(327/8000),(41/1000),(115818841708279334/497164596825374154729),(86004090377435149/125000000000000000),4,(6585623988961895854251773571481528263/2752130892077924768000000000000000000),false,MergedCutProfiles.Batch681.profile27269,(fun _ => MergedCutProfiles.Batch681.profile27269)⟩
theorem profilesValid4836 : retention4836.ProfilesValid := by
  exact MergedCutProfiles.Batch681.valid27269
theorem numericValid4836 : retention4836.NumericValid := by decide +kernel
def certificate4836 : RatCutBinCertificate := ⟨⟨retention4836,(921729918191299331/500000000000000000),(77009395027439323/1000000000000000000),(11506622440002589959/1000000000000000000),(17173662233480934388993/500000000000000000),(2343567850783822951/1000000000000000000)⟩,(999950434298893991/1000000000000000000),(432171774323935681/500000000000000000),(964815869526681/100000000000000000),(2330162216050653/500000000000000000)⟩
theorem valid4836 : certificate4836.Valid := by decide +kernel
theorem sound4836 : certificate4836.Sound := rat_cut_bin_certificate_sound certificate4836 profilesValid4836 numericValid4836 valid4836

def retention4837 : RatCutRetentionCertificate := ⟨(327/8000),(41/1000),(23079244017670645/76486861050057562266),(173728262562419001/250000000000000000),4,(416317811841080910814689908429032367/173728262562419001000000000000000000),false,MergedCutProfiles.Batch681.profile27270,(fun _ => MergedCutProfiles.Batch681.profile27270)⟩
theorem profilesValid4837 : retention4837.ProfilesValid := by
  exact MergedCutProfiles.Batch681.valid27270
theorem numericValid4837 : retention4837.NumericValid := by decide +kernel
def certificate4837 : RatCutBinCertificate := ⟨⟨retention4837,(921729918191299331/500000000000000000),(77009395027439323/1000000000000000000),(11506622440002589959/1000000000000000000),(17173662233480934388993/500000000000000000),(234702323333448903/100000000000000000)⟩,(999950434298893991/1000000000000000000),(86088030612910263/100000000000000000),(10159994906227361/1000000000000000000),(196883360942077/40000000000000000)⟩
theorem valid4837 : certificate4837.Valid := by decide +kernel
theorem sound4837 : certificate4837.Sound := rat_cut_bin_certificate_sound certificate4837 profilesValid4837 numericValid4837 valid4837

def retention4838 : RatCutRetentionCertificate := ⟨(327/8000),(41/1000),(159062605777592803/76486861050057562266),(180018103337831031/200000000000000000),(18/5),(8621477089735011189855105220419126911/3600362066756620620000000000000000000),false,MergedCutProfiles.Batch681.profile27271,(fun _ => MergedCutProfiles.Batch681.profile27271)⟩
theorem profilesValid4838 : retention4838.ProfilesValid := by
  exact MergedCutProfiles.Batch681.valid27271
theorem numericValid4838 : retention4838.NumericValid := by decide +kernel
def certificate4838 : RatCutBinCertificate := ⟨⟨retention4838,(921729918191299331/500000000000000000),(77009395027439323/1000000000000000000),(11506622440002589959/1000000000000000000),(17173662233480934388993/500000000000000000),(293774829827863571/125000000000000000)⟩,(999950434298893991/1000000000000000000),(4049233465294283/5000000000000000),(9674142070007917/500000000000000000),(10512501429361457/1000000000000000000)⟩
theorem valid4838 : certificate4838.Valid := by decide +kernel
theorem sound4838 : certificate4838.Sound := rat_cut_bin_certificate_sound certificate4838 profilesValid4838 numericValid4838 valid4838

def retention4839 : RatCutRetentionCertificate := ⟨(327/8000),(41/1000),(1/40),(6203441625326119317/1000000000000000000),(13/10),(5455407703164142126916703993655190427359/2481376650130447726800000000000000000000),false,MergedCutProfiles.Batch681.profile27272,(fun _ => MergedCutProfiles.Batch681.profile27272)⟩
theorem profilesValid4839 : retention4839.ProfilesValid := by
  exact MergedCutProfiles.Batch681.valid27272
theorem numericValid4839 : retention4839.NumericValid := by decide +kernel
def certificate4839 : RatCutBinCertificate := ⟨⟨retention4839,(921729918191299331/500000000000000000),(77009395027439323/1000000000000000000),(11506622440002589959/1000000000000000000),(17173662233480934388993/500000000000000000),(17050796226896889/7812500000000000)⟩,(999950434298893991/1000000000000000000),(716579480011423573/1000000000000000000),(223044321861999/5000000000000000),(61983847813965891/1000000000000000000)⟩
theorem valid4839 : certificate4839.Valid := by decide +kernel
theorem sound4839 : certificate4839.Sound := rat_cut_bin_certificate_sound certificate4839 profilesValid4839 numericValid4839 valid4839

def retention4840 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(617796762484435519/2827245510846838412974),(67595933938051/122070312500000),4,(961868719382228405578097484195822491/442996712656411033600000000000000000),true,MergedCutProfiles.Batch681.profile27273,![MergedCutProfiles.Batch681.profile27273,MergedCutProfiles.Batch681.profile27274,MergedCutProfiles.Batch681.profile27275,MergedCutProfiles.Batch681.profile27276,MergedCutProfiles.Batch603.profile24147,MergedCutProfiles.Batch681.profile27277,MergedCutProfiles.Batch681.profile27278,MergedCutProfiles.Batch681.profile27279,MergedCutProfiles.Batch604.profile24160,MergedCutProfiles.Batch603.profile24148,MergedCutProfiles.Batch682.profile27280,MergedCutProfiles.Batch682.profile27281,MergedCutProfiles.Batch682.profile27282,MergedCutProfiles.Batch603.profile24149,MergedCutProfiles.Batch682.profile27283,MergedCutProfiles.Batch682.profile27284]⟩
theorem profilesValid4840 : retention4840.ProfilesValid := by
  change ∀ j : Fin 16, (retention4840.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch681.valid27273
  · exact MergedCutProfiles.Batch681.valid27274
  · exact MergedCutProfiles.Batch681.valid27275
  · exact MergedCutProfiles.Batch681.valid27276
  · exact MergedCutProfiles.Batch603.valid24147
  · exact MergedCutProfiles.Batch681.valid27277
  · exact MergedCutProfiles.Batch681.valid27278
  · exact MergedCutProfiles.Batch681.valid27279
  · exact MergedCutProfiles.Batch604.valid24160
  · exact MergedCutProfiles.Batch603.valid24148
  · exact MergedCutProfiles.Batch682.valid27280
  · exact MergedCutProfiles.Batch682.valid27281
  · exact MergedCutProfiles.Batch682.valid27282
  · exact MergedCutProfiles.Batch603.valid24149
  · exact MergedCutProfiles.Batch682.valid27283
  · exact MergedCutProfiles.Batch682.valid27284
theorem numericValid4840 : retention4840.NumericValid := by decide +kernel
def certificate4840 : RatCutBinCertificate := ⟨⟨retention4840,(1868372649154060891/1000000000000000000),(81190354661587239/1000000000000000000),(230577501884345397/20000000000000000),(32772344532278908303541/1000000000000000000),(2118646346690020991/1000000000000000000)⟩,(49997368973750471/50000000000000000),(397437758072407197/500000000000000000),(4529020468215431/200000000000000000),(9678966696778369/1000000000000000000)⟩
theorem valid4840 : certificate4840.Valid := by decide +kernel
theorem sound4840 : certificate4840.Sound := rat_cut_bin_certificate_sound certificate4840 profilesValid4840 numericValid4840 valid4840

def retention4841 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(565256235000000000/1413622755423419206487),(617796762484435519/1000000000000000000),4,(5693711238883716794221181393121780927/2471187049937742076000000000000000000),true,MergedCutProfiles.Batch681.profile27274,![MergedCutProfiles.Batch681.profile27274,MergedCutProfiles.Batch682.profile27285,MergedCutProfiles.Batch682.profile27286,MergedCutProfiles.Batch681.profile27278,MergedCutProfiles.Batch604.profile24160,MergedCutProfiles.Batch682.profile27280,MergedCutProfiles.Batch682.profile27282,MergedCutProfiles.Batch603.profile24149,MergedCutProfiles.Batch682.profile27284,MergedCutProfiles.Batch604.profile24161,MergedCutProfiles.Batch603.profile24150,MergedCutProfiles.Batch682.profile27287,MergedCutProfiles.Batch475.profile19025,MergedCutProfiles.Batch682.profile27288,MergedCutProfiles.Batch604.profile24162,MergedCutProfiles.Batch603.profile24152]⟩
theorem profilesValid4841 : retention4841.ProfilesValid := by
  change ∀ j : Fin 16, (retention4841.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch681.valid27274
  · exact MergedCutProfiles.Batch682.valid27285
  · exact MergedCutProfiles.Batch682.valid27286
  · exact MergedCutProfiles.Batch681.valid27278
  · exact MergedCutProfiles.Batch604.valid24160
  · exact MergedCutProfiles.Batch682.valid27280
  · exact MergedCutProfiles.Batch682.valid27282
  · exact MergedCutProfiles.Batch603.valid24149
  · exact MergedCutProfiles.Batch682.valid27284
  · exact MergedCutProfiles.Batch604.valid24161
  · exact MergedCutProfiles.Batch603.valid24150
  · exact MergedCutProfiles.Batch682.valid27287
  · exact MergedCutProfiles.Batch475.valid19025
  · exact MergedCutProfiles.Batch682.valid27288
  · exact MergedCutProfiles.Batch604.valid24162
  · exact MergedCutProfiles.Batch603.valid24152
theorem numericValid4841 : retention4841.NumericValid := by decide +kernel
def certificate4841 : RatCutBinCertificate := ⟨⟨retention4841,(1868372649154060891/1000000000000000000),(81190354661587239/1000000000000000000),(230577501884345397/20000000000000000),(32772344532278908303541/1000000000000000000),(2251407982302540309/1000000000000000000)⟩,(49997368973750471/50000000000000000),(347419442219308561/500000000000000000),(26093726640843029/500000000000000000),(23923085488904443/1000000000000000000)⟩
theorem valid4841 : certificate4841.Valid := by decide +kernel
theorem sound4841 : certificate4841.Sound := rat_cut_bin_certificate_sound certificate4841 profilesValid4841 numericValid4841 valid4841

def retention4842 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(2667396482512394507/2827245510846838412974),(113051247/100000000),(14/5),(10808675384466555056773967804396172791/4522049880000000000000000000000000000),true,MergedCutProfiles.Batch681.profile27276,![MergedCutProfiles.Batch681.profile27276,MergedCutProfiles.Batch604.profile24160,MergedCutProfiles.Batch682.profile27282,MergedCutProfiles.Batch682.profile27289,MergedCutProfiles.Batch682.profile27287,MergedCutProfiles.Batch682.profile27288,MergedCutProfiles.Batch682.profile27290,MergedCutProfiles.Batch682.profile27291,MergedCutProfiles.Batch682.profile27292,MergedCutProfiles.Batch603.profile24155,MergedCutProfiles.Batch603.profile24156,MergedCutProfiles.Batch682.profile27293,MergedCutProfiles.Batch682.profile27294,MergedCutProfiles.Batch682.profile27295,MergedCutProfiles.Batch354.profile14198,MergedCutProfiles.Batch603.profile24158]⟩
theorem profilesValid4842 : retention4842.ProfilesValid := by
  change ∀ j : Fin 16, (retention4842.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch681.valid27276
  · exact MergedCutProfiles.Batch604.valid24160
  · exact MergedCutProfiles.Batch682.valid27282
  · exact MergedCutProfiles.Batch682.valid27289
  · exact MergedCutProfiles.Batch682.valid27287
  · exact MergedCutProfiles.Batch682.valid27288
  · exact MergedCutProfiles.Batch682.valid27290
  · exact MergedCutProfiles.Batch682.valid27291
  · exact MergedCutProfiles.Batch682.valid27292
  · exact MergedCutProfiles.Batch603.valid24155
  · exact MergedCutProfiles.Batch603.valid24156
  · exact MergedCutProfiles.Batch682.valid27293
  · exact MergedCutProfiles.Batch682.valid27294
  · exact MergedCutProfiles.Batch682.valid27295
  · exact MergedCutProfiles.Batch354.valid14198
  · exact MergedCutProfiles.Batch603.valid24158
theorem numericValid4842 : retention4842.NumericValid := by decide +kernel
def certificate4842 : RatCutBinCertificate := ⟨⟨retention4842,(1868372649154060891/1000000000000000000),(81190354661587239/1000000000000000000),(230577501884345397/20000000000000000),(32772344532278908303541/1000000000000000000),(1176687096683036559/500000000000000000)⟩,(49997368973750471/50000000000000000),(232656454068824043/500000000000000000),(44675381685489637/250000000000000000),(118676652235091037/1000000000000000000)⟩
theorem valid4842 : certificate4842.Valid := by decide +kernel
theorem sound4842 : certificate4842.Sound := rat_cut_bin_certificate_sound certificate4842 profilesValid4842 numericValid4842 valid4842

def retention4843 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(32000000000000000000/1413622755423419206487),(2667396482512394507/1000000000000000000),(8/5),(2800675873023156719671/1280000000000000000000),true,MergedCutProfiles.Batch604.profile24172,![MergedCutProfiles.Batch604.profile24172,MergedCutProfiles.Batch682.profile27296,MergedCutProfiles.Batch682.profile27297,MergedCutProfiles.Batch355.profile14233,MergedCutProfiles.Batch355.profile14220,MergedCutProfiles.Batch356.profile14256,MergedCutProfiles.Batch604.profile24180,MergedCutProfiles.Batch682.profile27298,MergedCutProfiles.Batch682.profile27299,MergedCutProfiles.Batch682.profile27300,MergedCutProfiles.Batch682.profile27301,MergedCutProfiles.Batch356.profile14261,MergedCutProfiles.Batch356.profile14249,MergedCutProfiles.Batch682.profile27302,MergedCutProfiles.Batch682.profile27303,MergedCutProfiles.Batch682.profile27304]⟩
theorem profilesValid4843 : retention4843.ProfilesValid := by
  change ∀ j : Fin 16, (retention4843.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch604.valid24172
  · exact MergedCutProfiles.Batch682.valid27296
  · exact MergedCutProfiles.Batch682.valid27297
  · exact MergedCutProfiles.Batch355.valid14233
  · exact MergedCutProfiles.Batch355.valid14220
  · exact MergedCutProfiles.Batch356.valid14256
  · exact MergedCutProfiles.Batch604.valid24180
  · exact MergedCutProfiles.Batch682.valid27298
  · exact MergedCutProfiles.Batch682.valid27299
  · exact MergedCutProfiles.Batch682.valid27300
  · exact MergedCutProfiles.Batch682.valid27301
  · exact MergedCutProfiles.Batch356.valid14261
  · exact MergedCutProfiles.Batch356.valid14249
  · exact MergedCutProfiles.Batch682.valid27302
  · exact MergedCutProfiles.Batch682.valid27303
  · exact MergedCutProfiles.Batch682.valid27304
theorem numericValid4843 : retention4843.NumericValid := by decide +kernel
def certificate4843 : RatCutBinCertificate := ⟨⟨retention4843,(1868372649154060891/1000000000000000000),(81190354661587239/1000000000000000000),(230577501884345397/20000000000000000),(32772344532278908303541/1000000000000000000),(1083487821933713693/500000000000000000)⟩,(49997368973750471/50000000000000000),(354979371329941969/1000000000000000000),(69341252695171803/250000000000000000),(28514255571722973/100000000000000000)⟩
theorem valid4843 : certificate4843.Valid := by decide +kernel
theorem sound4843 : certificate4843.Sound := rat_cut_bin_certificate_sound certificate4843 profilesValid4843 numericValid4843 valid4843

def retention4844 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(1/2),64,1,(63846252801030998518146708381256195671/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch357.profile14283,(fun _ => MergedCutProfiles.Batch357.profile14283)⟩
theorem profilesValid4844 : retention4844.ProfilesValid := by
  exact MergedCutProfiles.Batch357.valid14283
theorem numericValid4844 : retention4844.NumericValid := by decide +kernel
def certificate4844 : RatCutBinCertificate := ⟨⟨retention4844,(1868372649154060891/1000000000000000000),(81190354661587239/1000000000000000000),(230577501884345397/20000000000000000),(32772344532278908303541/1000000000000000000),(984439968437171567/1000000000000000000)⟩,(49997368973750471/50000000000000000),(85637027995287/156250000000000),(122342659911090959/1000000000000000000),(4744327570855129/40000000000000000)⟩
theorem valid4844 : certificate4844.Valid := by decide +kernel
theorem sound4844 : certificate4844.Sound := rat_cut_bin_certificate_sound certificate4844 profilesValid4844 numericValid4844 valid4844

def retention4845 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(32000000000000000000/1413622755423419206487),(6460743440080467189/200000000000000000),1,(7820349184475959189547352327715425861/3589301911155815105000000000000000000),false,MergedCutProfiles.Batch682.profile27305,(fun _ => MergedCutProfiles.Batch682.profile27305)⟩
theorem profilesValid4845 : retention4845.ProfilesValid := by
  exact MergedCutProfiles.Batch682.valid27305
theorem numericValid4845 : retention4845.NumericValid := by decide +kernel
def certificate4845 : RatCutBinCertificate := ⟨⟨retention4845,(1744631854154060891/1000000000000000000),(81190354661587239/1000000000000000000),(230577501884345397/20000000000000000),(32772344532278908303541/1000000000000000000),(2166507614722135783/1000000000000000000)⟩,(199990172900740259/200000000000000000),(412475974724691/20000000000000000),(218027167774669431/250000000000000000),(1770587739621769459/1000000000000000000)⟩
theorem valid4845 : certificate4845.Valid := by decide +kernel
theorem sound4845 : certificate4845.Sound := rat_cut_bin_certificate_sound certificate4845 profilesValid4845 numericValid4845 valid4845

def retention4846 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(1/2),64,1,(63846252801030998518146708381256195671/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch357.profile14283,(fun _ => MergedCutProfiles.Batch357.profile14283)⟩
theorem profilesValid4846 : retention4846.ProfilesValid := by
  exact MergedCutProfiles.Batch357.valid14283
theorem numericValid4846 : retention4846.NumericValid := by decide +kernel
def certificate4846 : RatCutBinCertificate := ⟨⟨retention4846,(1744631854154060891/1000000000000000000),(81190354661587239/1000000000000000000),(230577501884345397/20000000000000000),(32772344532278908303541/1000000000000000000),(123163924282020649/125000000000000000)⟩,(199990172900740259/200000000000000000),(22673855832287477/500000000000000000),(50060322591744053/62500000000000000),(194298903472658003/250000000000000000)⟩
theorem valid4846 : certificate4846.Valid := by decide +kernel
theorem sound4846 : certificate4846.Sound := rat_cut_bin_certificate_sound certificate4846 profilesValid4846 numericValid4846 valid4846

def retention4847 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(695779427767055605/2827245510846838412974),(172222630635409803/250000000000000000),4,(146555014172707239889747651013638899/61234713114812374400000000000000000),false,MergedCutProfiles.Batch682.profile27306,(fun _ => MergedCutProfiles.Batch682.profile27306)⟩
theorem profilesValid4847 : retention4847.ProfilesValid := by
  exact MergedCutProfiles.Batch682.valid27306
theorem numericValid4847 : retention4847.NumericValid := by decide +kernel
def certificate4847 : RatCutBinCertificate := ⟨⟨retention4847,(1842166636154060891/1000000000000000000),(81190354661587239/1000000000000000000),(230577501884345397/20000000000000000),(32772344532278908303541/1000000000000000000),(1170719746998653177/500000000000000000)⟩,(999948117539833849/1000000000000000000),(864216494670062907/1000000000000000000),(4833345296685789/500000000000000000),(4666785226423169/1000000000000000000)⟩
theorem valid4847 : certificate4847.Valid := by decide +kernel
theorem sound4847 : certificate4847.Sound := rat_cut_bin_certificate_sound certificate4847 profilesValid4847 numericValid4847 valid4847

def certificates : List RatCutBinCertificate := [certificate4836,certificate4837,certificate4838,certificate4839,certificate4840,certificate4841,certificate4842,certificate4843,certificate4844,certificate4845,certificate4846,certificate4847]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4836,List.forall_mem_cons.mpr ⟨sound4837,List.forall_mem_cons.mpr ⟨sound4838,List.forall_mem_cons.mpr ⟨sound4839,List.forall_mem_cons.mpr ⟨sound4840,List.forall_mem_cons.mpr ⟨sound4841,List.forall_mem_cons.mpr ⟨sound4842,List.forall_mem_cons.mpr ⟨sound4843,List.forall_mem_cons.mpr ⟨sound4844,List.forall_mem_cons.mpr ⟨sound4845,List.forall_mem_cons.mpr ⟨sound4846,List.forall_mem_cons.mpr ⟨sound4847,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch403
