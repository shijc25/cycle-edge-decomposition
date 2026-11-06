import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch305
import Cycle12.MergedCutProfiles.Batch306
import Cycle12.MergedCutProfiles.Batch307

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch160

def retention1920 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(1/2),(936610154132484893/200000000000000000),(11/10),(73914832894438762026091865633444984719/74928812330598791440000000000000000000),false,MergedCutProfiles.Batch305.profile12226,(fun _ => MergedCutProfiles.Batch305.profile12226)⟩
theorem profilesValid1920 : retention1920.ProfilesValid := by
  exact MergedCutProfiles.Batch305.valid12226
theorem numericValid1920 : retention1920.NumericValid := by decide +kernel
def certificate1920 : RatCutBinCertificate := ⟨⟨retention1920,(483786689462153949/200000000000000000),(121143195939341811/500000000000000000),(9052768925236129457/500000000000000000),(34193528398953411263/200000000000000000),(950850731358201027/1000000000000000000)⟩,(494589501460708283/500000000000000000),(53344498764779201/125000000000000000),(209842396513569837/1000000000000000000),(153458011744023941/1000000000000000000)⟩
theorem valid1920 : certificate1920.Valid := by decide +kernel
theorem sound1920 : certificate1920.Sound := rat_cut_bin_certificate_sound certificate1920 profilesValid1920 numericValid1920 valid1920

def retention1921 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(1/2),64,1,(255419871002463909042457265882361431119/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch305.profile12226,(fun _ => MergedCutProfiles.Batch305.profile12226)⟩
theorem profilesValid1921 : retention1921.ProfilesValid := by
  exact MergedCutProfiles.Batch305.valid12226
theorem numericValid1921 : retention1921.NumericValid := by decide +kernel
def certificate1921 : RatCutBinCertificate := ⟨⟨retention1921,(483786689462153949/200000000000000000),(121143195939341811/500000000000000000),(9052768925236129457/500000000000000000),(34193528398953411263/200000000000000000),(965363242879281727/1000000000000000000)⟩,(494589501460708283/500000000000000000),(380007587113277889/1000000000000000000),(252308286460108811/1000000000000000000),(237326516720074073/1000000000000000000)⟩
theorem valid1921 : certificate1921.Valid := by decide +kernel
theorem sound1921 : certificate1921.Sound := rat_cut_bin_certificate_sound certificate1921 profilesValid1921 numericValid1921 valid1921

def retention1922 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(4331361531394973881/9412525033197477019),(2767977877874708691/1000000000000000000),(5/4),(189238911327008746909056441143809942799/177150584183981356224000000000000000000),false,MergedCutProfiles.Batch305.profile12227,(fun _ => MergedCutProfiles.Batch305.profile12227)⟩
theorem profilesValid1922 : retention1922.ProfilesValid := by
  exact MergedCutProfiles.Batch305.valid12227
theorem numericValid1922 : retention1922.NumericValid := by decide +kernel
def certificate1922 : RatCutBinCertificate := ⟨⟨retention1922,(546849352262153949/200000000000000000),(121143195939341811/500000000000000000),(9052768925236129457/500000000000000000),(34193528398953411263/200000000000000000),(1022482095800649909/1000000000000000000)⟩,(493881539091200339/500000000000000000),(37009380530748691/100000000000000000),(262030139892462317/1000000000000000000),(170939121785614077/1000000000000000000)⟩
theorem valid1922 : certificate1922.Valid := by decide +kernel
theorem sound1922 : certificate1922.Sound := rat_cut_bin_certificate_sound certificate1922 profilesValid1922 numericValid1922 valid1922

def retention1923 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(4643805820564908374/9412525033197477019),(4331361531394973881/1000000000000000000),(11/10),(1724611093874394463982788531445349868279/1732544612557989552400000000000000000000),false,MergedCutProfiles.Batch305.profile12228,(fun _ => MergedCutProfiles.Batch305.profile12228)⟩
theorem profilesValid1923 : retention1923.ProfilesValid := by
  exact MergedCutProfiles.Batch305.valid12228
theorem numericValid1923 : retention1923.NumericValid := by decide +kernel
def certificate1923 : RatCutBinCertificate := ⟨⟨retention1923,(546849352262153949/200000000000000000),(121143195939341811/500000000000000000),(9052768925236129457/500000000000000000),(34193528398953411263/200000000000000000),(119395071746238757/125000000000000000)⟩,(493881539091200339/500000000000000000),(198089357960433311/500000000000000000),(237001916944783151/1000000000000000000),(85858585816604313/500000000000000000)⟩
theorem valid1923 : certificate1923.Valid := by decide +kernel
theorem sound1923 : certificate1923.Sound := rat_cut_bin_certificate_sound certificate1923 profilesValid1923 numericValid1923 valid1923

def retention1924 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(4690243878770557458/9412525033197477019),(2321902910282454187/500000000000000000),(11/10),(114855853676651975717765093564011085509/116095145514122709350000000000000000000),false,MergedCutProfiles.Batch305.profile12229,(fun _ => MergedCutProfiles.Batch305.profile12229)⟩
theorem profilesValid1924 : retention1924.ProfilesValid := by
  exact MergedCutProfiles.Batch305.valid12229
theorem numericValid1924 : retention1924.NumericValid := by decide +kernel
def certificate1924 : RatCutBinCertificate := ⟨⟨retention1924,(546849352262153949/200000000000000000),(121143195939341811/500000000000000000),(9052768925236129457/500000000000000000),(34193528398953411263/200000000000000000),(237266424609200919/250000000000000000)⟩,(493881539091200339/500000000000000000),(398722965456363221/1000000000000000000),(58663621430709729/250000000000000000),(85436490563853611/500000000000000000)⟩
theorem valid1924 : certificate1924.Valid := by decide +kernel
theorem sound1924 : certificate1924.Sound := rat_cut_bin_certificate_sound certificate1924 profilesValid1924 numericValid1924 valid1924

def retention1925 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(1/2),(2345121939385278729/500000000000000000),(11/10),(115676843666965941112164586189659070181/117256096969263936450000000000000000000),false,MergedCutProfiles.Batch305.profile12226,(fun _ => MergedCutProfiles.Batch305.profile12226)⟩
theorem profilesValid1925 : retention1925.ProfilesValid := by
  exact MergedCutProfiles.Batch305.valid12226
theorem numericValid1925 : retention1925.NumericValid := by decide +kernel
def certificate1925 : RatCutBinCertificate := ⟨⟨retention1925,(546849352262153949/200000000000000000),(121143195939341811/500000000000000000),(9052768925236129457/500000000000000000),(34193528398953411263/200000000000000000),(236568048167009253/250000000000000000)⟩,(493881539091200339/500000000000000000),(39990004210806279/100000000000000000),(116786980993054201/500000000000000000),(84950908008628639/500000000000000000)⟩
theorem valid1925 : certificate1925.Valid := by decide +kernel
theorem sound1925 : certificate1925.Sound := rat_cut_bin_certificate_sound certificate1925 profilesValid1925 numericValid1925 valid1925

def retention1926 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(1351099432874585923/9244737841268092559),(453735087501386871/500000000000000000),(12/5),(283300986558246770131/160000000000000000000),true,MergedCutProfiles.Batch305.profile12230,![MergedCutProfiles.Batch305.profile12230,MergedCutProfiles.Batch305.profile12231,MergedCutProfiles.Batch305.profile12232,MergedCutProfiles.Batch305.profile12233,MergedCutProfiles.Batch305.profile12234,MergedCutProfiles.Batch305.profile12235,MergedCutProfiles.Batch305.profile12236,MergedCutProfiles.Batch305.profile12237,MergedCutProfiles.Batch305.profile12238,MergedCutProfiles.Batch305.profile12239,MergedCutProfiles.Batch306.profile12240,MergedCutProfiles.Batch306.profile12241,MergedCutProfiles.Batch306.profile12242,MergedCutProfiles.Batch306.profile12243,MergedCutProfiles.Batch306.profile12244,MergedCutProfiles.Batch306.profile12245]⟩
theorem profilesValid1926 : retention1926.ProfilesValid := by
  change ∀ j : Fin 16, (retention1926.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch305.valid12230
  · exact MergedCutProfiles.Batch305.valid12231
  · exact MergedCutProfiles.Batch305.valid12232
  · exact MergedCutProfiles.Batch305.valid12233
  · exact MergedCutProfiles.Batch305.valid12234
  · exact MergedCutProfiles.Batch305.valid12235
  · exact MergedCutProfiles.Batch305.valid12236
  · exact MergedCutProfiles.Batch305.valid12237
  · exact MergedCutProfiles.Batch305.valid12238
  · exact MergedCutProfiles.Batch305.valid12239
  · exact MergedCutProfiles.Batch306.valid12240
  · exact MergedCutProfiles.Batch306.valid12241
  · exact MergedCutProfiles.Batch306.valid12242
  · exact MergedCutProfiles.Batch306.valid12243
  · exact MergedCutProfiles.Batch306.valid12244
  · exact MergedCutProfiles.Batch306.valid12245
theorem numericValid1926 : retention1926.NumericValid := by decide +kernel
def certificate1926 : RatCutBinCertificate := ⟨⟨retention1926,(2428078689874166461/1000000000000000000),(123364672097640231/500000000000000000),(4570958873971526223/250000000000000000),(84787762377982862633/500000000000000000),(422985382548630983/250000000000000000)⟩,(494555334263642661/500000000000000000),(168688078011405987/500000000000000000),(296037204987180819/1000000000000000000),(77773709317075593/500000000000000000)⟩
theorem valid1926 : certificate1926.Valid := by decide +kernel
theorem sound1926 : certificate1926.Sound := rat_cut_bin_certificate_sound certificate1926 profilesValid1926 numericValid1926 valid1926

def retention1927 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(2657912801639541935/9244737841268092559),(1351099432874585923/1000000000000000000),(17/10),(1820389200364243575703/1280000000000000000000),true,MergedCutProfiles.Batch306.profile12246,![MergedCutProfiles.Batch306.profile12246,MergedCutProfiles.Batch306.profile12247,MergedCutProfiles.Batch306.profile12248,MergedCutProfiles.Batch306.profile12249,MergedCutProfiles.Batch306.profile12250,MergedCutProfiles.Batch306.profile12251,MergedCutProfiles.Batch306.profile12252,MergedCutProfiles.Batch306.profile12253,MergedCutProfiles.Batch306.profile12254,MergedCutProfiles.Batch306.profile12255,MergedCutProfiles.Batch306.profile12256,MergedCutProfiles.Batch306.profile12257,MergedCutProfiles.Batch306.profile12258,MergedCutProfiles.Batch306.profile12259,MergedCutProfiles.Batch306.profile12260,MergedCutProfiles.Batch306.profile12261]⟩
theorem profilesValid1927 : retention1927.ProfilesValid := by
  change ∀ j : Fin 16, (retention1927.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch306.valid12246
  · exact MergedCutProfiles.Batch306.valid12247
  · exact MergedCutProfiles.Batch306.valid12248
  · exact MergedCutProfiles.Batch306.valid12249
  · exact MergedCutProfiles.Batch306.valid12250
  · exact MergedCutProfiles.Batch306.valid12251
  · exact MergedCutProfiles.Batch306.valid12252
  · exact MergedCutProfiles.Batch306.valid12253
  · exact MergedCutProfiles.Batch306.valid12254
  · exact MergedCutProfiles.Batch306.valid12255
  · exact MergedCutProfiles.Batch306.valid12256
  · exact MergedCutProfiles.Batch306.valid12257
  · exact MergedCutProfiles.Batch306.valid12258
  · exact MergedCutProfiles.Batch306.valid12259
  · exact MergedCutProfiles.Batch306.valid12260
  · exact MergedCutProfiles.Batch306.valid12261
theorem numericValid1927 : retention1927.NumericValid := by decide +kernel
def certificate1927 : RatCutBinCertificate := ⟨⟨retention1927,(2428078689874166461/1000000000000000000),(123364672097640231/500000000000000000),(4570958873971526223/250000000000000000),(84787762377982862633/500000000000000000),(1366442497725492931/1000000000000000000)⟩,(494555334263642661/500000000000000000),(183575378972630053/500000000000000000),(264966967224948299/1000000000000000000),(155676730605911693/1000000000000000000)⟩
theorem valid1927 : certificate1927.Valid := by decide +kernel
theorem sound1927 : certificate1927.Sound := rat_cut_bin_certificate_sound certificate1927 profilesValid1927 numericValid1927 valid1927

def retention1928 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(4077179214986203741/9244737841268092559),(531582560327908387/200000000000000000),(11/10),(275658102719366714551/256000000000000000000),true,MergedCutProfiles.Batch306.profile12262,![MergedCutProfiles.Batch306.profile12262,MergedCutProfiles.Batch306.profile12263,MergedCutProfiles.Batch306.profile12264,MergedCutProfiles.Batch306.profile12265,MergedCutProfiles.Batch306.profile12266,MergedCutProfiles.Batch306.profile12267,MergedCutProfiles.Batch306.profile12268,MergedCutProfiles.Batch306.profile12269,MergedCutProfiles.Batch306.profile12270,MergedCutProfiles.Batch306.profile12271,MergedCutProfiles.Batch306.profile12272,MergedCutProfiles.Batch306.profile12273,MergedCutProfiles.Batch306.profile12274,MergedCutProfiles.Batch306.profile12275,MergedCutProfiles.Batch306.profile12276,MergedCutProfiles.Batch306.profile12277]⟩
theorem profilesValid1928 : retention1928.ProfilesValid := by
  change ∀ j : Fin 16, (retention1928.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch306.valid12262
  · exact MergedCutProfiles.Batch306.valid12263
  · exact MergedCutProfiles.Batch306.valid12264
  · exact MergedCutProfiles.Batch306.valid12265
  · exact MergedCutProfiles.Batch306.valid12266
  · exact MergedCutProfiles.Batch306.valid12267
  · exact MergedCutProfiles.Batch306.valid12268
  · exact MergedCutProfiles.Batch306.valid12269
  · exact MergedCutProfiles.Batch306.valid12270
  · exact MergedCutProfiles.Batch306.valid12271
  · exact MergedCutProfiles.Batch306.valid12272
  · exact MergedCutProfiles.Batch306.valid12273
  · exact MergedCutProfiles.Batch306.valid12274
  · exact MergedCutProfiles.Batch306.valid12275
  · exact MergedCutProfiles.Batch306.valid12276
  · exact MergedCutProfiles.Batch306.valid12277
theorem numericValid1928 : retention1928.NumericValid := by decide +kernel
def certificate1928 : RatCutBinCertificate := ⟨⟨retention1928,(2428078689874166461/1000000000000000000),(123364672097640231/500000000000000000),(4570958873971526223/250000000000000000),(84787762377982862633/500000000000000000),(208145904500937151/200000000000000000)⟩,(494555334263642661/500000000000000000),(20762521048054167/50000000000000000),(109898069353640891/500000000000000000),(155103285265734917/1000000000000000000)⟩
theorem valid1928 : certificate1928.Valid := by decide +kernel
theorem sound1928 : certificate1928.Sound := rat_cut_bin_certificate_sound certificate1928 profilesValid1928 numericValid1928 valid1928

def retention1929 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(4503742370140446709/9244737841268092559),(4077179214986203741/1000000000000000000),1,(250476275451077252701/256000000000000000000),true,MergedCutProfiles.Batch306.profile12278,![MergedCutProfiles.Batch306.profile12278,MergedCutProfiles.Batch306.profile12279,MergedCutProfiles.Batch305.profile12239,MergedCutProfiles.Batch307.profile12280,MergedCutProfiles.Batch307.profile12281,MergedCutProfiles.Batch307.profile12282,MergedCutProfiles.Batch307.profile12283,MergedCutProfiles.Batch307.profile12284,MergedCutProfiles.Batch307.profile12285,MergedCutProfiles.Batch307.profile12286,MergedCutProfiles.Batch307.profile12287,MergedCutProfiles.Batch307.profile12288,MergedCutProfiles.Batch307.profile12289,MergedCutProfiles.Batch307.profile12290,MergedCutProfiles.Batch307.profile12291,MergedCutProfiles.Batch307.profile12292]⟩
theorem profilesValid1929 : retention1929.ProfilesValid := by
  change ∀ j : Fin 16, (retention1929.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch306.valid12278
  · exact MergedCutProfiles.Batch306.valid12279
  · exact MergedCutProfiles.Batch305.valid12239
  · exact MergedCutProfiles.Batch307.valid12280
  · exact MergedCutProfiles.Batch307.valid12281
  · exact MergedCutProfiles.Batch307.valid12282
  · exact MergedCutProfiles.Batch307.valid12283
  · exact MergedCutProfiles.Batch307.valid12284
  · exact MergedCutProfiles.Batch307.valid12285
  · exact MergedCutProfiles.Batch307.valid12286
  · exact MergedCutProfiles.Batch307.valid12287
  · exact MergedCutProfiles.Batch307.valid12288
  · exact MergedCutProfiles.Batch307.valid12289
  · exact MergedCutProfiles.Batch307.valid12290
  · exact MergedCutProfiles.Batch307.valid12291
  · exact MergedCutProfiles.Batch307.valid12292
theorem numericValid1929 : retention1929.NumericValid := by decide +kernel
def certificate1929 : RatCutBinCertificate := ⟨⟨retention1929,(2428078689874166461/1000000000000000000),(123364672097640231/500000000000000000),(4570958873971526223/250000000000000000),(84787762377982862633/500000000000000000),(94564579927252011/100000000000000000)⟩,(494555334263642661/500000000000000000),(215271312547314303/500000000000000000),(3228667669731957/15625000000000000),(156656213691168631/1000000000000000000)⟩
theorem valid1929 : certificate1929.Valid := by decide +kernel
theorem sound1929 : certificate1929.Sound := rat_cut_bin_certificate_sound certificate1929 profilesValid1929 numericValid1929 valid1929

def retention1930 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(417660690161842699/840430712842553869),(4503742370140446709/1000000000000000000),(11/10),(1784390062875870344699659975800652377319/1801496948056178683600000000000000000000),false,MergedCutProfiles.Batch307.profile12293,(fun _ => MergedCutProfiles.Batch307.profile12293)⟩
theorem profilesValid1930 : retention1930.ProfilesValid := by
  exact MergedCutProfiles.Batch307.valid12293
theorem numericValid1930 : retention1930.NumericValid := by decide +kernel
def certificate1930 : RatCutBinCertificate := ⟨⟨retention1930,(2428078689874166461/1000000000000000000),(123364672097640231/500000000000000000),(4570958873971526223/250000000000000000),(84787762377982862633/500000000000000000),(119306435238864161/125000000000000000)⟩,(494555334263642661/500000000000000000),(210960178393423029/500000000000000000),(106993774956787071/500000000000000000),(156081195881269393/1000000000000000000)⟩
theorem valid1930 : certificate1930.Valid := by decide +kernel
theorem sound1930 : certificate1930.Sound := rat_cut_bin_certificate_sound certificate1930 profilesValid1930 numericValid1930 valid1930

def retention1931 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(1/2),(4594267591780269689/1000000000000000000),(11/10),(1811350084154687772984051459976896722479/1837707036712107875600000000000000000000),false,MergedCutProfiles.Batch307.profile12294,(fun _ => MergedCutProfiles.Batch307.profile12294)⟩
theorem profilesValid1931 : retention1931.ProfilesValid := by
  exact MergedCutProfiles.Batch307.valid12294
theorem numericValid1931 : retention1931.NumericValid := by decide +kernel
def certificate1931 : RatCutBinCertificate := ⟨⟨retention1931,(2428078689874166461/1000000000000000000),(123364672097640231/500000000000000000),(4570958873971526223/250000000000000000),(84787762377982862633/500000000000000000),(59350332165068603/62500000000000000)⟩,(494555334263642661/500000000000000000),(84638663233760561/200000000000000000),(106445504553186151/500000000000000000),(155066530970201677/1000000000000000000)⟩
theorem valid1931 : certificate1931.Valid := by decide +kernel
theorem sound1931 : certificate1931.Sound := rat_cut_bin_certificate_sound certificate1931 profilesValid1931 numericValid1931 valid1931

def certificates : List RatCutBinCertificate := [certificate1920,certificate1921,certificate1922,certificate1923,certificate1924,certificate1925,certificate1926,certificate1927,certificate1928,certificate1929,certificate1930,certificate1931]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1920,List.forall_mem_cons.mpr ⟨sound1921,List.forall_mem_cons.mpr ⟨sound1922,List.forall_mem_cons.mpr ⟨sound1923,List.forall_mem_cons.mpr ⟨sound1924,List.forall_mem_cons.mpr ⟨sound1925,List.forall_mem_cons.mpr ⟨sound1926,List.forall_mem_cons.mpr ⟨sound1927,List.forall_mem_cons.mpr ⟨sound1928,List.forall_mem_cons.mpr ⟨sound1929,List.forall_mem_cons.mpr ⟨sound1930,List.forall_mem_cons.mpr ⟨sound1931,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch160
