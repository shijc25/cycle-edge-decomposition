import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch303
import Cycle12.MergedCutProfiles.Batch304
import Cycle12.MergedCutProfiles.Batch305

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch159

def retention1908 : RatCutRetentionCertificate := ⟨(107/1600),(67/1000),(1/2),(4775547558273080407/1000000000000000000),(11/10),(1885907394008884566808728353262694100071/1910219023309232162800000000000000000000),false,MergedCutProfiles.Batch303.profile12158,(fun _ => MergedCutProfiles.Batch303.profile12158)⟩
theorem profilesValid1908 : retention1908.ProfilesValid := by
  exact MergedCutProfiles.Batch303.valid12158
theorem numericValid1908 : retention1908.NumericValid := by decide +kernel
def certificate1908 : RatCutBinCertificate := ⟨⟨retention1908,(1210339299435513181/500000000000000000),(11895173549139047/50000000000000000),(18061616308736539321/1000000000000000000),(4331171436219614029/25000000000000000),(190438120632679739/200000000000000000)⟩,(989299106743340583/1000000000000000000),(414534370247111441/1000000000000000000),(220426055559889/1000000000000000),(80934749565677561/500000000000000000)⟩
theorem valid1908 : certificate1908.Valid := by decide +kernel
theorem sound1908 : certificate1908.Sound := rat_cut_bin_certificate_sound certificate1908 profilesValid1908 numericValid1908 valid1908

def retention1909 : RatCutRetentionCertificate := ⟨(107/1600),(67/1000),(1/2),64,1,(63854918235650112212759369774927339199/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch303.profile12158,(fun _ => MergedCutProfiles.Batch303.profile12158)⟩
theorem profilesValid1909 : retention1909.ProfilesValid := by
  exact MergedCutProfiles.Batch303.valid12158
theorem numericValid1909 : retention1909.NumericValid := by decide +kernel
def certificate1909 : RatCutBinCertificate := ⟨⟨retention1909,(1210339299435513181/500000000000000000),(11895173549139047/50000000000000000),(18061616308736539321/1000000000000000000),(4331171436219614029/25000000000000000),(241461947382053941/250000000000000000)⟩,(989299106743340583/1000000000000000000),(370694479545407619/1000000000000000000),(130716807087529149/500000000000000000),(246061924734122501/1000000000000000000)⟩
theorem valid1909 : certificate1909.Valid := by decide +kernel
theorem sound1909 : certificate1909.Sound := rat_cut_bin_certificate_sound certificate1909 profilesValid1909 numericValid1909 valid1909

def retention1910 : RatCutRetentionCertificate := ⟨(107/1600),(67/1000),(32525861771089299/70472799357435143),(1413435205725931191/500000000000000000),(5/4),(48256935912250656745700031508397612231/45229926583229798112000000000000000000),false,MergedCutProfiles.Batch303.profile12159,(fun _ => MergedCutProfiles.Batch303.profile12159)⟩
theorem profilesValid1910 : retention1910.ProfilesValid := by
  exact MergedCutProfiles.Batch303.valid12159
theorem numericValid1910 : retention1910.NumericValid := by decide +kernel
def certificate1910 : RatCutBinCertificate := ⟨⟨retention1910,(1364516669435513181/500000000000000000),(11895173549139047/50000000000000000),(18061616308736539321/1000000000000000000),(4331171436219614029/25000000000000000),(25549367718130429/25000000000000000)⟩,(987930887553558009/1000000000000000000),(369708746796032287/1000000000000000000),(262413051217236333/1000000000000000000),(85921647278451099/500000000000000000)⟩
theorem valid1910 : certificate1910.Valid := by decide +kernel
theorem sound1910 : certificate1910.Sound := rat_cut_bin_certificate_sound certificate1910 profilesValid1910 numericValid1910 valid1910

def retention1911 : RatCutRetentionCertificate := ⟨(107/1600),(67/1000),(69744252525061523/140945598714870286),(552939650108518083/125000000000000000),(11/10),(25856113484464194997272195625528757743/26020689416871439200000000000000000000),false,MergedCutProfiles.Batch304.profile12160,(fun _ => MergedCutProfiles.Batch304.profile12160)⟩
theorem profilesValid1911 : retention1911.ProfilesValid := by
  exact MergedCutProfiles.Batch304.valid12160
theorem numericValid1911 : retention1911.NumericValid := by decide +kernel
def certificate1911 : RatCutBinCertificate := ⟨⟨retention1911,(1364516669435513181/500000000000000000),(11895173549139047/50000000000000000),(18061616308736539321/1000000000000000000),(4331171436219614029/25000000000000000),(954123208587520039/1000000000000000000)⟩,(987930887553558009/1000000000000000000),(198000103875149687/500000000000000000),(237167227937753323/1000000000000000000),(172268554200457613/1000000000000000000)⟩
theorem valid1911 : certificate1911.Valid := by decide +kernel
theorem sound1911 : certificate1911.Sound := rat_cut_bin_certificate_sound certificate1911 profilesValid1911 numericValid1911 valid1911

def retention1912 : RatCutRetentionCertificate := ⟨(107/1600),(67/1000),(598754407927653175/1198037589076397431),(1185652292926045891/250000000000000000),(11/10),(117072248549574163962763120243506888719/118565229292604589100000000000000000000),false,MergedCutProfiles.Batch304.profile12161,(fun _ => MergedCutProfiles.Batch304.profile12161)⟩
theorem profilesValid1912 : retention1912.ProfilesValid := by
  exact MergedCutProfiles.Batch304.valid12161
theorem numericValid1912 : retention1912.NumericValid := by decide +kernel
def certificate1912 : RatCutBinCertificate := ⟨⟨retention1912,(1364516669435513181/500000000000000000),(11895173549139047/50000000000000000),(18061616308736539321/1000000000000000000),(4331171436219614029/25000000000000000),(37914268311061277/40000000000000000)⟩,(987930887553558009/1000000000000000000),(398618257084823641/1000000000000000000),(14671923323631287/62500000000000000),(171308065601526023/1000000000000000000)⟩
theorem valid1912 : certificate1912.Valid := by decide +kernel
theorem sound1912 : certificate1912.Sound := rat_cut_bin_certificate_sound certificate1912 profilesValid1912 numericValid1912 valid1912

def retention1913 : RatCutRetentionCertificate := ⟨(107/1600),(67/1000),(1/2),(23950176317106127/5000000000000000),(11/10),(4729659251495305666544671241244416959/4790035263421225400000000000000000000),false,MergedCutProfiles.Batch303.profile12158,(fun _ => MergedCutProfiles.Batch303.profile12158)⟩
theorem profilesValid1913 : retention1913.ProfilesValid := by
  exact MergedCutProfiles.Batch303.valid12158
theorem numericValid1913 : retention1913.NumericValid := by decide +kernel
def certificate1913 : RatCutBinCertificate := ⟨⟨retention1913,(1364516669435513181/500000000000000000),(11895173549139047/50000000000000000),(18061616308736539321/1000000000000000000),(4331171436219614029/25000000000000000),(947844370436792401/1000000000000000000)⟩,(987930887553558009/1000000000000000000),(199311722791540381/500000000000000000),(117373000652446703/500000000000000000),(171545167353415637/1000000000000000000)⟩
theorem valid1913 : certificate1913.Valid := by decide +kernel
theorem sound1913 : certificate1913.Sound := rat_cut_bin_certificate_sound certificate1913 profilesValid1913 numericValid1913 valid1913

def retention1914 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(1297393292160431650/9412525033197477019),(56112657262993401/62500000000000000),(49/20),(71757257552005577111/40000000000000000000),true,MergedCutProfiles.Batch304.profile12162,![MergedCutProfiles.Batch304.profile12162,MergedCutProfiles.Batch304.profile12163,MergedCutProfiles.Batch304.profile12164,MergedCutProfiles.Batch304.profile12165,MergedCutProfiles.Batch304.profile12166,MergedCutProfiles.Batch304.profile12167,MergedCutProfiles.Batch304.profile12168,MergedCutProfiles.Batch304.profile12169,MergedCutProfiles.Batch304.profile12170,MergedCutProfiles.Batch304.profile12171,MergedCutProfiles.Batch304.profile12172,MergedCutProfiles.Batch304.profile12173,MergedCutProfiles.Batch304.profile12174,MergedCutProfiles.Batch304.profile12175,MergedCutProfiles.Batch304.profile12176,MergedCutProfiles.Batch304.profile12177]⟩
theorem profilesValid1914 : retention1914.ProfilesValid := by
  change ∀ j : Fin 16, (retention1914.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch304.valid12162
  · exact MergedCutProfiles.Batch304.valid12163
  · exact MergedCutProfiles.Batch304.valid12164
  · exact MergedCutProfiles.Batch304.valid12165
  · exact MergedCutProfiles.Batch304.valid12166
  · exact MergedCutProfiles.Batch304.valid12167
  · exact MergedCutProfiles.Batch304.valid12168
  · exact MergedCutProfiles.Batch304.valid12169
  · exact MergedCutProfiles.Batch304.valid12170
  · exact MergedCutProfiles.Batch304.valid12171
  · exact MergedCutProfiles.Batch304.valid12172
  · exact MergedCutProfiles.Batch304.valid12173
  · exact MergedCutProfiles.Batch304.valid12174
  · exact MergedCutProfiles.Batch304.valid12175
  · exact MergedCutProfiles.Batch304.valid12176
  · exact MergedCutProfiles.Batch304.valid12177
theorem numericValid1914 : retention1914.NumericValid := by decide +kernel
def certificate1914 : RatCutBinCertificate := ⟨⟨retention1914,(483786689462153949/200000000000000000),(121143195939341811/500000000000000000),(9052768925236129457/500000000000000000),(34193528398953411263/200000000000000000),(1714574061031771587/1000000000000000000)⟩,(494589501460708283/500000000000000000),(339967878231607017/1000000000000000000),(36653957531435313/125000000000000000),(153607270584475363/1000000000000000000)⟩
theorem valid1914 : certificate1914.Valid := by decide +kernel
theorem sound1914 : certificate1914.Sound := rat_cut_bin_certificate_sound certificate1914 profilesValid1914 numericValid1914 valid1914

def retention1915 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(2526990979441390470/9412525033197477019),(25947865843208633/20000000000000000),(9/5),(37590497076936009381/25600000000000000000),true,MergedCutProfiles.Batch304.profile12178,![MergedCutProfiles.Batch304.profile12178,MergedCutProfiles.Batch304.profile12179,MergedCutProfiles.Batch304.profile12180,MergedCutProfiles.Batch304.profile12181,MergedCutProfiles.Batch304.profile12182,MergedCutProfiles.Batch304.profile12183,MergedCutProfiles.Batch304.profile12184,MergedCutProfiles.Batch304.profile12185,MergedCutProfiles.Batch304.profile12186,MergedCutProfiles.Batch304.profile12187,MergedCutProfiles.Batch304.profile12188,MergedCutProfiles.Batch304.profile12189,MergedCutProfiles.Batch304.profile12190,MergedCutProfiles.Batch304.profile12191,MergedCutProfiles.Batch304.profile12192,MergedCutProfiles.Batch304.profile12193]⟩
theorem profilesValid1915 : retention1915.ProfilesValid := by
  change ∀ j : Fin 16, (retention1915.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch304.valid12178
  · exact MergedCutProfiles.Batch304.valid12179
  · exact MergedCutProfiles.Batch304.valid12180
  · exact MergedCutProfiles.Batch304.valid12181
  · exact MergedCutProfiles.Batch304.valid12182
  · exact MergedCutProfiles.Batch304.valid12183
  · exact MergedCutProfiles.Batch304.valid12184
  · exact MergedCutProfiles.Batch304.valid12185
  · exact MergedCutProfiles.Batch304.valid12186
  · exact MergedCutProfiles.Batch304.valid12187
  · exact MergedCutProfiles.Batch304.valid12188
  · exact MergedCutProfiles.Batch304.valid12189
  · exact MergedCutProfiles.Batch304.valid12190
  · exact MergedCutProfiles.Batch304.valid12191
  · exact MergedCutProfiles.Batch304.valid12192
  · exact MergedCutProfiles.Batch304.valid12193
theorem numericValid1915 : retention1915.NumericValid := by decide +kernel
def certificate1915 : RatCutBinCertificate := ⟨⟨retention1915,(483786689462153949/200000000000000000),(121143195939341811/500000000000000000),(9052768925236129457/500000000000000000),(34193528398953411263/200000000000000000),(352519398415764797/250000000000000000)⟩,(494589501460708283/500000000000000000),(365518560955152073/1000000000000000000),(53321172376784581/200000000000000000),(77168178810581897/500000000000000000)⟩
theorem valid1915 : certificate1915.Valid := by decide +kernel
theorem sound1915 : certificate1915.Sound := rat_cut_bin_certificate_sound certificate1915 profilesValid1915 numericValid1915 valid1915

def retention1916 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(4033743321904714788/9412525033197477019),(252699097944139047/100000000000000000),(23/20),(141840525602334125199/128000000000000000000),true,MergedCutProfiles.Batch304.profile12194,![MergedCutProfiles.Batch304.profile12194,MergedCutProfiles.Batch304.profile12195,MergedCutProfiles.Batch304.profile12196,MergedCutProfiles.Batch304.profile12197,MergedCutProfiles.Batch304.profile12198,MergedCutProfiles.Batch304.profile12199,MergedCutProfiles.Batch305.profile12200,MergedCutProfiles.Batch305.profile12201,MergedCutProfiles.Batch305.profile12202,MergedCutProfiles.Batch305.profile12203,MergedCutProfiles.Batch305.profile12204,MergedCutProfiles.Batch305.profile12205,MergedCutProfiles.Batch305.profile12206,MergedCutProfiles.Batch305.profile12207,MergedCutProfiles.Batch305.profile12208,MergedCutProfiles.Batch305.profile12209]⟩
theorem profilesValid1916 : retention1916.ProfilesValid := by
  change ∀ j : Fin 16, (retention1916.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch304.valid12194
  · exact MergedCutProfiles.Batch304.valid12195
  · exact MergedCutProfiles.Batch304.valid12196
  · exact MergedCutProfiles.Batch304.valid12197
  · exact MergedCutProfiles.Batch304.valid12198
  · exact MergedCutProfiles.Batch304.valid12199
  · exact MergedCutProfiles.Batch305.valid12200
  · exact MergedCutProfiles.Batch305.valid12201
  · exact MergedCutProfiles.Batch305.valid12202
  · exact MergedCutProfiles.Batch305.valid12203
  · exact MergedCutProfiles.Batch305.valid12204
  · exact MergedCutProfiles.Batch305.valid12205
  · exact MergedCutProfiles.Batch305.valid12206
  · exact MergedCutProfiles.Batch305.valid12207
  · exact MergedCutProfiles.Batch305.valid12208
  · exact MergedCutProfiles.Batch305.valid12209
theorem numericValid1916 : retention1916.NumericValid := by decide +kernel
def certificate1916 : RatCutBinCertificate := ⟨⟨retention1916,(483786689462153949/200000000000000000),(121143195939341811/500000000000000000),(9052768925236129457/500000000000000000),(34193528398953411263/200000000000000000),(1070885554901359001/1000000000000000000)⟩,(494589501460708283/500000000000000000),(412391944902954589/1000000000000000000),(44463632189180449/200000000000000000),(154791919043020267/1000000000000000000)⟩
theorem valid1916 : certificate1916.Valid := by decide +kernel
theorem sound1916 : certificate1916.Sound := rat_cut_bin_certificate_sound certificate1916 profilesValid1916 numericValid1916 valid1916

def retention1917 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(4545322940249911883/9412525033197477019),(1008435830476178697/250000000000000000),1,(63100987834011815037/64000000000000000000),true,MergedCutProfiles.Batch305.profile12210,![MergedCutProfiles.Batch305.profile12210,MergedCutProfiles.Batch305.profile12211,MergedCutProfiles.Batch305.profile12212,MergedCutProfiles.Batch304.profile12175,MergedCutProfiles.Batch304.profile12186,MergedCutProfiles.Batch305.profile12213,MergedCutProfiles.Batch305.profile12214,MergedCutProfiles.Batch305.profile12215,MergedCutProfiles.Batch305.profile12216,MergedCutProfiles.Batch305.profile12217,MergedCutProfiles.Batch305.profile12218,MergedCutProfiles.Batch305.profile12219,MergedCutProfiles.Batch305.profile12220,MergedCutProfiles.Batch305.profile12221,MergedCutProfiles.Batch305.profile12222,MergedCutProfiles.Batch305.profile12223]⟩
theorem profilesValid1917 : retention1917.ProfilesValid := by
  change ∀ j : Fin 16, (retention1917.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch305.valid12210
  · exact MergedCutProfiles.Batch305.valid12211
  · exact MergedCutProfiles.Batch305.valid12212
  · exact MergedCutProfiles.Batch304.valid12175
  · exact MergedCutProfiles.Batch304.valid12186
  · exact MergedCutProfiles.Batch305.valid12213
  · exact MergedCutProfiles.Batch305.valid12214
  · exact MergedCutProfiles.Batch305.valid12215
  · exact MergedCutProfiles.Batch305.valid12216
  · exact MergedCutProfiles.Batch305.valid12217
  · exact MergedCutProfiles.Batch305.valid12218
  · exact MergedCutProfiles.Batch305.valid12219
  · exact MergedCutProfiles.Batch305.valid12220
  · exact MergedCutProfiles.Batch305.valid12221
  · exact MergedCutProfiles.Batch305.valid12222
  · exact MergedCutProfiles.Batch305.valid12223
theorem numericValid1917 : retention1917.NumericValid := by decide +kernel
def certificate1917 : RatCutBinCertificate := ⟨⟨retention1917,(483786689462153949/200000000000000000),(121143195939341811/500000000000000000),(9052768925236129457/500000000000000000),(34193528398953411263/200000000000000000),(953571651145915883/1000000000000000000)⟩,(494589501460708283/500000000000000000),(216314908528467257/500000000000000000),(204880919985959293/1000000000000000000),(78037502122056911/500000000000000000)⟩
theorem valid1917 : certificate1917.Valid := by decide +kernel
theorem sound1917 : certificate1917.Sound := rat_cut_bin_certificate_sound certificate1917 profilesValid1917 numericValid1917 valid1917

def retention1918 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(4636683931348935113/9412525033197477019),(4545322940249911883/1000000000000000000),(11/10),(37071661320305210002144454222967453239/37104677063264586800000000000000000000),false,MergedCutProfiles.Batch305.profile12224,(fun _ => MergedCutProfiles.Batch305.profile12224)⟩
theorem profilesValid1918 : retention1918.ProfilesValid := by
  exact MergedCutProfiles.Batch305.valid12224
theorem numericValid1918 : retention1918.NumericValid := by decide +kernel
def certificate1918 : RatCutBinCertificate := ⟨⟨retention1918,(483786689462153949/200000000000000000),(121143195939341811/500000000000000000),(9052768925236129457/500000000000000000),(34193528398953411263/200000000000000000),(963493205019589899/1000000000000000000)⟩,(494589501460708283/500000000000000000),(422477485088871941/1000000000000000000),(106753580919222379/500000000000000000),(31443100471126347/200000000000000000)⟩
theorem valid1918 : certificate1918.Valid := by decide +kernel
theorem sound1918 : certificate1918.Sound := rat_cut_bin_certificate_sound certificate1918 profilesValid1918 numericValid1918 valid1918

def retention1919 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(4683050770662424465/9412525033197477019),(4636683931348935113/1000000000000000000),(11/10),(1837428526604590994647571296180993199311/1854673572539574045200000000000000000000),false,MergedCutProfiles.Batch305.profile12225,(fun _ => MergedCutProfiles.Batch305.profile12225)⟩
theorem profilesValid1919 : retention1919.ProfilesValid := by
  exact MergedCutProfiles.Batch305.valid12225
theorem numericValid1919 : retention1919.NumericValid := by decide +kernel
def certificate1919 : RatCutBinCertificate := ⟨⟨retention1919,(483786689462153949/200000000000000000),(121143195939341811/500000000000000000),(9052768925236129457/500000000000000000),(34193528398953411263/200000000000000000),(955085046981886983/1000000000000000000)⟩,(494589501460708283/500000000000000000),(425303846210686833/1000000000000000000),(105540702629584457/500000000000000000),(77363847461615487/500000000000000000)⟩
theorem valid1919 : certificate1919.Valid := by decide +kernel
theorem sound1919 : certificate1919.Sound := rat_cut_bin_certificate_sound certificate1919 profilesValid1919 numericValid1919 valid1919

def certificates : List RatCutBinCertificate := [certificate1908,certificate1909,certificate1910,certificate1911,certificate1912,certificate1913,certificate1914,certificate1915,certificate1916,certificate1917,certificate1918,certificate1919]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1908,List.forall_mem_cons.mpr ⟨sound1909,List.forall_mem_cons.mpr ⟨sound1910,List.forall_mem_cons.mpr ⟨sound1911,List.forall_mem_cons.mpr ⟨sound1912,List.forall_mem_cons.mpr ⟨sound1913,List.forall_mem_cons.mpr ⟨sound1914,List.forall_mem_cons.mpr ⟨sound1915,List.forall_mem_cons.mpr ⟨sound1916,List.forall_mem_cons.mpr ⟨sound1917,List.forall_mem_cons.mpr ⟨sound1918,List.forall_mem_cons.mpr ⟨sound1919,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch159
