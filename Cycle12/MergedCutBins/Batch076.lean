import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch153
import Cycle12.MergedCutProfiles.Batch154
import Cycle12.MergedCutProfiles.Batch155

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch076

def retention912 : RatCutRetentionCertificate := ⟨(1/20),(201/4000),(976858777773082276/18861153311560677731),(424915481584249977/500000000000000000),(29/10),(1313764653467380333997/640000000000000000000),true,MergedCutProfiles.Batch153.profile6150,![MergedCutProfiles.Batch153.profile6150,MergedCutProfiles.Batch153.profile6151,MergedCutProfiles.Batch153.profile6152,MergedCutProfiles.Batch153.profile6153,MergedCutProfiles.Batch153.profile6154,MergedCutProfiles.Batch153.profile6155,MergedCutProfiles.Batch153.profile6156,MergedCutProfiles.Batch153.profile6157,MergedCutProfiles.Batch153.profile6158,MergedCutProfiles.Batch153.profile6159,MergedCutProfiles.Batch154.profile6160,MergedCutProfiles.Batch154.profile6161,MergedCutProfiles.Batch153.profile6148,MergedCutProfiles.Batch154.profile6162,MergedCutProfiles.Batch154.profile6163,MergedCutProfiles.Batch154.profile6164]⟩
theorem profilesValid912 : retention912.ProfilesValid := by
  change ∀ j : Fin 16, (retention912.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch153.valid6150
  · exact MergedCutProfiles.Batch153.valid6151
  · exact MergedCutProfiles.Batch153.valid6152
  · exact MergedCutProfiles.Batch153.valid6153
  · exact MergedCutProfiles.Batch153.valid6154
  · exact MergedCutProfiles.Batch153.valid6155
  · exact MergedCutProfiles.Batch153.valid6156
  · exact MergedCutProfiles.Batch153.valid6157
  · exact MergedCutProfiles.Batch153.valid6158
  · exact MergedCutProfiles.Batch153.valid6159
  · exact MergedCutProfiles.Batch154.valid6160
  · exact MergedCutProfiles.Batch154.valid6161
  · exact MergedCutProfiles.Batch153.valid6148
  · exact MergedCutProfiles.Batch154.valid6162
  · exact MergedCutProfiles.Batch154.valid6163
  · exact MergedCutProfiles.Batch154.valid6164
theorem numericValid912 : retention912.NumericValid := by decide +kernel
def certificate912 : RatCutBinCertificate := ⟨⟨retention912,(1081120266088097079/500000000000000000),(121091336014959573/1000000000000000000),(13319948354367943353/1000000000000000000),(251589832803632728293/1000000000000000000),(997870596590547621/500000000000000000)⟩,(992426697239596233/1000000000000000000),(38167790899756271/100000000000000000),(250695926038579777/1000000000000000000),(4176695212767623/31250000000000000)⟩
theorem valid912 : certificate912.Valid := by decide +kernel
theorem sound912 : certificate912.Sound := rat_cut_bin_certificate_sound certificate912 profilesValid912 numericValid912 valid912

def retention913 : RatCutRetentionCertificate := ⟨(1/20),(201/4000),(1940915258743077449/18861153311560677731),(244214694443270569/250000000000000000),(51/20),(604901297361917768601/320000000000000000000),true,MergedCutProfiles.Batch153.profile6151,![MergedCutProfiles.Batch153.profile6151,MergedCutProfiles.Batch154.profile6165,MergedCutProfiles.Batch154.profile6166,MergedCutProfiles.Batch154.profile6167,MergedCutProfiles.Batch154.profile6168,MergedCutProfiles.Batch154.profile6169,MergedCutProfiles.Batch153.profile6149,MergedCutProfiles.Batch154.profile6170,MergedCutProfiles.Batch154.profile6171,MergedCutProfiles.Batch154.profile6172,MergedCutProfiles.Batch154.profile6173,MergedCutProfiles.Batch154.profile6174,MergedCutProfiles.Batch154.profile6175,MergedCutProfiles.Batch154.profile6176,MergedCutProfiles.Batch154.profile6177,MergedCutProfiles.Batch154.profile6178]⟩
theorem profilesValid913 : retention913.ProfilesValid := by
  change ∀ j : Fin 16, (retention913.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch153.valid6151
  · exact MergedCutProfiles.Batch154.valid6165
  · exact MergedCutProfiles.Batch154.valid6166
  · exact MergedCutProfiles.Batch154.valid6167
  · exact MergedCutProfiles.Batch154.valid6168
  · exact MergedCutProfiles.Batch154.valid6169
  · exact MergedCutProfiles.Batch153.valid6149
  · exact MergedCutProfiles.Batch154.valid6170
  · exact MergedCutProfiles.Batch154.valid6171
  · exact MergedCutProfiles.Batch154.valid6172
  · exact MergedCutProfiles.Batch154.valid6173
  · exact MergedCutProfiles.Batch154.valid6174
  · exact MergedCutProfiles.Batch154.valid6175
  · exact MergedCutProfiles.Batch154.valid6176
  · exact MergedCutProfiles.Batch154.valid6177
  · exact MergedCutProfiles.Batch154.valid6178
theorem numericValid913 : retention913.NumericValid := by decide +kernel
def certificate913 : RatCutBinCertificate := ⟨⟨retention913,(1081120266088097079/500000000000000000),(121091336014959573/1000000000000000000),(13319948354367943353/1000000000000000000),(251589832803632728293/1000000000000000000),(184018183123259171/100000000000000000)⟩,(992426697239596233/1000000000000000000),(12249726029265049/31250000000000000),(24090107133536927/100000000000000000),(26717323132617113/200000000000000000)⟩
theorem valid913 : certificate913.Valid := by decide +kernel
theorem sound913 : certificate913.Sound := rat_cut_bin_certificate_sound certificate913 profilesValid913 numericValid913 valid913

def retention914 : RatCutRetentionCertificate := ⟨(1/20),(201/4000),(5915622307310017009/18861153311560677731),(1940915258743077449/1000000000000000000),(31/20),(1760401568173332153401/1280000000000000000000),true,MergedCutProfiles.Batch154.profile6179,![MergedCutProfiles.Batch154.profile6179,MergedCutProfiles.Batch154.profile6180,MergedCutProfiles.Batch154.profile6181,MergedCutProfiles.Batch154.profile6182,MergedCutProfiles.Batch154.profile6183,MergedCutProfiles.Batch154.profile6184,MergedCutProfiles.Batch154.profile6185,MergedCutProfiles.Batch154.profile6186,MergedCutProfiles.Batch154.profile6187,MergedCutProfiles.Batch154.profile6188,MergedCutProfiles.Batch154.profile6189,MergedCutProfiles.Batch154.profile6190,MergedCutProfiles.Batch154.profile6191,MergedCutProfiles.Batch154.profile6192,MergedCutProfiles.Batch154.profile6193,MergedCutProfiles.Batch154.profile6194]⟩
theorem profilesValid914 : retention914.ProfilesValid := by
  change ∀ j : Fin 16, (retention914.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch154.valid6179
  · exact MergedCutProfiles.Batch154.valid6180
  · exact MergedCutProfiles.Batch154.valid6181
  · exact MergedCutProfiles.Batch154.valid6182
  · exact MergedCutProfiles.Batch154.valid6183
  · exact MergedCutProfiles.Batch154.valid6184
  · exact MergedCutProfiles.Batch154.valid6185
  · exact MergedCutProfiles.Batch154.valid6186
  · exact MergedCutProfiles.Batch154.valid6187
  · exact MergedCutProfiles.Batch154.valid6188
  · exact MergedCutProfiles.Batch154.valid6189
  · exact MergedCutProfiles.Batch154.valid6190
  · exact MergedCutProfiles.Batch154.valid6191
  · exact MergedCutProfiles.Batch154.valid6192
  · exact MergedCutProfiles.Batch154.valid6193
  · exact MergedCutProfiles.Batch154.valid6194
theorem numericValid914 : retention914.NumericValid := by decide +kernel
def certificate914 : RatCutBinCertificate := ⟨⟨retention914,(1081120266088097079/500000000000000000),(121091336014959573/1000000000000000000),(13319948354367943353/1000000000000000000),(251589832803632728293/1000000000000000000),(672420345167160849/500000000000000000)⟩,(992426697239596233/1000000000000000000),(218279452789266739/500000000000000000),(201606688911681591/1000000000000000000),(67291183196245303/500000000000000000)⟩
theorem valid914 : certificate914.Valid := by decide +kernel
theorem sound914 : certificate914.Sound := rat_cut_bin_certificate_sound certificate914 profilesValid914 numericValid914 valid914

def retention915 : RatCutRetentionCertificate := ⟨(1/20),(201/4000),(8807555514959357667/18861153311560677731),(5915622307310017009/1000000000000000000),1,(262076737900169793889/256000000000000000000),true,MergedCutProfiles.Batch153.profile6158,![MergedCutProfiles.Batch153.profile6158,MergedCutProfiles.Batch154.profile6195,MergedCutProfiles.Batch154.profile6196,MergedCutProfiles.Batch154.profile6197,MergedCutProfiles.Batch154.profile6198,MergedCutProfiles.Batch154.profile6199,MergedCutProfiles.Batch155.profile6200,MergedCutProfiles.Batch155.profile6201,MergedCutProfiles.Batch155.profile6202,MergedCutProfiles.Batch155.profile6203,MergedCutProfiles.Batch155.profile6204,MergedCutProfiles.Batch155.profile6205,MergedCutProfiles.Batch155.profile6206,MergedCutProfiles.Batch155.profile6207,MergedCutProfiles.Batch155.profile6208,MergedCutProfiles.Batch155.profile6209]⟩
theorem profilesValid915 : retention915.ProfilesValid := by
  change ∀ j : Fin 16, (retention915.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch153.valid6158
  · exact MergedCutProfiles.Batch154.valid6195
  · exact MergedCutProfiles.Batch154.valid6196
  · exact MergedCutProfiles.Batch154.valid6197
  · exact MergedCutProfiles.Batch154.valid6198
  · exact MergedCutProfiles.Batch154.valid6199
  · exact MergedCutProfiles.Batch155.valid6200
  · exact MergedCutProfiles.Batch155.valid6201
  · exact MergedCutProfiles.Batch155.valid6202
  · exact MergedCutProfiles.Batch155.valid6203
  · exact MergedCutProfiles.Batch155.valid6204
  · exact MergedCutProfiles.Batch155.valid6205
  · exact MergedCutProfiles.Batch155.valid6206
  · exact MergedCutProfiles.Batch155.valid6207
  · exact MergedCutProfiles.Batch155.valid6208
  · exact MergedCutProfiles.Batch155.valid6209
theorem numericValid915 : retention915.NumericValid := by decide +kernel
def certificate915 : RatCutBinCertificate := ⟨⟨retention915,(1081120266088097079/500000000000000000),(121091336014959573/1000000000000000000),(13319948354367943353/1000000000000000000),(251589832803632728293/1000000000000000000),(1004078780478243191/1000000000000000000)⟩,(992426697239596233/1000000000000000000),(19747985816729483/40000000000000000),(78916640811303303/500000000000000000),(67184090159310359/500000000000000000)⟩
theorem valid915 : certificate915.Valid := by decide +kernel
theorem sound915 : certificate915.Sound := rat_cut_bin_certificate_sound certificate915 profilesValid915 numericValid915 valid915

def retention916 : RatCutRetentionCertificate := ⟨(1/20),(201/4000),(9349397656666325462/18861153311560677731),(8807555514959357667/1000000000000000000),(21/20),(671698643628423695116405837135331120451/671051848758808203200000000000000000000),false,MergedCutProfiles.Batch155.profile6210,(fun _ => MergedCutProfiles.Batch155.profile6210)⟩
theorem profilesValid916 : retention916.ProfilesValid := by
  exact MergedCutProfiles.Batch155.valid6210
theorem numericValid916 : retention916.NumericValid := by decide +kernel
def certificate916 : RatCutBinCertificate := ⟨⟨retention916,(1081120266088097079/500000000000000000),(121091336014959573/1000000000000000000),(13319948354367943353/1000000000000000000),(251589832803632728293/1000000000000000000),(980323056607035527/1000000000000000000)⟩,(992426697239596233/1000000000000000000),(490716098968240019/1000000000000000000),(39987044615843601/250000000000000000),(67276918316653911/500000000000000000)⟩
theorem valid916 : certificate916.Valid := by decide +kernel
theorem sound916 : certificate916.Sound := rat_cut_bin_certificate_sound certificate916 profilesValid916 numericValid916 valid916

def retention917 : RatCutRetentionCertificate := ⟨(1/20),(201/4000),(1/2),(4674698828333162731/500000000000000000),(21/20),(3717044464343401285489824563364222331199/3739759062666530184800000000000000000000),false,MergedCutProfiles.Batch155.profile6211,(fun _ => MergedCutProfiles.Batch155.profile6211)⟩
theorem profilesValid917 : retention917.ProfilesValid := by
  exact MergedCutProfiles.Batch155.valid6211
theorem numericValid917 : retention917.NumericValid := by decide +kernel
def certificate917 : RatCutBinCertificate := ⟨⟨retention917,(1081120266088097079/500000000000000000),(121091336014959573/1000000000000000000),(13319948354367943353/1000000000000000000),(251589832803632728293/1000000000000000000),(243321363315337109/250000000000000000)⟩,(992426697239596233/1000000000000000000),(246239779122803061/500000000000000000),(79347979663335667/500000000000000000),(66668195886001791/500000000000000000)⟩
theorem valid917 : certificate917.Valid := by decide +kernel
theorem sound917 : certificate917.Sound := rat_cut_bin_certificate_sound certificate917 profilesValid917 numericValid917 valid917

def retention918 : RatCutRetentionCertificate := ⟨(1/20),(201/4000),(1/2),64,1,(63848650439292519190727158287982109439/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch155.profile6211,(fun _ => MergedCutProfiles.Batch155.profile6211)⟩
theorem profilesValid918 : retention918.ProfilesValid := by
  exact MergedCutProfiles.Batch155.valid6211
theorem numericValid918 : retention918.NumericValid := by decide +kernel
def certificate918 : RatCutBinCertificate := ⟨⟨retention918,(1081120266088097079/500000000000000000),(121091336014959573/1000000000000000000),(13319948354367943353/1000000000000000000),(251589832803632728293/1000000000000000000),(9779781376576421/10000000000000000)⟩,(992426697239596233/1000000000000000000),(116365476772409557/250000000000000000),(178587560502506807/1000000000000000000),(170711424281341209/1000000000000000000)⟩
theorem valid918 : certificate918.Valid := by decide +kernel
theorem sound918 : certificate918.Sound := rat_cut_bin_certificate_sound certificate918 profilesValid918 numericValid918 valid918

def retention919 : RatCutRetentionCertificate := ⟨(1/20),(201/4000),(8507563527774461897/18861153311560677731),(1899957685178174593/500000000000000000),(6/5),(415186387092723050481177024389889603359/379991537035634918600000000000000000000),false,MergedCutProfiles.Batch155.profile6212,(fun _ => MergedCutProfiles.Batch155.profile6212)⟩
theorem profilesValid919 : retention919.ProfilesValid := by
  exact MergedCutProfiles.Batch155.valid6212
theorem numericValid919 : retention919.NumericValid := by decide +kernel
def certificate919 : RatCutBinCertificate := ⟨⟨retention919,(1270914715588097079/500000000000000000),(121091336014959573/1000000000000000000),(13319948354367943353/1000000000000000000),(251589832803632728293/1000000000000000000),(1064887908719554127/1000000000000000000)⟩,(991095567537685141/1000000000000000000),(377235344020989093/1000000000000000000),(31875067315910649/125000000000000000),(7503342739538433/40000000000000000)⟩
theorem valid919 : certificate919.Valid := by decide +kernel
theorem sound919 : certificate919.Sound := rat_cut_bin_certificate_sound certificate919 profilesValid919 numericValid919 valid919

def retention920 : RatCutRetentionCertificate := ⟨(1/20),(201/4000),(9304596936753535760/18861153311560677731),(8507563527774461897/1000000000000000000),(21/20),(13676488234624140514796004192050290898471/13612101644439139035200000000000000000000),false,MergedCutProfiles.Batch155.profile6213,(fun _ => MergedCutProfiles.Batch155.profile6213)⟩
theorem profilesValid920 : retention920.ProfilesValid := by
  exact MergedCutProfiles.Batch155.valid6213
theorem numericValid920 : retention920.NumericValid := by decide +kernel
def certificate920 : RatCutBinCertificate := ⟨⟨retention920,(1270914715588097079/500000000000000000),(121091336014959573/1000000000000000000),(13319948354367943353/1000000000000000000),(251589832803632728293/1000000000000000000),(980465694928123483/1000000000000000000)⟩,(991095567537685141/1000000000000000000),(409716891338112197/1000000000000000000),(44939257731832641/200000000000000000),(188182239461717061/1000000000000000000)⟩
theorem valid920 : certificate920.Valid := by decide +kernel
theorem sound920 : certificate920.Sound := rat_cut_bin_certificate_sound certificate920 profilesValid920 numericValid920 valid920

def retention921 : RatCutRetentionCertificate := ⟨(1/20),(201/4000),(9397642906121071118/18861153311560677731),(116307461709419197/12500000000000000),(21/20),(579921972088503507080346509882465411/581537308547095985000000000000000000),false,MergedCutProfiles.Batch155.profile6214,(fun _ => MergedCutProfiles.Batch155.profile6214)⟩
theorem profilesValid921 : retention921.ProfilesValid := by
  exact MergedCutProfiles.Batch155.valid6214
theorem numericValid921 : retention921.NumericValid := by decide +kernel
def certificate921 : RatCutBinCertificate := ⟨⟨retention921,(1270914715588097079/500000000000000000),(121091336014959573/1000000000000000000),(13319948354367943353/1000000000000000000),(251589832803632728293/1000000000000000000),(972958007302173313/1000000000000000000)⟩,(991095567537685141/1000000000000000000),(412878411580667319/1000000000000000000),(6933986203067261/31250000000000000),(7441800070872629/40000000000000000)⟩
theorem valid921 : certificate921.Valid := by decide +kernel
theorem sound921 : certificate921.Sound := rat_cut_bin_certificate_sound certificate921 profilesValid921 numericValid921 valid921

def retention922 : RatCutRetentionCertificate := ⟨(1/20),(201/4000),(1/2),(4698821453060535559/500000000000000000),(21/20),(3736629632977123695360178349027034355559/3759057162448428447200000000000000000000),false,MergedCutProfiles.Batch155.profile6211,(fun _ => MergedCutProfiles.Batch155.profile6211)⟩
theorem profilesValid922 : retention922.ProfilesValid := by
  exact MergedCutProfiles.Batch155.valid6211
theorem numericValid922 : retention922.NumericValid := by decide +kernel
def certificate922 : RatCutBinCertificate := ⟨⟨retention922,(1270914715588097079/500000000000000000),(121091336014959573/1000000000000000000),(13319948354367943353/1000000000000000000),(251589832803632728293/1000000000000000000),(484884727533751979/500000000000000000)⟩,(991095567537685141/1000000000000000000),(2071179673119577/5000000000000000),(55172239312525613/250000000000000000),(184644561266692301/1000000000000000000)⟩
theorem valid922 : certificate922.Valid := by decide +kernel
theorem sound922 : certificate922.Sound := rat_cut_bin_certificate_sound certificate922 profilesValid922 numericValid922 valid922

def retention923 : RatCutRetentionCertificate := ⟨(201/4000),(101/2000),(841118284693925491/18648088304642895400),(832790380885074743/1000000000000000000),(59/20),(20749056374080269539/10000000000000000000),true,MergedCutProfiles.Batch155.profile6215,![MergedCutProfiles.Batch155.profile6215,MergedCutProfiles.Batch155.profile6216,MergedCutProfiles.Batch155.profile6217,MergedCutProfiles.Batch155.profile6218,MergedCutProfiles.Batch155.profile6219,MergedCutProfiles.Batch155.profile6220,MergedCutProfiles.Batch155.profile6221,MergedCutProfiles.Batch155.profile6222,MergedCutProfiles.Batch155.profile6223,MergedCutProfiles.Batch155.profile6224,MergedCutProfiles.Batch155.profile6225,MergedCutProfiles.Batch155.profile6226,MergedCutProfiles.Batch155.profile6227,MergedCutProfiles.Batch155.profile6228,MergedCutProfiles.Batch155.profile6229,MergedCutProfiles.Batch155.profile6230]⟩
theorem profilesValid923 : retention923.ProfilesValid := by
  change ∀ j : Fin 16, (retention923.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch155.valid6215
  · exact MergedCutProfiles.Batch155.valid6216
  · exact MergedCutProfiles.Batch155.valid6217
  · exact MergedCutProfiles.Batch155.valid6218
  · exact MergedCutProfiles.Batch155.valid6219
  · exact MergedCutProfiles.Batch155.valid6220
  · exact MergedCutProfiles.Batch155.valid6221
  · exact MergedCutProfiles.Batch155.valid6222
  · exact MergedCutProfiles.Batch155.valid6223
  · exact MergedCutProfiles.Batch155.valid6224
  · exact MergedCutProfiles.Batch155.valid6225
  · exact MergedCutProfiles.Batch155.valid6226
  · exact MergedCutProfiles.Batch155.valid6227
  · exact MergedCutProfiles.Batch155.valid6228
  · exact MergedCutProfiles.Batch155.valid6229
  · exact MergedCutProfiles.Batch155.valid6230
theorem numericValid923 : retention923.NumericValid := by decide +kernel
def certificate923 : RatCutBinCertificate := ⟨⟨retention923,(2167774325693329727/1000000000000000000),(30615167816376129/250000000000000000),(13375694810516664019/1000000000000000000),(249789381237389577433/1000000000000000000),(2016345373338895847/1000000000000000000)⟩,(49618211182754897/50000000000000000),(379255549928096107/1000000000000000000),(31629577568894933/125000000000000000),(134080982891247789/1000000000000000000)⟩
theorem valid923 : certificate923.Valid := by decide +kernel
theorem sound923 : certificate923.Sound := rat_cut_bin_certificate_sound certificate923 profilesValid923 numericValid923 valid923

def certificates : List RatCutBinCertificate := [certificate912,certificate913,certificate914,certificate915,certificate916,certificate917,certificate918,certificate919,certificate920,certificate921,certificate922,certificate923]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound912,List.forall_mem_cons.mpr ⟨sound913,List.forall_mem_cons.mpr ⟨sound914,List.forall_mem_cons.mpr ⟨sound915,List.forall_mem_cons.mpr ⟨sound916,List.forall_mem_cons.mpr ⟨sound917,List.forall_mem_cons.mpr ⟨sound918,List.forall_mem_cons.mpr ⟨sound919,List.forall_mem_cons.mpr ⟨sound920,List.forall_mem_cons.mpr ⟨sound921,List.forall_mem_cons.mpr ⟨sound922,List.forall_mem_cons.mpr ⟨sound923,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch076
