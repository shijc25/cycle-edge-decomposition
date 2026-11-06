import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch155
import Cycle12.MergedCutProfiles.Batch156
import Cycle12.MergedCutProfiles.Batch157

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch077

def retention924 : RatCutRetentionCertificate := ⟨(201/4000),(101/2000),(910810574807205749/18648088304642895400),(841118284693925491/1000000000000000000),(29/10),(2634714832978304271471/1280000000000000000000),true,MergedCutProfiles.Batch155.profile6231,![MergedCutProfiles.Batch155.profile6231,MergedCutProfiles.Batch155.profile6232,MergedCutProfiles.Batch155.profile6233,MergedCutProfiles.Batch155.profile6234,MergedCutProfiles.Batch155.profile6235,MergedCutProfiles.Batch155.profile6236,MergedCutProfiles.Batch155.profile6237,MergedCutProfiles.Batch155.profile6238,MergedCutProfiles.Batch155.profile6239,MergedCutProfiles.Batch156.profile6240,MergedCutProfiles.Batch156.profile6241,MergedCutProfiles.Batch156.profile6242,MergedCutProfiles.Batch156.profile6243,MergedCutProfiles.Batch156.profile6244,MergedCutProfiles.Batch156.profile6245,MergedCutProfiles.Batch156.profile6246]⟩
theorem profilesValid924 : retention924.ProfilesValid := by
  change ∀ j : Fin 16, (retention924.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch155.valid6231
  · exact MergedCutProfiles.Batch155.valid6232
  · exact MergedCutProfiles.Batch155.valid6233
  · exact MergedCutProfiles.Batch155.valid6234
  · exact MergedCutProfiles.Batch155.valid6235
  · exact MergedCutProfiles.Batch155.valid6236
  · exact MergedCutProfiles.Batch155.valid6237
  · exact MergedCutProfiles.Batch155.valid6238
  · exact MergedCutProfiles.Batch155.valid6239
  · exact MergedCutProfiles.Batch156.valid6240
  · exact MergedCutProfiles.Batch156.valid6241
  · exact MergedCutProfiles.Batch156.valid6242
  · exact MergedCutProfiles.Batch156.valid6243
  · exact MergedCutProfiles.Batch156.valid6244
  · exact MergedCutProfiles.Batch156.valid6245
  · exact MergedCutProfiles.Batch156.valid6246
theorem numericValid924 : retention924.NumericValid := by decide +kernel
def certificate924 : RatCutBinCertificate := ⟨⟨retention924,(2167774325693329727/1000000000000000000),(30615167816376129/250000000000000000),(13375694810516664019/1000000000000000000),(249789381237389577433/1000000000000000000),(500200790923752157/250000000000000000)⟩,(49618211182754897/50000000000000000),(190318744912362161/500000000000000000),(125849690971630953/500000000000000000),(67069849509927769/500000000000000000)⟩
theorem valid924 : certificate924.Valid := by decide +kernel
theorem sound924 : certificate924.Sound := rat_cut_bin_certificate_sound certificate924 profilesValid924 numericValid924 valid924

def retention925 : RatCutRetentionCertificate := ⟨(201/4000),(101/2000),(29368651210662643/372961766092857908),(910810574807205749/1000000000000000000),(27/10),(628329916735403990717/320000000000000000000),true,MergedCutProfiles.Batch156.profile6247,![MergedCutProfiles.Batch156.profile6247,MergedCutProfiles.Batch156.profile6248,MergedCutProfiles.Batch156.profile6249,MergedCutProfiles.Batch155.profile6221,MergedCutProfiles.Batch156.profile6250,MergedCutProfiles.Batch156.profile6251,MergedCutProfiles.Batch156.profile6252,MergedCutProfiles.Batch155.profile6228,MergedCutProfiles.Batch156.profile6253,MergedCutProfiles.Batch156.profile6254,MergedCutProfiles.Batch156.profile6255,MergedCutProfiles.Batch156.profile6256,MergedCutProfiles.Batch156.profile6257,MergedCutProfiles.Batch156.profile6258,MergedCutProfiles.Batch156.profile6259,MergedCutProfiles.Batch156.profile6260]⟩
theorem profilesValid925 : retention925.ProfilesValid := by
  change ∀ j : Fin 16, (retention925.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch156.valid6247
  · exact MergedCutProfiles.Batch156.valid6248
  · exact MergedCutProfiles.Batch156.valid6249
  · exact MergedCutProfiles.Batch155.valid6221
  · exact MergedCutProfiles.Batch156.valid6250
  · exact MergedCutProfiles.Batch156.valid6251
  · exact MergedCutProfiles.Batch156.valid6252
  · exact MergedCutProfiles.Batch155.valid6228
  · exact MergedCutProfiles.Batch156.valid6253
  · exact MergedCutProfiles.Batch156.valid6254
  · exact MergedCutProfiles.Batch156.valid6255
  · exact MergedCutProfiles.Batch156.valid6256
  · exact MergedCutProfiles.Batch156.valid6257
  · exact MergedCutProfiles.Batch156.valid6258
  · exact MergedCutProfiles.Batch156.valid6259
  · exact MergedCutProfiles.Batch156.valid6260
theorem numericValid925 : retention925.NumericValid := by decide +kernel
def certificate925 : RatCutBinCertificate := ⟨⟨retention925,(2167774325693329727/1000000000000000000),(30615167816376129/250000000000000000),(13375694810516664019/1000000000000000000),(249789381237389577433/1000000000000000000),(190993347065590341/100000000000000000)⟩,(49618211182754897/50000000000000000),(386209748224352137/1000000000000000000),(123179023922093173/500000000000000000),(33528552907181211/250000000000000000)⟩
theorem valid925 : certificate925.Valid := by decide +kernel
theorem sound925 : certificate925.Sound := rat_cut_bin_certificate_sound certificate925 profilesValid925 numericValid925 valid925

def retention926 : RatCutRetentionCertificate := ⟨(201/4000),(101/2000),(110781312032613337/466202207616072385),(29368651210662643/20000000000000000),(19/10),(2274588926491063864114469328362429581/1468432560533132150000000000000000000),false,MergedCutProfiles.Batch156.profile6261,(fun _ => MergedCutProfiles.Batch156.profile6261)⟩
theorem profilesValid926 : retention926.ProfilesValid := by
  exact MergedCutProfiles.Batch156.valid6261
theorem numericValid926 : retention926.NumericValid := by decide +kernel
def certificate926 : RatCutBinCertificate := ⟨⟨retention926,(2167774325693329727/1000000000000000000),(30615167816376129/250000000000000000),(13375694810516664019/1000000000000000000),(249789381237389577433/1000000000000000000),(377818797738157343/250000000000000000)⟩,(49618211182754897/50000000000000000),(415469899601385927/1000000000000000000),(219603308443777543/1000000000000000000),(16839478210048979/125000000000000000)⟩
theorem valid926 : certificate926.Valid := by decide +kernel
theorem sound926 : certificate926.Sound := rat_cut_bin_certificate_sound certificate926 profilesValid926 numericValid926 valid926

def retention927 : RatCutRetentionCertificate := ⟨(201/4000),(101/2000),(8294172128656315767/18648088304642895400),(110781312032613337/25000000000000000),(21/20),(34381496359235567223/32000000000000000000),true,MergedCutProfiles.Batch156.profile6262,![MergedCutProfiles.Batch156.profile6262,MergedCutProfiles.Batch156.profile6263,MergedCutProfiles.Batch156.profile6264,MergedCutProfiles.Batch156.profile6265,MergedCutProfiles.Batch156.profile6266,MergedCutProfiles.Batch156.profile6267,MergedCutProfiles.Batch156.profile6268,MergedCutProfiles.Batch156.profile6269,MergedCutProfiles.Batch156.profile6270,MergedCutProfiles.Batch156.profile6271,MergedCutProfiles.Batch156.profile6272,MergedCutProfiles.Batch156.profile6273,MergedCutProfiles.Batch156.profile6274,MergedCutProfiles.Batch156.profile6275,MergedCutProfiles.Batch156.profile6276,MergedCutProfiles.Batch156.profile6277]⟩
theorem profilesValid927 : retention927.ProfilesValid := by
  change ∀ j : Fin 16, (retention927.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch156.valid6262
  · exact MergedCutProfiles.Batch156.valid6263
  · exact MergedCutProfiles.Batch156.valid6264
  · exact MergedCutProfiles.Batch156.valid6265
  · exact MergedCutProfiles.Batch156.valid6266
  · exact MergedCutProfiles.Batch156.valid6267
  · exact MergedCutProfiles.Batch156.valid6268
  · exact MergedCutProfiles.Batch156.valid6269
  · exact MergedCutProfiles.Batch156.valid6270
  · exact MergedCutProfiles.Batch156.valid6271
  · exact MergedCutProfiles.Batch156.valid6272
  · exact MergedCutProfiles.Batch156.valid6273
  · exact MergedCutProfiles.Batch156.valid6274
  · exact MergedCutProfiles.Batch156.valid6275
  · exact MergedCutProfiles.Batch156.valid6276
  · exact MergedCutProfiles.Batch156.valid6277
theorem numericValid927 : retention927.NumericValid := by decide +kernel
def certificate927 : RatCutBinCertificate := ⟨⟨retention927,(2167774325693329727/1000000000000000000),(30615167816376129/250000000000000000),(13375694810516664019/1000000000000000000),(249789381237389577433/1000000000000000000),(131697530028775933/125000000000000000)⟩,(49618211182754897/50000000000000000),(482198642665128693/1000000000000000000),(41521498293797331/250000000000000000),(33983202798550583/250000000000000000)⟩
theorem valid927 : certificate927.Valid := by decide +kernel
theorem sound927 : certificate927.Sound := rat_cut_bin_certificate_sound certificate927 profilesValid927 numericValid927 valid927

def retention928 : RatCutRetentionCertificate := ⟨(201/4000),(101/2000),(9161926045282713909/18648088304642895400),(8294172128656315767/1000000000000000000),(21/20),(13376598048429291537807398957913850440191/13270675405850105227200000000000000000000),false,MergedCutProfiles.Batch156.profile6278,(fun _ => MergedCutProfiles.Batch156.profile6278)⟩
theorem profilesValid928 : retention928.ProfilesValid := by
  exact MergedCutProfiles.Batch156.valid6278
theorem numericValid928 : retention928.NumericValid := by decide +kernel
def certificate928 : RatCutBinCertificate := ⟨⟨retention928,(2167774325693329727/1000000000000000000),(30615167816376129/250000000000000000),(13375694810516664019/1000000000000000000),(249789381237389577433/1000000000000000000),(987141208653274393/1000000000000000000)⟩,(49618211182754897/50000000000000000),(24331322824378837/50000000000000000),(162876630462833253/1000000000000000000),(27417358581807251/200000000000000000)⟩
theorem valid928 : certificate928.Valid := by decide +kernel
theorem sound928 : certificate928.Sound := rat_cut_bin_certificate_sound certificate928 profilesValid928 numericValid928 valid928

def retention929 : RatCutRetentionCertificate := ⟨(201/4000),(101/2000),(9253545305735541049/18648088304642895400),(9161926045282713909/1000000000000000000),(21/20),(4890492959675570601032607296192118752973/4886360557484114084800000000000000000000),false,MergedCutProfiles.Batch156.profile6279,(fun _ => MergedCutProfiles.Batch156.profile6279)⟩
theorem profilesValid929 : retention929.ProfilesValid := by
  exact MergedCutProfiles.Batch156.valid6279
theorem numericValid929 : retention929.NumericValid := by decide +kernel
def certificate929 : RatCutBinCertificate := ⟨⟨retention929,(2167774325693329727/1000000000000000000),(30615167816376129/250000000000000000),(13375694810516664019/1000000000000000000),(249789381237389577433/1000000000000000000),(980005314225161003/1000000000000000000)⟩,(49618211182754897/50000000000000000),(487102652276770729/1000000000000000000),(126979594265333/781250000000000),(13716815013669807/100000000000000000)⟩
theorem valid929 : certificate929.Valid := by decide +kernel
theorem sound929 : certificate929.Sound := rat_cut_bin_certificate_sound certificate929 profilesValid929 numericValid929 valid929

def retention930 : RatCutRetentionCertificate := ⟨(201/4000),(101/2000),(1/2),(9253545305735541049/1000000000000000000),(21/20),(14712535910623584171105547382293555691679/14805672489176865678400000000000000000000),false,MergedCutProfiles.Batch157.profile6280,(fun _ => MergedCutProfiles.Batch157.profile6280)⟩
theorem profilesValid930 : retention930.ProfilesValid := by
  exact MergedCutProfiles.Batch157.valid6280
theorem numericValid930 : retention930.NumericValid := by decide +kernel
def certificate930 : RatCutBinCertificate := ⟨⟨retention930,(2167774325693329727/1000000000000000000),(30615167816376129/250000000000000000),(13375694810516664019/1000000000000000000),(249789381237389577433/1000000000000000000),(38914760890701021/40000000000000000)⟩,(49618211182754897/50000000000000000),(490383306484090393/1000000000000000000),(160185201994625143/1000000000000000000),(134405482179663989/1000000000000000000)⟩
theorem valid930 : certificate930.Valid := by decide +kernel
theorem sound930 : certificate930.Sound := rat_cut_bin_certificate_sound certificate930 profilesValid930 numericValid930 valid930

def retention931 : RatCutRetentionCertificate := ⟨(201/4000),(101/2000),(1/2),64,1,(63848725488632703689495114220850027239/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch157.profile6280,(fun _ => MergedCutProfiles.Batch157.profile6280)⟩
theorem profilesValid931 : retention931.ProfilesValid := by
  exact MergedCutProfiles.Batch157.valid6280
theorem numericValid931 : retention931.NumericValid := by decide +kernel
def certificate931 : RatCutBinCertificate := ⟨⟨retention931,(2167774325693329727/1000000000000000000),(30615167816376129/250000000000000000),(13375694810516664019/1000000000000000000),(249789381237389577433/1000000000000000000),(61111825458702521/62500000000000000)⟩,(49618211182754897/50000000000000000),(463029910470344531/1000000000000000000),(45113429890239689/250000000000000000),(86225750832378873/500000000000000000)⟩
theorem valid931 : certificate931.Valid := by decide +kernel
theorem sound931 : certificate931.Sound := rat_cut_bin_certificate_sound certificate931 profilesValid931 numericValid931 valid931

def retention932 : RatCutRetentionCertificate := ⟨(201/4000),(101/2000),(841542657703567921/1864808830464289540),(1898174946371158641/500000000000000000),(6/5),(34552199108727924727828842775814938773/31636249106185977350000000000000000000),false,MergedCutProfiles.Batch157.profile6281,(fun _ => MergedCutProfiles.Batch157.profile6281)⟩
theorem profilesValid932 : retention932.ProfilesValid := by
  exact MergedCutProfiles.Batch157.valid6281
theorem numericValid932 : retention932.NumericValid := by decide +kernel
def certificate932 : RatCutBinCertificate := ⟨⟨retention932,(2545035750693329727/1000000000000000000),(30615167816376129/250000000000000000),(13375694810516664019/1000000000000000000),(249789381237389577433/1000000000000000000),(532103491503345319/500000000000000000)⟩,(991033715424263813/1000000000000000000),(188176306685892311/500000000000000000),(15991379024270657/62500000000000000),(94037306770036399/500000000000000000)⟩
theorem valid932 : certificate932.Valid := by decide +kernel
theorem sound932 : certificate932.Sound := rat_cut_bin_certificate_sound certificate932 profilesValid932 numericValid932 valid932

def retention933 : RatCutRetentionCertificate := ⟨(201/4000),(101/2000),(2300957027665121173/4662022076160723850),(841542657703567921/100000000000000000),(21/20),(135186343329297402887810253425330047799/134646825232570867360000000000000000000),false,MergedCutProfiles.Batch157.profile6282,(fun _ => MergedCutProfiles.Batch157.profile6282)⟩
theorem profilesValid933 : retention933.ProfilesValid := by
  exact MergedCutProfiles.Batch157.valid6282
theorem numericValid933 : retention933.NumericValid := by decide +kernel
def certificate933 : RatCutBinCertificate := ⟨⟨retention933,(2545035750693329727/1000000000000000000),(30615167816376129/250000000000000000),(13375694810516664019/1000000000000000000),(249789381237389577433/1000000000000000000),(97953952727936719/100000000000000000)⟩,(991033715424263813/1000000000000000000),(81776603816181051/200000000000000000),(112720583407999967/500000000000000000),(47109034151855421/250000000000000000)⟩
theorem valid933 : certificate933.Valid := by decide +kernel
theorem sound933 : certificate933.Sound := rat_cut_bin_certificate_sound certificate933 profilesValid933 numericValid933 valid933

def retention934 : RatCutRetentionCertificate := ⟨(201/4000),(101/2000),(9295866391767089539/18648088304642895400),(2300957027665121173/250000000000000000),(21/20),(917191034535581778368733889674134033871/920382811066048469200000000000000000000),false,MergedCutProfiles.Batch157.profile6283,(fun _ => MergedCutProfiles.Batch157.profile6283)⟩
theorem profilesValid934 : retention934.ProfilesValid := by
  exact MergedCutProfiles.Batch157.valid6283
theorem numericValid934 : retention934.NumericValid := by decide +kernel
def certificate934 : RatCutBinCertificate := ⟨⟨retention934,(2545035750693329727/1000000000000000000),(30615167816376129/250000000000000000),(13375694810516664019/1000000000000000000),(249789381237389577433/1000000000000000000),(194412970270956309/200000000000000000)⟩,(991033715424263813/1000000000000000000),(51503389751319533/125000000000000000),(222641468707038737/1000000000000000000),(186330915801069149/1000000000000000000)⟩
theorem valid934 : certificate934.Valid := by decide +kernel
theorem sound934 : certificate934.Sound := rat_cut_bin_certificate_sound certificate934 profilesValid934 numericValid934 valid934

def retention935 : RatCutRetentionCertificate := ⟨(201/4000),(101/2000),(1/2),(9295866391767089539/1000000000000000000),(21/20),(14781265369767438719870340286620829936359/14873386226827343262400000000000000000000),false,MergedCutProfiles.Batch157.profile6280,(fun _ => MergedCutProfiles.Batch157.profile6280)⟩
theorem profilesValid935 : retention935.ProfilesValid := by
  exact MergedCutProfiles.Batch157.valid6280
theorem numericValid935 : retention935.NumericValid := by decide +kernel
def certificate935 : RatCutBinCertificate := ⟨⟨retention935,(2545035750693329727/1000000000000000000),(30615167816376129/250000000000000000),(13375694810516664019/1000000000000000000),(249789381237389577433/1000000000000000000),(969339072239368899/1000000000000000000)⟩,(991033715424263813/1000000000000000000),(413185737265078069/1000000000000000000),(55403955113517247/250000000000000000),(92579178223433827/500000000000000000)⟩
theorem valid935 : certificate935.Valid := by decide +kernel
theorem sound935 : certificate935.Sound := rat_cut_bin_certificate_sound certificate935 profilesValid935 numericValid935 valid935

def certificates : List RatCutBinCertificate := [certificate924,certificate925,certificate926,certificate927,certificate928,certificate929,certificate930,certificate931,certificate932,certificate933,certificate934,certificate935]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound924,List.forall_mem_cons.mpr ⟨sound925,List.forall_mem_cons.mpr ⟨sound926,List.forall_mem_cons.mpr ⟨sound927,List.forall_mem_cons.mpr ⟨sound928,List.forall_mem_cons.mpr ⟨sound929,List.forall_mem_cons.mpr ⟨sound930,List.forall_mem_cons.mpr ⟨sound931,List.forall_mem_cons.mpr ⟨sound932,List.forall_mem_cons.mpr ⟨sound933,List.forall_mem_cons.mpr ⟨sound934,List.forall_mem_cons.mpr ⟨sound935,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch077
