import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch131
import Cycle12.MergedCutProfiles.Batch132
import Cycle12.MergedCutProfiles.Batch133

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch065

def retention780 : RatCutRetentionCertificate := ⟨(189/4000),(19/400),(3531263278513580671/7146980483221052809),(611449198476595573/62500000000000000),(21/20),(246135680888760176123630531482551048719/244579679390638229200000000000000000000),false,MergedCutProfiles.Batch131.profile5245,(fun _ => MergedCutProfiles.Batch131.profile5245)⟩
theorem profilesValid780 : retention780.ProfilesValid := by
  exact MergedCutProfiles.Batch131.valid5245
theorem numericValid780 : retention780.NumericValid := by decide +kernel
def certificate780 : RatCutBinCertificate := ⟨⟨retention780,(2138748609051754391/1000000000000000000),(26668397193078727/250000000000000000),(63647384072139359/5000000000000000),(273316494600652788773/1000000000000000000),(987542275905744999/1000000000000000000)⟩,(124124230016156549/125000000000000000),(19309095745169469/40000000000000000),(165700614187487481/1000000000000000000),(141720415824947851/1000000000000000000)⟩
theorem valid780 : certificate780.Valid := by decide +kernel
theorem sound780 : certificate780.Sound := rat_cut_bin_certificate_sound certificate780 profilesValid780 numericValid780 valid780

def retention781 : RatCutRetentionCertificate := ⟨(189/4000),(19/400),(3566575911298716478/7146980483221052809),(10593789835540742013/1000000000000000000),(21/20),(16919245272453550514508761518546393561151/16950063736865187220800000000000000000000),false,MergedCutProfiles.Batch131.profile5246,(fun _ => MergedCutProfiles.Batch131.profile5246)⟩
theorem profilesValid781 : retention781.ProfilesValid := by
  exact MergedCutProfiles.Batch131.valid5246
theorem numericValid781 : retention781.NumericValid := by decide +kernel
def certificate781 : RatCutBinCertificate := ⟨⟨retention781,(2138748609051754391/1000000000000000000),(26668397193078727/250000000000000000),(63647384072139359/5000000000000000),(273316494600652788773/1000000000000000000),(97936219793028391/100000000000000000)⟩,(124124230016156549/125000000000000000),(484593771365221733/1000000000000000000),(164344934508077879/1000000000000000000),(70195646266360727/500000000000000000)⟩
theorem valid781 : certificate781.Valid := by decide +kernel
theorem sound781 : certificate781.Sound := rat_cut_bin_certificate_sound certificate781 profilesValid781 numericValid781 valid781

def retention782 : RatCutRetentionCertificate := ⟨(189/4000),(19/400),(1/2),(5349863866948074717/500000000000000000),(21/20),(4264719378229574805006474081135017707751/4279891093558459773600000000000000000000),false,MergedCutProfiles.Batch131.profile5247,(fun _ => MergedCutProfiles.Batch131.profile5247)⟩
theorem profilesValid782 : retention782.ProfilesValid := by
  exact MergedCutProfiles.Batch131.valid5247
theorem numericValid782 : retention782.NumericValid := by decide +kernel
def certificate782 : RatCutBinCertificate := ⟨⟨retention782,(2138748609051754391/1000000000000000000),(26668397193078727/250000000000000000),(63647384072139359/5000000000000000),(273316494600652788773/1000000000000000000),(30551109769349617/31250000000000000)⟩,(124124230016156549/125000000000000000),(242595209914489947/500000000000000000),(81956532427457699/500000000000000000),(34975495440387851/250000000000000000)⟩
theorem valid782 : certificate782.Valid := by decide +kernel
theorem sound782 : certificate782.Sound := rat_cut_bin_certificate_sound certificate782 profilesValid782 numericValid782 valid782

def retention783 : RatCutRetentionCertificate := ⟨(189/4000),(19/400),(3189062310966691967/7146980483221052809),(3754698975349443237/1000000000000000000),(6/5),(413569985028822073732496127305742176711/375469897534944323700000000000000000000),false,MergedCutProfiles.Batch131.profile5248,(fun _ => MergedCutProfiles.Batch131.profile5248)⟩
theorem profilesValid783 : retention783.ProfilesValid := by
  exact MergedCutProfiles.Batch131.valid5248
theorem numericValid783 : retention783.NumericValid := by decide +kernel
def certificate783 : RatCutBinCertificate := ⟨⟨retention783,(2514253550051754391/1000000000000000000),(26668397193078727/250000000000000000),(63647384072139359/5000000000000000),(273316494600652788773/1000000000000000000),(538093710892289671/500000000000000000)⟩,(495881279454352571/500000000000000000),(373449002383769599/1000000000000000000),(258710545220315509/1000000000000000000),(38352648968513291/200000000000000000)⟩
theorem valid783 : certificate783.Valid := by decide +kernel
theorem sound783 : certificate783.Sound := rat_cut_bin_certificate_sound certificate783 profilesValid783 numericValid783 valid783

def retention784 : RatCutRetentionCertificate := ⟨(189/4000),(19/400),(10568126364026384677/21440941449663158427),(9567186932900075901/1000000000000000000),(21/20),(15433610548775820736615101548652287832839/15307499092640121441600000000000000000000),false,MergedCutProfiles.Batch131.profile5249,(fun _ => MergedCutProfiles.Batch131.profile5249)⟩
theorem profilesValid784 : retention784.ProfilesValid := by
  exact MergedCutProfiles.Batch131.valid5249
theorem numericValid784 : retention784.NumericValid := by decide +kernel
def certificate784 : RatCutBinCertificate := ⟨⟨retention784,(2514253550051754391/1000000000000000000),(26668397193078727/250000000000000000),(63647384072139359/5000000000000000),(273316494600652788773/1000000000000000000),(986114645452870093/1000000000000000000)⟩,(495881279454352571/500000000000000000),(407560237439573151/1000000000000000000),(226626264624347163/1000000000000000000),(96482832218854711/500000000000000000)⟩
theorem valid784 : certificate784.Valid := by decide +kernel
theorem sound784 : certificate784.Sound := rat_cut_bin_certificate_sound certificate784 profilesValid784 numericValid784 valid784

def retention785 : RatCutRetentionCertificate := ⟨(189/4000),(19/400),(10673807627666648524/21440941449663158427),(10568126364026384677/1000000000000000000),(21/20),(16917592164360437828577228174334218174071/16909002182442215483200000000000000000000),false,MergedCutProfiles.Batch131.profile5250,(fun _ => MergedCutProfiles.Batch131.profile5250)⟩
theorem profilesValid785 : retention785.ProfilesValid := by
  exact MergedCutProfiles.Batch131.valid5250
theorem numericValid785 : retention785.NumericValid := by decide +kernel
def certificate785 : RatCutBinCertificate := ⟨⟨retention785,(2514253550051754391/1000000000000000000),(26668397193078727/250000000000000000),(63647384072139359/5000000000000000),(273316494600652788773/1000000000000000000),(978384198390233437/1000000000000000000)⟩,(495881279454352571/500000000000000000),(205390234074033949/500000000000000000),(55937170582565101/250000000000000000),(95343947225017023/500000000000000000)⟩
theorem valid785 : certificate785.Valid := by decide +kernel
theorem sound785 : certificate785.Sound := rat_cut_bin_certificate_sound certificate785 profilesValid785 numericValid785 valid785

def retention786 : RatCutRetentionCertificate := ⟨(189/4000),(19/400),(1/2),(2668451906916662131/250000000000000000),(21/20),(1063553564606407520378376292695731064399/1067380762766664852400000000000000000000),false,MergedCutProfiles.Batch131.profile5247,(fun _ => MergedCutProfiles.Batch131.profile5247)⟩
theorem profilesValid786 : retention786.ProfilesValid := by
  exact MergedCutProfiles.Batch131.valid5247
theorem numericValid786 : retention786.NumericValid := by decide +kernel
def certificate786 : RatCutBinCertificate := ⟨⟨retention786,(2514253550051754391/1000000000000000000),(26668397193078727/250000000000000000),(63647384072139359/5000000000000000),(273316494600652788773/1000000000000000000),(194858119180552841/200000000000000000)⟩,(495881279454352571/500000000000000000),(412506413110778521/1000000000000000000),(55554196576111037/250000000000000000),(188795922519024537/1000000000000000000)⟩
theorem valid786 : certificate786.Valid := by decide +kernel
theorem sound786 : certificate786.Sound := rat_cut_bin_certificate_sound certificate786 profilesValid786 numericValid786 valid786

def retention787 : RatCutRetentionCertificate := ⟨(19/400),(191/4000),(841595600945419971/21187119060085996196),(20831574280827227/25000000000000000),(59/20),(8355083067872540813/4000000000000000000),true,MergedCutProfiles.Batch131.profile5251,![MergedCutProfiles.Batch131.profile5251,MergedCutProfiles.Batch131.profile5252,MergedCutProfiles.Batch131.profile5253,MergedCutProfiles.Batch131.profile5254,MergedCutProfiles.Batch131.profile5255,MergedCutProfiles.Batch131.profile5256,MergedCutProfiles.Batch131.profile5257,MergedCutProfiles.Batch131.profile5258,MergedCutProfiles.Batch131.profile5259,MergedCutProfiles.Batch131.profile5260,MergedCutProfiles.Batch131.profile5261,MergedCutProfiles.Batch131.profile5262,MergedCutProfiles.Batch131.profile5263,MergedCutProfiles.Batch131.profile5264,MergedCutProfiles.Batch131.profile5265,MergedCutProfiles.Batch131.profile5266]⟩
theorem profilesValid787 : retention787.ProfilesValid := by
  change ∀ j : Fin 16, (retention787.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch131.valid5251
  · exact MergedCutProfiles.Batch131.valid5252
  · exact MergedCutProfiles.Batch131.valid5253
  · exact MergedCutProfiles.Batch131.valid5254
  · exact MergedCutProfiles.Batch131.valid5255
  · exact MergedCutProfiles.Batch131.valid5256
  · exact MergedCutProfiles.Batch131.valid5257
  · exact MergedCutProfiles.Batch131.valid5258
  · exact MergedCutProfiles.Batch131.valid5259
  · exact MergedCutProfiles.Batch131.valid5260
  · exact MergedCutProfiles.Batch131.valid5261
  · exact MergedCutProfiles.Batch131.valid5262
  · exact MergedCutProfiles.Batch131.valid5263
  · exact MergedCutProfiles.Batch131.valid5264
  · exact MergedCutProfiles.Batch131.valid5265
  · exact MergedCutProfiles.Batch131.valid5266
theorem numericValid787 : retention787.NumericValid := by decide +kernel
def certificate787 : RatCutBinCertificate := ⟨⟨retention787,(10710553993607843/5000000000000000),(107936348659400079/1000000000000000000),(12781485468971221657/1000000000000000000),(33898123835131850651/125000000000000000),(2035397885099813961/1000000000000000000)⟩,(496468725252630099/500000000000000000),(94665272935726009/250000000000000000),(10144535863961247/40000000000000000),(5419650845900173/40000000000000000)⟩
theorem valid787 : certificate787.Valid := by decide +kernel
theorem sound787 : certificate787.Sound := rat_cut_bin_certificate_sound certificate787 profilesValid787 numericValid787 valid787

def retention788 : RatCutRetentionCertificate := ⟨(19/400),(191/4000),(218850260250000000/5296779765021499049),(841595600945419971/1000000000000000000),(59/20),(2672548571742618322643/1280000000000000000000),true,MergedCutProfiles.Batch131.profile5267,![MergedCutProfiles.Batch131.profile5267,MergedCutProfiles.Batch131.profile5268,MergedCutProfiles.Batch131.profile5269,MergedCutProfiles.Batch131.profile5270,MergedCutProfiles.Batch131.profile5271,MergedCutProfiles.Batch131.profile5272,MergedCutProfiles.Batch131.profile5273,MergedCutProfiles.Batch131.profile5274,MergedCutProfiles.Batch131.profile5275,MergedCutProfiles.Batch131.profile5276,MergedCutProfiles.Batch131.profile5277,MergedCutProfiles.Batch131.profile5278,MergedCutProfiles.Batch131.profile5279,MergedCutProfiles.Batch132.profile5280,MergedCutProfiles.Batch132.profile5281,MergedCutProfiles.Batch132.profile5282]⟩
theorem profilesValid788 : retention788.ProfilesValid := by
  change ∀ j : Fin 16, (retention788.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch131.valid5267
  · exact MergedCutProfiles.Batch131.valid5268
  · exact MergedCutProfiles.Batch131.valid5269
  · exact MergedCutProfiles.Batch131.valid5270
  · exact MergedCutProfiles.Batch131.valid5271
  · exact MergedCutProfiles.Batch131.valid5272
  · exact MergedCutProfiles.Batch131.valid5273
  · exact MergedCutProfiles.Batch131.valid5274
  · exact MergedCutProfiles.Batch131.valid5275
  · exact MergedCutProfiles.Batch131.valid5276
  · exact MergedCutProfiles.Batch131.valid5277
  · exact MergedCutProfiles.Batch131.valid5278
  · exact MergedCutProfiles.Batch131.valid5279
  · exact MergedCutProfiles.Batch132.valid5280
  · exact MergedCutProfiles.Batch132.valid5281
  · exact MergedCutProfiles.Batch132.valid5282
theorem numericValid788 : retention788.NumericValid := by decide +kernel
def certificate788 : RatCutBinCertificate := ⟨⟨retention788,(10710553993607843/5000000000000000),(107936348659400079/1000000000000000000),(12781485468971221657/1000000000000000000),(33898123835131850651/125000000000000000),(2034555775356963501/1000000000000000000)⟩,(496468725252630099/500000000000000000),(4715621159465263/12500000000000000),(15936659470847171/62500000000000000),(34119569957027879/250000000000000000)⟩
theorem valid788 : certificate788.Valid := by decide +kernel
theorem sound788 : certificate788.Sound := rat_cut_bin_certificate_sound certificate788 profilesValid788 numericValid788 valid788

def retention789 : RatCutRetentionCertificate := ⟨(19/400),(191/4000),(1026906569937625153/21187119060085996196),(875401041/1000000000),(57/20),(6598483059876866721/3200000000000000000),true,MergedCutProfiles.Batch132.profile5283,![MergedCutProfiles.Batch132.profile5283,MergedCutProfiles.Batch132.profile5284,MergedCutProfiles.Batch132.profile5285,MergedCutProfiles.Batch132.profile5286,MergedCutProfiles.Batch132.profile5287,MergedCutProfiles.Batch132.profile5288,MergedCutProfiles.Batch132.profile5289,MergedCutProfiles.Batch132.profile5290,MergedCutProfiles.Batch131.profile5261,MergedCutProfiles.Batch132.profile5291,MergedCutProfiles.Batch132.profile5292,MergedCutProfiles.Batch132.profile5293,MergedCutProfiles.Batch132.profile5294,MergedCutProfiles.Batch132.profile5295,MergedCutProfiles.Batch132.profile5296,MergedCutProfiles.Batch132.profile5297]⟩
theorem profilesValid789 : retention789.ProfilesValid := by
  change ∀ j : Fin 16, (retention789.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch132.valid5283
  · exact MergedCutProfiles.Batch132.valid5284
  · exact MergedCutProfiles.Batch132.valid5285
  · exact MergedCutProfiles.Batch132.valid5286
  · exact MergedCutProfiles.Batch132.valid5287
  · exact MergedCutProfiles.Batch132.valid5288
  · exact MergedCutProfiles.Batch132.valid5289
  · exact MergedCutProfiles.Batch132.valid5290
  · exact MergedCutProfiles.Batch131.valid5261
  · exact MergedCutProfiles.Batch132.valid5291
  · exact MergedCutProfiles.Batch132.valid5292
  · exact MergedCutProfiles.Batch132.valid5293
  · exact MergedCutProfiles.Batch132.valid5294
  · exact MergedCutProfiles.Batch132.valid5295
  · exact MergedCutProfiles.Batch132.valid5296
  · exact MergedCutProfiles.Batch132.valid5297
theorem numericValid789 : retention789.NumericValid := by decide +kernel
def certificate789 : RatCutBinCertificate := ⟨⟨retention789,(10710553993607843/5000000000000000),(107936348659400079/1000000000000000000),(12781485468971221657/1000000000000000000),(33898123835131850651/125000000000000000),(502615611899295879/250000000000000000)⟩,(496468725252630099/500000000000000000),(5869412776642953/15625000000000000),(128278350672772241/500000000000000000),(139912806741322039/1000000000000000000)⟩
theorem valid789 : certificate789.Valid := by decide +kernel
theorem sound789 : certificate789.Sound := rat_cut_bin_certificate_sound certificate789 profilesValid789 numericValid789 valid789

def retention790 : RatCutRetentionCertificate := ⟨(19/400),(191/4000),(2209412026405382513/21187119060085996196),(1026906569937625153/1000000000000000000),(5/2),(96538985253718134869/51200000000000000000),true,MergedCutProfiles.Batch132.profile5298,![MergedCutProfiles.Batch132.profile5298,MergedCutProfiles.Batch132.profile5299,MergedCutProfiles.Batch132.profile5300,MergedCutProfiles.Batch132.profile5301,MergedCutProfiles.Batch132.profile5302,MergedCutProfiles.Batch132.profile5303,MergedCutProfiles.Batch132.profile5304,MergedCutProfiles.Batch132.profile5305,MergedCutProfiles.Batch132.profile5306,MergedCutProfiles.Batch132.profile5307,MergedCutProfiles.Batch132.profile5308,MergedCutProfiles.Batch132.profile5309,MergedCutProfiles.Batch132.profile5310,MergedCutProfiles.Batch132.profile5311,MergedCutProfiles.Batch132.profile5312,MergedCutProfiles.Batch132.profile5313]⟩
theorem profilesValid790 : retention790.ProfilesValid := by
  change ∀ j : Fin 16, (retention790.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch132.valid5298
  · exact MergedCutProfiles.Batch132.valid5299
  · exact MergedCutProfiles.Batch132.valid5300
  · exact MergedCutProfiles.Batch132.valid5301
  · exact MergedCutProfiles.Batch132.valid5302
  · exact MergedCutProfiles.Batch132.valid5303
  · exact MergedCutProfiles.Batch132.valid5304
  · exact MergedCutProfiles.Batch132.valid5305
  · exact MergedCutProfiles.Batch132.valid5306
  · exact MergedCutProfiles.Batch132.valid5307
  · exact MergedCutProfiles.Batch132.valid5308
  · exact MergedCutProfiles.Batch132.valid5309
  · exact MergedCutProfiles.Batch132.valid5310
  · exact MergedCutProfiles.Batch132.valid5311
  · exact MergedCutProfiles.Batch132.valid5312
  · exact MergedCutProfiles.Batch132.valid5313
theorem numericValid790 : retention790.NumericValid := by decide +kernel
def certificate790 : RatCutBinCertificate := ⟨⟨retention790,(10710553993607843/5000000000000000),(107936348659400079/1000000000000000000),(12781485468971221657/1000000000000000000),(33898123835131850651/125000000000000000),(18402961112180913/10000000000000000)⟩,(496468725252630099/500000000000000000),(24111683980084331/62500000000000000),(3855632799993939/15625000000000000),(27999273115408187/200000000000000000)⟩
theorem valid790 : certificate790.Valid := by decide +kernel
theorem sound790 : certificate790.Sound := rat_cut_bin_certificate_sound certificate790 profilesValid790 numericValid790 valid790

def retention791 : RatCutRetentionCertificate := ⟨(19/400),(191/4000),(7077460369990681321/21187119060085996196),(2209412026405382513/1000000000000000000),(29/20),(1702276680664012534633/1280000000000000000000),true,MergedCutProfiles.Batch132.profile5314,![MergedCutProfiles.Batch132.profile5314,MergedCutProfiles.Batch132.profile5315,MergedCutProfiles.Batch132.profile5316,MergedCutProfiles.Batch132.profile5317,MergedCutProfiles.Batch132.profile5313,MergedCutProfiles.Batch132.profile5318,MergedCutProfiles.Batch132.profile5319,MergedCutProfiles.Batch133.profile5320,MergedCutProfiles.Batch133.profile5321,MergedCutProfiles.Batch133.profile5322,MergedCutProfiles.Batch133.profile5323,MergedCutProfiles.Batch133.profile5324,MergedCutProfiles.Batch133.profile5325,MergedCutProfiles.Batch133.profile5326,MergedCutProfiles.Batch133.profile5327,MergedCutProfiles.Batch133.profile5328]⟩
theorem profilesValid791 : retention791.ProfilesValid := by
  change ∀ j : Fin 16, (retention791.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch132.valid5314
  · exact MergedCutProfiles.Batch132.valid5315
  · exact MergedCutProfiles.Batch132.valid5316
  · exact MergedCutProfiles.Batch132.valid5317
  · exact MergedCutProfiles.Batch132.valid5313
  · exact MergedCutProfiles.Batch132.valid5318
  · exact MergedCutProfiles.Batch132.valid5319
  · exact MergedCutProfiles.Batch133.valid5320
  · exact MergedCutProfiles.Batch133.valid5321
  · exact MergedCutProfiles.Batch133.valid5322
  · exact MergedCutProfiles.Batch133.valid5323
  · exact MergedCutProfiles.Batch133.valid5324
  · exact MergedCutProfiles.Batch133.valid5325
  · exact MergedCutProfiles.Batch133.valid5326
  · exact MergedCutProfiles.Batch133.valid5327
  · exact MergedCutProfiles.Batch133.valid5328
theorem numericValid791 : retention791.NumericValid := by decide +kernel
def certificate791 : RatCutBinCertificate := ⟨⟨retention791,(10710553993607843/5000000000000000),(107936348659400079/1000000000000000000),(12781485468971221657/1000000000000000000),(33898123835131850651/125000000000000000),(65183525837036719/50000000000000000)⟩,(496468725252630099/500000000000000000),(437242040312753953/1000000000000000000),(201041028539979623/1000000000000000000),(140004861929681561/1000000000000000000)⟩
theorem valid791 : certificate791.Valid := by decide +kernel
theorem sound791 : certificate791.Sound := rat_cut_bin_certificate_sound certificate791 profilesValid791 numericValid791 valid791

def certificates : List RatCutBinCertificate := [certificate780,certificate781,certificate782,certificate783,certificate784,certificate785,certificate786,certificate787,certificate788,certificate789,certificate790,certificate791]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound780,List.forall_mem_cons.mpr ⟨sound781,List.forall_mem_cons.mpr ⟨sound782,List.forall_mem_cons.mpr ⟨sound783,List.forall_mem_cons.mpr ⟨sound784,List.forall_mem_cons.mpr ⟨sound785,List.forall_mem_cons.mpr ⟨sound786,List.forall_mem_cons.mpr ⟨sound787,List.forall_mem_cons.mpr ⟨sound788,List.forall_mem_cons.mpr ⟨sound789,List.forall_mem_cons.mpr ⟨sound790,List.forall_mem_cons.mpr ⟨sound791,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch065
