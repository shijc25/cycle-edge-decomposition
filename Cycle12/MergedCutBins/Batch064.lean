import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch129
import Cycle12.MergedCutProfiles.Batch130
import Cycle12.MergedCutProfiles.Batch131

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch064

def retention768 : RatCutRetentionCertificate := ⟨(47/1000),(189/4000),(10720772374146673549/21698958102430916216),(5100223529321450751/500000000000000000),(21/20),(4109632573769467286846392026868950968639/4080178823457160600800000000000000000000),false,MergedCutProfiles.Batch129.profile5162,(fun _ => MergedCutProfiles.Batch129.profile5162)⟩
theorem profilesValid768 : retention768.ProfilesValid := by
  exact MergedCutProfiles.Batch129.valid5162
theorem numericValid768 : retention768.NumericValid := by decide +kernel
def certificate768 : RatCutBinCertificate := ⟨⟨retention768,(42740837380569851/20000000000000000),(105420224118676281/1000000000000000000),(12677791270123688181/1000000000000000000),(137740909997000893777/500000000000000000),(494279659072749581/500000000000000000)⟩,(993044919335267451/1000000000000000000),(481703642778055957/1000000000000000000),(33289459637845021/200000000000000000),(142994166875119129/1000000000000000000)⟩
theorem valid768 : certificate768.Valid := by decide +kernel
theorem sound768 : certificate768.Sound := rat_cut_bin_certificate_sound certificate768 profilesValid768 numericValid768 valid768

def retention769 : RatCutRetentionCertificate := ⟨(47/1000),(189/4000),(1546854299698305755/3099851157490130888),(10720772374146673549/1000000000000000000),(21/20),(17126280750789698813957435409410333449479/17153235798634677678400000000000000000000),false,MergedCutProfiles.Batch129.profile5163,(fun _ => MergedCutProfiles.Batch129.profile5163)⟩
theorem profilesValid769 : retention769.ProfilesValid := by
  exact MergedCutProfiles.Batch129.valid5163
theorem numericValid769 : retention769.NumericValid := by decide +kernel
def certificate769 : RatCutBinCertificate := ⟨⟨retention769,(42740837380569851/20000000000000000),(105420224118676281/1000000000000000000),(12677791270123688181/1000000000000000000),(137740909997000893777/500000000000000000),(979769184029032627/1000000000000000000)⟩,(993044919335267451/1000000000000000000),(484710735634022517/1000000000000000000),(164260214874261261/1000000000000000000),(140509688966066491/1000000000000000000)⟩
theorem valid769 : certificate769.Valid := by decide +kernel
theorem sound769 : certificate769.Sound := rat_cut_bin_certificate_sound certificate769 profilesValid769 numericValid769 valid769

def retention770 : RatCutRetentionCertificate := ⟨(47/1000),(189/4000),(1/2),(2165596019577628057/200000000000000000),(21/20),(690670242996678033998815067712890748639/692990726264840978240000000000000000000),false,MergedCutProfiles.Batch129.profile5164,(fun _ => MergedCutProfiles.Batch129.profile5164)⟩
theorem profilesValid770 : retention770.ProfilesValid := by
  exact MergedCutProfiles.Batch129.valid5164
theorem numericValid770 : retention770.NumericValid := by decide +kernel
def certificate770 : RatCutBinCertificate := ⟨⟨retention770,(42740837380569851/20000000000000000),(105420224118676281/1000000000000000000),(12677791270123688181/1000000000000000000),(137740909997000893777/500000000000000000),(488996055605300101/500000000000000000)⟩,(993044919335267451/1000000000000000000),(60666982967958931/125000000000000000),(163807900028747523/1000000000000000000),(139994388358751823/1000000000000000000)⟩
theorem valid770 : certificate770.Valid := by decide +kernel
theorem sound770 : certificate770.Sound := rat_cut_bin_certificate_sound certificate770 profilesValid770 numericValid770 valid770

def retention771 : RatCutRetentionCertificate := ⟨(47/1000),(189/4000),(374525154189376915/834575311631958316),(1873149586018979/500000000000000),(6/5),(16430279298860873469899978439930572511/14985196688151832000000000000000000000),false,MergedCutProfiles.Batch129.profile5165,(fun _ => MergedCutProfiles.Batch129.profile5165)⟩
theorem profilesValid771 : retention771.ProfilesValid := by
  exact MergedCutProfiles.Batch129.valid5165
theorem numericValid771 : retention771.NumericValid := by decide +kernel
def certificate771 : RatCutBinCertificate := ⟨⟨retention771,(50250140960569851/20000000000000000),(105420224118676281/1000000000000000000),(12677791270123688181/1000000000000000000),(137740909997000893777/500000000000000000),(535680518422463799/500000000000000000)⟩,(991821792288095387/1000000000000000000),(47027068981075479/125000000000000000),(255995041352464971/1000000000000000000),(18898233201464659/100000000000000000)⟩
theorem valid771 : certificate771.Valid := by decide +kernel
theorem sound771 : certificate771.Sound := rat_cut_bin_certificate_sound certificate771 profilesValid771 numericValid771 valid771

def retention772 : RatCutRetentionCertificate := ⟨(47/1000),(189/4000),(192079072640291856/387481394686266361),(973765400892379979/100000000000000000),(21/20),(156286224748577029539645841201467551439/155802464142780796640000000000000000000),false,MergedCutProfiles.Batch129.profile5166,(fun _ => MergedCutProfiles.Batch129.profile5166)⟩
theorem profilesValid772 : retention772.ProfilesValid := by
  exact MergedCutProfiles.Batch129.valid5166
theorem numericValid772 : retention772.NumericValid := by decide +kernel
def certificate772 : RatCutBinCertificate := ⟨⟨retention772,(50250140960569851/20000000000000000),(105420224118676281/1000000000000000000),(12677791270123688181/1000000000000000000),(137740909997000893777/500000000000000000),(981167155791010647/1000000000000000000)⟩,(991821792288095387/1000000000000000000),(82160058597109533/200000000000000000),(55932761328238761/250000000000000000),(189922042433272367/1000000000000000000)⟩
theorem valid772 : certificate772.Valid := by decide +kernel
theorem sound772 : certificate772.Sound := rat_cut_bin_certificate_sound certificate772 profilesValid772 numericValid772 valid772

def retention773 : RatCutRetentionCertificate := ⟨(47/1000),(189/4000),(1/2),(84034594280127687/7812500000000000),(21/20),(267980850693223656494365018029724607351/268910701696408598400000000000000000000),false,MergedCutProfiles.Batch129.profile5164,(fun _ => MergedCutProfiles.Batch129.profile5164)⟩
theorem profilesValid773 : retention773.ProfilesValid := by
  exact MergedCutProfiles.Batch129.valid5164
theorem numericValid773 : retention773.NumericValid := by decide +kernel
def certificate773 : RatCutBinCertificate := ⟨⟨retention773,(50250140960569851/20000000000000000),(105420224118676281/1000000000000000000),(12677791270123688181/1000000000000000000),(137740909997000893777/500000000000000000),(974604429297308843/1000000000000000000)⟩,(991821792288095387/1000000000000000000),(206783256339884067/500000000000000000),(221279454935105071/1000000000000000000),(11761143049555259/62500000000000000)⟩
theorem valid773 : certificate773.Valid := by decide +kernel
theorem sound773 : certificate773.Sound := rat_cut_bin_certificate_sound certificate773 profilesValid773 numericValid773 valid773

def retention774 : RatCutRetentionCertificate := ⟨(189/4000),(19/400),(837724155532640260/21440941449663158427),(414714928481505079/500000000000000000),3,(268597479450439366863/128000000000000000000),true,MergedCutProfiles.Batch129.profile5167,![MergedCutProfiles.Batch129.profile5167,MergedCutProfiles.Batch129.profile5168,MergedCutProfiles.Batch129.profile5169,MergedCutProfiles.Batch129.profile5170,MergedCutProfiles.Batch129.profile5171,MergedCutProfiles.Batch129.profile5172,MergedCutProfiles.Batch129.profile5173,MergedCutProfiles.Batch129.profile5174,MergedCutProfiles.Batch129.profile5175,MergedCutProfiles.Batch129.profile5176,MergedCutProfiles.Batch129.profile5177,MergedCutProfiles.Batch129.profile5178,MergedCutProfiles.Batch129.profile5179,MergedCutProfiles.Batch129.profile5180,MergedCutProfiles.Batch129.profile5181,MergedCutProfiles.Batch129.profile5182]⟩
theorem profilesValid774 : retention774.ProfilesValid := by
  change ∀ j : Fin 16, (retention774.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch129.valid5167
  · exact MergedCutProfiles.Batch129.valid5168
  · exact MergedCutProfiles.Batch129.valid5169
  · exact MergedCutProfiles.Batch129.valid5170
  · exact MergedCutProfiles.Batch129.valid5171
  · exact MergedCutProfiles.Batch129.valid5172
  · exact MergedCutProfiles.Batch129.valid5173
  · exact MergedCutProfiles.Batch129.valid5174
  · exact MergedCutProfiles.Batch129.valid5175
  · exact MergedCutProfiles.Batch129.valid5176
  · exact MergedCutProfiles.Batch129.valid5177
  · exact MergedCutProfiles.Batch129.valid5178
  · exact MergedCutProfiles.Batch129.valid5179
  · exact MergedCutProfiles.Batch129.valid5180
  · exact MergedCutProfiles.Batch129.valid5181
  · exact MergedCutProfiles.Batch129.valid5182
theorem numericValid774 : retention774.NumericValid := by decide +kernel
def certificate774 : RatCutBinCertificate := ⟨⟨retention774,(2138748609051754391/1000000000000000000),(26668397193078727/250000000000000000),(63647384072139359/5000000000000000),(273316494600652788773/1000000000000000000),(2044640945635243999/1000000000000000000)⟩,(124124230016156549/125000000000000000),(379494997241199507/1000000000000000000),(252804558713109121/1000000000000000000),(134132299956507711/1000000000000000000)⟩
theorem valid774 : certificate774.Valid := by decide +kernel
theorem sound774 : certificate774.Sound := rat_cut_bin_certificate_sound certificate774 profilesValid774 numericValid774 valid774

def retention775 : RatCutRetentionCertificate := ⟨(189/4000),(19/400),(871176641000000000/21440941449663158427),(41886207776632013/50000000000000000),(59/20),(4175347370508326573/2000000000000000000),true,MergedCutProfiles.Batch129.profile5183,![MergedCutProfiles.Batch129.profile5183,MergedCutProfiles.Batch129.profile5184,MergedCutProfiles.Batch129.profile5185,MergedCutProfiles.Batch129.profile5186,MergedCutProfiles.Batch129.profile5187,MergedCutProfiles.Batch129.profile5188,MergedCutProfiles.Batch129.profile5189,MergedCutProfiles.Batch129.profile5190,MergedCutProfiles.Batch129.profile5191,MergedCutProfiles.Batch129.profile5192,MergedCutProfiles.Batch129.profile5193,MergedCutProfiles.Batch129.profile5194,MergedCutProfiles.Batch129.profile5195,MergedCutProfiles.Batch129.profile5196,MergedCutProfiles.Batch129.profile5197,MergedCutProfiles.Batch129.profile5198]⟩
theorem profilesValid775 : retention775.ProfilesValid := by
  change ∀ j : Fin 16, (retention775.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch129.valid5183
  · exact MergedCutProfiles.Batch129.valid5184
  · exact MergedCutProfiles.Batch129.valid5185
  · exact MergedCutProfiles.Batch129.valid5186
  · exact MergedCutProfiles.Batch129.valid5187
  · exact MergedCutProfiles.Batch129.valid5188
  · exact MergedCutProfiles.Batch129.valid5189
  · exact MergedCutProfiles.Batch129.valid5190
  · exact MergedCutProfiles.Batch129.valid5191
  · exact MergedCutProfiles.Batch129.valid5192
  · exact MergedCutProfiles.Batch129.valid5193
  · exact MergedCutProfiles.Batch129.valid5194
  · exact MergedCutProfiles.Batch129.valid5195
  · exact MergedCutProfiles.Batch129.valid5196
  · exact MergedCutProfiles.Batch129.valid5197
  · exact MergedCutProfiles.Batch129.valid5198
theorem numericValid775 : retention775.NumericValid := by decide +kernel
def certificate775 : RatCutBinCertificate := ⟨⟨retention775,(2138748609051754391/1000000000000000000),(26668397193078727/250000000000000000),(63647384072139359/5000000000000000),(273316494600652788773/1000000000000000000),(2034793046666104827/1000000000000000000)⟩,(124124230016156549/125000000000000000),(379740843248537261/1000000000000000000),(252566452610274997/1000000000000000000),(135068201915630293/1000000000000000000)⟩
theorem valid775 : certificate775.Valid := by decide +kernel
theorem sound775 : certificate775.Sound := rat_cut_bin_certificate_sound certificate775 profilesValid775 numericValid775 valid775

def retention776 : RatCutRetentionCertificate := ⟨(189/4000),(19/400),(962942314591033217/21440941449663158427),(871176641/1000000000),(57/20),(33146972410624499491/16000000000000000000),true,MergedCutProfiles.Batch129.profile5199,![MergedCutProfiles.Batch129.profile5199,MergedCutProfiles.Batch130.profile5200,MergedCutProfiles.Batch130.profile5201,MergedCutProfiles.Batch130.profile5202,MergedCutProfiles.Batch130.profile5203,MergedCutProfiles.Batch130.profile5204,MergedCutProfiles.Batch130.profile5205,MergedCutProfiles.Batch130.profile5206,MergedCutProfiles.Batch130.profile5207,MergedCutProfiles.Batch130.profile5208,MergedCutProfiles.Batch130.profile5209,MergedCutProfiles.Batch130.profile5210,MergedCutProfiles.Batch129.profile5181,MergedCutProfiles.Batch130.profile5211,MergedCutProfiles.Batch130.profile5212,MergedCutProfiles.Batch130.profile5213]⟩
theorem profilesValid776 : retention776.ProfilesValid := by
  change ∀ j : Fin 16, (retention776.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch129.valid5199
  · exact MergedCutProfiles.Batch130.valid5200
  · exact MergedCutProfiles.Batch130.valid5201
  · exact MergedCutProfiles.Batch130.valid5202
  · exact MergedCutProfiles.Batch130.valid5203
  · exact MergedCutProfiles.Batch130.valid5204
  · exact MergedCutProfiles.Batch130.valid5205
  · exact MergedCutProfiles.Batch130.valid5206
  · exact MergedCutProfiles.Batch130.valid5207
  · exact MergedCutProfiles.Batch130.valid5208
  · exact MergedCutProfiles.Batch130.valid5209
  · exact MergedCutProfiles.Batch130.valid5210
  · exact MergedCutProfiles.Batch129.valid5181
  · exact MergedCutProfiles.Batch130.valid5211
  · exact MergedCutProfiles.Batch130.valid5212
  · exact MergedCutProfiles.Batch130.valid5213
theorem numericValid776 : retention776.NumericValid := by decide +kernel
def certificate776 : RatCutBinCertificate := ⟨⟨retention776,(2138748609051754391/1000000000000000000),(26668397193078727/250000000000000000),(63647384072139359/5000000000000000),(273316494600652788773/1000000000000000000),(2020597738679208079/1000000000000000000)⟩,(124124230016156549/125000000000000000),(1505028454991429/4000000000000000),(255955393861654033/1000000000000000000),(2799834661457967/20000000000000000)⟩
theorem valid776 : certificate776.Valid := by decide +kernel
theorem sound776 : certificate776.Sound := rat_cut_bin_certificate_sound certificate776 profilesValid776 numericValid776 valid776

def retention777 : RatCutRetentionCertificate := ⟨(189/4000),(19/400),(583124707941731231/7146980483221052809),(962942314591033217/1000000000000000000),(13/5),(624762659625219008173/320000000000000000000),true,MergedCutProfiles.Batch130.profile5214,![MergedCutProfiles.Batch130.profile5214,MergedCutProfiles.Batch129.profile5186,MergedCutProfiles.Batch130.profile5215,MergedCutProfiles.Batch130.profile5216,MergedCutProfiles.Batch130.profile5217,MergedCutProfiles.Batch130.profile5218,MergedCutProfiles.Batch129.profile5196,MergedCutProfiles.Batch130.profile5219,MergedCutProfiles.Batch130.profile5220,MergedCutProfiles.Batch130.profile5221,MergedCutProfiles.Batch130.profile5222,MergedCutProfiles.Batch130.profile5223,MergedCutProfiles.Batch130.profile5224,MergedCutProfiles.Batch130.profile5225,MergedCutProfiles.Batch130.profile5226,MergedCutProfiles.Batch130.profile5227]⟩
theorem profilesValid777 : retention777.ProfilesValid := by
  change ∀ j : Fin 16, (retention777.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch130.valid5214
  · exact MergedCutProfiles.Batch129.valid5186
  · exact MergedCutProfiles.Batch130.valid5215
  · exact MergedCutProfiles.Batch130.valid5216
  · exact MergedCutProfiles.Batch130.valid5217
  · exact MergedCutProfiles.Batch130.valid5218
  · exact MergedCutProfiles.Batch129.valid5196
  · exact MergedCutProfiles.Batch130.valid5219
  · exact MergedCutProfiles.Batch130.valid5220
  · exact MergedCutProfiles.Batch130.valid5221
  · exact MergedCutProfiles.Batch130.valid5222
  · exact MergedCutProfiles.Batch130.valid5223
  · exact MergedCutProfiles.Batch130.valid5224
  · exact MergedCutProfiles.Batch130.valid5225
  · exact MergedCutProfiles.Batch130.valid5226
  · exact MergedCutProfiles.Batch130.valid5227
theorem numericValid777 : retention777.NumericValid := by decide +kernel
def certificate777 : RatCutBinCertificate := ⟨⟨retention777,(2138748609051754391/1000000000000000000),(26668397193078727/250000000000000000),(63647384072139359/5000000000000000),(273316494600652788773/1000000000000000000),(1905776741943870607/1000000000000000000)⟩,(124124230016156549/125000000000000000),(95840353465577517/250000000000000000),(249078231103170019/1000000000000000000),(70029924770241541/500000000000000000)⟩
theorem valid777 : certificate777.Valid := by decide +kernel
theorem sound777 : certificate777.Sound := rat_cut_bin_certificate_sound certificate777 profilesValid777 numericValid777 valid777

def retention778 : RatCutRetentionCertificate := ⟨(189/4000),(19/400),(5831347546298746888/21440941449663158427),(1749374123825193693/1000000000000000000),(17/10),(342869632641924694180890191076943912533/233249883176692492400000000000000000000),false,MergedCutProfiles.Batch130.profile5228,(fun _ => MergedCutProfiles.Batch130.profile5228)⟩
theorem profilesValid778 : retention778.ProfilesValid := by
  exact MergedCutProfiles.Batch130.valid5228
theorem numericValid778 : retention778.NumericValid := by decide +kernel
def certificate778 : RatCutBinCertificate := ⟨⟨retention778,(2138748609051754391/1000000000000000000),(26668397193078727/250000000000000000),(63647384072139359/5000000000000000),(273316494600652788773/1000000000000000000),(359873557977684141/250000000000000000)⟩,(124124230016156549/125000000000000000),(419595570898001701/1000000000000000000),(216000062696527609/1000000000000000000),(353042910078519/2500000000000000)⟩
theorem valid778 : certificate778.Valid := by decide +kernel
theorem sound778 : certificate778.Sound := rat_cut_bin_certificate_sound certificate778 profilesValid778 numericValid778 valid778

def retention779 : RatCutRetentionCertificate := ⟨(189/4000),(19/400),(9783187175625529168/21440941449663158427),(728918443287343361/125000000000000000),1,(33393106158884692241/32000000000000000000),true,MergedCutProfiles.Batch130.profile5229,![MergedCutProfiles.Batch130.profile5229,MergedCutProfiles.Batch130.profile5230,MergedCutProfiles.Batch130.profile5231,MergedCutProfiles.Batch130.profile5232,MergedCutProfiles.Batch130.profile5233,MergedCutProfiles.Batch130.profile5234,MergedCutProfiles.Batch130.profile5235,MergedCutProfiles.Batch130.profile5236,MergedCutProfiles.Batch130.profile5237,MergedCutProfiles.Batch130.profile5238,MergedCutProfiles.Batch130.profile5239,MergedCutProfiles.Batch131.profile5240,MergedCutProfiles.Batch131.profile5241,MergedCutProfiles.Batch131.profile5242,MergedCutProfiles.Batch131.profile5243,MergedCutProfiles.Batch131.profile5244]⟩
theorem profilesValid779 : retention779.ProfilesValid := by
  change ∀ j : Fin 16, (retention779.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch130.valid5229
  · exact MergedCutProfiles.Batch130.valid5230
  · exact MergedCutProfiles.Batch130.valid5231
  · exact MergedCutProfiles.Batch130.valid5232
  · exact MergedCutProfiles.Batch130.valid5233
  · exact MergedCutProfiles.Batch130.valid5234
  · exact MergedCutProfiles.Batch130.valid5235
  · exact MergedCutProfiles.Batch130.valid5236
  · exact MergedCutProfiles.Batch130.valid5237
  · exact MergedCutProfiles.Batch130.valid5238
  · exact MergedCutProfiles.Batch130.valid5239
  · exact MergedCutProfiles.Batch131.valid5240
  · exact MergedCutProfiles.Batch131.valid5241
  · exact MergedCutProfiles.Batch131.valid5242
  · exact MergedCutProfiles.Batch131.valid5243
  · exact MergedCutProfiles.Batch131.valid5244
theorem numericValid779 : retention779.NumericValid := by decide +kernel
def certificate779 : RatCutBinCertificate := ⟨⟨retention779,(2138748609051754391/1000000000000000000),(26668397193078727/250000000000000000),(63647384072139359/5000000000000000),(273316494600652788773/1000000000000000000),(1025610558259846567/1000000000000000000)⟩,(124124230016156549/125000000000000000),(96624951837761383/200000000000000000),(10338211022208351/62500000000000000),(5727087568194943/40000000000000000)⟩
theorem valid779 : certificate779.Valid := by decide +kernel
theorem sound779 : certificate779.Sound := rat_cut_bin_certificate_sound certificate779 profilesValid779 numericValid779 valid779

def certificates : List RatCutBinCertificate := [certificate768,certificate769,certificate770,certificate771,certificate772,certificate773,certificate774,certificate775,certificate776,certificate777,certificate778,certificate779]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound768,List.forall_mem_cons.mpr ⟨sound769,List.forall_mem_cons.mpr ⟨sound770,List.forall_mem_cons.mpr ⟨sound771,List.forall_mem_cons.mpr ⟨sound772,List.forall_mem_cons.mpr ⟨sound773,List.forall_mem_cons.mpr ⟨sound774,List.forall_mem_cons.mpr ⟨sound775,List.forall_mem_cons.mpr ⟨sound776,List.forall_mem_cons.mpr ⟨sound777,List.forall_mem_cons.mpr ⟨sound778,List.forall_mem_cons.mpr ⟨sound779,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch064
