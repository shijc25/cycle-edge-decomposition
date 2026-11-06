import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch042
import Cycle12.MergedCutProfiles.Batch043
import Cycle12.MergedCutProfiles.Batch044
import Cycle12.MergedCutProfiles.Batch332
import Cycle12.MergedCutProfiles.Batch333

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch179

def retention2148 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(2796324740612454870/6681711178962032593),(5387970833370115109/1000000000000000000),(11/10),(2474097160703733247345165086014134018999/2155188333348046043600000000000000000000),false,MergedCutProfiles.Batch332.profile13283,(fun _ => MergedCutProfiles.Batch332.profile13283)⟩
theorem profilesValid2148 : retention2148.ProfilesValid := by
  exact MergedCutProfiles.Batch332.valid13283
theorem numericValid2148 : retention2148.NumericValid := by decide +kernel
def certificate2148 : RatCutBinCertificate := ⟨⟨retention2148,(2262800956086418053/1000000000000000000),(36585906920747501/1000000000000000000),(9524976261342470737/1000000000000000000),(1215300036292237339909/1000000000000000000),(284602967588548949/250000000000000000)⟩,(499100604507620927/500000000000000000),(211867756284026001/1000000000000000000),(91827183758595513/200000000000000000),(201876689748574379/500000000000000000)⟩
theorem valid2148 : certificate2148.Valid := by decide +kernel
theorem sound2148 : certificate2148.Sound := rat_cut_bin_certificate_sound certificate2148 profilesValid2148 numericValid2148 valid2148

def retention2149 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(62922295855436990025/126952512400278619267),(5313017007163664253/100000000000000000),1,(23741376545050376678356313666007059039/23613408920727396680000000000000000000),false,MergedCutProfiles.Batch332.profile13284,(fun _ => MergedCutProfiles.Batch332.profile13284)⟩
theorem profilesValid2149 : retention2149.ProfilesValid := by
  exact MergedCutProfiles.Batch332.valid13284
theorem numericValid2149 : retention2149.NumericValid := by decide +kernel
def certificate2149 : RatCutBinCertificate := ⟨⟨retention2149,(2262800956086418053/1000000000000000000),(36585906920747501/1000000000000000000),(9524976261342470737/1000000000000000000),(1215300036292237339909/1000000000000000000),(199345548415490547/200000000000000000)⟩,(499100604507620927/500000000000000000),(241984604739036741/1000000000000000000),(207281956413080963/500000000000000000),(404862307482244331/1000000000000000000)⟩
theorem valid2149 : certificate2149.Valid := by decide +kernel
theorem sound2149 : certificate2149.Sound := rat_cut_bin_certificate_sound certificate2149 profilesValid2149 numericValid2149 valid2149

def retention2150 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(1/2),(2516891834217479601/40000000000000000),1,(251058148005896877525813108727881055259/251689183421747960100000000000000000000),false,MergedCutProfiles.Batch042.profile1701,(fun _ => MergedCutProfiles.Batch042.profile1701)⟩
theorem profilesValid2150 : retention2150.ProfilesValid := by
  exact MergedCutProfiles.Batch042.valid1701
theorem numericValid2150 : retention2150.NumericValid := by decide +kernel
def certificate2150 : RatCutBinCertificate := ⟨⟨retention2150,(2262800956086418053/1000000000000000000),(36585906920747501/1000000000000000000),(9524976261342470737/1000000000000000000),(1215300036292237339909/1000000000000000000),(61800078987769451/62500000000000000)⟩,(499100604507620927/500000000000000000),(6098110346539217/25000000000000000),(411824306640656911/1000000000000000000),(200092848167533963/500000000000000000)⟩
theorem valid2150 : certificate2150.Valid := by decide +kernel
theorem sound2150 : certificate2150.Sound := rat_cut_bin_certificate_sound certificate2150 profilesValid2150 numericValid2150 valid2150

def retention2151 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(696992927718115081/118033013126607082996),(6900920076416981/10000000000000000),(77/20),(9158001145444783919/4000000000000000000),true,MergedCutProfiles.Batch332.profile13285,![MergedCutProfiles.Batch332.profile13285,MergedCutProfiles.Batch332.profile13286,MergedCutProfiles.Batch043.profile1749,MergedCutProfiles.Batch332.profile13287,MergedCutProfiles.Batch332.profile13288,MergedCutProfiles.Batch043.profile1750,MergedCutProfiles.Batch332.profile13289,MergedCutProfiles.Batch332.profile13290,MergedCutProfiles.Batch043.profile1751,MergedCutProfiles.Batch043.profile1723,MergedCutProfiles.Batch332.profile13291,MergedCutProfiles.Batch043.profile1752,MergedCutProfiles.Batch332.profile13292,MergedCutProfiles.Batch332.profile13293,MergedCutProfiles.Batch043.profile1725,MergedCutProfiles.Batch332.profile13294]⟩
theorem profilesValid2151 : retention2151.ProfilesValid := by
  change ∀ j : Fin 16, (retention2151.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch332.valid13285
  · exact MergedCutProfiles.Batch332.valid13286
  · exact MergedCutProfiles.Batch043.valid1749
  · exact MergedCutProfiles.Batch332.valid13287
  · exact MergedCutProfiles.Batch332.valid13288
  · exact MergedCutProfiles.Batch043.valid1750
  · exact MergedCutProfiles.Batch332.valid13289
  · exact MergedCutProfiles.Batch332.valid13290
  · exact MergedCutProfiles.Batch043.valid1751
  · exact MergedCutProfiles.Batch043.valid1723
  · exact MergedCutProfiles.Batch332.valid13291
  · exact MergedCutProfiles.Batch043.valid1752
  · exact MergedCutProfiles.Batch332.valid13292
  · exact MergedCutProfiles.Batch332.valid13293
  · exact MergedCutProfiles.Batch043.valid1725
  · exact MergedCutProfiles.Batch332.valid13294
theorem numericValid2151 : retention2151.NumericValid := by decide +kernel
def certificate2151 : RatCutBinCertificate := ⟨⟨retention2151,(983015305491488317/500000000000000000),(39310593322721927/1000000000000000000),(603711306359428117/62500000000000000),(143236628970677986199/125000000000000000),(2258695590925955889/1000000000000000000)⟩,(998346947772430521/1000000000000000000),(233783167812143379/500000000000000000),(17698301284246593/100000000000000000),(1326351039060053/15625000000000000)⟩
theorem valid2151 : certificate2151.Valid := by decide +kernel
theorem sound2151 : certificate2151.Sound := rat_cut_bin_certificate_sound certificate2151 profilesValid2151 numericValid2151 valid2151

def retention2152 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(230232614846477732/29508253281651770749),(696992927718115081/1000000000000000000),(77/20),(2917571035623453163969/1280000000000000000000),true,MergedCutProfiles.Batch332.profile13295,![MergedCutProfiles.Batch332.profile13295,MergedCutProfiles.Batch332.profile13296,MergedCutProfiles.Batch332.profile13287,MergedCutProfiles.Batch332.profile13297,MergedCutProfiles.Batch332.profile13298,MergedCutProfiles.Batch044.profile1765,MergedCutProfiles.Batch332.profile13299,MergedCutProfiles.Batch332.profile13300,MergedCutProfiles.Batch043.profile1738,MergedCutProfiles.Batch332.profile13301,MergedCutProfiles.Batch042.profile1710,MergedCutProfiles.Batch332.profile13302,MergedCutProfiles.Batch332.profile13303,MergedCutProfiles.Batch042.profile1712,MergedCutProfiles.Batch332.profile13304,MergedCutProfiles.Batch332.profile13305]⟩
theorem profilesValid2152 : retention2152.ProfilesValid := by
  change ∀ j : Fin 16, (retention2152.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch332.valid13295
  · exact MergedCutProfiles.Batch332.valid13296
  · exact MergedCutProfiles.Batch332.valid13287
  · exact MergedCutProfiles.Batch332.valid13297
  · exact MergedCutProfiles.Batch332.valid13298
  · exact MergedCutProfiles.Batch044.valid1765
  · exact MergedCutProfiles.Batch332.valid13299
  · exact MergedCutProfiles.Batch332.valid13300
  · exact MergedCutProfiles.Batch043.valid1738
  · exact MergedCutProfiles.Batch332.valid13301
  · exact MergedCutProfiles.Batch042.valid1710
  · exact MergedCutProfiles.Batch332.valid13302
  · exact MergedCutProfiles.Batch332.valid13303
  · exact MergedCutProfiles.Batch042.valid1712
  · exact MergedCutProfiles.Batch332.valid13304
  · exact MergedCutProfiles.Batch332.valid13305
theorem numericValid2152 : retention2152.NumericValid := by decide +kernel
def certificate2152 : RatCutBinCertificate := ⟨⟨retention2152,(983015305491488317/500000000000000000),(39310593322721927/1000000000000000000),(603711306359428117/62500000000000000),(143236628970677986199/125000000000000000),(14053423000523073/6250000000000000)⟩,(998346947772430521/1000000000000000000),(29188500102066903/62500000000000000),(177401705565647303/1000000000000000000),(42462797722976651/500000000000000000)⟩
theorem valid2152 : certificate2152.Valid := by decide +kernel
theorem sound2152 : certificate2152.Sound := rat_cut_bin_certificate_sound certificate2152 profilesValid2152 numericValid2152 valid2152

def retention2153 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(282280595750000000/29508253281651770749),(57558153711619433/62500000000000000),3,(35970799482032337873/16000000000000000000),true,MergedCutProfiles.Batch332.profile13306,![MergedCutProfiles.Batch332.profile13306,MergedCutProfiles.Batch332.profile13307,MergedCutProfiles.Batch332.profile13308,MergedCutProfiles.Batch332.profile13309,MergedCutProfiles.Batch332.profile13290,MergedCutProfiles.Batch332.profile13310,MergedCutProfiles.Batch332.profile13311,MergedCutProfiles.Batch332.profile13292,MergedCutProfiles.Batch332.profile13312,MergedCutProfiles.Batch332.profile13313,MergedCutProfiles.Batch332.profile13314,MergedCutProfiles.Batch332.profile13315,MergedCutProfiles.Batch332.profile13305,MergedCutProfiles.Batch042.profile1714,MergedCutProfiles.Batch043.profile1756,MergedCutProfiles.Batch332.profile13316]⟩
theorem profilesValid2153 : retention2153.ProfilesValid := by
  change ∀ j : Fin 16, (retention2153.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch332.valid13306
  · exact MergedCutProfiles.Batch332.valid13307
  · exact MergedCutProfiles.Batch332.valid13308
  · exact MergedCutProfiles.Batch332.valid13309
  · exact MergedCutProfiles.Batch332.valid13290
  · exact MergedCutProfiles.Batch332.valid13310
  · exact MergedCutProfiles.Batch332.valid13311
  · exact MergedCutProfiles.Batch332.valid13292
  · exact MergedCutProfiles.Batch332.valid13312
  · exact MergedCutProfiles.Batch332.valid13313
  · exact MergedCutProfiles.Batch332.valid13314
  · exact MergedCutProfiles.Batch332.valid13315
  · exact MergedCutProfiles.Batch332.valid13305
  · exact MergedCutProfiles.Batch042.valid1714
  · exact MergedCutProfiles.Batch043.valid1756
  · exact MergedCutProfiles.Batch332.valid13316
theorem numericValid2153 : retention2153.NumericValid := by decide +kernel
def certificate2153 : RatCutBinCertificate := ⟨⟨retention2153,(983015305491488317/500000000000000000),(39310593322721927/1000000000000000000),(603711306359428117/62500000000000000),(143236628970677986199/125000000000000000),(556042830182627721/250000000000000000)⟩,(998346947772430521/1000000000000000000),(203365658050698009/500000000000000000),(113685546385670957/500000000000000000),(1658145457543971/12500000000000000)⟩
theorem valid2153 : certificate2153.Valid := by decide +kernel
theorem sound2153 : certificate2153.Sound := rat_cut_bin_certificate_sound certificate2153 profilesValid2153 numericValid2153 valid2153

def retention2154 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(283736818941917012/29508253281651770749),(1129122383/1000000000),(51/20),(1119148242615618669/500000000000000000),true,MergedCutProfiles.Batch332.profile13306,![MergedCutProfiles.Batch332.profile13306,MergedCutProfiles.Batch332.profile13317,MergedCutProfiles.Batch332.profile13308,MergedCutProfiles.Batch332.profile13309,MergedCutProfiles.Batch332.profile13318,MergedCutProfiles.Batch332.profile13310,MergedCutProfiles.Batch332.profile13311,MergedCutProfiles.Batch332.profile13319,MergedCutProfiles.Batch332.profile13312,MergedCutProfiles.Batch332.profile13313,MergedCutProfiles.Batch332.profile13314,MergedCutProfiles.Batch332.profile13315,MergedCutProfiles.Batch043.profile1755,MergedCutProfiles.Batch042.profile1714,MergedCutProfiles.Batch333.profile13320,MergedCutProfiles.Batch332.profile13316]⟩
theorem profilesValid2154 : retention2154.ProfilesValid := by
  change ∀ j : Fin 16, (retention2154.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch332.valid13306
  · exact MergedCutProfiles.Batch332.valid13317
  · exact MergedCutProfiles.Batch332.valid13308
  · exact MergedCutProfiles.Batch332.valid13309
  · exact MergedCutProfiles.Batch332.valid13318
  · exact MergedCutProfiles.Batch332.valid13310
  · exact MergedCutProfiles.Batch332.valid13311
  · exact MergedCutProfiles.Batch332.valid13319
  · exact MergedCutProfiles.Batch332.valid13312
  · exact MergedCutProfiles.Batch332.valid13313
  · exact MergedCutProfiles.Batch332.valid13314
  · exact MergedCutProfiles.Batch332.valid13315
  · exact MergedCutProfiles.Batch043.valid1755
  · exact MergedCutProfiles.Batch042.valid1714
  · exact MergedCutProfiles.Batch333.valid13320
  · exact MergedCutProfiles.Batch332.valid13316
theorem numericValid2154 : retention2154.NumericValid := by decide +kernel
def certificate2154 : RatCutBinCertificate := ⟨⟨retention2154,(983015305491488317/500000000000000000),(39310593322721927/1000000000000000000),(603711306359428117/62500000000000000),(143236628970677986199/125000000000000000),(554473348904327793/250000000000000000)⟩,(998346947772430521/1000000000000000000),(370242567711799941/1000000000000000000),(32735289278883731/125000000000000000),(43650165310734251/250000000000000000)⟩
theorem valid2154 : certificate2154.Valid := by decide +kernel
theorem sound2154 : certificate2154.Sound := rat_cut_bin_certificate_sound certificate2154 profilesValid2154 numericValid2154 valid2154

def retention2155 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(1241275120780334583/118033013126607082996),(70934204735479253/62500000000000000),(51/20),(178736674640614179361/80000000000000000000),true,MergedCutProfiles.Batch333.profile13321,![MergedCutProfiles.Batch333.profile13321,MergedCutProfiles.Batch333.profile13322,MergedCutProfiles.Batch332.profile13297,MergedCutProfiles.Batch333.profile13323,MergedCutProfiles.Batch043.profile1737,MergedCutProfiles.Batch333.profile13324,MergedCutProfiles.Batch042.profile1709,MergedCutProfiles.Batch333.profile13325,MergedCutProfiles.Batch332.profile13294,MergedCutProfiles.Batch332.profile13314,MergedCutProfiles.Batch044.profile1768,MergedCutProfiles.Batch043.profile1755,MergedCutProfiles.Batch333.profile13326,MergedCutProfiles.Batch042.profile1715,MergedCutProfiles.Batch043.profile1742,MergedCutProfiles.Batch333.profile13327]⟩
theorem profilesValid2155 : retention2155.ProfilesValid := by
  change ∀ j : Fin 16, (retention2155.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch333.valid13321
  · exact MergedCutProfiles.Batch333.valid13322
  · exact MergedCutProfiles.Batch332.valid13297
  · exact MergedCutProfiles.Batch333.valid13323
  · exact MergedCutProfiles.Batch043.valid1737
  · exact MergedCutProfiles.Batch333.valid13324
  · exact MergedCutProfiles.Batch042.valid1709
  · exact MergedCutProfiles.Batch333.valid13325
  · exact MergedCutProfiles.Batch332.valid13294
  · exact MergedCutProfiles.Batch332.valid13314
  · exact MergedCutProfiles.Batch044.valid1768
  · exact MergedCutProfiles.Batch043.valid1755
  · exact MergedCutProfiles.Batch333.valid13326
  · exact MergedCutProfiles.Batch042.valid1715
  · exact MergedCutProfiles.Batch043.valid1742
  · exact MergedCutProfiles.Batch333.valid13327
theorem numericValid2155 : retention2155.NumericValid := by decide +kernel
def certificate2155 : RatCutBinCertificate := ⟨⟨retention2155,(983015305491488317/500000000000000000),(39310593322721927/1000000000000000000),(603711306359428117/62500000000000000),(143236628970677986199/125000000000000000),(138362834040086591/62500000000000000)⟩,(998346947772430521/1000000000000000000),(92517540036591609/250000000000000000),(13102682083188083/50000000000000000),(87337646505663753/500000000000000000)⟩
theorem valid2155 : certificate2155.Valid := by decide +kernel
theorem sound2155 : certificate2155.Sound := rat_cut_bin_certificate_sound certificate2155 profilesValid2155 numericValid2155 valid2155

def retention2156 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(3859265543724573663/118033013126607082996),(1241275120780334583/1000000000000000000),(12/5),(680459673781713137083/320000000000000000000),true,MergedCutProfiles.Batch333.profile13328,![MergedCutProfiles.Batch333.profile13328,MergedCutProfiles.Batch332.profile13291,MergedCutProfiles.Batch042.profile1711,MergedCutProfiles.Batch333.profile13329,MergedCutProfiles.Batch333.profile13330,MergedCutProfiles.Batch042.profile1719,MergedCutProfiles.Batch043.profile1745,MergedCutProfiles.Batch333.profile13331,MergedCutProfiles.Batch333.profile13332,MergedCutProfiles.Batch333.profile13333,MergedCutProfiles.Batch333.profile13334,MergedCutProfiles.Batch333.profile13335,MergedCutProfiles.Batch333.profile13336,MergedCutProfiles.Batch333.profile13337,MergedCutProfiles.Batch333.profile13338,MergedCutProfiles.Batch333.profile13339]⟩
theorem profilesValid2156 : retention2156.ProfilesValid := by
  change ∀ j : Fin 16, (retention2156.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch333.valid13328
  · exact MergedCutProfiles.Batch332.valid13291
  · exact MergedCutProfiles.Batch042.valid1711
  · exact MergedCutProfiles.Batch333.valid13329
  · exact MergedCutProfiles.Batch333.valid13330
  · exact MergedCutProfiles.Batch042.valid1719
  · exact MergedCutProfiles.Batch043.valid1745
  · exact MergedCutProfiles.Batch333.valid13331
  · exact MergedCutProfiles.Batch333.valid13332
  · exact MergedCutProfiles.Batch333.valid13333
  · exact MergedCutProfiles.Batch333.valid13334
  · exact MergedCutProfiles.Batch333.valid13335
  · exact MergedCutProfiles.Batch333.valid13336
  · exact MergedCutProfiles.Batch333.valid13337
  · exact MergedCutProfiles.Batch333.valid13338
  · exact MergedCutProfiles.Batch333.valid13339
theorem numericValid2156 : retention2156.NumericValid := by decide +kernel
def certificate2156 : RatCutBinCertificate := ⟨⟨retention2156,(983015305491488317/500000000000000000),(39310593322721927/1000000000000000000),(603711306359428117/62500000000000000),(143236628970677986199/125000000000000000),(2107233580360525259/1000000000000000000)⟩,(998346947772430521/1000000000000000000),(373851869151004229/1000000000000000000),(64578495965780359/250000000000000000),(21855456229985369/125000000000000000)⟩
theorem valid2156 : certificate2156.Valid := by decide +kernel
theorem sound2156 : certificate2156.Sound := rat_cut_bin_certificate_sound certificate2156 profilesValid2156 numericValid2156 valid2156

def retention2157 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(40800947489680775479/118033013126607082996),(3859265543724573663/1000000000000000000),(5/4),(323345753682220089503320875529976562239/246992994798372714432000000000000000000),false,MergedCutProfiles.Batch333.profile13340,(fun _ => MergedCutProfiles.Batch333.profile13340)⟩
theorem profilesValid2157 : retention2157.ProfilesValid := by
  exact MergedCutProfiles.Batch333.valid13340
theorem numericValid2157 : retention2157.NumericValid := by decide +kernel
def certificate2157 : RatCutBinCertificate := ⟨⟨retention2157,(983015305491488317/500000000000000000),(39310593322721927/1000000000000000000),(603711306359428117/62500000000000000),(143236628970677986199/125000000000000000),(1299127782093181151/1000000000000000000)⟩,(998346947772430521/1000000000000000000),(107749547584315059/250000000000000000),(206251070376496543/1000000000000000000),(88021468904807999/500000000000000000)⟩
theorem valid2157 : certificate2157.Valid := by decide +kernel
theorem sound2157 : certificate2157.Sound := rat_cut_bin_certificate_sound certificate2157 profilesValid2157 numericValid2157 valid2157

def retention2158 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(14594180502298628325/29508253281651770749),(40800947489680775479/1000000000000000000),1,(164193320460436489250603556052405022883/163203789958723101916000000000000000000),false,MergedCutProfiles.Batch333.profile13341,(fun _ => MergedCutProfiles.Batch333.profile13341)⟩
theorem profilesValid2158 : retention2158.ProfilesValid := by
  exact MergedCutProfiles.Batch333.valid13341
theorem numericValid2158 : retention2158.NumericValid := by decide +kernel
def certificate2158 : RatCutBinCertificate := ⟨⟨retention2158,(983015305491488317/500000000000000000),(39310593322721927/1000000000000000000),(603711306359428117/62500000000000000),(143236628970677986199/125000000000000000),(998062035829893/1000000000000000)⟩,(998346947772430521/1000000000000000000),(46299702464239149/100000000000000000),(90239520710419763/500000000000000000),(175533747816057973/1000000000000000000)⟩
theorem valid2158 : certificate2158.Valid := by decide +kernel
theorem sound2158 : certificate2158.Sound := rat_cut_bin_certificate_sound certificate2158 profilesValid2158 numericValid2158 valid2158

def retention2159 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(58960489229286458433/118033013126607082996),(583767220091945133/10000000000000000),1,(233069589508595683584926112555141965519/233506888036778053200000000000000000000),false,MergedCutProfiles.Batch333.profile13342,(fun _ => MergedCutProfiles.Batch333.profile13342)⟩
theorem profilesValid2159 : retention2159.ProfilesValid := by
  exact MergedCutProfiles.Batch333.valid13342
theorem numericValid2159 : retention2159.NumericValid := by decide +kernel
def certificate2159 : RatCutBinCertificate := ⟨⟨retention2159,(983015305491488317/500000000000000000),(39310593322721927/1000000000000000000),(603711306359428117/62500000000000000),(143236628970677986199/125000000000000000),(990126135424256181/1000000000000000000)⟩,(998346947772430521/1000000000000000000),(463600482061781859/1000000000000000000),(180014755015591699/1000000000000000000),(87486127595039559/500000000000000000)⟩
theorem valid2159 : certificate2159.Valid := by decide +kernel
theorem sound2159 : certificate2159.Sound := rat_cut_bin_certificate_sound certificate2159 profilesValid2159 numericValid2159 valid2159

def certificates : List RatCutBinCertificate := [certificate2148,certificate2149,certificate2150,certificate2151,certificate2152,certificate2153,certificate2154,certificate2155,certificate2156,certificate2157,certificate2158,certificate2159]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2148,List.forall_mem_cons.mpr ⟨sound2149,List.forall_mem_cons.mpr ⟨sound2150,List.forall_mem_cons.mpr ⟨sound2151,List.forall_mem_cons.mpr ⟨sound2152,List.forall_mem_cons.mpr ⟨sound2153,List.forall_mem_cons.mpr ⟨sound2154,List.forall_mem_cons.mpr ⟨sound2155,List.forall_mem_cons.mpr ⟨sound2156,List.forall_mem_cons.mpr ⟨sound2157,List.forall_mem_cons.mpr ⟨sound2158,List.forall_mem_cons.mpr ⟨sound2159,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch179
