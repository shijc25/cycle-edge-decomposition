import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch320
import Cycle12.MergedCutProfiles.Batch456
import Cycle12.MergedCutProfiles.Batch580
import Cycle12.MergedCutProfiles.Batch581
import Cycle12.MergedCutProfiles.Batch582
import Cycle12.MergedCutProfiles.Batch583

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch318

def retention3816 : RatCutRetentionCertificate := ⟨(19/1000),(39/2000),(32000000000000000000/1470698876854605526097),(40020737941417039/20000000000000000),(37/20),(13913771789984718877/6400000000000000000),true,MergedCutProfiles.Batch580.profile23238,![MergedCutProfiles.Batch580.profile23238,MergedCutProfiles.Batch580.profile23239,MergedCutProfiles.Batch581.profile23240,MergedCutProfiles.Batch581.profile23241,MergedCutProfiles.Batch581.profile23242,MergedCutProfiles.Batch581.profile23243,MergedCutProfiles.Batch581.profile23244,MergedCutProfiles.Batch581.profile23245,MergedCutProfiles.Batch581.profile23246,MergedCutProfiles.Batch581.profile23247,MergedCutProfiles.Batch581.profile23248,MergedCutProfiles.Batch581.profile23249,MergedCutProfiles.Batch581.profile23250,MergedCutProfiles.Batch581.profile23251,MergedCutProfiles.Batch581.profile23252,MergedCutProfiles.Batch581.profile23253]⟩
theorem profilesValid3816 : retention3816.ProfilesValid := by
  change ∀ j : Fin 16, (retention3816.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch580.valid23238
  · exact MergedCutProfiles.Batch580.valid23239
  · exact MergedCutProfiles.Batch581.valid23240
  · exact MergedCutProfiles.Batch581.valid23241
  · exact MergedCutProfiles.Batch581.valid23242
  · exact MergedCutProfiles.Batch581.valid23243
  · exact MergedCutProfiles.Batch581.valid23244
  · exact MergedCutProfiles.Batch581.valid23245
  · exact MergedCutProfiles.Batch581.valid23246
  · exact MergedCutProfiles.Batch581.valid23247
  · exact MergedCutProfiles.Batch581.valid23248
  · exact MergedCutProfiles.Batch581.valid23249
  · exact MergedCutProfiles.Batch581.valid23250
  · exact MergedCutProfiles.Batch581.valid23251
  · exact MergedCutProfiles.Batch581.valid23252
  · exact MergedCutProfiles.Batch581.valid23253
theorem numericValid3816 : retention3816.NumericValid := by decide +kernel
def certificate3816 : RatCutBinCertificate := ⟨⟨retention3816,(1812427699421595639/1000000000000000000),(3988876601543201/250000000000000000),(8434505002173129721/1000000000000000000),(24868242594516611726429/1000000000000000000),(1083842003058494991/500000000000000000)⟩,(999928220709849401/1000000000000000000),(4338094801437243/12500000000000000),(285667937399832317/1000000000000000000),(63557144184186149/250000000000000000)⟩
theorem valid3816 : certificate3816.Valid := by decide +kernel
theorem sound3816 : certificate3816.Sound := rat_cut_bin_certificate_sound certificate3816 profilesValid3816 numericValid3816 valid3816

def retention3817 : RatCutRetentionCertificate := ⟨(19/1000),(39/2000),(1/2),64,1,(63842822702664759229062174174466583311/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch581.profile23254,(fun _ => MergedCutProfiles.Batch581.profile23254)⟩
theorem profilesValid3817 : retention3817.ProfilesValid := by
  exact MergedCutProfiles.Batch581.valid23254
theorem numericValid3817 : retention3817.NumericValid := by decide +kernel
def certificate3817 : RatCutBinCertificate := ⟨⟨retention3817,(1812427699421595639/1000000000000000000),(3988876601543201/250000000000000000),(8434505002173129721/1000000000000000000),(24868242594516611726429/1000000000000000000),(198823109050433361/200000000000000000)⟩,(999928220709849401/1000000000000000000),(29690885094084457/62500000000000000),(21418792072464967/125000000000000000),(167724426369860521/1000000000000000000)⟩
theorem valid3817 : certificate3817.Valid := by decide +kernel
theorem sound3817 : certificate3817.Sound := rat_cut_bin_certificate_sound certificate3817 profilesValid3817 numericValid3817 valid3817

def retention3818 : RatCutRetentionCertificate := ⟨(19/1000),(39/2000),(32000000000000000000/1470698876854605526097),(9291593723557627199/500000000000000000),1,(158577990934952660963937643815171563991/74332749788461017592000000000000000000),false,MergedCutProfiles.Batch581.profile23255,(fun _ => MergedCutProfiles.Batch581.profile23255)⟩
theorem profilesValid3818 : retention3818.ProfilesValid := by
  exact MergedCutProfiles.Batch581.valid23255
theorem numericValid3818 : retention3818.NumericValid := by decide +kernel
def certificate3818 : RatCutBinCertificate := ⟨⟨retention3818,(1784811234421595639/1000000000000000000),(3988876601543201/250000000000000000),(8434505002173129721/1000000000000000000),(24868242594516611726429/1000000000000000000),(2129976630903532683/1000000000000000000)⟩,(499964657216023217/500000000000000000),(1288382126350751/40000000000000000),(209464003493829029/250000000000000000),(200122743947062531/125000000000000000)⟩
theorem valid3818 : certificate3818.Valid := by decide +kernel
theorem sound3818 : certificate3818.Sound := rat_cut_bin_certificate_sound certificate3818 profilesValid3818 numericValid3818 valid3818

def retention3819 : RatCutRetentionCertificate := ⟨(19/1000),(39/2000),(1/2),64,1,(63842822702664759229062174174466583311/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch581.profile23254,(fun _ => MergedCutProfiles.Batch581.profile23254)⟩
theorem profilesValid3819 : retention3819.ProfilesValid := by
  exact MergedCutProfiles.Batch581.valid23254
theorem numericValid3819 : retention3819.NumericValid := by decide +kernel
def certificate3819 : RatCutBinCertificate := ⟨⟨retention3819,(1784811234421595639/1000000000000000000),(3988876601543201/250000000000000000),(8434505002173129721/1000000000000000000),(24868242594516611726429/1000000000000000000),(124270973395825457/125000000000000000)⟩,(499964657216023217/500000000000000000),(34504032621872487/500000000000000000),(369621697847785811/500000000000000000),(144727729981800669/200000000000000000)⟩
theorem valid3819 : certificate3819.Valid := by decide +kernel
theorem sound3819 : certificate3819.Sound := rat_cut_bin_certificate_sound certificate3819 profilesValid3819 numericValid3819 valid3819

def retention3820 : RatCutRetentionCertificate := ⟨(39/2000),(1/50),(571299157837811295/2789512166984465611873),(140010576864476839/250000000000000000),4,(244010445551188301594464272877207251/112008461491581471200000000000000000),true,MergedCutProfiles.Batch581.profile23256,![MergedCutProfiles.Batch581.profile23256,MergedCutProfiles.Batch581.profile23257,MergedCutProfiles.Batch581.profile23258,MergedCutProfiles.Batch581.profile23259,MergedCutProfiles.Batch581.profile23260,MergedCutProfiles.Batch581.profile23261,MergedCutProfiles.Batch581.profile23262,MergedCutProfiles.Batch581.profile23263,MergedCutProfiles.Batch581.profile23264,MergedCutProfiles.Batch581.profile23265,MergedCutProfiles.Batch581.profile23266,MergedCutProfiles.Batch581.profile23267,MergedCutProfiles.Batch581.profile23268,MergedCutProfiles.Batch581.profile23269,MergedCutProfiles.Batch581.profile23270,MergedCutProfiles.Batch581.profile23271]⟩
theorem profilesValid3820 : retention3820.ProfilesValid := by
  change ∀ j : Fin 16, (retention3820.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch581.valid23256
  · exact MergedCutProfiles.Batch581.valid23257
  · exact MergedCutProfiles.Batch581.valid23258
  · exact MergedCutProfiles.Batch581.valid23259
  · exact MergedCutProfiles.Batch581.valid23260
  · exact MergedCutProfiles.Batch581.valid23261
  · exact MergedCutProfiles.Batch581.valid23262
  · exact MergedCutProfiles.Batch581.valid23263
  · exact MergedCutProfiles.Batch581.valid23264
  · exact MergedCutProfiles.Batch581.valid23265
  · exact MergedCutProfiles.Batch581.valid23266
  · exact MergedCutProfiles.Batch581.valid23267
  · exact MergedCutProfiles.Batch581.valid23268
  · exact MergedCutProfiles.Batch581.valid23269
  · exact MergedCutProfiles.Batch581.valid23270
  · exact MergedCutProfiles.Batch581.valid23271
theorem numericValid3820 : retention3820.NumericValid := by decide +kernel
def certificate3820 : RatCutBinCertificate := ⟨⟨retention3820,(1813812703620473571/1000000000000000000),(16814618099358171/1000000000000000000),(530621290649660437/62500000000000000),(23739285423009214710321/1000000000000000000),(2164130831692165749/1000000000000000000)⟩,(999924813466456109/1000000000000000000),(346518028262032489/500000000000000000),(1321153979835991/25000000000000000),(184219626645283/8000000000000000)⟩
theorem valid3820 : certificate3820.Valid := by decide +kernel
theorem sound3820 : certificate3820.Sound := rat_cut_bin_certificate_sound certificate3820 profilesValid3820 numericValid3820 valid3820

def retention3821 : RatCutRetentionCertificate := ⟨(39/2000),(1/50),(1233712672000000000/2789512166984465611873),(114259831567562259/200000000000000000),4,(5031393637562324882577225293378034119/2285196631351245180000000000000000000),true,MergedCutProfiles.Batch581.profile23257,![MergedCutProfiles.Batch581.profile23257,MergedCutProfiles.Batch581.profile23272,MergedCutProfiles.Batch581.profile23273,MergedCutProfiles.Batch581.profile23264,MergedCutProfiles.Batch581.profile23266,MergedCutProfiles.Batch581.profile23268,MergedCutProfiles.Batch581.profile23270,MergedCutProfiles.Batch581.profile23274,MergedCutProfiles.Batch581.profile23275,MergedCutProfiles.Batch581.profile23276,MergedCutProfiles.Batch581.profile23277,MergedCutProfiles.Batch581.profile23278,MergedCutProfiles.Batch581.profile23279,MergedCutProfiles.Batch582.profile23280,MergedCutProfiles.Batch582.profile23281,MergedCutProfiles.Batch582.profile23282]⟩
theorem profilesValid3821 : retention3821.ProfilesValid := by
  change ∀ j : Fin 16, (retention3821.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch581.valid23257
  · exact MergedCutProfiles.Batch581.valid23272
  · exact MergedCutProfiles.Batch581.valid23273
  · exact MergedCutProfiles.Batch581.valid23264
  · exact MergedCutProfiles.Batch581.valid23266
  · exact MergedCutProfiles.Batch581.valid23268
  · exact MergedCutProfiles.Batch581.valid23270
  · exact MergedCutProfiles.Batch581.valid23274
  · exact MergedCutProfiles.Batch581.valid23275
  · exact MergedCutProfiles.Batch581.valid23276
  · exact MergedCutProfiles.Batch581.valid23277
  · exact MergedCutProfiles.Batch581.valid23278
  · exact MergedCutProfiles.Batch581.valid23279
  · exact MergedCutProfiles.Batch582.valid23280
  · exact MergedCutProfiles.Batch582.valid23281
  · exact MergedCutProfiles.Batch582.valid23282
theorem numericValid3821 : retention3821.NumericValid := by decide +kernel
def certificate3821 : RatCutBinCertificate := ⟨⟨retention3821,(1813812703620473571/1000000000000000000),(16814618099358171/1000000000000000000),(530621290649660437/62500000000000000),(23739285423009214710321/1000000000000000000),(437472814850264819/200000000000000000)⟩,(999924813466456109/1000000000000000000),(676352172113449729/1000000000000000000),(59166145219015227/1000000000000000000),(6526189748301083/250000000000000000)⟩
theorem valid3821 : certificate3821.Valid := by decide +kernel
theorem sound3821 : certificate3821.Sound := rat_cut_bin_certificate_sound certificate3821 profilesValid3821 numericValid3821 valid3821

def retention3822 : RatCutRetentionCertificate := ⟨(39/2000),(1/50),(2370391246976389676/2789512166984465611873),(38553521/31250000),(13/5),(2913737582964704708920843885902949391/1233712672000000000000000000000000000),true,MergedCutProfiles.Batch581.profile23259,![MergedCutProfiles.Batch581.profile23259,MergedCutProfiles.Batch581.profile23264,MergedCutProfiles.Batch581.profile23267,MergedCutProfiles.Batch581.profile23271,MergedCutProfiles.Batch582.profile23283,MergedCutProfiles.Batch582.profile23284,MergedCutProfiles.Batch582.profile23285,MergedCutProfiles.Batch582.profile23286,MergedCutProfiles.Batch582.profile23287,MergedCutProfiles.Batch582.profile23288,MergedCutProfiles.Batch582.profile23289,MergedCutProfiles.Batch582.profile23290,MergedCutProfiles.Batch582.profile23291,MergedCutProfiles.Batch582.profile23292,MergedCutProfiles.Batch582.profile23293,MergedCutProfiles.Batch582.profile23294]⟩
theorem profilesValid3822 : retention3822.ProfilesValid := by
  change ∀ j : Fin 16, (retention3822.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch581.valid23259
  · exact MergedCutProfiles.Batch581.valid23264
  · exact MergedCutProfiles.Batch581.valid23267
  · exact MergedCutProfiles.Batch581.valid23271
  · exact MergedCutProfiles.Batch582.valid23283
  · exact MergedCutProfiles.Batch582.valid23284
  · exact MergedCutProfiles.Batch582.valid23285
  · exact MergedCutProfiles.Batch582.valid23286
  · exact MergedCutProfiles.Batch582.valid23287
  · exact MergedCutProfiles.Batch582.valid23288
  · exact MergedCutProfiles.Batch582.valid23289
  · exact MergedCutProfiles.Batch582.valid23290
  · exact MergedCutProfiles.Batch582.valid23291
  · exact MergedCutProfiles.Batch582.valid23292
  · exact MergedCutProfiles.Batch582.valid23293
  · exact MergedCutProfiles.Batch582.valid23294
theorem numericValid3822 : retention3822.NumericValid := by decide +kernel
def certificate3822 : RatCutBinCertificate := ⟨⟨retention3822,(1813812703620473571/1000000000000000000),(16814618099358171/1000000000000000000),(530621290649660437/62500000000000000),(23739285423009214710321/1000000000000000000),(2352423490799600051/1000000000000000000)⟩,(999924813466456109/1000000000000000000),(397332631293014517/1000000000000000000),(58983812202923941/250000000000000000),(166489380714331151/1000000000000000000)⟩
theorem valid3822 : certificate3822.Valid := by decide +kernel
theorem sound3822 : certificate3822.Sound := rat_cut_bin_certificate_sound certificate3822 profilesValid3822 numericValid3822 valid3822

def retention3823 : RatCutRetentionCertificate := ⟨(39/2000),(1/50),(64000000000000000000/2789512166984465611873),(592597811744097419/250000000000000000),(17/10),(693571276957466306159/320000000000000000000),true,MergedCutProfiles.Batch582.profile23295,![MergedCutProfiles.Batch582.profile23295,MergedCutProfiles.Batch582.profile23296,MergedCutProfiles.Batch582.profile23297,MergedCutProfiles.Batch582.profile23298,MergedCutProfiles.Batch582.profile23299,MergedCutProfiles.Batch582.profile23300,MergedCutProfiles.Batch582.profile23301,MergedCutProfiles.Batch582.profile23302,MergedCutProfiles.Batch582.profile23303,MergedCutProfiles.Batch582.profile23304,MergedCutProfiles.Batch582.profile23305,MergedCutProfiles.Batch582.profile23306,MergedCutProfiles.Batch582.profile23307,MergedCutProfiles.Batch582.profile23308,MergedCutProfiles.Batch582.profile23309,MergedCutProfiles.Batch582.profile23310]⟩
theorem profilesValid3823 : retention3823.ProfilesValid := by
  change ∀ j : Fin 16, (retention3823.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch582.valid23295
  · exact MergedCutProfiles.Batch582.valid23296
  · exact MergedCutProfiles.Batch582.valid23297
  · exact MergedCutProfiles.Batch582.valid23298
  · exact MergedCutProfiles.Batch582.valid23299
  · exact MergedCutProfiles.Batch582.valid23300
  · exact MergedCutProfiles.Batch582.valid23301
  · exact MergedCutProfiles.Batch582.valid23302
  · exact MergedCutProfiles.Batch582.valid23303
  · exact MergedCutProfiles.Batch582.valid23304
  · exact MergedCutProfiles.Batch582.valid23305
  · exact MergedCutProfiles.Batch582.valid23306
  · exact MergedCutProfiles.Batch582.valid23307
  · exact MergedCutProfiles.Batch582.valid23308
  · exact MergedCutProfiles.Batch582.valid23309
  · exact MergedCutProfiles.Batch582.valid23310
theorem numericValid3823 : retention3823.NumericValid := by decide +kernel
def certificate3823 : RatCutBinCertificate := ⟨⟨retention3823,(1813812703620473571/1000000000000000000),(16814618099358171/1000000000000000000),(530621290649660437/62500000000000000),(23739285423009214710321/1000000000000000000),(270162912319847999/125000000000000000)⟩,(999924813466456109/1000000000000000000),(82057835770806677/250000000000000000),(30609624195181857/100000000000000000),(73949995313444119/250000000000000000)⟩
theorem valid3823 : certificate3823.Valid := by decide +kernel
theorem sound3823 : certificate3823.Sound := rat_cut_bin_certificate_sound certificate3823 profilesValid3823 numericValid3823 valid3823

def retention3824 : RatCutRetentionCertificate := ⟨(39/2000),(1/50),(1/2),64,1,(255371464603724458416314582080588160479/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch582.profile23311,(fun _ => MergedCutProfiles.Batch582.profile23311)⟩
theorem profilesValid3824 : retention3824.ProfilesValid := by
  exact MergedCutProfiles.Batch582.valid23311
theorem numericValid3824 : retention3824.NumericValid := by decide +kernel
def certificate3824 : RatCutBinCertificate := ⟨⟨retention3824,(1813812703620473571/1000000000000000000),(16814618099358171/1000000000000000000),(530621290649660437/62500000000000000),(23739285423009214710321/1000000000000000000),(993952465415678531/1000000000000000000)⟩,(999924813466456109/1000000000000000000),(238414196008889497/500000000000000000),(6801321842012447/40000000000000000),(5200236042063647/31250000000000000)⟩
theorem valid3824 : certificate3824.Valid := by decide +kernel
theorem sound3824 : certificate3824.Sound := rat_cut_bin_certificate_sound certificate3824 profilesValid3824 numericValid3824 valid3824

def retention3825 : RatCutRetentionCertificate := ⟨(39/2000),(1/50),(64000000000000000000/2789512166984465611873),(4689831584664203259/250000000000000000),1,(39920367014942580322451100552502552367/18759326338656813036000000000000000000),false,MergedCutProfiles.Batch582.profile23312,(fun _ => MergedCutProfiles.Batch582.profile23312)⟩
theorem profilesValid3825 : retention3825.ProfilesValid := by
  exact MergedCutProfiles.Batch582.valid23312
theorem numericValid3825 : retention3825.NumericValid := by decide +kernel
def certificate3825 : RatCutBinCertificate := ⟨⟨retention3825,(1785193768620473571/1000000000000000000),(16814618099358171/1000000000000000000),(530621290649660437/62500000000000000),(23739285423009214710321/1000000000000000000),(1062246056113134789/500000000000000000)⟩,(999925999785800919/1000000000000000000),(3208801069097277/100000000000000000),(16764134650210717/20000000000000000),(4998395178736237/3125000000000000)⟩
theorem valid3825 : certificate3825.Valid := by decide +kernel
theorem sound3825 : certificate3825.Sound := rat_cut_bin_certificate_sound certificate3825 profilesValid3825 numericValid3825 valid3825

def retention3826 : RatCutRetentionCertificate := ⟨(39/2000),(1/50),(1/2),64,1,(255371464603724458416314582080588160479/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch582.profile23311,(fun _ => MergedCutProfiles.Batch582.profile23311)⟩
theorem profilesValid3826 : retention3826.ProfilesValid := by
  exact MergedCutProfiles.Batch582.valid23311
theorem numericValid3826 : retention3826.NumericValid := by decide +kernel
def certificate3826 : RatCutBinCertificate := ⟨⟨retention3826,(1785193768620473571/1000000000000000000),(16814618099358171/1000000000000000000),(530621290649660437/62500000000000000),(23739285423009214710321/1000000000000000000),(99400914619680257/100000000000000000)⟩,(999925999785800919/1000000000000000000),(6858158787656349/100000000000000000),(370153130172247011/500000000000000000),(724562784888245639/1000000000000000000)⟩
theorem valid3826 : certificate3826.Valid := by decide +kernel
theorem sound3826 : certificate3826.Sound := rat_cut_bin_certificate_sound certificate3826 profilesValid3826 numericValid3826 valid3826

def retention3827 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(574586604590540383/2518089658483773843340),(34855506096673471/62500000000000000),4,(18931707806187025156129217302040847/8713876524168367750000000000000000),true,MergedCutProfiles.Batch582.profile23313,![MergedCutProfiles.Batch582.profile23313,MergedCutProfiles.Batch582.profile23314,MergedCutProfiles.Batch582.profile23315,MergedCutProfiles.Batch456.profile18248,MergedCutProfiles.Batch582.profile23316,MergedCutProfiles.Batch582.profile23317,MergedCutProfiles.Batch582.profile23318,MergedCutProfiles.Batch582.profile23319,MergedCutProfiles.Batch456.profile18262,MergedCutProfiles.Batch583.profile23320,MergedCutProfiles.Batch320.profile12834,MergedCutProfiles.Batch583.profile23321,MergedCutProfiles.Batch456.profile18250,MergedCutProfiles.Batch583.profile23322,MergedCutProfiles.Batch583.profile23323,MergedCutProfiles.Batch583.profile23324]⟩
theorem profilesValid3827 : retention3827.ProfilesValid := by
  change ∀ j : Fin 16, (retention3827.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch582.valid23313
  · exact MergedCutProfiles.Batch582.valid23314
  · exact MergedCutProfiles.Batch582.valid23315
  · exact MergedCutProfiles.Batch456.valid18248
  · exact MergedCutProfiles.Batch582.valid23316
  · exact MergedCutProfiles.Batch582.valid23317
  · exact MergedCutProfiles.Batch582.valid23318
  · exact MergedCutProfiles.Batch582.valid23319
  · exact MergedCutProfiles.Batch456.valid18262
  · exact MergedCutProfiles.Batch583.valid23320
  · exact MergedCutProfiles.Batch320.valid12834
  · exact MergedCutProfiles.Batch583.valid23321
  · exact MergedCutProfiles.Batch456.valid18250
  · exact MergedCutProfiles.Batch583.valid23322
  · exact MergedCutProfiles.Batch583.valid23323
  · exact MergedCutProfiles.Batch583.valid23324
theorem numericValid3827 : retention3827.NumericValid := by decide +kernel
def certificate3827 : RatCutBinCertificate := ⟨⟨retention3827,(36270588668945551/20000000000000000),(1860584005120499/100000000000000000),(1709187668475437333/200000000000000000),(21622674815746229464277/1000000000000000000),(1078399862623211893/500000000000000000)⟩,(499958769251285331/500000000000000000),(87784245119635717/125000000000000000),(6190020480778043/125000000000000000),(10750725626093439/500000000000000000)⟩
theorem valid3827 : certificate3827.Valid := by decide +kernel
theorem sound3827 : certificate3827.Sound := rat_cut_bin_certificate_sound certificate3827 profilesValid3827 numericValid3827 valid3827

def certificates : List RatCutBinCertificate := [certificate3816,certificate3817,certificate3818,certificate3819,certificate3820,certificate3821,certificate3822,certificate3823,certificate3824,certificate3825,certificate3826,certificate3827]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3816,List.forall_mem_cons.mpr ⟨sound3817,List.forall_mem_cons.mpr ⟨sound3818,List.forall_mem_cons.mpr ⟨sound3819,List.forall_mem_cons.mpr ⟨sound3820,List.forall_mem_cons.mpr ⟨sound3821,List.forall_mem_cons.mpr ⟨sound3822,List.forall_mem_cons.mpr ⟨sound3823,List.forall_mem_cons.mpr ⟨sound3824,List.forall_mem_cons.mpr ⟨sound3825,List.forall_mem_cons.mpr ⟨sound3826,List.forall_mem_cons.mpr ⟨sound3827,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch318
