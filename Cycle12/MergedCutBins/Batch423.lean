import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch397
import Cycle12.MergedCutProfiles.Batch706
import Cycle12.MergedCutProfiles.Batch707

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch423

def retention5076 : RatCutRetentionCertificate := ⟨(57/1000),(29/500),(137543459996880459/6176421779060339075),(2793030806498795889/1000000000000000000),(7/4),(133582932609960932762201617101666752781/59584657205307645632000000000000000000),false,MergedCutProfiles.Batch706.profile28259,(fun _ => MergedCutProfiles.Batch706.profile28259)⟩
theorem profilesValid5076 : retention5076.ProfilesValid := by
  exact MergedCutProfiles.Batch706.valid28259
theorem numericValid5076 : retention5076.NumericValid := by decide +kernel
def certificate5076 : RatCutBinCertificate := ⟨⟨retention5076,(1960806098992498591/1000000000000000000),(168442616661570077/1000000000000000000),(15031611954174764881/1000000000000000000),(818199300286210727751/40000000000000000),(275431177837774981/125000000000000000)⟩,(999919643059278609/1000000000000000000),(89380508028438211/125000000000000000),(11280553140533453/250000000000000000),(45172367522198151/1000000000000000000)⟩
theorem valid5076 : certificate5076.Valid := by decide +kernel
theorem sound5076 : certificate5076.Sound := rat_cut_bin_certificate_sound certificate5076 profilesValid5076 numericValid5076 valid5076

def retention5077 : RatCutRetentionCertificate := ⟨(57/1000),(29/500),(1/40),(30122017739316820521/1000000000000000000),(21/20),(11907125764080227148568788989506267834751/5355025375878545870400000000000000000000),false,MergedCutProfiles.Batch706.profile28260,(fun _ => MergedCutProfiles.Batch706.profile28260)⟩
theorem profilesValid5077 : retention5077.ProfilesValid := by
  exact MergedCutProfiles.Batch706.valid28260
theorem numericValid5077 : retention5077.NumericValid := by decide +kernel
def certificate5077 : RatCutBinCertificate := ⟨⟨retention5077,(1960806098992498591/1000000000000000000),(168442616661570077/1000000000000000000),(15031611954174764881/1000000000000000000),(818199300286210727751/40000000000000000),(440094228877026873/200000000000000000)⟩,(999919643059278609/1000000000000000000),(335873905515788701/500000000000000000),(60982348994239017/1000000000000000000),(119848244288508787/1000000000000000000)⟩
theorem valid5077 : certificate5077.Valid := by decide +kernel
theorem sound5077 : certificate5077.Sound := rat_cut_bin_certificate_sound certificate5077 profilesValid5077 numericValid5077 valid5077

def retention5078 : RatCutRetentionCertificate := ⟨(29/500),(59/1000),(158816736538166755/324820182763990649096),(616583839239860019/1000000000000000000),4,(9268999356952141537/4000000000000000000),true,MergedCutProfiles.Batch706.profile28261,![MergedCutProfiles.Batch706.profile28261,MergedCutProfiles.Batch706.profile28262,MergedCutProfiles.Batch706.profile28263,MergedCutProfiles.Batch706.profile28264,MergedCutProfiles.Batch706.profile28265,MergedCutProfiles.Batch706.profile28266,MergedCutProfiles.Batch706.profile28267,MergedCutProfiles.Batch706.profile28268,MergedCutProfiles.Batch706.profile28269,MergedCutProfiles.Batch706.profile28270,MergedCutProfiles.Batch706.profile28271,MergedCutProfiles.Batch706.profile28272,MergedCutProfiles.Batch706.profile28273,MergedCutProfiles.Batch706.profile28274,MergedCutProfiles.Batch706.profile28275,MergedCutProfiles.Batch706.profile28276]⟩
theorem profilesValid5078 : retention5078.ProfilesValid := by
  change ∀ j : Fin 16, (retention5078.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch706.valid28261
  · exact MergedCutProfiles.Batch706.valid28262
  · exact MergedCutProfiles.Batch706.valid28263
  · exact MergedCutProfiles.Batch706.valid28264
  · exact MergedCutProfiles.Batch706.valid28265
  · exact MergedCutProfiles.Batch706.valid28266
  · exact MergedCutProfiles.Batch706.valid28267
  · exact MergedCutProfiles.Batch706.valid28268
  · exact MergedCutProfiles.Batch706.valid28269
  · exact MergedCutProfiles.Batch706.valid28270
  · exact MergedCutProfiles.Batch706.valid28271
  · exact MergedCutProfiles.Batch706.valid28272
  · exact MergedCutProfiles.Batch706.valid28273
  · exact MergedCutProfiles.Batch706.valid28274
  · exact MergedCutProfiles.Batch706.valid28275
  · exact MergedCutProfiles.Batch706.valid28276
theorem numericValid5078 : retention5078.NumericValid := by decide +kernel
def certificate5078 : RatCutBinCertificate := ⟨⟨retention5078,(9763600878038829/5000000000000000),(175338961017292427/1000000000000000000),(478212759694574073/31250000000000000),(2500426975050413791941/125000000000000000),(445550552960227879/200000000000000000)⟩,(499959411292316717/500000000000000000),(694446892806802037/1000000000000000000),(26165139168219651/500000000000000000),(1485836591394013/62500000000000000)⟩
theorem valid5078 : certificate5078.Valid := by decide +kernel
theorem sound5078 : certificate5078.Sound := rat_cut_bin_certificate_sound certificate5078 profilesValid5078 numericValid5078 valid5078

def retention5079 : RatCutRetentionCertificate := ⟨(29/500),(59/1000),(33077348593750000/40602522845498831137),(31763347307633351/50000000000000000),4,(149911880872099857379/64000000000000000000),true,MergedCutProfiles.Batch706.profile28277,![MergedCutProfiles.Batch706.profile28277,MergedCutProfiles.Batch706.profile28278,MergedCutProfiles.Batch706.profile28265,MergedCutProfiles.Batch706.profile28267,MergedCutProfiles.Batch706.profile28268,MergedCutProfiles.Batch706.profile28270,MergedCutProfiles.Batch706.profile28279,MergedCutProfiles.Batch707.profile28280,MergedCutProfiles.Batch706.profile28275,MergedCutProfiles.Batch707.profile28281,MergedCutProfiles.Batch707.profile28282,MergedCutProfiles.Batch707.profile28283,MergedCutProfiles.Batch707.profile28284,MergedCutProfiles.Batch707.profile28285,MergedCutProfiles.Batch707.profile28286,MergedCutProfiles.Batch707.profile28287]⟩
theorem profilesValid5079 : retention5079.ProfilesValid := by
  change ∀ j : Fin 16, (retention5079.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch706.valid28277
  · exact MergedCutProfiles.Batch706.valid28278
  · exact MergedCutProfiles.Batch706.valid28265
  · exact MergedCutProfiles.Batch706.valid28267
  · exact MergedCutProfiles.Batch706.valid28268
  · exact MergedCutProfiles.Batch706.valid28270
  · exact MergedCutProfiles.Batch706.valid28279
  · exact MergedCutProfiles.Batch707.valid28280
  · exact MergedCutProfiles.Batch706.valid28275
  · exact MergedCutProfiles.Batch707.valid28281
  · exact MergedCutProfiles.Batch707.valid28282
  · exact MergedCutProfiles.Batch707.valid28283
  · exact MergedCutProfiles.Batch707.valid28284
  · exact MergedCutProfiles.Batch707.valid28285
  · exact MergedCutProfiles.Batch707.valid28286
  · exact MergedCutProfiles.Batch707.valid28287
theorem numericValid5079 : retention5079.NumericValid := by decide +kernel
def certificate5079 : RatCutBinCertificate := ⟨⟨retention5079,(9763600878038829/5000000000000000),(175338961017292427/1000000000000000000),(478212759694574073/31250000000000000),(2500426975050413791941/125000000000000000),(56321901838605019/25000000000000000)⟩,(499959411292316717/500000000000000000),(168397850585931421/250000000000000000),(3765710164284491/62500000000000000),(27775067256272563/1000000000000000000)⟩
theorem valid5079 : certificate5079.Valid := by decide +kernel
theorem sound5079 : certificate5079.Sound := rat_cut_bin_certificate_sound certificate5079 profilesValid5079 numericValid5079 valid5079

def retention5080 : RatCutRetentionCertificate := ⟨(29/500),(59/1000),(1065780317731926045/1299280731055962596384),(211695031/200000000),(59/20),(2563931697340854604983207274607734399/1058475155000000000000000000000000000),true,MergedCutProfiles.Batch706.profile28277,![MergedCutProfiles.Batch706.profile28277,MergedCutProfiles.Batch706.profile28278,MergedCutProfiles.Batch706.profile28265,MergedCutProfiles.Batch706.profile28267,MergedCutProfiles.Batch706.profile28268,MergedCutProfiles.Batch706.profile28270,MergedCutProfiles.Batch706.profile28279,MergedCutProfiles.Batch707.profile28280,MergedCutProfiles.Batch706.profile28275,MergedCutProfiles.Batch707.profile28281,MergedCutProfiles.Batch707.profile28282,MergedCutProfiles.Batch707.profile28283,MergedCutProfiles.Batch707.profile28284,MergedCutProfiles.Batch707.profile28285,MergedCutProfiles.Batch707.profile28286,MergedCutProfiles.Batch707.profile28287]⟩
theorem profilesValid5080 : retention5080.ProfilesValid := by
  change ∀ j : Fin 16, (retention5080.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch706.valid28277
  · exact MergedCutProfiles.Batch706.valid28278
  · exact MergedCutProfiles.Batch706.valid28265
  · exact MergedCutProfiles.Batch706.valid28267
  · exact MergedCutProfiles.Batch706.valid28268
  · exact MergedCutProfiles.Batch706.valid28270
  · exact MergedCutProfiles.Batch706.valid28279
  · exact MergedCutProfiles.Batch707.valid28280
  · exact MergedCutProfiles.Batch706.valid28275
  · exact MergedCutProfiles.Batch707.valid28281
  · exact MergedCutProfiles.Batch707.valid28282
  · exact MergedCutProfiles.Batch707.valid28283
  · exact MergedCutProfiles.Batch707.valid28284
  · exact MergedCutProfiles.Batch707.valid28285
  · exact MergedCutProfiles.Batch707.valid28286
  · exact MergedCutProfiles.Batch707.valid28287
theorem numericValid5080 : retention5080.NumericValid := by decide +kernel
def certificate5080 : RatCutBinCertificate := ⟨⟨retention5080,(9763600878038829/5000000000000000),(175338961017292427/1000000000000000000),(478212759694574073/31250000000000000),(2500426975050413791941/125000000000000000),(235628398626663861/100000000000000000)⟩,(499959411292316717/500000000000000000),(239308439977941237/500000000000000000),(168711851058882173/1000000000000000000),(107297221536882727/1000000000000000000)⟩
theorem valid5080 : certificate5080.Valid := by decide +kernel
theorem sound5080 : certificate5080.Sound := rat_cut_bin_certificate_sound certificate5080 profilesValid5080 numericValid5080 valid5080

def retention5081 : RatCutRetentionCertificate := ⟨(29/500),(59/1000),(429569705332028447/324820182763990649096),(213156063546385209/200000000000000000),(59/20),(54906995747329200402210178290518383533/22736646778281088960000000000000000000),true,MergedCutProfiles.Batch707.profile28288,![MergedCutProfiles.Batch707.profile28288,MergedCutProfiles.Batch707.profile28289,MergedCutProfiles.Batch706.profile28268,MergedCutProfiles.Batch706.profile28271,MergedCutProfiles.Batch707.profile28280,MergedCutProfiles.Batch706.profile28276,MergedCutProfiles.Batch707.profile28290,MergedCutProfiles.Batch707.profile28284,MergedCutProfiles.Batch707.profile28291,MergedCutProfiles.Batch707.profile28287,MergedCutProfiles.Batch707.profile28292,MergedCutProfiles.Batch707.profile28293,MergedCutProfiles.Batch707.profile28294,MergedCutProfiles.Batch707.profile28295,MergedCutProfiles.Batch707.profile28296,MergedCutProfiles.Batch707.profile28297]⟩
theorem profilesValid5081 : retention5081.ProfilesValid := by
  change ∀ j : Fin 16, (retention5081.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch707.valid28288
  · exact MergedCutProfiles.Batch707.valid28289
  · exact MergedCutProfiles.Batch706.valid28268
  · exact MergedCutProfiles.Batch706.valid28271
  · exact MergedCutProfiles.Batch707.valid28280
  · exact MergedCutProfiles.Batch706.valid28276
  · exact MergedCutProfiles.Batch707.valid28290
  · exact MergedCutProfiles.Batch707.valid28284
  · exact MergedCutProfiles.Batch707.valid28291
  · exact MergedCutProfiles.Batch707.valid28287
  · exact MergedCutProfiles.Batch707.valid28292
  · exact MergedCutProfiles.Batch707.valid28293
  · exact MergedCutProfiles.Batch707.valid28294
  · exact MergedCutProfiles.Batch707.valid28295
  · exact MergedCutProfiles.Batch707.valid28296
  · exact MergedCutProfiles.Batch707.valid28297
theorem numericValid5081 : retention5081.NumericValid := by decide +kernel
def certificate5081 : RatCutBinCertificate := ⟨⟨retention5081,(9763600878038829/5000000000000000),(175338961017292427/1000000000000000000),(478212759694574073/31250000000000000),(2500426975050413791941/125000000000000000),(587226930196085931/250000000000000000)⟩,(499959411292316717/500000000000000000),(478412631355099653/1000000000000000000),(42215598865791201/250000000000000000),(6704655871481253/62500000000000000)⟩
theorem valid5081 : certificate5081.Valid := by decide +kernel
theorem sound5081 : certificate5081.Sound := rat_cut_bin_certificate_sound certificate5081 profilesValid5081 numericValid5081 valid5081

def retention5082 : RatCutRetentionCertificate := ⟨(29/500),(59/1000),(2000000000000000000/40602522845498831137),(429569705332028447/250000000000000000),(21/10),(90406931430773983581735635177285884991/42956970533202844700000000000000000000),false,MergedCutProfiles.Batch707.profile28298,(fun _ => MergedCutProfiles.Batch707.profile28298)⟩
theorem profilesValid5082 : retention5082.ProfilesValid := by
  exact MergedCutProfiles.Batch707.valid28298
theorem numericValid5082 : retention5082.NumericValid := by decide +kernel
def certificate5082 : RatCutBinCertificate := ⟨⟨retention5082,(9763600878038829/5000000000000000),(175338961017292427/1000000000000000000),(478212759694574073/31250000000000000),(2500426975050413791941/125000000000000000),(2057606901268408711/1000000000000000000)⟩,(499959411292316717/500000000000000000),(438907747299061649/1000000000000000000),(199666232561980821/1000000000000000000),(76921487081169597/500000000000000000)⟩
theorem valid5082 : certificate5082.Valid := by decide +kernel
theorem sound5082 : certificate5082.Sound := rat_cut_bin_certificate_sound certificate5082 profilesValid5082 numericValid5082 valid5082

def retention5083 : RatCutRetentionCertificate := ⟨(29/500),(59/1000),(1/2),64,1,(255405170108452556830542331084108655439/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch397.profile15891,(fun _ => MergedCutProfiles.Batch397.profile15891)⟩
theorem profilesValid5083 : retention5083.ProfilesValid := by
  exact MergedCutProfiles.Batch397.valid15891
theorem numericValid5083 : retention5083.NumericValid := by decide +kernel
def certificate5083 : RatCutBinCertificate := ⟨⟨retention5083,(9763600878038829/5000000000000000),(175338961017292427/1000000000000000000),(478212759694574073/31250000000000000),(2500426975050413791941/125000000000000000),(975302253581277147/1000000000000000000)⟩,(499959411292316717/500000000000000000),(283180779075268093/500000000000000000),(111649086878663923/1000000000000000000),(107248300701092857/1000000000000000000)⟩
theorem valid5083 : certificate5083.Valid := by decide +kernel
theorem sound5083 : certificate5083.Sound := rat_cut_bin_certificate_sound certificate5083 profilesValid5083 numericValid5083 valid5083

def retention5084 : RatCutRetentionCertificate := ⟨(29/500),(59/1000),(2000000000000000000/40602522845498831137),(44374963460000941761/1000000000000000000),1,(11574188694989325091066052561663973259/5546870432500117720125000000000000000),false,MergedCutProfiles.Batch707.profile28298,(fun _ => MergedCutProfiles.Batch707.profile28298)⟩
theorem profilesValid5084 : retention5084.ProfilesValid := by
  exact MergedCutProfiles.Batch707.valid28298
theorem numericValid5084 : retention5084.NumericValid := by decide +kernel
def certificate5084 : RatCutBinCertificate := ⟨⟨retention5084,(8634092748038829/5000000000000000),(175338961017292427/1000000000000000000),(478212759694574073/31250000000000000),(2500426975050413791941/125000000000000000),(2066830196867296341/1000000000000000000)⟩,(124991026722507611/125000000000000000),(4039636795574199/250000000000000000),(885769159484972607/1000000000000000000),(69965290448775013/40000000000000000)⟩
theorem valid5084 : certificate5084.Valid := by decide +kernel
theorem sound5084 : certificate5084.Sound := rat_cut_bin_certificate_sound certificate5084 profilesValid5084 numericValid5084 valid5084

def retention5085 : RatCutRetentionCertificate := ⟨(29/500),(59/1000),(1/2),64,1,(255405170108452556830542331084108655439/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch397.profile15891,(fun _ => MergedCutProfiles.Batch397.profile15891)⟩
theorem profilesValid5085 : retention5085.ProfilesValid := by
  exact MergedCutProfiles.Batch397.valid15891
theorem numericValid5085 : retention5085.NumericValid := by decide +kernel
def certificate5085 : RatCutBinCertificate := ⟨⟨retention5085,(8634092748038829/5000000000000000),(175338961017292427/1000000000000000000),(478212759694574073/31250000000000000),(2500426975050413791941/125000000000000000),(48894531283207881/50000000000000000)⟩,(124991026722507611/125000000000000000),(17076026897790147/500000000000000000),(416137429921502481/500000000000000000),(200391761496190043/250000000000000000)⟩
theorem valid5085 : certificate5085.Valid := by decide +kernel
theorem sound5085 : certificate5085.Sound := rat_cut_bin_certificate_sound certificate5085 profilesValid5085 numericValid5085 valid5085

def retention5086 : RatCutRetentionCertificate := ⟨(29/500),(59/1000),(755187175327827655/1299280731055962596384),(747710074582007579/1000000000000000000),4,(7320150179693815027957069283106936631/2990840298328030316000000000000000000),false,MergedCutProfiles.Batch707.profile28299,(fun _ => MergedCutProfiles.Batch707.profile28299)⟩
theorem profilesValid5086 : retention5086.ProfilesValid := by
  exact MergedCutProfiles.Batch707.valid28299
theorem numericValid5086 : retention5086.NumericValid := by decide +kernel
def certificate5086 : RatCutBinCertificate := ⟨⟨retention5086,(9847147918038829/5000000000000000),(175338961017292427/1000000000000000000),(478212759694574073/31250000000000000),(2500426975050413791941/125000000000000000),(2357260076030154271/1000000000000000000)⟩,(999918127938741009/1000000000000000000),(39440424034417183/50000000000000000),(24061123238876629/1000000000000000000),(1184437302717131/100000000000000000)⟩
theorem valid5086 : certificate5086.Valid := by decide +kernel
theorem sound5086 : certificate5086.Sound := rat_cut_bin_certificate_sound certificate5086 profilesValid5086 numericValid5086 valid5086

def retention5087 : RatCutRetentionCertificate := ⟨(29/500),(59/1000),(876748866049168013/1299280731055962596384),(151037435065565531/200000000000000000),4,(7394946281885592024290938571591739399/3020748701311310620000000000000000000),false,MergedCutProfiles.Batch707.profile28300,(fun _ => MergedCutProfiles.Batch707.profile28300)⟩
theorem profilesValid5087 : retention5087.ProfilesValid := by
  exact MergedCutProfiles.Batch707.valid28300
theorem numericValid5087 : retention5087.NumericValid := by decide +kernel
def certificate5087 : RatCutBinCertificate := ⟨⟨retention5087,(9847147918038829/5000000000000000),(175338961017292427/1000000000000000000),(478212759694574073/31250000000000000),(2500426975050413791941/125000000000000000),(589446990288869317/250000000000000000)⟩,(999918127938741009/1000000000000000000),(393484638938482661/500000000000000000),(24499586324097871/1000000000000000000),(12082164183184453/1000000000000000000)⟩
theorem valid5087 : certificate5087.Valid := by decide +kernel
theorem sound5087 : certificate5087.Sound := rat_cut_bin_certificate_sound certificate5087 profilesValid5087 numericValid5087 valid5087

def certificates : List RatCutBinCertificate := [certificate5076,certificate5077,certificate5078,certificate5079,certificate5080,certificate5081,certificate5082,certificate5083,certificate5084,certificate5085,certificate5086,certificate5087]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound5076,List.forall_mem_cons.mpr ⟨sound5077,List.forall_mem_cons.mpr ⟨sound5078,List.forall_mem_cons.mpr ⟨sound5079,List.forall_mem_cons.mpr ⟨sound5080,List.forall_mem_cons.mpr ⟨sound5081,List.forall_mem_cons.mpr ⟨sound5082,List.forall_mem_cons.mpr ⟨sound5083,List.forall_mem_cons.mpr ⟨sound5084,List.forall_mem_cons.mpr ⟨sound5085,List.forall_mem_cons.mpr ⟨sound5086,List.forall_mem_cons.mpr ⟨sound5087,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch423
