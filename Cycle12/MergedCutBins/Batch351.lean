import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch411
import Cycle12.MergedCutProfiles.Batch631
import Cycle12.MergedCutProfiles.Batch632

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch351

def retention4212 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(31606932338478831585/231023569057642875442),(1746878002356292423/1000000000000000000),(39/20),(5081166228776610100411953339858225468071/2795004803770067876800000000000000000000),false,MergedCutProfiles.Batch631.profile25252,(fun _ => MergedCutProfiles.Batch631.profile25252)⟩
theorem profilesValid4212 : retention4212.ProfilesValid := by
  exact MergedCutProfiles.Batch631.valid25252
theorem numericValid4212 : retention4212.NumericValid := by decide +kernel
def certificate4212 : RatCutBinCertificate := ⟨⟨retention4212,(2091512834683361927/1000000000000000000),(24651154762240763/125000000000000000),(3262583755059211207/200000000000000000),(3780351506350753384643/1000000000000000000),(110539981783141667/62500000000000000)⟩,(999553714358143881/1000000000000000000),(199778345302699407/500000000000000000),(1461804943430711/6250000000000000),(83721148931210897/500000000000000000)⟩
theorem valid4212 : certificate4212.Valid := by decide +kernel
theorem sound4212 : certificate4212.Sound := rat_cut_bin_certificate_sound certificate4212 profilesValid4212 numericValid4212 valid4212

def retention4213 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(32000000000000000000/115511784528821437721),(6321386467695766317/200000000000000000),1,(45965691566515241960135750305257784001/31606932338478831585000000000000000000),false,MergedCutProfiles.Batch631.profile25253,(fun _ => MergedCutProfiles.Batch631.profile25253)⟩
theorem profilesValid4213 : retention4213.ProfilesValid := by
  exact MergedCutProfiles.Batch631.valid25253
theorem numericValid4213 : retention4213.NumericValid := by decide +kernel
def certificate4213 : RatCutBinCertificate := ⟨⟨retention4213,(2091512834683361927/1000000000000000000),(24651154762240763/125000000000000000),(3262583755059211207/200000000000000000),(3780351506350753384643/1000000000000000000),(1429006809993165879/1000000000000000000)⟩,(999553714358143881/1000000000000000000),(325417927621923987/1000000000000000000),(309241720425438853/1000000000000000000),(105650133375556031/250000000000000000)⟩
theorem valid4213 : certificate4213.Valid := by decide +kernel
theorem sound4213 : certificate4213.Sound := rat_cut_bin_certificate_sound certificate4213 profilesValid4213 numericValid4213 valid4213

def retention4214 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(1/2),64,1,(63852637809594976292697184500549005751/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch411.profile16479,(fun _ => MergedCutProfiles.Batch411.profile16479)⟩
theorem profilesValid4214 : retention4214.ProfilesValid := by
  exact MergedCutProfiles.Batch411.valid16479
theorem numericValid4214 : retention4214.NumericValid := by decide +kernel
def certificate4214 : RatCutBinCertificate := ⟨⟨retention4214,(2091512834683361927/1000000000000000000),(24651154762240763/125000000000000000),(3262583755059211207/200000000000000000),(3780351506350753384643/1000000000000000000),(486206421769337067/500000000000000000)⟩,(999553714358143881/1000000000000000000),(117714704408001373/250000000000000000),(174491603447197851/1000000000000000000),(16706297784627503/100000000000000000)⟩
theorem valid4214 : certificate4214.Valid := by decide +kernel
theorem sound4214 : certificate4214.Sound := rat_cut_bin_certificate_sound certificate4214 profilesValid4214 numericValid4214 valid4214

def retention4215 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(32000000000000000000/115511784528821437721),(4818381862134559887/200000000000000000),1,(34907963552523585706849420762421170901/24091909310672799435000000000000000000),false,MergedCutProfiles.Batch631.profile25253,(fun _ => MergedCutProfiles.Batch631.profile25253)⟩
theorem profilesValid4215 : retention4215.ProfilesValid := by
  exact MergedCutProfiles.Batch631.valid25253
theorem numericValid4215 : retention4215.NumericValid := by decide +kernel
def certificate4215 : RatCutBinCertificate := ⟨⟨retention4215,(1926299656683361927/1000000000000000000),(24651154762240763/125000000000000000),(3262583755059211207/200000000000000000),(3780351506350753384643/1000000000000000000),(1425662283532793501/1000000000000000000)⟩,(999588970913235653/1000000000000000000),(35874280553634089/1000000000000000000),(82736414609158023/100000000000000000),(34786546894995821/31250000000000000)⟩
theorem valid4215 : certificate4215.Valid := by decide +kernel
theorem sound4215 : certificate4215.Sound := rat_cut_bin_certificate_sound certificate4215 profilesValid4215 numericValid4215 valid4215

def retention4216 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(1/2),64,1,(63852637809594976292697184500549005751/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch411.profile16479,(fun _ => MergedCutProfiles.Batch411.profile16479)⟩
theorem profilesValid4216 : retention4216.ProfilesValid := by
  exact MergedCutProfiles.Batch411.valid16479
theorem numericValid4216 : retention4216.NumericValid := by decide +kernel
def certificate4216 : RatCutBinCertificate := ⟨⟨retention4216,(1926299656683361927/1000000000000000000),(24651154762240763/125000000000000000),(3262583755059211207/200000000000000000),(3780351506350753384643/1000000000000000000),(974410131207631859/1000000000000000000)⟩,(999588970913235653/1000000000000000000),(26243881860507837/500000000000000000),(781727847069156631/1000000000000000000),(187497011086950221/250000000000000000)⟩
theorem valid4216 : certificate4216.Valid := by decide +kernel
theorem sound4216 : certificate4216.Sound := rat_cut_bin_certificate_sound certificate4216 profilesValid4216 numericValid4216 valid4216

def retention4217 : RatCutRetentionCertificate := ⟨(31/500),(63/1000),(157812436052370191/44471963983586701429),(390624841713787601/500000000000000000),(18/5),(1518818350346637316029/640000000000000000000),true,MergedCutProfiles.Batch631.profile25254,![MergedCutProfiles.Batch631.profile25254,MergedCutProfiles.Batch631.profile25255,MergedCutProfiles.Batch631.profile25256,MergedCutProfiles.Batch631.profile25257,MergedCutProfiles.Batch631.profile25258,MergedCutProfiles.Batch631.profile25259,MergedCutProfiles.Batch631.profile25260,MergedCutProfiles.Batch631.profile25261,MergedCutProfiles.Batch631.profile25262,MergedCutProfiles.Batch631.profile25263,MergedCutProfiles.Batch631.profile25264,MergedCutProfiles.Batch631.profile25265,MergedCutProfiles.Batch631.profile25266,MergedCutProfiles.Batch631.profile25267,MergedCutProfiles.Batch631.profile25268,MergedCutProfiles.Batch631.profile25269]⟩
theorem profilesValid4217 : retention4217.ProfilesValid := by
  change ∀ j : Fin 16, (retention4217.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch631.valid25254
  · exact MergedCutProfiles.Batch631.valid25255
  · exact MergedCutProfiles.Batch631.valid25256
  · exact MergedCutProfiles.Batch631.valid25257
  · exact MergedCutProfiles.Batch631.valid25258
  · exact MergedCutProfiles.Batch631.valid25259
  · exact MergedCutProfiles.Batch631.valid25260
  · exact MergedCutProfiles.Batch631.valid25261
  · exact MergedCutProfiles.Batch631.valid25262
  · exact MergedCutProfiles.Batch631.valid25263
  · exact MergedCutProfiles.Batch631.valid25264
  · exact MergedCutProfiles.Batch631.valid25265
  · exact MergedCutProfiles.Batch631.valid25266
  · exact MergedCutProfiles.Batch631.valid25267
  · exact MergedCutProfiles.Batch631.valid25268
  · exact MergedCutProfiles.Batch631.valid25269
theorem numericValid4217 : retention4217.NumericValid := by decide +kernel
def certificate4217 : RatCutBinCertificate := ⟨⟨retention4217,(1049493266185437663/500000000000000000),(204909449857824037/1000000000000000000),(16465437042510239339/1000000000000000000),(1842051788571481264403/500000000000000000),(569778588868160261/250000000000000000)⟩,(62471410330652661/62500000000000000),(220756037324285471/500000000000000000),(49382350233023151/250000000000000000),(51009922185326579/500000000000000000)⟩
theorem valid4217 : certificate4217.Valid := by decide +kernel
theorem sound4217 : certificate4217.Sound := rat_cut_bin_certificate_sound certificate4217 profilesValid4217 numericValid4217 valid4217

def retention4218 : RatCutRetentionCertificate := ⟨(31/500),(63/1000),(220531419800000000/44471963983586701429),(157812436052370191/200000000000000000),(71/20),(603164108858028383231/256000000000000000000),true,MergedCutProfiles.Batch631.profile25270,![MergedCutProfiles.Batch631.profile25270,MergedCutProfiles.Batch631.profile25271,MergedCutProfiles.Batch631.profile25272,MergedCutProfiles.Batch631.profile25273,MergedCutProfiles.Batch631.profile25260,MergedCutProfiles.Batch631.profile25274,MergedCutProfiles.Batch631.profile25275,MergedCutProfiles.Batch631.profile25264,MergedCutProfiles.Batch631.profile25276,MergedCutProfiles.Batch631.profile25267,MergedCutProfiles.Batch631.profile25277,MergedCutProfiles.Batch631.profile25278,MergedCutProfiles.Batch631.profile25279,MergedCutProfiles.Batch632.profile25280,MergedCutProfiles.Batch632.profile25281,MergedCutProfiles.Batch632.profile25282]⟩
theorem profilesValid4218 : retention4218.ProfilesValid := by
  change ∀ j : Fin 16, (retention4218.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch631.valid25270
  · exact MergedCutProfiles.Batch631.valid25271
  · exact MergedCutProfiles.Batch631.valid25272
  · exact MergedCutProfiles.Batch631.valid25273
  · exact MergedCutProfiles.Batch631.valid25260
  · exact MergedCutProfiles.Batch631.valid25274
  · exact MergedCutProfiles.Batch631.valid25275
  · exact MergedCutProfiles.Batch631.valid25264
  · exact MergedCutProfiles.Batch631.valid25276
  · exact MergedCutProfiles.Batch631.valid25267
  · exact MergedCutProfiles.Batch631.valid25277
  · exact MergedCutProfiles.Batch631.valid25278
  · exact MergedCutProfiles.Batch631.valid25279
  · exact MergedCutProfiles.Batch632.valid25280
  · exact MergedCutProfiles.Batch632.valid25281
  · exact MergedCutProfiles.Batch632.valid25282
theorem numericValid4218 : retention4218.NumericValid := by decide +kernel
def certificate4218 : RatCutBinCertificate := ⟨⟨retention4218,(1049493266185437663/500000000000000000),(204909449857824037/1000000000000000000),(16465437042510239339/1000000000000000000),(1842051788571481264403/500000000000000000),(2263376577490692117/1000000000000000000)⟩,(62471410330652661/62500000000000000),(221064314711837303/500000000000000000),(98512887082648039/500000000000000000),(51135384166155189/500000000000000000)⟩
theorem valid4218 : certificate4218.Valid := by decide +kernel
theorem sound4218 : certificate4218.Sound := rat_cut_bin_certificate_sound certificate4218 profilesValid4218 numericValid4218 valid4218

def retention4219 : RatCutRetentionCertificate := ⟨(31/500),(63/1000),(1128965535831368938/222359819917933507145),(1102657099/1000000000),(27/10),(18719673797153421949/8000000000000000000),true,MergedCutProfiles.Batch631.profile25270,![MergedCutProfiles.Batch631.profile25270,MergedCutProfiles.Batch632.profile25283,MergedCutProfiles.Batch632.profile25284,MergedCutProfiles.Batch631.profile25273,MergedCutProfiles.Batch632.profile25285,MergedCutProfiles.Batch632.profile25286,MergedCutProfiles.Batch631.profile25263,MergedCutProfiles.Batch632.profile25287,MergedCutProfiles.Batch631.profile25266,MergedCutProfiles.Batch632.profile25288,MergedCutProfiles.Batch632.profile25289,MergedCutProfiles.Batch632.profile25290,MergedCutProfiles.Batch632.profile25291,MergedCutProfiles.Batch632.profile25292,MergedCutProfiles.Batch632.profile25293,MergedCutProfiles.Batch632.profile25294]⟩
theorem profilesValid4219 : retention4219.ProfilesValid := by
  change ∀ j : Fin 16, (retention4219.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch631.valid25270
  · exact MergedCutProfiles.Batch632.valid25283
  · exact MergedCutProfiles.Batch632.valid25284
  · exact MergedCutProfiles.Batch631.valid25273
  · exact MergedCutProfiles.Batch632.valid25285
  · exact MergedCutProfiles.Batch632.valid25286
  · exact MergedCutProfiles.Batch631.valid25263
  · exact MergedCutProfiles.Batch632.valid25287
  · exact MergedCutProfiles.Batch631.valid25266
  · exact MergedCutProfiles.Batch632.valid25288
  · exact MergedCutProfiles.Batch632.valid25289
  · exact MergedCutProfiles.Batch632.valid25290
  · exact MergedCutProfiles.Batch632.valid25291
  · exact MergedCutProfiles.Batch632.valid25292
  · exact MergedCutProfiles.Batch632.valid25293
  · exact MergedCutProfiles.Batch632.valid25294
theorem numericValid4219 : retention4219.NumericValid := by decide +kernel
def certificate4219 : RatCutBinCertificate := ⟨⟨retention4219,(1049493266185437663/500000000000000000),(204909449857824037/1000000000000000000),(16465437042510239339/1000000000000000000),(1842051788571481264403/500000000000000000),(2269429814084105729/1000000000000000000)⟩,(62471410330652661/62500000000000000),(74272297035226901/200000000000000000),(32596544313649083/125000000000000000),(85418244124663693/500000000000000000)⟩
theorem valid4219 : certificate4219.Valid := by decide +kernel
theorem sound4219 : certificate4219.Sound := rat_cut_bin_certificate_sound certificate4219 profilesValid4219 numericValid4219 valid4219

def retention4220 : RatCutRetentionCertificate := ⟨(31/500),(63/1000),(2010575396272411674/222359819917933507145),(564482767915684469/500000000000000000),(53/20),(1476357985215729576629/640000000000000000000),true,MergedCutProfiles.Batch632.profile25295,![MergedCutProfiles.Batch632.profile25295,MergedCutProfiles.Batch631.profile25258,MergedCutProfiles.Batch632.profile25296,MergedCutProfiles.Batch632.profile25297,MergedCutProfiles.Batch631.profile25276,MergedCutProfiles.Batch631.profile25277,MergedCutProfiles.Batch632.profile25298,MergedCutProfiles.Batch632.profile25299,MergedCutProfiles.Batch632.profile25300,MergedCutProfiles.Batch632.profile25301,MergedCutProfiles.Batch632.profile25302,MergedCutProfiles.Batch632.profile25303,MergedCutProfiles.Batch632.profile25304,MergedCutProfiles.Batch632.profile25305,MergedCutProfiles.Batch632.profile25306,MergedCutProfiles.Batch632.profile25307]⟩
theorem profilesValid4220 : retention4220.ProfilesValid := by
  change ∀ j : Fin 16, (retention4220.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch632.valid25295
  · exact MergedCutProfiles.Batch631.valid25258
  · exact MergedCutProfiles.Batch632.valid25296
  · exact MergedCutProfiles.Batch632.valid25297
  · exact MergedCutProfiles.Batch631.valid25276
  · exact MergedCutProfiles.Batch631.valid25277
  · exact MergedCutProfiles.Batch632.valid25298
  · exact MergedCutProfiles.Batch632.valid25299
  · exact MergedCutProfiles.Batch632.valid25300
  · exact MergedCutProfiles.Batch632.valid25301
  · exact MergedCutProfiles.Batch632.valid25302
  · exact MergedCutProfiles.Batch632.valid25303
  · exact MergedCutProfiles.Batch632.valid25304
  · exact MergedCutProfiles.Batch632.valid25305
  · exact MergedCutProfiles.Batch632.valid25306
  · exact MergedCutProfiles.Batch632.valid25307
theorem numericValid4220 : retention4220.NumericValid := by decide +kernel
def certificate4220 : RatCutBinCertificate := ⟨⟨retention4220,(1049493266185437663/500000000000000000),(204909449857824037/1000000000000000000),(16465437042510239339/1000000000000000000),(1842051788571481264403/500000000000000000),(447517209567867701/200000000000000000)⟩,(62471410330652661/62500000000000000),(74501618968599997/200000000000000000),(259638418392666513/1000000000000000000),(170883541515091907/1000000000000000000)⟩
theorem valid4220 : certificate4220.Valid := by decide +kernel
theorem sound4220 : certificate4220.Sound := rat_cut_bin_certificate_sound certificate4220 profilesValid4220 numericValid4220 valid4220

def retention4221 : RatCutRetentionCertificate := ⟨(31/500),(63/1000),(39786203396191876909/222359819917933507145),(1005287698136205837/500000000000000000),(9/5),(21447517407859634930026318102651932689/12566096226702572962500000000000000000),false,MergedCutProfiles.Batch632.profile25308,(fun _ => MergedCutProfiles.Batch632.profile25308)⟩
theorem profilesValid4221 : retention4221.ProfilesValid := by
  exact MergedCutProfiles.Batch632.valid25308
theorem numericValid4221 : retention4221.NumericValid := by decide +kernel
def certificate4221 : RatCutBinCertificate := ⟨⟨retention4221,(1049493266185437663/500000000000000000),(204909449857824037/1000000000000000000),(16465437042510239339/1000000000000000000),(1842051788571481264403/500000000000000000),(829878511300539147/500000000000000000)⟩,(62471410330652661/62500000000000000),(399660307436351191/1000000000000000000),(46758750121805291/200000000000000000),(171713531653278393/1000000000000000000)⟩
theorem valid4221 : certificate4221.Valid := by decide +kernel
theorem sound4221 : certificate4221.Sound := rat_cut_bin_certificate_sound certificate4221 profilesValid4221 numericValid4221 valid4221

def retention4222 : RatCutRetentionCertificate := ⟨(31/500),(63/1000),(12800000000000000000/44471963983586701429),(39786203396191876909/1000000000000000000),1,(228217284786589756168570323877521464043/159144813584767507636000000000000000000),false,MergedCutProfiles.Batch632.profile25309,(fun _ => MergedCutProfiles.Batch632.profile25309)⟩
theorem profilesValid4222 : retention4222.ProfilesValid := by
  exact MergedCutProfiles.Batch632.valid25309
theorem numericValid4222 : retention4222.NumericValid := by decide +kernel
def certificate4222 : RatCutBinCertificate := ⟨⟨retention4222,(1049493266185437663/500000000000000000),(204909449857824037/1000000000000000000),(16465437042510239339/1000000000000000000),(1842051788571481264403/500000000000000000),(175987650923596701/125000000000000000)⟩,(62471410330652661/62500000000000000),(40523450085606459/125000000000000000),(38828109029864593/125000000000000000),(211092930029266731/500000000000000000)⟩
theorem valid4222 : certificate4222.Valid := by decide +kernel
theorem sound4222 : certificate4222.Sound := rat_cut_bin_certificate_sound certificate4222 profilesValid4222 numericValid4222 valid4222

def retention4223 : RatCutRetentionCertificate := ⟨(31/500),(63/1000),(1/2),64,1,(255411314097293059585699365940977515079/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch632.profile25310,(fun _ => MergedCutProfiles.Batch632.profile25310)⟩
theorem profilesValid4223 : retention4223.ProfilesValid := by
  exact MergedCutProfiles.Batch632.valid25310
theorem numericValid4223 : retention4223.NumericValid := by decide +kernel
def certificate4223 : RatCutBinCertificate := ⟨⟨retention4223,(1049493266185437663/500000000000000000),(204909449857824037/1000000000000000000),(16465437042510239339/1000000000000000000),(1842051788571481264403/500000000000000000),(971578907085247513/1000000000000000000)⟩,(62471410330652661/62500000000000000),(23274357675826597/50000000000000000),(35713650950879773/200000000000000000),(34163942850620461/200000000000000000)⟩
theorem valid4223 : certificate4223.Valid := by decide +kernel
theorem sound4223 : certificate4223.Sound := rat_cut_bin_certificate_sound certificate4223 profilesValid4223 numericValid4223 valid4223

def certificates : List RatCutBinCertificate := [certificate4212,certificate4213,certificate4214,certificate4215,certificate4216,certificate4217,certificate4218,certificate4219,certificate4220,certificate4221,certificate4222,certificate4223]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4212,List.forall_mem_cons.mpr ⟨sound4213,List.forall_mem_cons.mpr ⟨sound4214,List.forall_mem_cons.mpr ⟨sound4215,List.forall_mem_cons.mpr ⟨sound4216,List.forall_mem_cons.mpr ⟨sound4217,List.forall_mem_cons.mpr ⟨sound4218,List.forall_mem_cons.mpr ⟨sound4219,List.forall_mem_cons.mpr ⟨sound4220,List.forall_mem_cons.mpr ⟨sound4221,List.forall_mem_cons.mpr ⟨sound4222,List.forall_mem_cons.mpr ⟨sound4223,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch351
