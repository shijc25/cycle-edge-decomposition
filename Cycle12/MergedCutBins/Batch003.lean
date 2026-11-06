import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch006
import Cycle12.MergedCutProfiles.Batch007
import Cycle12.MergedCutProfiles.Batch008

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch003

def retention36 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(65020710850000000/60435757821562209223),(117582184303574573/200000000000000000),4,(8896769143337742337/4000000000000000000),true,MergedCutProfiles.Batch006.profile254,![MergedCutProfiles.Batch006.profile254,MergedCutProfiles.Batch006.profile255,MergedCutProfiles.Batch006.profile244,MergedCutProfiles.Batch006.profile246,MergedCutProfiles.Batch006.profile248,MergedCutProfiles.Batch006.profile256,MergedCutProfiles.Batch006.profile257,MergedCutProfiles.Batch006.profile258,MergedCutProfiles.Batch006.profile259,MergedCutProfiles.Batch006.profile260,MergedCutProfiles.Batch006.profile261,MergedCutProfiles.Batch006.profile262,MergedCutProfiles.Batch006.profile263,MergedCutProfiles.Batch006.profile264,MergedCutProfiles.Batch006.profile265,MergedCutProfiles.Batch006.profile266]⟩
theorem profilesValid36 : retention36.ProfilesValid := by
  change ∀ j : Fin 16, (retention36.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch006.valid254
  · exact MergedCutProfiles.Batch006.valid255
  · exact MergedCutProfiles.Batch006.valid244
  · exact MergedCutProfiles.Batch006.valid246
  · exact MergedCutProfiles.Batch006.valid248
  · exact MergedCutProfiles.Batch006.valid256
  · exact MergedCutProfiles.Batch006.valid257
  · exact MergedCutProfiles.Batch006.valid258
  · exact MergedCutProfiles.Batch006.valid259
  · exact MergedCutProfiles.Batch006.valid260
  · exact MergedCutProfiles.Batch006.valid261
  · exact MergedCutProfiles.Batch006.valid262
  · exact MergedCutProfiles.Batch006.valid263
  · exact MergedCutProfiles.Batch006.valid264
  · exact MergedCutProfiles.Batch006.valid265
  · exact MergedCutProfiles.Batch006.valid266
theorem numericValid36 : retention36.NumericValid := by decide +kernel
def certificate36 : RatCutBinCertificate := ⟨⟨retention36,(1825187020779274317/1000000000000000000),(1970684370264843/1000000000000000000),(56001757170388503/7812500000000000),(8702706377686016146887/1000000000000000000),(2222185168076691241/1000000000000000000)⟩,(199958115250891559/200000000000000000),(557960941522593259/1000000000000000000),(58243818785942269/500000000000000000),(5233473552374039/100000000000000000)⟩
theorem valid36 : certificate36.Valid := by decide +kernel
theorem sound36 : certificate36.Sound := rat_cut_bin_certificate_sound certificate36 profilesValid36 numericValid36 valid36

def retention37 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(3006192787008929441/1208715156431244184460),(1300414217/1000000000),(12/5),(7361613821849233199/3200000000000000000),true,MergedCutProfiles.Batch006.profile242,![MergedCutProfiles.Batch006.profile242,MergedCutProfiles.Batch006.profile267,MergedCutProfiles.Batch006.profile257,MergedCutProfiles.Batch006.profile268,MergedCutProfiles.Batch006.profile269,MergedCutProfiles.Batch006.profile264,MergedCutProfiles.Batch006.profile266,MergedCutProfiles.Batch006.profile270,MergedCutProfiles.Batch006.profile271,MergedCutProfiles.Batch006.profile272,MergedCutProfiles.Batch006.profile273,MergedCutProfiles.Batch006.profile274,MergedCutProfiles.Batch006.profile275,MergedCutProfiles.Batch006.profile276,MergedCutProfiles.Batch006.profile277,MergedCutProfiles.Batch006.profile278]⟩
theorem profilesValid37 : retention37.ProfilesValid := by
  change ∀ j : Fin 16, (retention37.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch006.valid242
  · exact MergedCutProfiles.Batch006.valid267
  · exact MergedCutProfiles.Batch006.valid257
  · exact MergedCutProfiles.Batch006.valid268
  · exact MergedCutProfiles.Batch006.valid269
  · exact MergedCutProfiles.Batch006.valid264
  · exact MergedCutProfiles.Batch006.valid266
  · exact MergedCutProfiles.Batch006.valid270
  · exact MergedCutProfiles.Batch006.valid271
  · exact MergedCutProfiles.Batch006.valid272
  · exact MergedCutProfiles.Batch006.valid273
  · exact MergedCutProfiles.Batch006.valid274
  · exact MergedCutProfiles.Batch006.valid275
  · exact MergedCutProfiles.Batch006.valid276
  · exact MergedCutProfiles.Batch006.valid277
  · exact MergedCutProfiles.Batch006.valid278
theorem numericValid37 : retention37.NumericValid := by decide +kernel
def certificate37 : RatCutBinCertificate := ⟨⟨retention37,(1825187020779274317/1000000000000000000),(1970684370264843/1000000000000000000),(56001757170388503/7812500000000000),(8702706377686016146887/1000000000000000000),(2299300048701824317/1000000000000000000)⟩,(199958115250891559/200000000000000000),(341132272806686339/1000000000000000000),(18248601831340813/62500000000000000),(53494139333754907/250000000000000000)⟩
theorem valid37 : certificate37.Valid := by decide +kernel
theorem sound37 : certificate37.Sound := rat_cut_bin_certificate_sound certificate37 profilesValid37 numericValid37 valid37

def retention38 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(3200000000000000000/60435757821562209223),(3006192787008929441/1000000000000000000),(29/20),(2580099391996043901481/1280000000000000000000),true,MergedCutProfiles.Batch006.profile279,![MergedCutProfiles.Batch006.profile279,MergedCutProfiles.Batch007.profile280,MergedCutProfiles.Batch007.profile281,MergedCutProfiles.Batch007.profile282,MergedCutProfiles.Batch007.profile283,MergedCutProfiles.Batch007.profile284,MergedCutProfiles.Batch007.profile285,MergedCutProfiles.Batch007.profile286,MergedCutProfiles.Batch007.profile287,MergedCutProfiles.Batch007.profile288,MergedCutProfiles.Batch007.profile289,MergedCutProfiles.Batch007.profile290,MergedCutProfiles.Batch007.profile291,MergedCutProfiles.Batch007.profile292,MergedCutProfiles.Batch007.profile293,MergedCutProfiles.Batch007.profile294]⟩
theorem profilesValid38 : retention38.ProfilesValid := by
  change ∀ j : Fin 16, (retention38.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch006.valid279
  · exact MergedCutProfiles.Batch007.valid280
  · exact MergedCutProfiles.Batch007.valid281
  · exact MergedCutProfiles.Batch007.valid282
  · exact MergedCutProfiles.Batch007.valid283
  · exact MergedCutProfiles.Batch007.valid284
  · exact MergedCutProfiles.Batch007.valid285
  · exact MergedCutProfiles.Batch007.valid286
  · exact MergedCutProfiles.Batch007.valid287
  · exact MergedCutProfiles.Batch007.valid288
  · exact MergedCutProfiles.Batch007.valid289
  · exact MergedCutProfiles.Batch007.valid290
  · exact MergedCutProfiles.Batch007.valid291
  · exact MergedCutProfiles.Batch007.valid292
  · exact MergedCutProfiles.Batch007.valid293
  · exact MergedCutProfiles.Batch007.valid294
theorem numericValid38 : retention38.NumericValid := by decide +kernel
def certificate38 : RatCutBinCertificate := ⟨⟨retention38,(1825187020779274317/1000000000000000000),(1970684370264843/1000000000000000000),(56001757170388503/7812500000000000),(8702706377686016146887/1000000000000000000),(25187188373024877/12500000000000000)⟩,(199958115250891559/200000000000000000),(1107116931524439/3906250000000000),(359198711670169909/1000000000000000000),(1892030814588117/5000000000000000)⟩
theorem valid38 : certificate38.Valid := by decide +kernel
theorem sound38 : certificate38.Sound := rat_cut_bin_certificate_sound certificate38 profilesValid38 numericValid38 valid38

def retention39 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(1/2),64,1,(255368860549321472084694123425840443671/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch007.profile295,(fun _ => MergedCutProfiles.Batch007.profile295)⟩
theorem profilesValid39 : retention39.ProfilesValid := by
  exact MergedCutProfiles.Batch007.valid295
theorem numericValid39 : retention39.NumericValid := by decide +kernel
def certificate39 : RatCutBinCertificate := ⟨⟨retention39,(1825187020779274317/1000000000000000000),(1970684370264843/1000000000000000000),(56001757170388503/7812500000000000),(8702706377686016146887/1000000000000000000),(997032832127892971/1000000000000000000)⟩,(199958115250891559/200000000000000000),(10434253676383781/25000000000000000),(108969311147248201/500000000000000000),(106956794229878967/500000000000000000)⟩
theorem valid39 : certificate39.Valid := by decide +kernel
theorem sound39 : certificate39.Sound := rat_cut_bin_certificate_sound certificate39 profilesValid39 numericValid39 valid39

def retention40 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(3200000000000000000/60435757821562209223),(3229170141460172409/1000000000000000000),(27/20),(10244432764945466652144324670558550130431/5166672226336275854400000000000000000000),false,MergedCutProfiles.Batch007.profile296,(fun _ => MergedCutProfiles.Batch007.profile296)⟩
theorem profilesValid40 : retention40.ProfilesValid := by
  exact MergedCutProfiles.Batch007.valid296
theorem numericValid40 : retention40.NumericValid := by decide +kernel
def certificate40 : RatCutBinCertificate := ⟨⟨retention40,(2161557425779274317/1000000000000000000),(1970684370264843/1000000000000000000),(56001757170388503/7812500000000000),(8702706377686016146887/1000000000000000000),(990994530807218707/500000000000000000)⟩,(999751980771060843/1000000000000000000),(201373691809474903/1000000000000000000),(95123847297897707/200000000000000000),(522217631540646757/1000000000000000000)⟩
theorem valid40 : certificate40.Valid := by decide +kernel
theorem sound40 : certificate40.Sound := rat_cut_bin_certificate_sound certificate40 profilesValid40 numericValid40 valid40

def retention41 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(1/2),64,1,(255368860549321472084694123425840443671/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch007.profile295,(fun _ => MergedCutProfiles.Batch007.profile295)⟩
theorem profilesValid41 : retention41.ProfilesValid := by
  exact MergedCutProfiles.Batch007.valid295
theorem numericValid41 : retention41.NumericValid := by decide +kernel
def certificate41 : RatCutBinCertificate := ⟨⟨retention41,(2161557425779274317/1000000000000000000),(1970684370264843/1000000000000000000),(56001757170388503/7812500000000000),(8702706377686016146887/1000000000000000000),(249235089341164183/250000000000000000)⟩,(999751980771060843/1000000000000000000),(200172684110383271/500000000000000000),(23316606843139387/100000000000000000),(114415034466232029/500000000000000000)⟩
theorem valid41 : certificate41.Valid := by decide +kernel
theorem sound41 : certificate41.Sound := rat_cut_bin_certificate_sound certificate41 profilesValid41 numericValid41 valid41

def retention42 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(298815238790132929/460659976857643419290),(116010850728139807/200000000000000000),4,(566648436938681401707/256000000000000000000),true,MergedCutProfiles.Batch007.profile297,![MergedCutProfiles.Batch007.profile297,MergedCutProfiles.Batch007.profile298,MergedCutProfiles.Batch007.profile299,MergedCutProfiles.Batch007.profile300,MergedCutProfiles.Batch007.profile301,MergedCutProfiles.Batch007.profile302,MergedCutProfiles.Batch007.profile303,MergedCutProfiles.Batch007.profile304,MergedCutProfiles.Batch007.profile305,MergedCutProfiles.Batch007.profile306,MergedCutProfiles.Batch007.profile307,MergedCutProfiles.Batch007.profile308,MergedCutProfiles.Batch007.profile309,MergedCutProfiles.Batch007.profile310,MergedCutProfiles.Batch007.profile311,MergedCutProfiles.Batch007.profile312]⟩
theorem profilesValid42 : retention42.ProfilesValid := by
  change ∀ j : Fin 16, (retention42.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch007.valid297
  · exact MergedCutProfiles.Batch007.valid298
  · exact MergedCutProfiles.Batch007.valid299
  · exact MergedCutProfiles.Batch007.valid300
  · exact MergedCutProfiles.Batch007.valid301
  · exact MergedCutProfiles.Batch007.valid302
  · exact MergedCutProfiles.Batch007.valid303
  · exact MergedCutProfiles.Batch007.valid304
  · exact MergedCutProfiles.Batch007.valid305
  · exact MergedCutProfiles.Batch007.valid306
  · exact MergedCutProfiles.Batch007.valid307
  · exact MergedCutProfiles.Batch007.valid308
  · exact MergedCutProfiles.Batch007.valid309
  · exact MergedCutProfiles.Batch007.valid310
  · exact MergedCutProfiles.Batch007.valid311
  · exact MergedCutProfiles.Batch007.valid312
theorem numericValid42 : retention42.NumericValid := by decide +kernel
def certificate42 : RatCutBinCertificate := ⟨⟨retention42,(1833625041264357003/1000000000000000000),(1291114465089419/500000000000000000),(290195100374488423/40000000000000000),(839228398002528746119/125000000000000000),(276357485916601017/125000000000000000)⟩,(999727426327723233/1000000000000000000),(281778877059953327/500000000000000000),(5662503202348993/50000000000000000),(50536129263513807/1000000000000000000)⟩
theorem valid42 : certificate42.Valid := by decide +kernel
theorem sound42 : certificate42.Sound := rat_cut_bin_certificate_sound certificate42 profilesValid42 numericValid42 valid42

def retention43 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(63778306600000000/46065997685764341929),(298815238790132929/500000000000000000),4,(1070367384630286025131832562552873227/478104382064212686400000000000000000),true,MergedCutProfiles.Batch007.profile313,![MergedCutProfiles.Batch007.profile313,MergedCutProfiles.Batch007.profile300,MergedCutProfiles.Batch007.profile314,MergedCutProfiles.Batch007.profile315,MergedCutProfiles.Batch007.profile316,MergedCutProfiles.Batch007.profile317,MergedCutProfiles.Batch007.profile311,MergedCutProfiles.Batch007.profile318,MergedCutProfiles.Batch007.profile319,MergedCutProfiles.Batch008.profile320,MergedCutProfiles.Batch008.profile321,MergedCutProfiles.Batch008.profile322,MergedCutProfiles.Batch008.profile323,MergedCutProfiles.Batch008.profile324,MergedCutProfiles.Batch008.profile325,MergedCutProfiles.Batch008.profile326]⟩
theorem profilesValid43 : retention43.ProfilesValid := by
  change ∀ j : Fin 16, (retention43.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch007.valid313
  · exact MergedCutProfiles.Batch007.valid300
  · exact MergedCutProfiles.Batch007.valid314
  · exact MergedCutProfiles.Batch007.valid315
  · exact MergedCutProfiles.Batch007.valid316
  · exact MergedCutProfiles.Batch007.valid317
  · exact MergedCutProfiles.Batch007.valid311
  · exact MergedCutProfiles.Batch007.valid318
  · exact MergedCutProfiles.Batch007.valid319
  · exact MergedCutProfiles.Batch008.valid320
  · exact MergedCutProfiles.Batch008.valid321
  · exact MergedCutProfiles.Batch008.valid322
  · exact MergedCutProfiles.Batch008.valid323
  · exact MergedCutProfiles.Batch008.valid324
  · exact MergedCutProfiles.Batch008.valid325
  · exact MergedCutProfiles.Batch008.valid326
theorem numericValid43 : retention43.NumericValid := by decide +kernel
def certificate43 : RatCutBinCertificate := ⟨⟨retention43,(1833625041264357003/1000000000000000000),(1291114465089419/500000000000000000),(290195100374488423/40000000000000000),(839228398002528746119/125000000000000000),(2236162854903074333/1000000000000000000)⟩,(999727426327723233/1000000000000000000),(273100028996242553/500000000000000000),(61737271826991133/500000000000000000),(11185247131542803/200000000000000000)⟩
theorem valid43 : certificate43.Valid := by decide +kernel
theorem sound43 : certificate43.Sound := rat_cut_bin_certificate_sound certificate43 profilesValid43 numericValid43 valid43

def retention44 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(1448888628483975001/921319953715286838580),(318891533/250000000),(49/20),(37096695121204516661/16000000000000000000),true,MergedCutProfiles.Batch008.profile327,![MergedCutProfiles.Batch008.profile327,MergedCutProfiles.Batch008.profile328,MergedCutProfiles.Batch008.profile329,MergedCutProfiles.Batch008.profile330,MergedCutProfiles.Batch007.profile308,MergedCutProfiles.Batch008.profile331,MergedCutProfiles.Batch007.profile318,MergedCutProfiles.Batch007.profile319,MergedCutProfiles.Batch008.profile320,MergedCutProfiles.Batch008.profile332,MergedCutProfiles.Batch008.profile333,MergedCutProfiles.Batch008.profile334,MergedCutProfiles.Batch008.profile325,MergedCutProfiles.Batch008.profile335,MergedCutProfiles.Batch008.profile336,MergedCutProfiles.Batch008.profile337]⟩
theorem profilesValid44 : retention44.ProfilesValid := by
  change ∀ j : Fin 16, (retention44.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch008.valid327
  · exact MergedCutProfiles.Batch008.valid328
  · exact MergedCutProfiles.Batch008.valid329
  · exact MergedCutProfiles.Batch008.valid330
  · exact MergedCutProfiles.Batch007.valid308
  · exact MergedCutProfiles.Batch008.valid331
  · exact MergedCutProfiles.Batch007.valid318
  · exact MergedCutProfiles.Batch007.valid319
  · exact MergedCutProfiles.Batch008.valid320
  · exact MergedCutProfiles.Batch008.valid332
  · exact MergedCutProfiles.Batch008.valid333
  · exact MergedCutProfiles.Batch008.valid334
  · exact MergedCutProfiles.Batch008.valid325
  · exact MergedCutProfiles.Batch008.valid335
  · exact MergedCutProfiles.Batch008.valid336
  · exact MergedCutProfiles.Batch008.valid337
theorem numericValid44 : retention44.NumericValid := by decide +kernel
def certificate44 : RatCutBinCertificate := ⟨⟨retention44,(1833625041264357003/1000000000000000000),(1291114465089419/500000000000000000),(290195100374488423/40000000000000000),(839228398002528746119/125000000000000000),(2316944471349964773/1000000000000000000)⟩,(999727426327723233/1000000000000000000),(42658525227155697/125000000000000000),(291831495152905087/1000000000000000000),(1323773345249013/6250000000000000)⟩
theorem valid44 : certificate44.Valid := by decide +kernel
theorem sound44 : certificate44.Sound := rat_cut_bin_certificate_sound certificate44 profilesValid44 numericValid44 valid44

def retention45 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(24209386524715704381/921319953715286838580),(1448888628483975001/1000000000000000000),(11/5),(685355015594606050733/320000000000000000000),true,MergedCutProfiles.Batch008.profile338,![MergedCutProfiles.Batch008.profile338,MergedCutProfiles.Batch008.profile339,MergedCutProfiles.Batch008.profile340,MergedCutProfiles.Batch008.profile341,MergedCutProfiles.Batch008.profile342,MergedCutProfiles.Batch008.profile343,MergedCutProfiles.Batch008.profile344,MergedCutProfiles.Batch008.profile345,MergedCutProfiles.Batch008.profile346,MergedCutProfiles.Batch008.profile347,MergedCutProfiles.Batch008.profile348,MergedCutProfiles.Batch008.profile349,MergedCutProfiles.Batch008.profile350,MergedCutProfiles.Batch008.profile351,MergedCutProfiles.Batch008.profile352,MergedCutProfiles.Batch008.profile353]⟩
theorem profilesValid45 : retention45.ProfilesValid := by
  change ∀ j : Fin 16, (retention45.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch008.valid338
  · exact MergedCutProfiles.Batch008.valid339
  · exact MergedCutProfiles.Batch008.valid340
  · exact MergedCutProfiles.Batch008.valid341
  · exact MergedCutProfiles.Batch008.valid342
  · exact MergedCutProfiles.Batch008.valid343
  · exact MergedCutProfiles.Batch008.valid344
  · exact MergedCutProfiles.Batch008.valid345
  · exact MergedCutProfiles.Batch008.valid346
  · exact MergedCutProfiles.Batch008.valid347
  · exact MergedCutProfiles.Batch008.valid348
  · exact MergedCutProfiles.Batch008.valid349
  · exact MergedCutProfiles.Batch008.valid350
  · exact MergedCutProfiles.Batch008.valid351
  · exact MergedCutProfiles.Batch008.valid352
  · exact MergedCutProfiles.Batch008.valid353
theorem numericValid45 : retention45.NumericValid := by decide +kernel
def certificate45 : RatCutBinCertificate := ⟨⟨retention45,(1833625041264357003/1000000000000000000),(1291114465089419/500000000000000000),(290195100374488423/40000000000000000),(839228398002528746119/125000000000000000),(267537326324437837/125000000000000000)⟩,(999727426327723233/1000000000000000000),(17410679790093321/50000000000000000),(284436116321421631/1000000000000000000),(105972496853567143/500000000000000000)⟩
theorem valid45 : certificate45.Valid := by decide +kernel
theorem sound45 : certificate45.Sound := rat_cut_bin_certificate_sound certificate45 profilesValid45 numericValid45 valid45

def retention46 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(3200000000000000000/46065997685764341929),(24209386524715704381/1000000000000000000),1,(37736838452604142626012299451341026663/19367509219772563504800000000000000000),false,MergedCutProfiles.Batch008.profile354,(fun _ => MergedCutProfiles.Batch008.profile354)⟩
theorem profilesValid46 : retention46.ProfilesValid := by
  exact MergedCutProfiles.Batch008.valid354
theorem numericValid46 : retention46.NumericValid := by decide +kernel
def certificate46 : RatCutBinCertificate := ⟨⟨retention46,(1833625041264357003/1000000000000000000),(1291114465089419/500000000000000000),(290195100374488423/40000000000000000),(839228398002528746119/125000000000000000),(1947808464651167139/1000000000000000000)⟩,(999727426327723233/1000000000000000000),(221289332057401317/1000000000000000000),(444768301273964891/1000000000000000000),(801589126452452023/1000000000000000000)⟩
theorem valid46 : certificate46.Valid := by decide +kernel
theorem sound46 : certificate46.Sound := rat_cut_bin_certificate_sound certificate46 profilesValid46 numericValid46 valid46

def retention47 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(1/2),64,1,(255368898673698792760224881759734912191/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch008.profile355,(fun _ => MergedCutProfiles.Batch008.profile355)⟩
theorem profilesValid47 : retention47.ProfilesValid := by
  exact MergedCutProfiles.Batch008.valid355
theorem numericValid47 : retention47.NumericValid := by decide +kernel
def certificate47 : RatCutBinCertificate := ⟨⟨retention47,(1833625041264357003/1000000000000000000),(1291114465089419/500000000000000000),(290195100374488423/40000000000000000),(839228398002528746119/125000000000000000),(498441059091835401/500000000000000000)⟩,(999727426327723233/1000000000000000000),(419900974571929269/1000000000000000000),(107867474353646389/500000000000000000),(42341122332523997/200000000000000000)⟩
theorem valid47 : certificate47.Valid := by decide +kernel
theorem sound47 : certificate47.Sound := rat_cut_bin_certificate_sound certificate47 profilesValid47 numericValid47 valid47

def certificates : List RatCutBinCertificate := [certificate36,certificate37,certificate38,certificate39,certificate40,certificate41,certificate42,certificate43,certificate44,certificate45,certificate46,certificate47]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound36,List.forall_mem_cons.mpr ⟨sound37,List.forall_mem_cons.mpr ⟨sound38,List.forall_mem_cons.mpr ⟨sound39,List.forall_mem_cons.mpr ⟨sound40,List.forall_mem_cons.mpr ⟨sound41,List.forall_mem_cons.mpr ⟨sound42,List.forall_mem_cons.mpr ⟨sound43,List.forall_mem_cons.mpr ⟨sound44,List.forall_mem_cons.mpr ⟨sound45,List.forall_mem_cons.mpr ⟨sound46,List.forall_mem_cons.mpr ⟨sound47,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch003
