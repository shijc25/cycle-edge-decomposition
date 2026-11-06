import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch031
import Cycle12.MergedCutProfiles.Batch032
import Cycle12.MergedCutProfiles.Batch033

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch016

def retention192 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(3839425248852907999/95005518140300851637),(617446893133130543/500000000000000000),(47/20),(333287448847921699257/160000000000000000000),true,MergedCutProfiles.Batch031.profile1277,![MergedCutProfiles.Batch031.profile1277,MergedCutProfiles.Batch031.profile1278,MergedCutProfiles.Batch031.profile1279,MergedCutProfiles.Batch032.profile1280,MergedCutProfiles.Batch032.profile1281,MergedCutProfiles.Batch032.profile1282,MergedCutProfiles.Batch032.profile1283,MergedCutProfiles.Batch032.profile1284,MergedCutProfiles.Batch032.profile1285,MergedCutProfiles.Batch032.profile1286,MergedCutProfiles.Batch032.profile1287,MergedCutProfiles.Batch032.profile1288,MergedCutProfiles.Batch032.profile1289,MergedCutProfiles.Batch032.profile1290,MergedCutProfiles.Batch032.profile1291,MergedCutProfiles.Batch032.profile1292]⟩
theorem profilesValid192 : retention192.ProfilesValid := by
  change ∀ j : Fin 16, (retention192.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch031.valid1277
  · exact MergedCutProfiles.Batch031.valid1278
  · exact MergedCutProfiles.Batch031.valid1279
  · exact MergedCutProfiles.Batch032.valid1280
  · exact MergedCutProfiles.Batch032.valid1281
  · exact MergedCutProfiles.Batch032.valid1282
  · exact MergedCutProfiles.Batch032.valid1283
  · exact MergedCutProfiles.Batch032.valid1284
  · exact MergedCutProfiles.Batch032.valid1285
  · exact MergedCutProfiles.Batch032.valid1286
  · exact MergedCutProfiles.Batch032.valid1287
  · exact MergedCutProfiles.Batch032.valid1288
  · exact MergedCutProfiles.Batch032.valid1289
  · exact MergedCutProfiles.Batch032.valid1290
  · exact MergedCutProfiles.Batch032.valid1291
  · exact MergedCutProfiles.Batch032.valid1292
theorem numericValid192 : retention192.NumericValid := by decide +kernel
def certificate192 : RatCutBinCertificate := ⟨⟨retention192,(1949347535396698671/1000000000000000000),(12287303118992409/500000000000000000),(555878577904152321/62500000000000000),(53069362478983016179/62500000000000000),(20703890501096113/10000000000000000)⟩,(997755748188441097/1000000000000000000),(93934022530038151/250000000000000000),(8014531385059501/31250000000000000),(172884802215788939/1000000000000000000)⟩
theorem valid192 : certificate192.Valid := by decide +kernel
theorem sound192 : certificate192.Sound := rat_cut_bin_certificate_sound certificate192 profilesValid192 numericValid192 valid192

def retention193 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(33266286800345827005/95005518140300851637),(3839425248852907999/1000000000000000000),(5/4),(319327669031700536674930283971979720399/245723215926586111936000000000000000000),false,MergedCutProfiles.Batch032.profile1293,(fun _ => MergedCutProfiles.Batch032.profile1293)⟩
theorem profilesValid193 : retention193.ProfilesValid := by
  exact MergedCutProfiles.Batch032.valid1293
theorem numericValid193 : retention193.NumericValid := by decide +kernel
def certificate193 : RatCutBinCertificate := ⟨⟨retention193,(1949347535396698671/1000000000000000000),(12287303118992409/500000000000000000),(555878577904152321/62500000000000000),(53069362478983016179/62500000000000000),(258561886263112483/200000000000000000)⟩,(997755748188441097/1000000000000000000),(215536638879347273/500000000000000000),(103093940354021219/500000000000000000),(175011550424496817/1000000000000000000)⟩
theorem valid193 : certificate193.Valid := by decide +kernel
theorem sound193 : certificate193.Sound := rat_cut_bin_certificate_sound certificate193 profilesValid193 numericValid193 valid193

def retention194 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(46658528281481668102/95005518140300851637),(6653257360069165401/200000000000000000),1,(134591838619787876471892736624008675659/133065147201383308020000000000000000000),false,MergedCutProfiles.Batch032.profile1294,(fun _ => MergedCutProfiles.Batch032.profile1294)⟩
theorem profilesValid194 : retention194.ProfilesValid := by
  exact MergedCutProfiles.Batch032.valid1294
theorem numericValid194 : retention194.NumericValid := by decide +kernel
def certificate194 : RatCutBinCertificate := ⟨⟨retention194,(1949347535396698671/1000000000000000000),(12287303118992409/500000000000000000),(555878577904152321/62500000000000000),(53069362478983016179/62500000000000000),(100608713952158889/100000000000000000)⟩,(997755748188441097/1000000000000000000),(115487856490994473/250000000000000000),(181285363730019647/1000000000000000000),(35326237956327547/200000000000000000)⟩
theorem valid194 : certificate194.Valid := by decide +kernel
theorem sound194 : certificate194.Sound := rat_cut_bin_certificate_sound certificate194 profilesValid194 numericValid194 valid194

def retention195 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(47125113564296484784/95005518140300851637),(23329264140740834051/500000000000000000),1,(1463871530634606727678302237050360699/1458079008796302128187500000000000000),false,MergedCutProfiles.Batch032.profile1295,(fun _ => MergedCutProfiles.Batch032.profile1295)⟩
theorem profilesValid195 : retention195.ProfilesValid := by
  exact MergedCutProfiles.Batch032.valid1295
theorem numericValid195 : retention195.NumericValid := by decide +kernel
def certificate195 : RatCutBinCertificate := ⟨⟨retention195,(1949347535396698671/1000000000000000000),(12287303118992409/500000000000000000),(555878577904152321/62500000000000000),(53069362478983016179/62500000000000000),(499293292872319731/500000000000000000)⟩,(997755748188441097/1000000000000000000),(461951044033917611/1000000000000000000),(181285658690662827/1000000000000000000),(88416982375717501/500000000000000000)⟩
theorem valid195 : certificate195.Valid := by decide +kernel
theorem sound195 : certificate195.Sound := rat_cut_bin_certificate_sound certificate195 profilesValid195 numericValid195 valid195

def retention196 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(1/2),(2945319597768530299/62500000000000000),1,(46943547157794703657360511528519006631/47125113564296484784000000000000000000),false,MergedCutProfiles.Batch032.profile1296,(fun _ => MergedCutProfiles.Batch032.profile1296)⟩
theorem profilesValid196 : retention196.ProfilesValid := by
  exact MergedCutProfiles.Batch032.valid1296
theorem numericValid196 : retention196.NumericValid := by decide +kernel
def certificate196 : RatCutBinCertificate := ⟨⟨retention196,(1949347535396698671/1000000000000000000),(12287303118992409/500000000000000000),(555878577904152321/62500000000000000),(53069362478983016179/62500000000000000),(990761019228947149/1000000000000000000)⟩,(997755748188441097/1000000000000000000),(465513763530422269/1000000000000000000),(4463697694097713/25000000000000000),(172862594011757967/1000000000000000000)⟩
theorem valid196 : certificate196.Valid := by decide +kernel
theorem sound196 : certificate196.Sound := rat_cut_bin_certificate_sound certificate196 profilesValid196 numericValid196 valid196

def retention197 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(38525661895648250022/95005518140300851637),(353688061770049553/100000000000000000),(13/10),(16857011961494589003754998517234677711/14147522470801982120000000000000000000),false,MergedCutProfiles.Batch032.profile1297,(fun _ => MergedCutProfiles.Batch032.profile1297)⟩
theorem profilesValid197 : retention197.ProfilesValid := by
  exact MergedCutProfiles.Batch032.valid1297
theorem numericValid197 : retention197.NumericValid := by decide +kernel
def certificate197 : RatCutBinCertificate := ⟨⟨retention197,(2328057820396698671/1000000000000000000),(12287303118992409/500000000000000000),(555878577904152321/62500000000000000),(53069362478983016179/62500000000000000),(591577287263455519/500000000000000000)⟩,(997319718375536051/1000000000000000000),(343300037560583177/1000000000000000000),(144826772254072613/500000000000000000),(109711161147925507/500000000000000000)⟩
theorem valid197 : certificate197.Valid := by decide +kernel
theorem sound197 : certificate197.Sound := rat_cut_bin_certificate_sound certificate197 profilesValid197 numericValid197 valid197

def retention198 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(47008628927472901506/95005518140300851637),(19262830947824125011/500000000000000000),1,(242048499609706651464133415226265079/240785386847801562637500000000000000),false,MergedCutProfiles.Batch032.profile1298,(fun _ => MergedCutProfiles.Batch032.profile1298)⟩
theorem profilesValid198 : retention198.ProfilesValid := by
  exact MergedCutProfiles.Batch032.valid1298
theorem numericValid198 : retention198.NumericValid := by decide +kernel
def certificate198 : RatCutBinCertificate := ⟨⟨retention198,(2328057820396698671/1000000000000000000),(12287303118992409/500000000000000000),(555878577904152321/62500000000000000),(53069362478983016179/62500000000000000),(499406644649211773/500000000000000000)⟩,(997319718375536051/1000000000000000000),(203329798585462937/500000000000000000),(45487123043349937/200000000000000000),(3450387894421107/15625000000000000)⟩
theorem valid198 : certificate198.Valid := by decide +kernel
theorem sound198 : certificate198.Sound := rat_cut_bin_certificate_sound certificate198 profilesValid198 numericValid198 valid198

def retention199 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(47478715216747630522/95005518140300851637),(23504314463736450753/500000000000000000),1,(48802569672182087966872758712842609/48967321799450939068750000000000000),false,MergedCutProfiles.Batch032.profile1299,(fun _ => MergedCutProfiles.Batch032.profile1299)⟩
theorem profilesValid199 : retention199.ProfilesValid := by
  exact MergedCutProfiles.Batch032.valid1299
theorem numericValid199 : retention199.NumericValid := by decide +kernel
def certificate199 : RatCutBinCertificate := ⟨⟨retention199,(2328057820396698671/1000000000000000000),(12287303118992409/500000000000000000),(555878577904152321/62500000000000000),(53069362478983016179/62500000000000000),(990202954807799249/1000000000000000000)⟩,(997319718375536051/1000000000000000000),(410195715840803859/1000000000000000000),(224269333169816023/1000000000000000000),(216902463888651067/1000000000000000000)⟩
theorem valid199 : certificate199.Valid := by decide +kernel
theorem sound199 : certificate199.Sound := rat_cut_bin_certificate_sound certificate199 profilesValid199 numericValid199 valid199

def retention200 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(1/2),(23739357608373815261/500000000000000000),1,(9459533561998746747369828284405139687/9495743043349526104400000000000000000),false,MergedCutProfiles.Batch032.profile1296,(fun _ => MergedCutProfiles.Batch032.profile1296)⟩
theorem profilesValid200 : retention200.ProfilesValid := by
  exact MergedCutProfiles.Batch032.valid1296
theorem numericValid200 : retention200.NumericValid := by decide +kernel
def certificate200 : RatCutBinCertificate := ⟨⟨retention200,(2328057820396698671/1000000000000000000),(12287303118992409/500000000000000000),(555878577904152321/62500000000000000),(53069362478983016179/62500000000000000),(989754253906877813/1000000000000000000)⟩,(997319718375536051/1000000000000000000),(20519083816601611/50000000000000000),(56025916913513943/250000000000000000),(216690344096186597/1000000000000000000)⟩
theorem valid200 : certificate200.Valid := by decide +kernel
theorem sound200 : certificate200.Sound := rat_cut_bin_certificate_sound certificate200 profilesValid200 numericValid200 valid200

def retention201 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(693340107958764868/87129209707661412453),(686475354414618681/1000000000000000000),(77/20),(2903285946205574233489/1280000000000000000000),true,MergedCutProfiles.Batch032.profile1300,![MergedCutProfiles.Batch032.profile1300,MergedCutProfiles.Batch032.profile1301,MergedCutProfiles.Batch032.profile1302,MergedCutProfiles.Batch032.profile1303,MergedCutProfiles.Batch032.profile1304,MergedCutProfiles.Batch032.profile1305,MergedCutProfiles.Batch032.profile1306,MergedCutProfiles.Batch032.profile1307,MergedCutProfiles.Batch032.profile1308,MergedCutProfiles.Batch032.profile1309,MergedCutProfiles.Batch032.profile1310,MergedCutProfiles.Batch032.profile1311,MergedCutProfiles.Batch032.profile1312,MergedCutProfiles.Batch032.profile1313,MergedCutProfiles.Batch032.profile1314,MergedCutProfiles.Batch032.profile1315]⟩
theorem profilesValid201 : retention201.ProfilesValid := by
  change ∀ j : Fin 16, (retention201.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch032.valid1300
  · exact MergedCutProfiles.Batch032.valid1301
  · exact MergedCutProfiles.Batch032.valid1302
  · exact MergedCutProfiles.Batch032.valid1303
  · exact MergedCutProfiles.Batch032.valid1304
  · exact MergedCutProfiles.Batch032.valid1305
  · exact MergedCutProfiles.Batch032.valid1306
  · exact MergedCutProfiles.Batch032.valid1307
  · exact MergedCutProfiles.Batch032.valid1308
  · exact MergedCutProfiles.Batch032.valid1309
  · exact MergedCutProfiles.Batch032.valid1310
  · exact MergedCutProfiles.Batch032.valid1311
  · exact MergedCutProfiles.Batch032.valid1312
  · exact MergedCutProfiles.Batch032.valid1313
  · exact MergedCutProfiles.Batch032.valid1314
  · exact MergedCutProfiles.Batch032.valid1315
theorem numericValid201 : retention201.NumericValid := by decide +kernel
def certificate201 : RatCutBinCertificate := ⟨⟨retention201,(24398007666006109/12500000000000000),(5353370290855499/200000000000000000),(4507486493507919757/500000000000000000),(789324760767518664023/1000000000000000000),(449175977615696019/200000000000000000)⟩,(498793911335631743/500000000000000000),(230208180544286989/500000000000000000),(182473430956557337/1000000000000000000),(43476574594789929/500000000000000000)⟩
theorem valid201 : certificate201.Valid := by decide +kernel
theorem sound201 : certificate201.Sound := rat_cut_bin_certificate_sound certificate201 profilesValid201 numericValid201 valid201

def retention202 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(293452652764033985/29043069902553804151),(173335026989691217/250000000000000000),(19/5),(720342332132506488589/320000000000000000000),true,MergedCutProfiles.Batch032.profile1316,![MergedCutProfiles.Batch032.profile1316,MergedCutProfiles.Batch032.profile1317,MergedCutProfiles.Batch032.profile1318,MergedCutProfiles.Batch032.profile1304,MergedCutProfiles.Batch032.profile1319,MergedCutProfiles.Batch033.profile1320,MergedCutProfiles.Batch033.profile1321,MergedCutProfiles.Batch033.profile1322,MergedCutProfiles.Batch033.profile1323,MergedCutProfiles.Batch033.profile1324,MergedCutProfiles.Batch032.profile1313,MergedCutProfiles.Batch033.profile1325,MergedCutProfiles.Batch033.profile1326,MergedCutProfiles.Batch033.profile1327,MergedCutProfiles.Batch033.profile1328,MergedCutProfiles.Batch033.profile1329]⟩
theorem profilesValid202 : retention202.ProfilesValid := by
  change ∀ j : Fin 16, (retention202.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch032.valid1316
  · exact MergedCutProfiles.Batch032.valid1317
  · exact MergedCutProfiles.Batch032.valid1318
  · exact MergedCutProfiles.Batch032.valid1304
  · exact MergedCutProfiles.Batch032.valid1319
  · exact MergedCutProfiles.Batch033.valid1320
  · exact MergedCutProfiles.Batch033.valid1321
  · exact MergedCutProfiles.Batch033.valid1322
  · exact MergedCutProfiles.Batch033.valid1323
  · exact MergedCutProfiles.Batch033.valid1324
  · exact MergedCutProfiles.Batch032.valid1313
  · exact MergedCutProfiles.Batch033.valid1325
  · exact MergedCutProfiles.Batch033.valid1326
  · exact MergedCutProfiles.Batch033.valid1327
  · exact MergedCutProfiles.Batch033.valid1328
  · exact MergedCutProfiles.Batch033.valid1329
theorem numericValid202 : retention202.NumericValid := by decide +kernel
def certificate202 : RatCutBinCertificate := ⟨⟨retention202,(24398007666006109/12500000000000000),(5353370290855499/200000000000000000),(4507486493507919757/500000000000000000),(789324760767518664023/1000000000000000000),(445809459842507843/200000000000000000)⟩,(498793911335631743/500000000000000000),(230662343336506149/500000000000000000),(90884906532214439/500000000000000000),(17392570007891893/200000000000000000)⟩
theorem valid202 : certificate202.Valid := by decide +kernel
theorem sound202 : certificate202.Sound := rat_cut_bin_certificate_sound certificate202 profilesValid202 numericValid202 valid202

def retention203 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(1096485554000000000/87129209707661412453),(176071591658420391/200000000000000000),(31/10),(569778390809958557299/256000000000000000000),true,MergedCutProfiles.Batch033.profile1330,![MergedCutProfiles.Batch033.profile1330,MergedCutProfiles.Batch033.profile1331,MergedCutProfiles.Batch033.profile1332,MergedCutProfiles.Batch033.profile1333,MergedCutProfiles.Batch033.profile1334,MergedCutProfiles.Batch033.profile1335,MergedCutProfiles.Batch032.profile1310,MergedCutProfiles.Batch033.profile1324,MergedCutProfiles.Batch033.profile1336,MergedCutProfiles.Batch033.profile1337,MergedCutProfiles.Batch033.profile1338,MergedCutProfiles.Batch033.profile1339,MergedCutProfiles.Batch033.profile1340,MergedCutProfiles.Batch033.profile1341,MergedCutProfiles.Batch033.profile1342,MergedCutProfiles.Batch033.profile1343]⟩
theorem profilesValid203 : retention203.ProfilesValid := by
  change ∀ j : Fin 16, (retention203.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch033.valid1330
  · exact MergedCutProfiles.Batch033.valid1331
  · exact MergedCutProfiles.Batch033.valid1332
  · exact MergedCutProfiles.Batch033.valid1333
  · exact MergedCutProfiles.Batch033.valid1334
  · exact MergedCutProfiles.Batch033.valid1335
  · exact MergedCutProfiles.Batch032.valid1310
  · exact MergedCutProfiles.Batch033.valid1324
  · exact MergedCutProfiles.Batch033.valid1336
  · exact MergedCutProfiles.Batch033.valid1337
  · exact MergedCutProfiles.Batch033.valid1338
  · exact MergedCutProfiles.Batch033.valid1339
  · exact MergedCutProfiles.Batch033.valid1340
  · exact MergedCutProfiles.Batch033.valid1341
  · exact MergedCutProfiles.Batch033.valid1342
  · exact MergedCutProfiles.Batch033.valid1343
theorem numericValid203 : retention203.NumericValid := by decide +kernel
def certificate203 : RatCutBinCertificate := ⟨⟨retention203,(24398007666006109/12500000000000000),(5353370290855499/200000000000000000),(4507486493507919757/500000000000000000),(789324760767518664023/1000000000000000000),(2207731132634185487/1000000000000000000)⟩,(498793911335631743/500000000000000000),(51336063848620821/125000000000000000),(223830504010021123/1000000000000000000),(25212808573705877/200000000000000000)⟩
theorem valid203 : certificate203.Valid := by decide +kernel
theorem sound203 : certificate203.Sound := rat_cut_bin_certificate_sound certificate203 profilesValid203 numericValid203 valid203

def certificates : List RatCutBinCertificate := [certificate192,certificate193,certificate194,certificate195,certificate196,certificate197,certificate198,certificate199,certificate200,certificate201,certificate202,certificate203]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound192,List.forall_mem_cons.mpr ⟨sound193,List.forall_mem_cons.mpr ⟨sound194,List.forall_mem_cons.mpr ⟨sound195,List.forall_mem_cons.mpr ⟨sound196,List.forall_mem_cons.mpr ⟨sound197,List.forall_mem_cons.mpr ⟨sound198,List.forall_mem_cons.mpr ⟨sound199,List.forall_mem_cons.mpr ⟨sound200,List.forall_mem_cons.mpr ⟨sound201,List.forall_mem_cons.mpr ⟨sound202,List.forall_mem_cons.mpr ⟨sound203,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch016
