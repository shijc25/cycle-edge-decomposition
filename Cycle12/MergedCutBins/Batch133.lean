import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch256
import Cycle12.MergedCutProfiles.Batch257
import Cycle12.MergedCutProfiles.Batch258

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch133

def retention1596 : RatCutRetentionCertificate := ⟨(127/2000),(509/8000),(1/2),(5381206549068056339/1000000000000000000),(11/10),(2134505585168515819394144734912197564199/2152482619627222535600000000000000000000),false,MergedCutProfiles.Batch256.profile10269,(fun _ => MergedCutProfiles.Batch256.profile10269)⟩
theorem profilesValid1596 : retention1596.ProfilesValid := by
  exact MergedCutProfiles.Batch256.valid10269
theorem numericValid1596 : retention1596.NumericValid := by decide +kernel
def certificate1596 : RatCutBinCertificate := ⟨⟨retention1596,(589829448289107973/250000000000000000),(209830266746550371/1000000000000000000),(4231928338231689781/250000000000000000),(36789342620044720287/200000000000000000),(479736094150385587/500000000000000000)⟩,(61863994757145671/62500000000000000),(8660592280487823/20000000000000000),(10227306590331389/50000000000000000),(153768310790366737/1000000000000000000)⟩
theorem valid1596 : certificate1596.Valid := by decide +kernel
theorem sound1596 : certificate1596.Sound := rat_cut_bin_certificate_sound certificate1596 profilesValid1596 numericValid1596 valid1596

def retention1597 : RatCutRetentionCertificate := ⟨(127/2000),(509/8000),(1/2),64,1,(15963364601777903472439151603522163279/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch256.profile10269,(fun _ => MergedCutProfiles.Batch256.profile10269)⟩
theorem profilesValid1597 : retention1597.ProfilesValid := by
  exact MergedCutProfiles.Batch256.valid10269
theorem numericValid1597 : retention1597.NumericValid := by decide +kernel
def certificate1597 : RatCutBinCertificate := ⟨⟨retention1597,(589829448289107973/250000000000000000),(209830266746550371/1000000000000000000),(4231928338231689781/250000000000000000),(36789342620044720287/200000000000000000),(968464452969686839/1000000000000000000)⟩,(61863994757145671/62500000000000000),(394591610045928641/1000000000000000000),(119237255817950627/500000000000000000),(112586582070848473/500000000000000000)⟩
theorem valid1597 : certificate1597.Valid := by decide +kernel
theorem sound1597 : certificate1597.Sound := rat_cut_bin_certificate_sound certificate1597 profilesValid1597 numericValid1597 valid1597

def retention1598 : RatCutRetentionCertificate := ⟨(127/2000),(509/8000),(5047318271742319356/10858091147154489655),(806378388037493157/250000000000000000),(6/5),(592627252275727399356249674792185101/559984991692703581250000000000000000),false,MergedCutProfiles.Batch256.profile10270,(fun _ => MergedCutProfiles.Batch256.profile10270)⟩
theorem profilesValid1598 : retention1598.ProfilesValid := by
  exact MergedCutProfiles.Batch256.valid10270
theorem numericValid1598 : retention1598.NumericValid := by decide +kernel
def certificate1598 : RatCutBinCertificate := ⟨⟨retention1598,(669701878289107973/250000000000000000),(209830266746550371/1000000000000000000),(4231928338231689781/250000000000000000),(36789342620044720287/200000000000000000),(254608212212698441/250000000000000000)⟩,(494220854216931411/500000000000000000),(97318678788491461/250000000000000000),(243454423042391463/1000000000000000000),(83633601032899641/500000000000000000)⟩
theorem valid1598 : certificate1598.Valid := by decide +kernel
theorem sound1598 : certificate1598.Sound := rat_cut_bin_certificate_sound certificate1598 profilesValid1598 numericValid1598 valid1598

def retention1599 : RatCutRetentionCertificate := ⟨(127/2000),(509/8000),(5357830051951085888/10858091147154489655),(1261829567935579839/250000000000000000),(11/10),(505688498464392227111584076617572959471/504731827174231935600000000000000000000),false,MergedCutProfiles.Batch256.profile10271,(fun _ => MergedCutProfiles.Batch256.profile10271)⟩
theorem profilesValid1599 : retention1599.ProfilesValid := by
  exact MergedCutProfiles.Batch256.valid10271
theorem numericValid1599 : retention1599.NumericValid := by decide +kernel
def certificate1599 : RatCutBinCertificate := ⟨⟨retention1599,(669701878289107973/250000000000000000),(209830266746550371/1000000000000000000),(4231928338231689781/250000000000000000),(36789342620044720287/200000000000000000),(96536173946056467/100000000000000000)⟩,(494220854216931411/500000000000000000),(205337616426235943/500000000000000000),(223842320132710831/1000000000000000000),(2617148106425197/15625000000000000)⟩
theorem valid1599 : certificate1599.Valid := by decide +kernel
theorem sound1599 : certificate1599.Sound := rat_cut_bin_certificate_sound certificate1599 profilesValid1599 numericValid1599 valid1599

def retention1600 : RatCutRetentionCertificate := ⟨(127/2000),(509/8000),(5411408352470596747/10858091147154489655),(83716094561735717/15625000000000000),(11/10),(133224597286300710544141348323430842151/133945751298777147200000000000000000000),false,MergedCutProfiles.Batch256.profile10272,(fun _ => MergedCutProfiles.Batch256.profile10272)⟩
theorem profilesValid1600 : retention1600.ProfilesValid := by
  exact MergedCutProfiles.Batch256.valid10272
theorem numericValid1600 : retention1600.NumericValid := by decide +kernel
def certificate1600 : RatCutBinCertificate := ⟨⟨retention1600,(669701878289107973/250000000000000000),(209830266746550371/1000000000000000000),(4231928338231689781/250000000000000000),(36789342620044720287/200000000000000000),(958082843269656279/1000000000000000000)⟩,(494220854216931411/500000000000000000),(41379527869100167/100000000000000000),(6908673077774667/31250000000000000),(41415184793611391/250000000000000000)⟩
theorem valid1600 : certificate1600.Valid := by decide +kernel
theorem sound1600 : certificate1600.Sound := rat_cut_bin_certificate_sound certificate1600 profilesValid1600 numericValid1600 valid1600

def retention1601 : RatCutRetentionCertificate := ⟨(127/2000),(509/8000),(1/2),(5411408352470596747/1000000000000000000),(11/10),(2146885053143910903514686462110465836951/2164563340988238698800000000000000000000),false,MergedCutProfiles.Batch256.profile10269,(fun _ => MergedCutProfiles.Batch256.profile10269)⟩
theorem profilesValid1601 : retention1601.ProfilesValid := by
  exact MergedCutProfiles.Batch256.valid10269
theorem numericValid1601 : retention1601.NumericValid := by decide +kernel
def certificate1601 : RatCutBinCertificate := ⟨⟨retention1601,(669701878289107973/250000000000000000),(209830266746550371/1000000000000000000),(4231928338231689781/250000000000000000),(36789342620044720287/200000000000000000),(23882492527761363/25000000000000000)⟩,(494220854216931411/500000000000000000),(415000817731854369/1000000000000000000),(220015576869671369/1000000000000000000),(164658277072836691/1000000000000000000)⟩
theorem valid1601 : certificate1601.Valid := by decide +kernel
theorem sound1601 : certificate1601.Sound := rat_cut_bin_certificate_sound certificate1601 profilesValid1601 numericValid1601 valid1601

def retention1602 : RatCutRetentionCertificate := ⟨(509/8000),(51/800),(263164850595589514/2701768652877649923),(871328204294733959/1000000000000000000),(13/5),(2436995230656489743851/1280000000000000000000),true,MergedCutProfiles.Batch256.profile10273,![MergedCutProfiles.Batch256.profile10273,MergedCutProfiles.Batch256.profile10274,MergedCutProfiles.Batch256.profile10275,MergedCutProfiles.Batch256.profile10276,MergedCutProfiles.Batch256.profile10277,MergedCutProfiles.Batch256.profile10278,MergedCutProfiles.Batch256.profile10279,MergedCutProfiles.Batch257.profile10280,MergedCutProfiles.Batch257.profile10281,MergedCutProfiles.Batch257.profile10282,MergedCutProfiles.Batch257.profile10283,MergedCutProfiles.Batch257.profile10284,MergedCutProfiles.Batch257.profile10285,MergedCutProfiles.Batch257.profile10286,MergedCutProfiles.Batch257.profile10287,MergedCutProfiles.Batch257.profile10288]⟩
theorem profilesValid1602 : retention1602.ProfilesValid := by
  change ∀ j : Fin 16, (retention1602.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch256.valid10273
  · exact MergedCutProfiles.Batch256.valid10274
  · exact MergedCutProfiles.Batch256.valid10275
  · exact MergedCutProfiles.Batch256.valid10276
  · exact MergedCutProfiles.Batch256.valid10277
  · exact MergedCutProfiles.Batch256.valid10278
  · exact MergedCutProfiles.Batch256.valid10279
  · exact MergedCutProfiles.Batch257.valid10280
  · exact MergedCutProfiles.Batch257.valid10281
  · exact MergedCutProfiles.Batch257.valid10282
  · exact MergedCutProfiles.Batch257.valid10283
  · exact MergedCutProfiles.Batch257.valid10284
  · exact MergedCutProfiles.Batch257.valid10285
  · exact MergedCutProfiles.Batch257.valid10286
  · exact MergedCutProfiles.Batch257.valid10287
  · exact MergedCutProfiles.Batch257.valid10288
theorem numericValid1602 : retention1602.NumericValid := by decide +kernel
def certificate1602 : RatCutBinCertificate := ⟨⟨retention1602,(473824445381424539/200000000000000000),(52706141081196361/250000000000000000),(16967775142051727919/1000000000000000000),(1433717631298357343/7812500000000000),(1827329235055737539/1000000000000000000)⟩,(247442534552934607/250000000000000000),(339814519689335391/1000000000000000000),(293397120847049169/1000000000000000000),(155422011858568693/1000000000000000000)⟩
theorem valid1602 : certificate1602.Valid := by decide +kernel
theorem sound1602 : certificate1602.Sound := rat_cut_bin_certificate_sound certificate1602 profilesValid1602 numericValid1602 valid1602

def retention1603 : RatCutRetentionCertificate := ⟨(509/8000),(51/800),(928060276084599635/5403537305755299846),(131582425297794757/125000000000000000),(11/5),(272434972173104020457/160000000000000000000),true,MergedCutProfiles.Batch257.profile10289,![MergedCutProfiles.Batch257.profile10289,MergedCutProfiles.Batch257.profile10290,MergedCutProfiles.Batch257.profile10291,MergedCutProfiles.Batch257.profile10292,MergedCutProfiles.Batch257.profile10293,MergedCutProfiles.Batch257.profile10294,MergedCutProfiles.Batch257.profile10295,MergedCutProfiles.Batch257.profile10296,MergedCutProfiles.Batch257.profile10297,MergedCutProfiles.Batch257.profile10298,MergedCutProfiles.Batch257.profile10299,MergedCutProfiles.Batch257.profile10300,MergedCutProfiles.Batch257.profile10301,MergedCutProfiles.Batch257.profile10302,MergedCutProfiles.Batch257.profile10303,MergedCutProfiles.Batch257.profile10304]⟩
theorem profilesValid1603 : retention1603.ProfilesValid := by
  change ∀ j : Fin 16, (retention1603.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch257.valid10289
  · exact MergedCutProfiles.Batch257.valid10290
  · exact MergedCutProfiles.Batch257.valid10291
  · exact MergedCutProfiles.Batch257.valid10292
  · exact MergedCutProfiles.Batch257.valid10293
  · exact MergedCutProfiles.Batch257.valid10294
  · exact MergedCutProfiles.Batch257.valid10295
  · exact MergedCutProfiles.Batch257.valid10296
  · exact MergedCutProfiles.Batch257.valid10297
  · exact MergedCutProfiles.Batch257.valid10298
  · exact MergedCutProfiles.Batch257.valid10299
  · exact MergedCutProfiles.Batch257.valid10300
  · exact MergedCutProfiles.Batch257.valid10301
  · exact MergedCutProfiles.Batch257.valid10302
  · exact MergedCutProfiles.Batch257.valid10303
  · exact MergedCutProfiles.Batch257.valid10304
theorem numericValid1603 : retention1603.NumericValid := by decide +kernel
def certificate1603 : RatCutBinCertificate := ⟨⟨retention1603,(473824445381424539/200000000000000000),(52706141081196361/250000000000000000),(16967775142051727919/1000000000000000000),(1433717631298357343/7812500000000000),(1637926507825552673/1000000000000000000)⟩,(247442534552934607/250000000000000000),(7061156918299739/20000000000000000),(279360052484093639/1000000000000000000),(155440704188461301/1000000000000000000)⟩
theorem valid1603 : certificate1603.Valid := by decide +kernel
theorem sound1603 : certificate1603.Sound := rat_cut_bin_certificate_sound certificate1603 profilesValid1603 numericValid1603 valid1603

def retention1604 : RatCutRetentionCertificate := ⟨(509/8000),(51/800),(3762042678733151539/10807074611510599692),(185612055216919927/100000000000000000),(29/20),(165338937771110567927/128000000000000000000),true,MergedCutProfiles.Batch257.profile10305,![MergedCutProfiles.Batch257.profile10305,MergedCutProfiles.Batch257.profile10306,MergedCutProfiles.Batch257.profile10307,MergedCutProfiles.Batch257.profile10308,MergedCutProfiles.Batch257.profile10309,MergedCutProfiles.Batch257.profile10310,MergedCutProfiles.Batch257.profile10311,MergedCutProfiles.Batch257.profile10312,MergedCutProfiles.Batch257.profile10313,MergedCutProfiles.Batch257.profile10314,MergedCutProfiles.Batch257.profile10315,MergedCutProfiles.Batch257.profile10316,MergedCutProfiles.Batch257.profile10317,MergedCutProfiles.Batch257.profile10318,MergedCutProfiles.Batch257.profile10319,MergedCutProfiles.Batch258.profile10320]⟩
theorem profilesValid1604 : retention1604.ProfilesValid := by
  change ∀ j : Fin 16, (retention1604.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch257.valid10305
  · exact MergedCutProfiles.Batch257.valid10306
  · exact MergedCutProfiles.Batch257.valid10307
  · exact MergedCutProfiles.Batch257.valid10308
  · exact MergedCutProfiles.Batch257.valid10309
  · exact MergedCutProfiles.Batch257.valid10310
  · exact MergedCutProfiles.Batch257.valid10311
  · exact MergedCutProfiles.Batch257.valid10312
  · exact MergedCutProfiles.Batch257.valid10313
  · exact MergedCutProfiles.Batch257.valid10314
  · exact MergedCutProfiles.Batch257.valid10315
  · exact MergedCutProfiles.Batch257.valid10316
  · exact MergedCutProfiles.Batch257.valid10317
  · exact MergedCutProfiles.Batch257.valid10318
  · exact MergedCutProfiles.Batch257.valid10319
  · exact MergedCutProfiles.Batch258.valid10320
theorem numericValid1604 : retention1604.NumericValid := by decide +kernel
def certificate1604 : RatCutBinCertificate := ⟨⟨retention1604,(473824445381424539/200000000000000000),(52706141081196361/250000000000000000),(16967775142051727919/1000000000000000000),(1433717631298357343/7812500000000000),(624504771226770713/500000000000000000)⟩,(247442534552934607/250000000000000000),(48991603609632581/125000000000000000),(240955769015683961/1000000000000000000),(155333451534696623/1000000000000000000)⟩
theorem valid1604 : certificate1604.Valid := by decide +kernel
theorem sound1604 : certificate1604.Sound := rat_cut_bin_certificate_sound certificate1604 profilesValid1604 numericValid1604 valid1604

def retention1605 : RatCutRetentionCertificate := ⟨(509/8000),(51/800),(5020460538580769465/10807074611510599692),(3762042678733151539/1000000000000000000),1,(261251544305345729059/256000000000000000000),true,MergedCutProfiles.Batch258.profile10321,![MergedCutProfiles.Batch258.profile10321,MergedCutProfiles.Batch258.profile10322,MergedCutProfiles.Batch257.profile10308,MergedCutProfiles.Batch258.profile10323,MergedCutProfiles.Batch258.profile10324,MergedCutProfiles.Batch257.profile10312,MergedCutProfiles.Batch258.profile10325,MergedCutProfiles.Batch258.profile10326,MergedCutProfiles.Batch257.profile10316,MergedCutProfiles.Batch258.profile10327,MergedCutProfiles.Batch258.profile10328,MergedCutProfiles.Batch258.profile10320,MergedCutProfiles.Batch258.profile10329,MergedCutProfiles.Batch258.profile10330,MergedCutProfiles.Batch258.profile10331,MergedCutProfiles.Batch258.profile10332]⟩
theorem profilesValid1605 : retention1605.ProfilesValid := by
  change ∀ j : Fin 16, (retention1605.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch258.valid10321
  · exact MergedCutProfiles.Batch258.valid10322
  · exact MergedCutProfiles.Batch257.valid10308
  · exact MergedCutProfiles.Batch258.valid10323
  · exact MergedCutProfiles.Batch258.valid10324
  · exact MergedCutProfiles.Batch257.valid10312
  · exact MergedCutProfiles.Batch258.valid10325
  · exact MergedCutProfiles.Batch258.valid10326
  · exact MergedCutProfiles.Batch257.valid10316
  · exact MergedCutProfiles.Batch258.valid10327
  · exact MergedCutProfiles.Batch258.valid10328
  · exact MergedCutProfiles.Batch258.valid10320
  · exact MergedCutProfiles.Batch258.valid10329
  · exact MergedCutProfiles.Batch258.valid10330
  · exact MergedCutProfiles.Batch258.valid10331
  · exact MergedCutProfiles.Batch258.valid10332
theorem numericValid1605 : retention1605.NumericValid := by decide +kernel
def certificate1605 : RatCutBinCertificate := ⟨⟨retention1605,(473824445381424539/200000000000000000),(52706141081196361/250000000000000000),(16967775142051727919/1000000000000000000),(1433717631298357343/7812500000000000),(39642740727541793/40000000000000000)⟩,(247442534552934607/250000000000000000),(86899491699598173/200000000000000000),(25415015951323453/125000000000000000),(315272843054989/2000000000000000)⟩
theorem valid1605 : certificate1605.Valid := by decide +kernel
theorem sound1605 : certificate1605.Sound := rat_cut_bin_certificate_sound certificate1605 profilesValid1605 numericValid1605 valid1605

def retention1606 : RatCutRetentionCertificate := ⟨(509/8000),(51/800),(5329320027000635977/10807074611510599692),(1004092107716153893/200000000000000000),(11/10),(80510396180815299518787971558154100831/80327368617292311440000000000000000000),false,MergedCutProfiles.Batch258.profile10333,(fun _ => MergedCutProfiles.Batch258.profile10333)⟩
theorem profilesValid1606 : retention1606.ProfilesValid := by
  exact MergedCutProfiles.Batch258.valid10333
theorem numericValid1606 : retention1606.NumericValid := by decide +kernel
def certificate1606 : RatCutBinCertificate := ⟨⟨retention1606,(473824445381424539/200000000000000000),(52706141081196361/250000000000000000),(16967775142051727919/1000000000000000000),(1433717631298357343/7812500000000000),(969891813199263217/1000000000000000000)⟩,(247442534552934607/250000000000000000),(429157218525387259/1000000000000000000),(207804433360278247/1000000000000000000),(39055151088554789/250000000000000000)⟩
theorem valid1606 : certificate1606.Valid := by decide +kernel
theorem sound1606 : certificate1606.Sound := rat_cut_bin_certificate_sound certificate1606 profilesValid1606 numericValid1606 valid1606

def retention1607 : RatCutRetentionCertificate := ⟨(509/8000),(51/800),(5382613227270642337/10807074611510599692),(5329320027000635977/1000000000000000000),(11/10),(2121140449698417457648424698892855630431/2131728010800254390800000000000000000000),false,MergedCutProfiles.Batch258.profile10334,(fun _ => MergedCutProfiles.Batch258.profile10334)⟩
theorem profilesValid1607 : retention1607.ProfilesValid := by
  exact MergedCutProfiles.Batch258.valid10334
theorem numericValid1607 : retention1607.NumericValid := by decide +kernel
def certificate1607 : RatCutBinCertificate := ⟨⟨retention1607,(473824445381424539/200000000000000000),(52706141081196361/250000000000000000),(16967775142051727919/1000000000000000000),(1433717631298357343/7812500000000000),(962647026326945511/1000000000000000000)⟩,(247442534552934607/250000000000000000),(214899399347702173/500000000000000000),(647694345276351/3125000000000000),(19506672120861381/125000000000000000)⟩
theorem valid1607 : certificate1607.Valid := by decide +kernel
theorem sound1607 : certificate1607.Sound := rat_cut_bin_certificate_sound certificate1607 profilesValid1607 numericValid1607 valid1607

def certificates : List RatCutBinCertificate := [certificate1596,certificate1597,certificate1598,certificate1599,certificate1600,certificate1601,certificate1602,certificate1603,certificate1604,certificate1605,certificate1606,certificate1607]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1596,List.forall_mem_cons.mpr ⟨sound1597,List.forall_mem_cons.mpr ⟨sound1598,List.forall_mem_cons.mpr ⟨sound1599,List.forall_mem_cons.mpr ⟨sound1600,List.forall_mem_cons.mpr ⟨sound1601,List.forall_mem_cons.mpr ⟨sound1602,List.forall_mem_cons.mpr ⟨sound1603,List.forall_mem_cons.mpr ⟨sound1604,List.forall_mem_cons.mpr ⟨sound1605,List.forall_mem_cons.mpr ⟨sound1606,List.forall_mem_cons.mpr ⟨sound1607,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch133
