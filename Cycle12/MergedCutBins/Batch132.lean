import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch255
import Cycle12.MergedCutProfiles.Batch256

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch132

def retention1584 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(1360144311000203527/2727356343157655291),(5386710142575063473/1000000000000000000),(11/10),(2142110940151609245005079761034175940831/2154684057030025389200000000000000000000),false,MergedCutProfiles.Batch255.profile10214,(fun _ => MergedCutProfiles.Batch255.profile10214)⟩
theorem profilesValid1584 : retention1584.ProfilesValid := by
  exact MergedCutProfiles.Batch255.valid10214
theorem numericValid1584 : retention1584.NumericValid := by decide +kernel
def certificate1584 : RatCutBinCertificate := ⟨⟨retention1584,(591057572332507563/250000000000000000),(2610492019033761/12500000000000000),(8423975412553280809/500000000000000000),(184089318713182580423/1000000000000000000),(60120130677555569/62500000000000000)⟩,(989785481598171047/1000000000000000000),(108077169832044933/250000000000000000),(41030021354951297/200000000000000000),(154580197936157611/1000000000000000000)⟩
theorem valid1584 : certificate1584.Valid := by decide +kernel
theorem sound1584 : certificate1584.Sound := rat_cut_bin_certificate_sound certificate1584 profilesValid1584 numericValid1584 valid1584

def retention1585 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(1/2),(1360144311000203527/250000000000000000),(11/10),(539708981380141483785038695505528215279/544057724400081410800000000000000000000),false,MergedCutProfiles.Batch255.profile10215,(fun _ => MergedCutProfiles.Batch255.profile10215)⟩
theorem profilesValid1585 : retention1585.ProfilesValid := by
  exact MergedCutProfiles.Batch255.valid10215
theorem numericValid1585 : retention1585.NumericValid := by decide +kernel
def certificate1585 : RatCutBinCertificate := ⟨⟨retention1585,(591057572332507563/250000000000000000),(2610492019033761/12500000000000000),(8423975412553280809/500000000000000000),(184089318713182580423/1000000000000000000),(59985264730716093/62500000000000000)⟩,(989785481598171047/1000000000000000000),(432852014554472391/1000000000000000000),(204694807226349849/1000000000000000000),(154132665926597487/1000000000000000000)⟩
theorem valid1585 : certificate1585.Valid := by decide +kernel
theorem sound1585 : certificate1585.Sound := rat_cut_bin_certificate_sound certificate1585 profilesValid1585 numericValid1585 valid1585

def retention1586 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(1/2),64,1,(255413409409974727036934562903428521431/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch255.profile10215,(fun _ => MergedCutProfiles.Batch255.profile10215)⟩
theorem profilesValid1586 : retention1586.ProfilesValid := by
  exact MergedCutProfiles.Batch255.valid10215
theorem numericValid1586 : retention1586.NumericValid := by decide +kernel
def certificate1586 : RatCutBinCertificate := ⟨⟨retention1586,(591057572332507563/250000000000000000),(2610492019033761/12500000000000000),(8423975412553280809/500000000000000000),(184089318713182580423/1000000000000000000),(242100553026553801/250000000000000000)⟩,(989785481598171047/1000000000000000000),(195060714083873581/500000000000000000),(242656541237167647/1000000000000000000),(114549284005876043/500000000000000000)⟩
theorem valid1586 : certificate1586.Valid := by decide +kernel
theorem sound1586 : certificate1586.Sound := rat_cut_bin_certificate_sound certificate1586 profilesValid1586 numericValid1586 valid1586

def retention1587 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(5076353611839720289/10909425372630621164),(3244068728965307713/1000000000000000000),(6/5),(42891244916751954081207719698254645127/40550859112066346412500000000000000000),false,MergedCutProfiles.Batch255.profile10216,(fun _ => MergedCutProfiles.Batch255.profile10216)⟩
theorem profilesValid1587 : retention1587.ProfilesValid := by
  exact MergedCutProfiles.Batch255.valid10216
theorem numericValid1587 : retention1587.NumericValid := by decide +kernel
def certificate1587 : RatCutBinCertificate := ⟨⟨retention1587,(669157276582507563/250000000000000000),(2610492019033761/12500000000000000),(8423975412553280809/500000000000000000),(184089318713182580423/1000000000000000000),(101788932505401697/100000000000000000)⟩,(988431710939418637/1000000000000000000),(391972452351345799/1000000000000000000),(240918659137371781/1000000000000000000),(82811286765735809/500000000000000000)⟩
theorem valid1587 : certificate1587.Valid := by decide +kernel
theorem sound1587 : certificate1587.Sound := rat_cut_bin_certificate_sound certificate1587 profilesValid1587 numericValid1587 valid1587

def retention1588 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(1347162912636007545/2727356343157655291),(5076353611839720289/1000000000000000000),(11/10),(2032882876731369023897617202101822296839/2030541444735888115600000000000000000000),false,MergedCutProfiles.Batch255.profile10217,(fun _ => MergedCutProfiles.Batch255.profile10217)⟩
theorem profilesValid1588 : retention1588.ProfilesValid := by
  exact MergedCutProfiles.Batch255.valid10217
theorem numericValid1588 : retention1588.NumericValid := by decide +kernel
def certificate1588 : RatCutBinCertificate := ⟨⟨retention1588,(669157276582507563/250000000000000000),(2610492019033761/12500000000000000),(8423975412553280809/500000000000000000),(184089318713182580423/1000000000000000000),(241162404591793397/250000000000000000)⟩,(988431710939418637/1000000000000000000),(413605694095463909/1000000000000000000),(221244863146243679/1000000000000000000),(82788492002755989/500000000000000000)⟩
theorem valid1588 : certificate1588.Valid := by decide +kernel
theorem sound1588 : certificate1588.Sound := rat_cut_bin_certificate_sound certificate1588 profilesValid1588 numericValid1588 valid1588

def retention1589 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(2721269083524735241/5454712686315310582),(269432582527201509/50000000000000000),(11/10),(5355415007789798506302050261841645311/5388651650544030180000000000000000000),false,MergedCutProfiles.Batch255.profile10218,(fun _ => MergedCutProfiles.Batch255.profile10218)⟩
theorem profilesValid1589 : retention1589.ProfilesValid := by
  exact MergedCutProfiles.Batch255.valid10218
theorem numericValid1589 : retention1589.NumericValid := by decide +kernel
def certificate1589 : RatCutBinCertificate := ⟨⟨retention1589,(669157276582507563/250000000000000000),(2610492019033761/12500000000000000),(8423975412553280809/500000000000000000),(184089318713182580423/1000000000000000000),(957329044897007003/1000000000000000000)⟩,(988431710939418637/1000000000000000000),(83353696848632319/200000000000000000),(218464763308495421/1000000000000000000),(163710537473621369/1000000000000000000)⟩
theorem valid1589 : certificate1589.Valid := by decide +kernel
theorem sound1589 : certificate1589.Sound := rat_cut_bin_certificate_sound certificate1589 profilesValid1589 numericValid1589 valid1589

def retention1590 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(1/2),(2721269083524735241/500000000000000000),(11/10),(134977469545364942826857862212863056781/136063454176236762050000000000000000000),false,MergedCutProfiles.Batch255.profile10215,(fun _ => MergedCutProfiles.Batch255.profile10215)⟩
theorem profilesValid1590 : retention1590.ProfilesValid := by
  exact MergedCutProfiles.Batch255.valid10215
theorem numericValid1590 : retention1590.NumericValid := by decide +kernel
def certificate1590 : RatCutBinCertificate := ⟨⟨retention1590,(669157276582507563/250000000000000000),(2610492019033761/12500000000000000),(8423975412553280809/500000000000000000),(184089318713182580423/1000000000000000000),(238878888213310587/250000000000000000)⟩,(988431710939418637/1000000000000000000),(208779738734906417/500000000000000000),(8710929455470211/40000000000000000),(163130477400640847/1000000000000000000)⟩
theorem valid1590 : certificate1590.Valid := by decide +kernel
theorem sound1590 : certificate1590.Sound := rat_cut_bin_certificate_sound certificate1590 profilesValid1590 numericValid1590 valid1590

def retention1591 : RatCutRetentionCertificate := ⟨(127/2000),(509/8000),(286527918372233296/2171618229430897931),(457767686730367713/500000000000000000),(5/2),(46387949879857574421/25600000000000000000),true,MergedCutProfiles.Batch255.profile10219,![MergedCutProfiles.Batch255.profile10219,MergedCutProfiles.Batch255.profile10220,MergedCutProfiles.Batch255.profile10221,MergedCutProfiles.Batch255.profile10222,MergedCutProfiles.Batch255.profile10223,MergedCutProfiles.Batch255.profile10224,MergedCutProfiles.Batch255.profile10225,MergedCutProfiles.Batch255.profile10226,MergedCutProfiles.Batch255.profile10227,MergedCutProfiles.Batch255.profile10228,MergedCutProfiles.Batch255.profile10229,MergedCutProfiles.Batch255.profile10230,MergedCutProfiles.Batch255.profile10231,MergedCutProfiles.Batch255.profile10232,MergedCutProfiles.Batch255.profile10233,MergedCutProfiles.Batch255.profile10234]⟩
theorem profilesValid1591 : retention1591.ProfilesValid := by
  change ∀ j : Fin 16, (retention1591.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch255.valid10219
  · exact MergedCutProfiles.Batch255.valid10220
  · exact MergedCutProfiles.Batch255.valid10221
  · exact MergedCutProfiles.Batch255.valid10222
  · exact MergedCutProfiles.Batch255.valid10223
  · exact MergedCutProfiles.Batch255.valid10224
  · exact MergedCutProfiles.Batch255.valid10225
  · exact MergedCutProfiles.Batch255.valid10226
  · exact MergedCutProfiles.Batch255.valid10227
  · exact MergedCutProfiles.Batch255.valid10228
  · exact MergedCutProfiles.Batch255.valid10229
  · exact MergedCutProfiles.Batch255.valid10230
  · exact MergedCutProfiles.Batch255.valid10231
  · exact MergedCutProfiles.Batch255.valid10232
  · exact MergedCutProfiles.Batch255.valid10233
  · exact MergedCutProfiles.Batch255.valid10234
theorem numericValid1591 : retention1591.NumericValid := by decide +kernel
def certificate1591 : RatCutBinCertificate := ⟨⟨retention1591,(589829448289107973/250000000000000000),(209830266746550371/1000000000000000000),(4231928338231689781/250000000000000000),(36789342620044720287/200000000000000000),(69555182819766403/40000000000000000)⟩,(61863994757145671/62500000000000000),(68203309750683571/200000000000000000),(292102084168024831/1000000000000000000),(76946248774494559/500000000000000000)⟩
theorem valid1591 : certificate1591.Valid := by decide +kernel
theorem sound1591 : certificate1591.Sound := rat_cut_bin_certificate_sound certificate1591 profilesValid1591 numericValid1591 valid1591

def retention1592 : RatCutRetentionCertificate := ⟨(127/2000),(509/8000),(3082355529144994572/10858091147154489655),(17907994898264581/12500000000000000),(7/4),(4599274062634221319/3200000000000000000),true,MergedCutProfiles.Batch255.profile10235,![MergedCutProfiles.Batch255.profile10235,MergedCutProfiles.Batch255.profile10236,MergedCutProfiles.Batch255.profile10237,MergedCutProfiles.Batch255.profile10238,MergedCutProfiles.Batch255.profile10239,MergedCutProfiles.Batch256.profile10240,MergedCutProfiles.Batch256.profile10241,MergedCutProfiles.Batch256.profile10242,MergedCutProfiles.Batch256.profile10243,MergedCutProfiles.Batch256.profile10244,MergedCutProfiles.Batch256.profile10245,MergedCutProfiles.Batch256.profile10246,MergedCutProfiles.Batch256.profile10247,MergedCutProfiles.Batch256.profile10248,MergedCutProfiles.Batch256.profile10249,MergedCutProfiles.Batch256.profile10250]⟩
theorem profilesValid1592 : retention1592.ProfilesValid := by
  change ∀ j : Fin 16, (retention1592.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch255.valid10235
  · exact MergedCutProfiles.Batch255.valid10236
  · exact MergedCutProfiles.Batch255.valid10237
  · exact MergedCutProfiles.Batch255.valid10238
  · exact MergedCutProfiles.Batch255.valid10239
  · exact MergedCutProfiles.Batch256.valid10240
  · exact MergedCutProfiles.Batch256.valid10241
  · exact MergedCutProfiles.Batch256.valid10242
  · exact MergedCutProfiles.Batch256.valid10243
  · exact MergedCutProfiles.Batch256.valid10244
  · exact MergedCutProfiles.Batch256.valid10245
  · exact MergedCutProfiles.Batch256.valid10246
  · exact MergedCutProfiles.Batch256.valid10247
  · exact MergedCutProfiles.Batch256.valid10248
  · exact MergedCutProfiles.Batch256.valid10249
  · exact MergedCutProfiles.Batch256.valid10250
theorem numericValid1592 : retention1592.NumericValid := by decide +kernel
def certificate1592 : RatCutBinCertificate := ⟨⟨retention1592,(589829448289107973/250000000000000000),(209830266746550371/1000000000000000000),(4231928338231689781/250000000000000000),(36789342620044720287/200000000000000000),(1386070560122644631/1000000000000000000)⟩,(61863994757145671/62500000000000000),(186058727594682219/500000000000000000),(2600243437217473/10000000000000000),(3092065160024179/20000000000000000)⟩
theorem valid1592 : certificate1592.Valid := by decide +kernel
theorem sound1592 : certificate1592.Sound := rat_cut_bin_certificate_sound certificate1592 profilesValid1592 numericValid1592 valid1592

def retention1593 : RatCutRetentionCertificate := ⟨(127/2000),(509/8000),(4823303058791840059/10858091147154489655),(770588882286248643/250000000000000000),(11/10),(344331472291448050059/320000000000000000000),true,MergedCutProfiles.Batch256.profile10251,![MergedCutProfiles.Batch256.profile10251,MergedCutProfiles.Batch256.profile10252,MergedCutProfiles.Batch256.profile10253,MergedCutProfiles.Batch256.profile10254,MergedCutProfiles.Batch256.profile10255,MergedCutProfiles.Batch256.profile10256,MergedCutProfiles.Batch256.profile10257,MergedCutProfiles.Batch256.profile10258,MergedCutProfiles.Batch256.profile10259,MergedCutProfiles.Batch256.profile10260,MergedCutProfiles.Batch256.profile10261,MergedCutProfiles.Batch256.profile10262,MergedCutProfiles.Batch256.profile10263,MergedCutProfiles.Batch256.profile10264,MergedCutProfiles.Batch256.profile10265,MergedCutProfiles.Batch256.profile10266]⟩
theorem profilesValid1593 : retention1593.ProfilesValid := by
  change ∀ j : Fin 16, (retention1593.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch256.valid10251
  · exact MergedCutProfiles.Batch256.valid10252
  · exact MergedCutProfiles.Batch256.valid10253
  · exact MergedCutProfiles.Batch256.valid10254
  · exact MergedCutProfiles.Batch256.valid10255
  · exact MergedCutProfiles.Batch256.valid10256
  · exact MergedCutProfiles.Batch256.valid10257
  · exact MergedCutProfiles.Batch256.valid10258
  · exact MergedCutProfiles.Batch256.valid10259
  · exact MergedCutProfiles.Batch256.valid10260
  · exact MergedCutProfiles.Batch256.valid10261
  · exact MergedCutProfiles.Batch256.valid10262
  · exact MergedCutProfiles.Batch256.valid10263
  · exact MergedCutProfiles.Batch256.valid10264
  · exact MergedCutProfiles.Batch256.valid10265
  · exact MergedCutProfiles.Batch256.valid10266
theorem numericValid1593 : retention1593.NumericValid := by decide +kernel
def certificate1593 : RatCutBinCertificate := ⟨⟨retention1593,(589829448289107973/250000000000000000),(209830266746550371/1000000000000000000),(4231928338231689781/250000000000000000),(36789342620044720287/200000000000000000),(1043855183138935551/1000000000000000000)⟩,(61863994757145671/62500000000000000),(424025512842179059/1000000000000000000),(106088108023092591/500000000000000000),(15547822955930187/100000000000000000)⟩
theorem valid1593 : certificate1593.Valid := by decide +kernel
theorem sound1593 : certificate1593.Sound := rat_cut_bin_certificate_sound certificate1593 profilesValid1593 numericValid1593 valid1593

def retention1594 : RatCutRetentionCertificate := ⟨(127/2000),(509/8000),(5327927276305006276/10858091147154489655),(4823303058791840059/1000000000000000000),(11/10),(1939565398840213035538200777554464634239/1929321223516736023600000000000000000000),false,MergedCutProfiles.Batch256.profile10267,(fun _ => MergedCutProfiles.Batch256.profile10267)⟩
theorem profilesValid1594 : retention1594.ProfilesValid := by
  exact MergedCutProfiles.Batch256.valid10267
theorem numericValid1594 : retention1594.NumericValid := by decide +kernel
def certificate1594 : RatCutBinCertificate := ⟨⟨retention1594,(589829448289107973/250000000000000000),(209830266746550371/1000000000000000000),(4231928338231689781/250000000000000000),(36789342620044720287/200000000000000000),(60820810564771403/62500000000000000)⟩,(61863994757145671/62500000000000000),(53909545698340747/125000000000000000),(12876064878857723/62500000000000000),(154454669343972331/1000000000000000000)⟩
theorem valid1594 : certificate1594.Valid := by decide +kernel
theorem sound1594 : certificate1594.Sound := rat_cut_bin_certificate_sound certificate1594 profilesValid1594 numericValid1594 valid1594

def retention1595 : RatCutRetentionCertificate := ⟨(127/2000),(509/8000),(5381206549068056339/10858091147154489655),(1331981819076251569/250000000000000000),(11/10),(16645691728767620500313119725312751183/16649772738453144612500000000000000000),false,MergedCutProfiles.Batch256.profile10268,(fun _ => MergedCutProfiles.Batch256.profile10268)⟩
theorem profilesValid1595 : retention1595.ProfilesValid := by
  exact MergedCutProfiles.Batch256.valid10268
theorem numericValid1595 : retention1595.NumericValid := by decide +kernel
def certificate1595 : RatCutBinCertificate := ⟨⟨retention1595,(589829448289107973/250000000000000000),(209830266746550371/1000000000000000000),(4231928338231689781/250000000000000000),(36789342620044720287/200000000000000000),(120947348100911373/125000000000000000)⟩,(61863994757145671/62500000000000000),(429777704767607651/1000000000000000000),(5182000079131303/25000000000000000),(156765753295756893/1000000000000000000)⟩
theorem valid1595 : certificate1595.Valid := by decide +kernel
theorem sound1595 : certificate1595.Sound := rat_cut_bin_certificate_sound certificate1595 profilesValid1595 numericValid1595 valid1595

def certificates : List RatCutBinCertificate := [certificate1584,certificate1585,certificate1586,certificate1587,certificate1588,certificate1589,certificate1590,certificate1591,certificate1592,certificate1593,certificate1594,certificate1595]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1584,List.forall_mem_cons.mpr ⟨sound1585,List.forall_mem_cons.mpr ⟨sound1586,List.forall_mem_cons.mpr ⟨sound1587,List.forall_mem_cons.mpr ⟨sound1588,List.forall_mem_cons.mpr ⟨sound1589,List.forall_mem_cons.mpr ⟨sound1590,List.forall_mem_cons.mpr ⟨sound1591,List.forall_mem_cons.mpr ⟨sound1592,List.forall_mem_cons.mpr ⟨sound1593,List.forall_mem_cons.mpr ⟨sound1594,List.forall_mem_cons.mpr ⟨sound1595,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch132
