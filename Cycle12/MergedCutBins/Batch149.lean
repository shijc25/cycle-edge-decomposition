import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch285
import Cycle12.MergedCutProfiles.Batch286

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch149

def retention1788 : RatCutRetentionCertificate := ⟨(131/2000),(21/320),(2336757767392168191/5039138065107057977),(1493316537816292213/500000000000000000),(5/4),(50927362670323614223864801371012376079/47786129210121350816000000000000000000),false,MergedCutProfiles.Batch285.profile11405,(fun _ => MergedCutProfiles.Batch285.profile11405)⟩
theorem profilesValid1788 : retention1788.ProfilesValid := by
  exact MergedCutProfiles.Batch285.valid11405
theorem numericValid1788 : retention1788.NumericValid := by decide +kernel
def certificate1788 : RatCutBinCertificate := ⟨⟨retention1788,(677273761815486283/250000000000000000),(45230715810772159/200000000000000000),(8793127356470729633/500000000000000000),(44344995454039285709/250000000000000000),(255543192687353699/250000000000000000)⟩,(494061227883225717/500000000000000000),(586117563314781/1562500000000000),(64268299176752867/250000000000000000),(34027377249726479/200000000000000000)⟩
theorem valid1788 : certificate1788.Valid := by decide +kernel
theorem sound1788 : certificate1788.Sound := rat_cut_bin_certificate_sound certificate1788 profilesValid1788 numericValid1788 valid1788

def retention1789 : RatCutRetentionCertificate := ⟨(131/2000),(21/320),(4961030914320381813/10078276130214115954),(2336757767392168191/500000000000000000),(11/10),(58478224888090168010411737197365857903/58418944184804204775000000000000000000),false,MergedCutProfiles.Batch285.profile11406,(fun _ => MergedCutProfiles.Batch285.profile11406)⟩
theorem profilesValid1789 : retention1789.ProfilesValid := by
  exact MergedCutProfiles.Batch285.valid11406
theorem numericValid1789 : retention1789.NumericValid := by decide +kernel
def certificate1789 : RatCutBinCertificate := ⟨⟨retention1789,(677273761815486283/250000000000000000),(45230715810772159/200000000000000000),(8793127356470729633/500000000000000000),(44344995454039285709/250000000000000000),(962683347265246751/1000000000000000000)⟩,(494061227883225717/500000000000000000),(199147822512664247/500000000000000000),(117523806407390221/500000000000000000),(34698434298650939/200000000000000000)⟩
theorem valid1789 : certificate1789.Valid := by decide +kernel
theorem sound1789 : certificate1789.Sound := rat_cut_bin_certificate_sound certificate1789 profilesValid1789 numericValid1789 valid1789

def retention1790 : RatCutRetentionCertificate := ⟨(131/2000),(21/320),(192716970133214832/387626005008235229),(4961030914320381813/1000000000000000000),(11/10),(179344021970433594887031254501451607261/180401124157104793200000000000000000000),false,MergedCutProfiles.Batch285.profile11407,(fun _ => MergedCutProfiles.Batch285.profile11407)⟩
theorem profilesValid1790 : retention1790.ProfilesValid := by
  exact MergedCutProfiles.Batch285.valid11407
theorem numericValid1790 : retention1790.NumericValid := by decide +kernel
def certificate1790 : RatCutBinCertificate := ⟨⟨retention1790,(677273761815486283/250000000000000000),(45230715810772159/200000000000000000),(8793127356470729633/500000000000000000),(44344995454039285709/250000000000000000),(95580941500334459/100000000000000000)⟩,(494061227883225717/500000000000000000),(200580041761155933/500000000000000000),(232421116375648649/1000000000000000000),(34391245342833659/200000000000000000)⟩
theorem valid1790 : certificate1790.Valid := by decide +kernel
theorem sound1790 : certificate1790.Sound := rat_cut_bin_certificate_sound certificate1790 profilesValid1790 numericValid1790 valid1790

def retention1791 : RatCutRetentionCertificate := ⟨(131/2000),(21/320),(1/2),(156582538233237051/31250000000000000),(11/10),(495622742253509037986543905898813967119/501064122346358563200000000000000000000),false,MergedCutProfiles.Batch285.profile11404,(fun _ => MergedCutProfiles.Batch285.profile11404)⟩
theorem profilesValid1791 : retention1791.ProfilesValid := by
  exact MergedCutProfiles.Batch285.valid11404
theorem numericValid1791 : retention1791.NumericValid := by decide +kernel
def certificate1791 : RatCutBinCertificate := ⟨⟨retention1791,(677273761815486283/250000000000000000),(45230715810772159/200000000000000000),(8793127356470729633/500000000000000000),(44344995454039285709/250000000000000000),(2377023967891247/2500000000000000)⟩,(494061227883225717/500000000000000000),(403269581978923141/1000000000000000000),(46099985780294721/200000000000000000),(169996363141139957/1000000000000000000)⟩
theorem valid1791 : certificate1791.Valid := by decide +kernel
theorem sound1791 : certificate1791.Sound := rat_cut_bin_certificate_sound certificate1791 profilesValid1791 numericValid1791 valid1791

def retention1792 : RatCutRetentionCertificate := ⟨(21/320),(263/4000),(1376738482141323233/10032012802675960868),(114441921153487039/125000000000000000),(49/20),(287452458408298811269/160000000000000000000),true,MergedCutProfiles.Batch285.profile11408,![MergedCutProfiles.Batch285.profile11408,MergedCutProfiles.Batch285.profile11409,MergedCutProfiles.Batch285.profile11410,MergedCutProfiles.Batch285.profile11411,MergedCutProfiles.Batch285.profile11412,MergedCutProfiles.Batch285.profile11413,MergedCutProfiles.Batch285.profile11414,MergedCutProfiles.Batch285.profile11415,MergedCutProfiles.Batch285.profile11416,MergedCutProfiles.Batch285.profile11417,MergedCutProfiles.Batch285.profile11418,MergedCutProfiles.Batch285.profile11419,MergedCutProfiles.Batch285.profile11420,MergedCutProfiles.Batch285.profile11421,MergedCutProfiles.Batch285.profile11422,MergedCutProfiles.Batch285.profile11423]⟩
theorem profilesValid1792 : retention1792.ProfilesValid := by
  change ∀ j : Fin 16, (retention1792.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch285.valid11408
  · exact MergedCutProfiles.Batch285.valid11409
  · exact MergedCutProfiles.Batch285.valid11410
  · exact MergedCutProfiles.Batch285.valid11411
  · exact MergedCutProfiles.Batch285.valid11412
  · exact MergedCutProfiles.Batch285.valid11413
  · exact MergedCutProfiles.Batch285.valid11414
  · exact MergedCutProfiles.Batch285.valid11415
  · exact MergedCutProfiles.Batch285.valid11416
  · exact MergedCutProfiles.Batch285.valid11417
  · exact MergedCutProfiles.Batch285.valid11418
  · exact MergedCutProfiles.Batch285.valid11419
  · exact MergedCutProfiles.Batch285.valid11420
  · exact MergedCutProfiles.Batch285.valid11421
  · exact MergedCutProfiles.Batch285.valid11422
  · exact MergedCutProfiles.Batch285.valid11423
theorem numericValid1792 : retention1792.NumericValid := by decide +kernel
def certificate1792 : RatCutBinCertificate := ⟨⟨retention1792,(2397985695522510043/1000000000000000000),(14200228663144707/62500000000000000),(8814343946614643429/500000000000000000),(35398377488915435619/200000000000000000),(860407492292457817/500000000000000000)⟩,(494740779456432851/500000000000000000),(333359347296219751/1000000000000000000),(300424722591464213/1000000000000000000),(158625585782026457/1000000000000000000)⟩
theorem valid1792 : certificate1792.Valid := by decide +kernel
theorem sound1792 : certificate1792.Sound := rat_cut_bin_certificate_sound certificate1792 profilesValid1792 numericValid1792 valid1792

def retention1793 : RatCutRetentionCertificate := ⟨(21/320),(263/4000),(2846503603730614039/10032012802675960868),(1376738482141323233/1000000000000000000),(17/10),(1832676474640072994813/1280000000000000000000),true,MergedCutProfiles.Batch285.profile11424,![MergedCutProfiles.Batch285.profile11424,MergedCutProfiles.Batch285.profile11425,MergedCutProfiles.Batch285.profile11426,MergedCutProfiles.Batch285.profile11427,MergedCutProfiles.Batch285.profile11428,MergedCutProfiles.Batch285.profile11429,MergedCutProfiles.Batch285.profile11430,MergedCutProfiles.Batch285.profile11431,MergedCutProfiles.Batch285.profile11432,MergedCutProfiles.Batch285.profile11433,MergedCutProfiles.Batch285.profile11434,MergedCutProfiles.Batch285.profile11435,MergedCutProfiles.Batch285.profile11436,MergedCutProfiles.Batch285.profile11437,MergedCutProfiles.Batch285.profile11438,MergedCutProfiles.Batch285.profile11439]⟩
theorem profilesValid1793 : retention1793.ProfilesValid := by
  change ∀ j : Fin 16, (retention1793.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch285.valid11424
  · exact MergedCutProfiles.Batch285.valid11425
  · exact MergedCutProfiles.Batch285.valid11426
  · exact MergedCutProfiles.Batch285.valid11427
  · exact MergedCutProfiles.Batch285.valid11428
  · exact MergedCutProfiles.Batch285.valid11429
  · exact MergedCutProfiles.Batch285.valid11430
  · exact MergedCutProfiles.Batch285.valid11431
  · exact MergedCutProfiles.Batch285.valid11432
  · exact MergedCutProfiles.Batch285.valid11433
  · exact MergedCutProfiles.Batch285.valid11434
  · exact MergedCutProfiles.Batch285.valid11435
  · exact MergedCutProfiles.Batch285.valid11436
  · exact MergedCutProfiles.Batch285.valid11437
  · exact MergedCutProfiles.Batch285.valid11438
  · exact MergedCutProfiles.Batch285.valid11439
theorem numericValid1793 : retention1793.NumericValid := by decide +kernel
def certificate1793 : RatCutBinCertificate := ⟨⟨retention1793,(2397985695522510043/1000000000000000000),(14200228663144707/62500000000000000),(8814343946614643429/500000000000000000),(35398377488915435619/200000000000000000),(172401198137618027/125000000000000000)⟩,(494740779456432851/500000000000000000),(365064431991635559/1000000000000000000),(267063147618325487/1000000000000000000),(15885038863307773/100000000000000000)⟩
theorem valid1793 : certificate1793.Valid := by decide +kernel
theorem sound1793 : certificate1793.Sound := rat_cut_bin_certificate_sound certificate1793 profilesValid1793 numericValid1793 valid1793

def retention1794 : RatCutRetentionCertificate := ⟨(21/320),(263/4000),(4410138050641961049/10032012802675960868),(2846503603730614039/1000000000000000000),(11/10),(1385465461448892258907/1280000000000000000000),true,MergedCutProfiles.Batch286.profile11440,![MergedCutProfiles.Batch286.profile11440,MergedCutProfiles.Batch286.profile11441,MergedCutProfiles.Batch286.profile11442,MergedCutProfiles.Batch286.profile11443,MergedCutProfiles.Batch286.profile11444,MergedCutProfiles.Batch286.profile11445,MergedCutProfiles.Batch286.profile11446,MergedCutProfiles.Batch286.profile11447,MergedCutProfiles.Batch286.profile11448,MergedCutProfiles.Batch286.profile11449,MergedCutProfiles.Batch286.profile11450,MergedCutProfiles.Batch286.profile11451,MergedCutProfiles.Batch286.profile11452,MergedCutProfiles.Batch286.profile11453,MergedCutProfiles.Batch286.profile11454,MergedCutProfiles.Batch286.profile11455]⟩
theorem profilesValid1794 : retention1794.ProfilesValid := by
  change ∀ j : Fin 16, (retention1794.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch286.valid11440
  · exact MergedCutProfiles.Batch286.valid11441
  · exact MergedCutProfiles.Batch286.valid11442
  · exact MergedCutProfiles.Batch286.valid11443
  · exact MergedCutProfiles.Batch286.valid11444
  · exact MergedCutProfiles.Batch286.valid11445
  · exact MergedCutProfiles.Batch286.valid11446
  · exact MergedCutProfiles.Batch286.valid11447
  · exact MergedCutProfiles.Batch286.valid11448
  · exact MergedCutProfiles.Batch286.valid11449
  · exact MergedCutProfiles.Batch286.valid11450
  · exact MergedCutProfiles.Batch286.valid11451
  · exact MergedCutProfiles.Batch286.valid11452
  · exact MergedCutProfiles.Batch286.valid11453
  · exact MergedCutProfiles.Batch286.valid11454
  · exact MergedCutProfiles.Batch286.valid11455
theorem numericValid1794 : retention1794.NumericValid := by decide +kernel
def certificate1794 : RatCutBinCertificate := ⟨⟨retention1794,(2397985695522510043/1000000000000000000),(14200228663144707/62500000000000000),(8814343946614643429/500000000000000000),(35398377488915435619/200000000000000000),(1048384422955948663/1000000000000000000)⟩,(494740779456432851/500000000000000000),(411679163450888313/1000000000000000000),(44590025030605693/200000000000000000),(160914217255422779/1000000000000000000)⟩
theorem valid1794 : certificate1794.Valid := by decide +kernel
theorem sound1794 : certificate1794.Sound := rat_cut_bin_certificate_sound certificate1794 profilesValid1794 numericValid1794 valid1794

def retention1795 : RatCutRetentionCertificate := ⟨(21/320),(263/4000),(2435768033428474645/5016006401337980434),(4410138050641961049/1000000000000000000),1,(251463647500955589849/256000000000000000000),true,MergedCutProfiles.Batch286.profile11456,![MergedCutProfiles.Batch286.profile11456,MergedCutProfiles.Batch286.profile11457,MergedCutProfiles.Batch286.profile11458,MergedCutProfiles.Batch286.profile11459,MergedCutProfiles.Batch286.profile11460,MergedCutProfiles.Batch286.profile11461,MergedCutProfiles.Batch286.profile11462,MergedCutProfiles.Batch286.profile11463,MergedCutProfiles.Batch286.profile11464,MergedCutProfiles.Batch286.profile11465,MergedCutProfiles.Batch286.profile11466,MergedCutProfiles.Batch286.profile11467,MergedCutProfiles.Batch286.profile11468,MergedCutProfiles.Batch286.profile11469,MergedCutProfiles.Batch286.profile11470,MergedCutProfiles.Batch286.profile11471]⟩
theorem profilesValid1795 : retention1795.ProfilesValid := by
  change ∀ j : Fin 16, (retention1795.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch286.valid11456
  · exact MergedCutProfiles.Batch286.valid11457
  · exact MergedCutProfiles.Batch286.valid11458
  · exact MergedCutProfiles.Batch286.valid11459
  · exact MergedCutProfiles.Batch286.valid11460
  · exact MergedCutProfiles.Batch286.valid11461
  · exact MergedCutProfiles.Batch286.valid11462
  · exact MergedCutProfiles.Batch286.valid11463
  · exact MergedCutProfiles.Batch286.valid11464
  · exact MergedCutProfiles.Batch286.valid11465
  · exact MergedCutProfiles.Batch286.valid11466
  · exact MergedCutProfiles.Batch286.valid11467
  · exact MergedCutProfiles.Batch286.valid11468
  · exact MergedCutProfiles.Batch286.valid11469
  · exact MergedCutProfiles.Batch286.valid11470
  · exact MergedCutProfiles.Batch286.valid11471
theorem numericValid1795 : retention1795.NumericValid := by decide +kernel
def certificate1795 : RatCutBinCertificate := ⟨⟨retention1795,(2397985695522510043/1000000000000000000),(14200228663144707/62500000000000000),(8814343946614643429/500000000000000000),(35398377488915435619/200000000000000000),(475682469834758781/500000000000000000)⟩,(494740779456432851/500000000000000000),(428561391364100091/1000000000000000000),(41661773205989649/200000000000000000),(6443503744799167/40000000000000000)⟩
theorem valid1795 : certificate1795.Valid := by decide +kernel
theorem sound1795 : certificate1795.Sound := rat_cut_bin_certificate_sound certificate1795 profilesValid1795 numericValid1795 valid1795

def retention1796 : RatCutRetentionCertificate := ⟨(21/320),(263/4000),(4969453941800773971/10032012802675960868),(487153606685694929/100000000000000000),(11/10),(971254195806642408938738467278303097/974307213371389858000000000000000000),false,MergedCutProfiles.Batch286.profile11472,(fun _ => MergedCutProfiles.Batch286.profile11472)⟩
theorem profilesValid1796 : retention1796.ProfilesValid := by
  exact MergedCutProfiles.Batch286.valid11472
theorem numericValid1796 : retention1796.NumericValid := by decide +kernel
def certificate1796 : RatCutBinCertificate := ⟨⟨retention1796,(2397985695522510043/1000000000000000000),(14200228663144707/62500000000000000),(8814343946614643429/500000000000000000),(35398377488915435619/200000000000000000),(481430899166739067/500000000000000000)⟩,(494740779456432851/500000000000000000),(419168099507550723/1000000000000000000),(216371514141600821/1000000000000000000),(8045492462973859/50000000000000000)⟩
theorem valid1796 : certificate1796.Valid := by decide +kernel
theorem sound1796 : certificate1796.Sound := rat_cut_bin_certificate_sound certificate1796 profilesValid1796 numericValid1796 valid1796

def retention1797 : RatCutRetentionCertificate := ⟨(21/320),(263/4000),(1/2),(4969453941800773971/1000000000000000000),(11/10),(1965576567338931789143090601035213817839/1987781576720309588400000000000000000000),false,MergedCutProfiles.Batch286.profile11473,(fun _ => MergedCutProfiles.Batch286.profile11473)⟩
theorem profilesValid1797 : retention1797.ProfilesValid := by
  exact MergedCutProfiles.Batch286.valid11473
theorem numericValid1797 : retention1797.NumericValid := by decide +kernel
def certificate1797 : RatCutBinCertificate := ⟨⟨retention1797,(2397985695522510043/1000000000000000000),(14200228663144707/62500000000000000),(8814343946614643429/500000000000000000),(35398377488915435619/200000000000000000),(47741236811798861/50000000000000000)⟩,(494740779456432851/500000000000000000),(105471061682302071/250000000000000000),(107009355725848259/500000000000000000),(158454861182154599/1000000000000000000)⟩
theorem valid1797 : certificate1797.Valid := by decide +kernel
theorem sound1797 : certificate1797.Sound := rat_cut_bin_certificate_sound certificate1797 profilesValid1797 numericValid1797 valid1797

def retention1798 : RatCutRetentionCertificate := ⟨(21/320),(263/4000),(1/2),64,1,(255417458333343694933422132900306791559/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch286.profile11473,(fun _ => MergedCutProfiles.Batch286.profile11473)⟩
theorem profilesValid1798 : retention1798.ProfilesValid := by
  exact MergedCutProfiles.Batch286.valid11473
theorem numericValid1798 : retention1798.NumericValid := by decide +kernel
def certificate1798 : RatCutBinCertificate := ⟨⟨retention1798,(2397985695522510043/1000000000000000000),(14200228663144707/62500000000000000),(8814343946614643429/500000000000000000),(35398377488915435619/200000000000000000),(96681788937686709/100000000000000000)⟩,(494740779456432851/500000000000000000),(47480787296261607/125000000000000000),(63116091562792819/250000000000000000),(118949906380864129/500000000000000000)⟩
theorem valid1798 : certificate1798.Valid := by decide +kernel
theorem sound1798 : certificate1798.Sound := rat_cut_bin_certificate_sound certificate1798 profilesValid1798 numericValid1798 valid1798

def retention1799 : RatCutRetentionCertificate := ⟨(21/320),(263/4000),(4650575479082364093/10032012802675960868),(742993280068030593/250000000000000000),(5/4),(791861915305827798705235255995217781/742993280068030593000000000000000000),false,MergedCutProfiles.Batch286.profile11474,(fun _ => MergedCutProfiles.Batch286.profile11474)⟩
theorem profilesValid1799 : retention1799.ProfilesValid := by
  exact MergedCutProfiles.Batch286.valid11474
theorem numericValid1799 : retention1799.NumericValid := by decide +kernel
def certificate1799 : RatCutBinCertificate := ⟨⟨retention1799,(2710793315522510043/1000000000000000000),(14200228663144707/62500000000000000),(8814343946614643429/500000000000000000),(35398377488915435619/200000000000000000),(1022085690808636347/1000000000000000000)⟩,(988104704045018349/1000000000000000000),(373897931278835023/1000000000000000000),(6456716757753871/25000000000000000),(170759858404195691/1000000000000000000)⟩
theorem valid1799 : certificate1799.Valid := by decide +kernel
theorem sound1799 : certificate1799.Sound := rat_cut_bin_certificate_sound certificate1799 profilesValid1799 numericValid1799 valid1799

def certificates : List RatCutBinCertificate := [certificate1788,certificate1789,certificate1790,certificate1791,certificate1792,certificate1793,certificate1794,certificate1795,certificate1796,certificate1797,certificate1798,certificate1799]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1788,List.forall_mem_cons.mpr ⟨sound1789,List.forall_mem_cons.mpr ⟨sound1790,List.forall_mem_cons.mpr ⟨sound1791,List.forall_mem_cons.mpr ⟨sound1792,List.forall_mem_cons.mpr ⟨sound1793,List.forall_mem_cons.mpr ⟨sound1794,List.forall_mem_cons.mpr ⟨sound1795,List.forall_mem_cons.mpr ⟨sound1796,List.forall_mem_cons.mpr ⟨sound1797,List.forall_mem_cons.mpr ⟨sound1798,List.forall_mem_cons.mpr ⟨sound1799,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch149
