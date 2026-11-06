import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs011

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch011

def certificate220 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs011.envelope220,(97933/50000),(26399/200000),(12821490825172820533/62500000000000000),(2215783199/1000000000),(11/5),(178104067/500000000),0,1,(1663414505955651/62500000000000000)⟩
theorem valid220 : certificate220.Valid := by
  refine ⟨MajorityCertificates.Inputs011.inputs_valid220,?_⟩
  decide +kernel
theorem sound220 : certificate220.Sound :=
  rat_witness_certificate_sound certificate220 valid220 MajorityCertificates.Inputs011.envelope_sound220

def certificate221 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs011.envelope221,(97933/50000),(26399/200000),(12821490825172820533/62500000000000000),(2548495257/1000000000),(11/5),(681651933/500000000),0,(141681074035090231/125000000000000000),(12549599567290579/500000000000000000)⟩
theorem valid221 : certificate221.Valid := by
  refine ⟨MajorityCertificates.Inputs011.inputs_valid221,?_⟩
  decide +kernel
theorem sound221 : certificate221.Sound :=
  rat_witness_certificate_sound certificate221 valid221 MajorityCertificates.Inputs011.envelope_sound221

def certificate222 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs011.envelope222,(195797/100000),(16449021/125000000),(204001344332391525971/1000000000000000000),(1109019419/500000000),(11/5),(22188157/62500000),0,1,(26814122963973243/1000000000000000000)⟩
theorem valid222 : certificate222.Valid := by
  refine ⟨MajorityCertificates.Inputs011.inputs_valid222,?_⟩
  decide +kernel
theorem sound222 : certificate222.Sound :=
  rat_witness_certificate_sound certificate222 valid222 MajorityCertificates.Inputs011.envelope_sound222

def certificate223 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs011.envelope223,(195797/100000),(16449021/125000000),(204001344332391525971/1000000000000000000),(1275535387/500000000),(11/5),(272729211/200000000),0,(566749598971556049/500000000000000000),(25252728792474909/1000000000000000000)⟩
theorem valid223 : certificate223.Valid := by
  refine ⟨MajorityCertificates.Inputs011.inputs_valid223,?_⟩
  decide +kernel
theorem sound223 : certificate223.Sound :=
  rat_witness_certificate_sound certificate223 valid223 MajorityCertificates.Inputs011.envelope_sound223

def certificate224 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs011.envelope224,(195729/100000),(16398667/125000000),(12679638681241212941/62500000000000000),(2222020411/1000000000),(11/5),(353685469/1000000000),0,1,(13516799924613263/500000000000000000)⟩
theorem valid224 : certificate224.Valid := by
  refine ⟨MajorityCertificates.Inputs011.inputs_valid224,?_⟩
  decide +kernel
theorem sound224 : certificate224.Sound :=
  rat_witness_certificate_sound certificate224 valid224 MajorityCertificates.Inputs011.envelope_sound224

def certificate225 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs011.envelope225,(195729/100000),(16398667/125000000),(12679638681241212941/62500000000000000),(255229737/100000000),(11/5),(682340817/500000000),0,(70846855201292757/62500000000000000),(25478828132664471/1000000000000000000)⟩
theorem valid225 : certificate225.Valid := by
  refine ⟨MajorityCertificates.Inputs011.inputs_valid225,?_⟩
  decide +kernel
theorem sound225 : certificate225.Sound :=
  rat_witness_certificate_sound certificate225 valid225 MajorityCertificates.Inputs011.envelope_sound225

def certificate226 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs011.envelope226,(39147/20000),(130947637/1000000000),(50655134347720589667/250000000000000000),(2222175689/1000000000),(11/5),(1411987/4000000),0,1,(27099958230213001/1000000000000000000)⟩
theorem valid226 : certificate226.Valid := by
  refine ⟨MajorityCertificates.Inputs011.inputs_valid226,?_⟩
  decide +kernel
theorem sound226 : certificate226.Sound :=
  rat_witness_certificate_sound certificate226 valid226 MajorityCertificates.Inputs011.envelope_sound226

def certificate227 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs011.envelope227,(39147/20000),(130947637/1000000000),(50655134347720589667/250000000000000000),(510909349/200000000),(11/5),(136402763/100000000),0,(566780093389300359/500000000000000000),(6373998954494737/250000000000000000)⟩
theorem valid227 : certificate227.Valid := by
  refine ⟨MajorityCertificates.Inputs011.inputs_valid227,?_⟩
  decide +kernel
theorem sound227 : certificate227.Sound :=
  rat_witness_certificate_sound certificate227 valid227 MajorityCertificates.Inputs011.envelope_sound227

def certificate228 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs011.envelope228,(195701/100000),(65352969/500000000),(40413199776386847259/200000000000000000),(1110804627/500000000),(11/5),(70487581/200000000),0,1,(27290145427084069/1000000000000000000)⟩
theorem valid228 : certificate228.Valid := by
  refine ⟨MajorityCertificates.Inputs011.inputs_valid228,?_⟩
  decide +kernel
theorem sound228 : certificate228.Sound :=
  rat_witness_certificate_sound certificate228 valid228 MajorityCertificates.Inputs011.envelope_sound228

def certificate229 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs011.envelope229,(195701/100000),(65352969/500000000),(40413199776386847259/200000000000000000),(2555900891/1000000000),(11/5),(1364206969/1000000000),0,(226717063659695799/200000000000000000),(6393488962020893/250000000000000000)⟩
theorem valid229 : certificate229.Valid := by
  refine ⟨MajorityCertificates.Inputs011.inputs_valid229,?_⟩
  decide +kernel
theorem sound229 : certificate229.Sound :=
  rat_witness_certificate_sound certificate229 valid229 MajorityCertificates.Inputs011.envelope_sound229

def certificate230 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs011.envelope230,(39119/20000),(65232119/500000000),(100332580072107007567/500000000000000000),(2227282547/1000000000),(11/5),(351453363/1000000000),0,1,(13693271250278519/500000000000000000)⟩
theorem valid230 : certificate230.Valid := by
  refine ⟨MajorityCertificates.Inputs011.inputs_valid230,?_⟩
  decide +kernel
theorem sound230 : certificate230.Sound :=
  rat_witness_certificate_sound certificate230 valid230 MajorityCertificates.Inputs011.envelope_sound230

def certificate231 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs011.envelope231,(39119/20000),(65232119/500000000),(100332580072107007567/500000000000000000),(2555947631/1000000000),(11/5),(683023027/500000000),0,(1133650323454992383/1000000000000000000),(25859479469644017/1000000000000000000)⟩
theorem valid231 : certificate231.Valid := by
  refine ⟨MajorityCertificates.Inputs011.inputs_valid231,?_⟩
  decide +kernel
theorem sound231 : certificate231.Sound :=
  rat_witness_certificate_sound certificate231 valid231 MajorityCertificates.Inputs011.envelope_sound231

def certificate232 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs011.envelope232,(195529/100000),(65030703/500000000),(19958276023943220001/100000000000000000),(444960103/200000000),(11/5),(175333537/500000000),0,1,(27771005950602637/1000000000000000000)⟩
theorem valid232 : certificate232.Valid := by
  refine ⟨MajorityCertificates.Inputs011.inputs_valid232,?_⟩
  decide +kernel
theorem sound232 : certificate232.Sound :=
  rat_witness_certificate_sound certificate232 valid232 MajorityCertificates.Inputs011.envelope_sound232

def certificate233 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs011.envelope233,(195529/100000),(65030703/500000000),(19958276023943220001/100000000000000000),(2558523227/1000000000),(11/5),(273275929/200000000),0,(45348018885807391/40000000000000000),(26013314557937917/1000000000000000000)⟩
theorem valid233 : certificate233.Valid := by
  refine ⟨MajorityCertificates.Inputs011.inputs_valid233,?_⟩
  decide +kernel
theorem sound233 : certificate233.Sound :=
  rat_witness_certificate_sound certificate233 valid233 MajorityCertificates.Inputs011.envelope_sound233

def certificate234 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs011.envelope234,(24433/12500),(64829287/500000000),(3970296207259030741/20000000000000000),(223022437/100000000),(9/4),(349205921/1000000000),0,1,(13940301166934373/500000000000000000)⟩
theorem valid234 : certificate234.Valid := by
  refine ⟨MajorityCertificates.Inputs011.inputs_valid234,?_⟩
  decide +kernel
theorem sound234 : certificate234.Sound :=
  rat_witness_certificate_sound certificate234 valid234 MajorityCertificates.Inputs011.envelope_sound234

def certificate235 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs011.envelope235,(24433/12500),(64829287/500000000),(3970296207259030741/20000000000000000),(640195219/250000000),(9/4),(1368810021/1000000000),0,(1133750487367235489/1000000000000000000),(6561071781341719/250000000000000000)⟩
theorem valid235 : certificate235.Valid := by
  refine ⟨MajorityCertificates.Inputs011.inputs_valid235,?_⟩
  decide +kernel
theorem sound235 : certificate235.Sound :=
  rat_witness_certificate_sound certificate235 valid235 MajorityCertificates.Inputs011.envelope_sound235

def certificate236 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs011.envelope236,(977/500),(64627871/500000000),(197461089196585477267/1000000000000000000),(2247933741/1000000000),(9/4),(346755627/1000000000),0,1,(27662162195154499/1000000000000000000)⟩
theorem valid236 : certificate236.Valid := by
  refine ⟨MajorityCertificates.Inputs011.inputs_valid236,?_⟩
  decide +kernel
theorem sound236 : certificate236.Sound :=
  rat_witness_certificate_sound certificate236 valid236 MajorityCertificates.Inputs011.envelope_sound236

def certificate237 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs011.envelope237,(977/500),(64627871/500000000),(197461089196585477267/1000000000000000000),(320425483/125000000),(9/4),(273824909/200000000),0,(113380036572545389/100000000000000000),(26395790366834957/1000000000000000000)⟩
theorem valid237 : certificate237.Valid := by
  refine ⟨MajorityCertificates.Inputs011.inputs_valid237,?_⟩
  decide +kernel
theorem sound237 : certificate237.Sound :=
  rat_witness_certificate_sound certificate237 valid237 MajorityCertificates.Inputs011.envelope_sound237

def certificate238 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs011.envelope238,(194289/100000),(5283/40000),(194800079243672712331/1000000000000000000),(274445929/125000000),(9/4),(11271929/31250000),0,1,(30116829065019949/1000000000000000000)⟩
theorem valid238 : certificate238.Valid := by
  refine ⟨MajorityCertificates.Inputs011.inputs_valid238,?_⟩
  decide +kernel
theorem sound238 : certificate238.Sound :=
  rat_witness_certificate_sound certificate238 valid238 MajorityCertificates.Inputs011.envelope_sound238

def certificate239 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs011.envelope239,(194289/100000),(5283/40000),(194800079243672712331/1000000000000000000),(641750451/250000000),(9/4),(686624361/500000000),0,(226794530419612341/200000000000000000),(13426106944505309/500000000000000000)⟩
theorem valid239 : certificate239.Valid := by
  refine ⟨MajorityCertificates.Inputs011.inputs_valid239,?_⟩
  decide +kernel
theorem sound239 : certificate239.Sound :=
  rat_witness_certificate_sound certificate239 valid239 MajorityCertificates.Inputs011.envelope_sound239

def certificates : List RatWitnessCertificate := [certificate220,certificate221,certificate222,certificate223,certificate224,certificate225,certificate226,certificate227,certificate228,certificate229,certificate230,certificate231,certificate232,certificate233,certificate234,certificate235,certificate236,certificate237,certificate238,certificate239]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound220,List.forall_mem_cons.mpr ⟨sound221,List.forall_mem_cons.mpr ⟨sound222,List.forall_mem_cons.mpr ⟨sound223,List.forall_mem_cons.mpr ⟨sound224,List.forall_mem_cons.mpr ⟨sound225,List.forall_mem_cons.mpr ⟨sound226,List.forall_mem_cons.mpr ⟨sound227,List.forall_mem_cons.mpr ⟨sound228,List.forall_mem_cons.mpr ⟨sound229,List.forall_mem_cons.mpr ⟨sound230,List.forall_mem_cons.mpr ⟨sound231,List.forall_mem_cons.mpr ⟨sound232,List.forall_mem_cons.mpr ⟨sound233,List.forall_mem_cons.mpr ⟨sound234,List.forall_mem_cons.mpr ⟨sound235,List.forall_mem_cons.mpr ⟨sound236,List.forall_mem_cons.mpr ⟨sound237,List.forall_mem_cons.mpr ⟨sound238,List.forall_mem_cons.mpr ⟨sound239,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch011
