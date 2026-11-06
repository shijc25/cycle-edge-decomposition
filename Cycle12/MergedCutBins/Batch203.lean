import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch378
import Cycle12.MergedCutProfiles.Batch379
import Cycle12.MergedCutProfiles.Batch380

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch203

def retention2436 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(975526256654613943/34872198057386390293),(214289609082661541/250000000000000000),3,(8620736100737274999/4000000000000000000),true,MergedCutProfiles.Batch378.profile15146,![MergedCutProfiles.Batch378.profile15146,MergedCutProfiles.Batch378.profile15147,MergedCutProfiles.Batch378.profile15148,MergedCutProfiles.Batch378.profile15149,MergedCutProfiles.Batch378.profile15150,MergedCutProfiles.Batch378.profile15151,MergedCutProfiles.Batch378.profile15152,MergedCutProfiles.Batch378.profile15153,MergedCutProfiles.Batch378.profile15154,MergedCutProfiles.Batch378.profile15155,MergedCutProfiles.Batch378.profile15156,MergedCutProfiles.Batch378.profile15157,MergedCutProfiles.Batch378.profile15158,MergedCutProfiles.Batch378.profile15159,MergedCutProfiles.Batch379.profile15160,MergedCutProfiles.Batch379.profile15161]⟩
theorem profilesValid2436 : retention2436.ProfilesValid := by
  change ∀ j : Fin 16, (retention2436.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch378.valid15146
  · exact MergedCutProfiles.Batch378.valid15147
  · exact MergedCutProfiles.Batch378.valid15148
  · exact MergedCutProfiles.Batch378.valid15149
  · exact MergedCutProfiles.Batch378.valid15150
  · exact MergedCutProfiles.Batch378.valid15151
  · exact MergedCutProfiles.Batch378.valid15152
  · exact MergedCutProfiles.Batch378.valid15153
  · exact MergedCutProfiles.Batch378.valid15154
  · exact MergedCutProfiles.Batch378.valid15155
  · exact MergedCutProfiles.Batch378.valid15156
  · exact MergedCutProfiles.Batch378.valid15157
  · exact MergedCutProfiles.Batch378.valid15158
  · exact MergedCutProfiles.Batch378.valid15159
  · exact MergedCutProfiles.Batch379.valid15160
  · exact MergedCutProfiles.Batch379.valid15161
theorem numericValid2436 : retention2436.NumericValid := by decide +kernel
def certificate2436 : RatCutBinCertificate := ⟨⟨retention2436,(1084425237518221649/500000000000000000),(65444215677591123/500000000000000000),(13547344760210798237/1000000000000000000),(237582768369219431269/500000000000000000),(130769617476026727/62500000000000000)⟩,(249001217545662629/250000000000000000),(178064331222038729/500000000000000000),(6904417907191449/25000000000000000),(150805042836339447/1000000000000000000)⟩
theorem valid2436 : certificate2436.Valid := by decide +kernel
theorem sound2436 : certificate2436.Sound := rat_cut_bin_certificate_sound certificate2436 profilesValid2436 numericValid2436 valid2436

def retention2437 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(1007884227000000000/34872198057386390293),(975526256654613943/1000000000000000000),(27/10),(171627414892229979777/80000000000000000000),true,MergedCutProfiles.Batch379.profile15162,![MergedCutProfiles.Batch379.profile15162,MergedCutProfiles.Batch379.profile15163,MergedCutProfiles.Batch379.profile15164,MergedCutProfiles.Batch379.profile15165,MergedCutProfiles.Batch379.profile15166,MergedCutProfiles.Batch379.profile15167,MergedCutProfiles.Batch379.profile15168,MergedCutProfiles.Batch379.profile15169,MergedCutProfiles.Batch379.profile15170,MergedCutProfiles.Batch379.profile15171,MergedCutProfiles.Batch379.profile15172,MergedCutProfiles.Batch379.profile15173,MergedCutProfiles.Batch379.profile15174,MergedCutProfiles.Batch379.profile15175,MergedCutProfiles.Batch379.profile15176,MergedCutProfiles.Batch379.profile15177]⟩
theorem profilesValid2437 : retention2437.ProfilesValid := by
  change ∀ j : Fin 16, (retention2437.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch379.valid15162
  · exact MergedCutProfiles.Batch379.valid15163
  · exact MergedCutProfiles.Batch379.valid15164
  · exact MergedCutProfiles.Batch379.valid15165
  · exact MergedCutProfiles.Batch379.valid15166
  · exact MergedCutProfiles.Batch379.valid15167
  · exact MergedCutProfiles.Batch379.valid15168
  · exact MergedCutProfiles.Batch379.valid15169
  · exact MergedCutProfiles.Batch379.valid15170
  · exact MergedCutProfiles.Batch379.valid15171
  · exact MergedCutProfiles.Batch379.valid15172
  · exact MergedCutProfiles.Batch379.valid15173
  · exact MergedCutProfiles.Batch379.valid15174
  · exact MergedCutProfiles.Batch379.valid15175
  · exact MergedCutProfiles.Batch379.valid15176
  · exact MergedCutProfiles.Batch379.valid15177
theorem numericValid2437 : retention2437.NumericValid := by decide +kernel
def certificate2437 : RatCutBinCertificate := ⟨⟨retention2437,(1084425237518221649/500000000000000000),(65444215677591123/500000000000000000),(13547344760210798237/1000000000000000000),(237582768369219431269/500000000000000000),(2088759698827433687/1000000000000000000)⟩,(249001217545662629/250000000000000000),(10543232483282779/31250000000000000),(296029292876835699/1000000000000000000),(88094520037653151/500000000000000000)⟩
theorem valid2437 : certificate2437.Valid := by decide +kernel
theorem sound2437 : certificate2437.Sound := rat_cut_bin_certificate_sound certificate2437 profilesValid2437 numericValid2437 valid2437

def retention2438 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(1251046083513270442/34872198057386390293),(1007884227/1000000000),(13/5),(33789869425566082413/16000000000000000000),true,MergedCutProfiles.Batch379.profile15178,![MergedCutProfiles.Batch379.profile15178,MergedCutProfiles.Batch379.profile15179,MergedCutProfiles.Batch379.profile15180,MergedCutProfiles.Batch379.profile15181,MergedCutProfiles.Batch379.profile15182,MergedCutProfiles.Batch379.profile15183,MergedCutProfiles.Batch378.profile15154,MergedCutProfiles.Batch379.profile15184,MergedCutProfiles.Batch379.profile15185,MergedCutProfiles.Batch379.profile15186,MergedCutProfiles.Batch378.profile15145,MergedCutProfiles.Batch379.profile15187,MergedCutProfiles.Batch379.profile15188,MergedCutProfiles.Batch379.profile15189,MergedCutProfiles.Batch379.profile15190,MergedCutProfiles.Batch379.profile15191]⟩
theorem profilesValid2438 : retention2438.ProfilesValid := by
  change ∀ j : Fin 16, (retention2438.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch379.valid15178
  · exact MergedCutProfiles.Batch379.valid15179
  · exact MergedCutProfiles.Batch379.valid15180
  · exact MergedCutProfiles.Batch379.valid15181
  · exact MergedCutProfiles.Batch379.valid15182
  · exact MergedCutProfiles.Batch379.valid15183
  · exact MergedCutProfiles.Batch378.valid15154
  · exact MergedCutProfiles.Batch379.valid15184
  · exact MergedCutProfiles.Batch379.valid15185
  · exact MergedCutProfiles.Batch379.valid15186
  · exact MergedCutProfiles.Batch378.valid15145
  · exact MergedCutProfiles.Batch379.valid15187
  · exact MergedCutProfiles.Batch379.valid15188
  · exact MergedCutProfiles.Batch379.valid15189
  · exact MergedCutProfiles.Batch379.valid15190
  · exact MergedCutProfiles.Batch379.valid15191
theorem numericValid2438 : retention2438.NumericValid := by decide +kernel
def certificate2438 : RatCutBinCertificate := ⟨⟨retention2438,(1084425237518221649/500000000000000000),(65444215677591123/500000000000000000),(13547344760210798237/1000000000000000000),(237582768369219431269/500000000000000000),(2057379488786422461/1000000000000000000)⟩,(249001217545662629/250000000000000000),(67592373771775877/200000000000000000),(59080287458111883/200000000000000000),(178694747744980797/1000000000000000000)⟩
theorem valid2438 : certificate2438.Valid := by decide +kernel
theorem sound2438 : certificate2438.Sound := rat_cut_bin_certificate_sound certificate2438 profilesValid2438 numericValid2438 valid2438

def retention2439 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(3813003213698563486/34872198057386390293),(625523041756635221/500000000000000000),(11/5),(1198283527386872535721/640000000000000000000),true,MergedCutProfiles.Batch379.profile15192,![MergedCutProfiles.Batch379.profile15192,MergedCutProfiles.Batch379.profile15193,MergedCutProfiles.Batch379.profile15194,MergedCutProfiles.Batch379.profile15195,MergedCutProfiles.Batch379.profile15196,MergedCutProfiles.Batch379.profile15197,MergedCutProfiles.Batch379.profile15198,MergedCutProfiles.Batch379.profile15199,MergedCutProfiles.Batch380.profile15200,MergedCutProfiles.Batch380.profile15201,MergedCutProfiles.Batch380.profile15202,MergedCutProfiles.Batch380.profile15203,MergedCutProfiles.Batch380.profile15204,MergedCutProfiles.Batch380.profile15205,MergedCutProfiles.Batch380.profile15206,MergedCutProfiles.Batch380.profile15207]⟩
theorem profilesValid2439 : retention2439.ProfilesValid := by
  change ∀ j : Fin 16, (retention2439.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch379.valid15192
  · exact MergedCutProfiles.Batch379.valid15193
  · exact MergedCutProfiles.Batch379.valid15194
  · exact MergedCutProfiles.Batch379.valid15195
  · exact MergedCutProfiles.Batch379.valid15196
  · exact MergedCutProfiles.Batch379.valid15197
  · exact MergedCutProfiles.Batch379.valid15198
  · exact MergedCutProfiles.Batch379.valid15199
  · exact MergedCutProfiles.Batch380.valid15200
  · exact MergedCutProfiles.Batch380.valid15201
  · exact MergedCutProfiles.Batch380.valid15202
  · exact MergedCutProfiles.Batch380.valid15203
  · exact MergedCutProfiles.Batch380.valid15204
  · exact MergedCutProfiles.Batch380.valid15205
  · exact MergedCutProfiles.Batch380.valid15206
  · exact MergedCutProfiles.Batch380.valid15207
theorem numericValid2439 : retention2439.NumericValid := by decide +kernel
def certificate2439 : RatCutBinCertificate := ⟨⟨retention2439,(1084425237518221649/500000000000000000),(65444215677591123/500000000000000000),(13547344760210798237/1000000000000000000),(237582768369219431269/500000000000000000),(228276695321066913/125000000000000000)⟩,(249001217545662629/250000000000000000),(350589325544502083/1000000000000000000),(281938349614980163/1000000000000000000),(35793745013169137/200000000000000000)⟩
theorem valid2439 : certificate2439.Valid := by decide +kernel
theorem sound2439 : certificate2439.Sound := rat_cut_bin_certificate_sound certificate2439 profilesValid2439 numericValid2439 valid2439

def retention2440 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(13627086588136731919/34872198057386390293),(1906501606849281743/500000000000000000),(6/5),(461431811050000342345312282435479840759/381300321369856348600000000000000000000),false,MergedCutProfiles.Batch380.profile15208,(fun _ => MergedCutProfiles.Batch380.profile15208)⟩
theorem profilesValid2440 : retention2440.ProfilesValid := by
  exact MergedCutProfiles.Batch380.valid15208
theorem numericValid2440 : retention2440.NumericValid := by decide +kernel
def certificate2440 : RatCutBinCertificate := ⟨⟨retention2440,(1084425237518221649/500000000000000000),(65444215677591123/500000000000000000),(13547344760210798237/1000000000000000000),(237582768369219431269/500000000000000000),(1185006339888950179/1000000000000000000)⟩,(249001217545662629/250000000000000000),(205440795421971829/500000000000000000),(55914682321948477/250000000000000000),(180855267731339999/1000000000000000000)⟩
theorem valid2440 : certificate2440.Valid := by decide +kernel
theorem sound2440 : certificate2440.Sound := rat_cut_bin_certificate_sound certificate2440 profilesValid2440 numericValid2440 valid2440

def retention2441 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(17131469306437384968/34872198057386390293),(13627086588136731919/1000000000000000000),1,(10901927324295692476656076498980375831/10901669270509385535200000000000000000),false,MergedCutProfiles.Batch380.profile15209,(fun _ => MergedCutProfiles.Batch380.profile15209)⟩
theorem profilesValid2441 : retention2441.ProfilesValid := by
  exact MergedCutProfiles.Batch380.valid15209
theorem numericValid2441 : retention2441.NumericValid := by decide +kernel
def certificate2441 : RatCutBinCertificate := ⟨⟨retention2441,(1084425237518221649/500000000000000000),(65444215677591123/500000000000000000),(13547344760210798237/1000000000000000000),(237582768369219431269/500000000000000000),(78325502154457/80000000000000)⟩,(249001217545662629/250000000000000000),(221111024750404203/500000000000000000),(196949539909782331/1000000000000000000),(17915367532512443/100000000000000000)⟩
theorem valid2441 : certificate2441.Valid := by decide +kernel
theorem sound2441 : certificate2441.Sound := rat_cut_bin_certificate_sound certificate2441 profilesValid2441 numericValid2441 valid2441

def retention2442 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(17302783999501758818/34872198057386390293),(2141433663304673121/125000000000000000),1,(13627827418558554918136029990987199747/13705175445149907974400000000000000000),false,MergedCutProfiles.Batch380.profile15210,(fun _ => MergedCutProfiles.Batch380.profile15210)⟩
theorem profilesValid2442 : retention2442.ProfilesValid := by
  exact MergedCutProfiles.Batch380.valid15210
theorem numericValid2442 : retention2442.NumericValid := by decide +kernel
def certificate2442 : RatCutBinCertificate := ⟨⟨retention2442,(1084425237518221649/500000000000000000),(65444215677591123/500000000000000000),(13547344760210798237/1000000000000000000),(237582768369219431269/500000000000000000),(486700741603817453/500000000000000000)⟩,(249001217545662629/250000000000000000),(44039336887606891/100000000000000000),(198445403740727901/1000000000000000000),(182027248237888029/1000000000000000000)⟩
theorem valid2442 : certificate2442.Valid := by decide +kernel
theorem sound2442 : certificate2442.Sound := rat_cut_bin_certificate_sound certificate2442 profilesValid2442 numericValid2442 valid2442

def retention2443 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(1/2),(8651391999750879409/500000000000000000),1,(3415792760452195329134591392449487407/3460556799900351763600000000000000000),false,MergedCutProfiles.Batch380.profile15211,(fun _ => MergedCutProfiles.Batch380.profile15211)⟩
theorem profilesValid2443 : retention2443.ProfilesValid := by
  exact MergedCutProfiles.Batch380.valid15211
theorem numericValid2443 : retention2443.NumericValid := by decide +kernel
def certificate2443 : RatCutBinCertificate := ⟨⟨retention2443,(1084425237518221649/500000000000000000),(65444215677591123/500000000000000000),(13547344760210798237/1000000000000000000),(237582768369219431269/500000000000000000),(966109693865992439/1000000000000000000)⟩,(249001217545662629/250000000000000000),(443546459859950573/1000000000000000000),(39174178531706377/200000000000000000),(178486250837410687/1000000000000000000)⟩
theorem valid2443 : certificate2443.Valid := by decide +kernel
theorem sound2443 : certificate2443.Sound := rat_cut_bin_certificate_sound certificate2443 profilesValid2443 numericValid2443 valid2443

def retention2444 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(15557412281586073540/34872198057386390293),(1354602112845585893/250000000000000000),(21/20),(583985463685600346054895175507231122551/541840845138234357200000000000000000000),false,MergedCutProfiles.Batch380.profile15212,(fun _ => MergedCutProfiles.Batch380.profile15212)⟩
theorem profilesValid2444 : retention2444.ProfilesValid := by
  exact MergedCutProfiles.Batch380.valid15212
theorem numericValid2444 : retention2444.NumericValid := by decide +kernel
def certificate2444 : RatCutBinCertificate := ⟨⟨retention2444,(1220843430518221649/500000000000000000),(65444215677591123/500000000000000000),(13547344760210798237/1000000000000000000),(237582768369219431269/500000000000000000),(263252304984817563/250000000000000000)⟩,(497750984234475721/500000000000000000),(113489319539287357/500000000000000000),(54535369604048939/125000000000000000),(46270126132267653/125000000000000000)⟩
theorem valid2444 : certificate2444.Valid := by decide +kernel
theorem sound2444 : certificate2444.Sound := rat_cut_bin_certificate_sound certificate2444 profilesValid2444 numericValid2444 valid2444

def retention2445 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(17185061820383985024/34872198057386390293),(777870614079303677/50000000000000000),1,(3887034112216714133177754333101897059/3889353070396518385000000000000000000),false,MergedCutProfiles.Batch380.profile15213,(fun _ => MergedCutProfiles.Batch380.profile15213)⟩
theorem profilesValid2445 : retention2445.ProfilesValid := by
  exact MergedCutProfiles.Batch380.valid15213
theorem numericValid2445 : retention2445.NumericValid := by decide +kernel
def certificate2445 : RatCutBinCertificate := ⟨⟨retention2445,(1220843430518221649/500000000000000000),(65444215677591123/500000000000000000),(13547344760210798237/1000000000000000000),(237582768369219431269/500000000000000000),(243953213841456331/250000000000000000)⟩,(497750984234475721/500000000000000000),(1530842968279787/6250000000000000),(410403251031494913/1000000000000000000),(375090849317313137/1000000000000000000)⟩
theorem valid2445 : certificate2445.Valid := by decide +kernel
theorem sound2445 : certificate2445.Sound := rat_cut_bin_certificate_sound certificate2445 profilesValid2445 numericValid2445 valid2445

def retention2446 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(17356912438587824875/34872198057386390293),(134258295471749883/7812500000000000),1,(68147860202388980680319324218694216543/68740247281535940096000000000000000000),false,MergedCutProfiles.Batch380.profile15214,(fun _ => MergedCutProfiles.Batch380.profile15214)⟩
theorem profilesValid2446 : retention2446.ProfilesValid := by
  exact MergedCutProfiles.Batch380.valid15214
theorem numericValid2446 : retention2446.NumericValid := by decide +kernel
def certificate2446 : RatCutBinCertificate := ⟨⟨retention2446,(1220843430518221649/500000000000000000),(65444215677591123/500000000000000000),(13547344760210798237/1000000000000000000),(237582768369219431269/500000000000000000),(967791365462658187/1000000000000000000)⟩,(497750984234475721/500000000000000000),(123482502638751453/500000000000000000),(81512117721303961/200000000000000000),(185838243314809737/500000000000000000)⟩
theorem valid2446 : certificate2446.Valid := by decide +kernel
theorem sound2446 : certificate2446.Sound := rat_cut_bin_certificate_sound certificate2446 profilesValid2446 numericValid2446 valid2446

def retention2447 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(1/2),(138855299508702599/8000000000000000),1,(17133176578841979979341977627543579049/17356912438587824875000000000000000000),false,MergedCutProfiles.Batch380.profile15211,(fun _ => MergedCutProfiles.Batch380.profile15211)⟩
theorem profilesValid2447 : retention2447.ProfilesValid := by
  exact MergedCutProfiles.Batch380.valid15211
theorem numericValid2447 : retention2447.NumericValid := by decide +kernel
def certificate2447 : RatCutBinCertificate := ⟨⟨retention2447,(1220843430518221649/500000000000000000),(65444215677591123/500000000000000000),(13547344760210798237/1000000000000000000),(237582768369219431269/500000000000000000),(24087970701945553/25000000000000000)⟩,(497750984234475721/500000000000000000),(124030061849347981/500000000000000000),(12688562586096821/31250000000000000),(368930765068157867/1000000000000000000)⟩
theorem valid2447 : certificate2447.Valid := by decide +kernel
theorem sound2447 : certificate2447.Sound := rat_cut_bin_certificate_sound certificate2447 profilesValid2447 numericValid2447 valid2447

def certificates : List RatCutBinCertificate := [certificate2436,certificate2437,certificate2438,certificate2439,certificate2440,certificate2441,certificate2442,certificate2443,certificate2444,certificate2445,certificate2446,certificate2447]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2436,List.forall_mem_cons.mpr ⟨sound2437,List.forall_mem_cons.mpr ⟨sound2438,List.forall_mem_cons.mpr ⟨sound2439,List.forall_mem_cons.mpr ⟨sound2440,List.forall_mem_cons.mpr ⟨sound2441,List.forall_mem_cons.mpr ⟨sound2442,List.forall_mem_cons.mpr ⟨sound2443,List.forall_mem_cons.mpr ⟨sound2444,List.forall_mem_cons.mpr ⟨sound2445,List.forall_mem_cons.mpr ⟨sound2446,List.forall_mem_cons.mpr ⟨sound2447,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch203
