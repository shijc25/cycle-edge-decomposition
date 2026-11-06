import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch103
import Cycle12.MergedCutProfiles.Batch104
import Cycle12.MergedCutProfiles.Batch105

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch052

def retention624 : RatCutRetentionCertificate := ⟨(7/160),(11/250),(223177401250000000/6369984013696635067),(817291728763740003/1000000000000000000),(31/10),(2712464834946768413247/1280000000000000000000),true,MergedCutProfiles.Batch104.profile4163,![MergedCutProfiles.Batch104.profile4163,MergedCutProfiles.Batch104.profile4164,MergedCutProfiles.Batch104.profile4165,MergedCutProfiles.Batch104.profile4166,MergedCutProfiles.Batch104.profile4167,MergedCutProfiles.Batch104.profile4168,MergedCutProfiles.Batch104.profile4169,MergedCutProfiles.Batch104.profile4170,MergedCutProfiles.Batch104.profile4171,MergedCutProfiles.Batch104.profile4172,MergedCutProfiles.Batch103.profile4158,MergedCutProfiles.Batch104.profile4173,MergedCutProfiles.Batch104.profile4174,MergedCutProfiles.Batch104.profile4175,MergedCutProfiles.Batch104.profile4176,MergedCutProfiles.Batch104.profile4177]⟩
theorem profilesValid624 : retention624.ProfilesValid := by
  change ∀ j : Fin 16, (retention624.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch104.valid4163
  · exact MergedCutProfiles.Batch104.valid4164
  · exact MergedCutProfiles.Batch104.valid4165
  · exact MergedCutProfiles.Batch104.valid4166
  · exact MergedCutProfiles.Batch104.valid4167
  · exact MergedCutProfiles.Batch104.valid4168
  · exact MergedCutProfiles.Batch104.valid4169
  · exact MergedCutProfiles.Batch104.valid4170
  · exact MergedCutProfiles.Batch104.valid4171
  · exact MergedCutProfiles.Batch104.valid4172
  · exact MergedCutProfiles.Batch103.valid4158
  · exact MergedCutProfiles.Batch104.valid4173
  · exact MergedCutProfiles.Batch104.valid4174
  · exact MergedCutProfiles.Batch104.valid4175
  · exact MergedCutProfiles.Batch104.valid4176
  · exact MergedCutProfiles.Batch104.valid4177
theorem numericValid624 : retention624.NumericValid := by decide +kernel
def certificate624 : RatCutBinCertificate := ⟨⟨retention624,(2102826811312011789/1000000000000000000),(5622540848385301/62500000000000000),(12034105757834079189/1000000000000000000),(38381348920839597449/125000000000000000),(2070376668142492227/1000000000000000000)⟩,(993756035613194971/1000000000000000000),(195547348792996467/500000000000000000),(7554427198518803/31250000000000000),(63415377615300527/500000000000000000)⟩
theorem valid624 : certificate624.Valid := by decide +kernel
theorem sound624 : certificate624.Sound := rat_cut_bin_certificate_sound certificate624 profilesValid624 numericValid624 valid624

def retention625 : RatCutRetentionCertificate := ⟨(7/160),(11/250),(479169413910566609/12739968027393270134),(178541921/200000000),(57/20),(33606833803064376511/16000000000000000000),true,MergedCutProfiles.Batch104.profile4178,![MergedCutProfiles.Batch104.profile4178,MergedCutProfiles.Batch104.profile4179,MergedCutProfiles.Batch104.profile4180,MergedCutProfiles.Batch104.profile4181,MergedCutProfiles.Batch104.profile4182,MergedCutProfiles.Batch104.profile4183,MergedCutProfiles.Batch104.profile4184,MergedCutProfiles.Batch104.profile4185,MergedCutProfiles.Batch104.profile4186,MergedCutProfiles.Batch104.profile4187,MergedCutProfiles.Batch104.profile4188,MergedCutProfiles.Batch104.profile4160,MergedCutProfiles.Batch104.profile4175,MergedCutProfiles.Batch104.profile4176,MergedCutProfiles.Batch104.profile4189,MergedCutProfiles.Batch104.profile4190]⟩
theorem profilesValid625 : retention625.ProfilesValid := by
  change ∀ j : Fin 16, (retention625.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch104.valid4178
  · exact MergedCutProfiles.Batch104.valid4179
  · exact MergedCutProfiles.Batch104.valid4180
  · exact MergedCutProfiles.Batch104.valid4181
  · exact MergedCutProfiles.Batch104.valid4182
  · exact MergedCutProfiles.Batch104.valid4183
  · exact MergedCutProfiles.Batch104.valid4184
  · exact MergedCutProfiles.Batch104.valid4185
  · exact MergedCutProfiles.Batch104.valid4186
  · exact MergedCutProfiles.Batch104.valid4187
  · exact MergedCutProfiles.Batch104.valid4188
  · exact MergedCutProfiles.Batch104.valid4160
  · exact MergedCutProfiles.Batch104.valid4175
  · exact MergedCutProfiles.Batch104.valid4176
  · exact MergedCutProfiles.Batch104.valid4189
  · exact MergedCutProfiles.Batch104.valid4190
theorem numericValid625 : retention625.NumericValid := by decide +kernel
def certificate625 : RatCutBinCertificate := ⟨⟨retention625,(2102826811312011789/1000000000000000000),(5622540848385301/62500000000000000),(12034105757834079189/1000000000000000000),(38381348920839597449/125000000000000000),(2055621011778793167/1000000000000000000)⟩,(993756035613194971/1000000000000000000),(379352167703487947/1000000000000000000),(252942964665353773/1000000000000000000),(141101727460188533/1000000000000000000)⟩
theorem valid625 : certificate625.Valid := by decide +kernel
theorem sound625 : certificate625.Sound := rat_cut_bin_certificate_sound certificate625 profilesValid625 numericValid625 valid625

def retention626 : RatCutRetentionCertificate := ⟨(7/160),(11/250),(397968919416658154/6369984013696635067),(479169413910566609/500000000000000000),(53/20),(321775167747395580259/160000000000000000000),true,MergedCutProfiles.Batch104.profile4191,![MergedCutProfiles.Batch104.profile4191,MergedCutProfiles.Batch104.profile4192,MergedCutProfiles.Batch104.profile4193,MergedCutProfiles.Batch104.profile4194,MergedCutProfiles.Batch104.profile4195,MergedCutProfiles.Batch104.profile4196,MergedCutProfiles.Batch104.profile4197,MergedCutProfiles.Batch104.profile4198,MergedCutProfiles.Batch104.profile4177,MergedCutProfiles.Batch104.profile4199,MergedCutProfiles.Batch105.profile4200,MergedCutProfiles.Batch105.profile4201,MergedCutProfiles.Batch105.profile4202,MergedCutProfiles.Batch105.profile4203,MergedCutProfiles.Batch105.profile4204,MergedCutProfiles.Batch105.profile4205]⟩
theorem profilesValid626 : retention626.ProfilesValid := by
  change ∀ j : Fin 16, (retention626.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch104.valid4191
  · exact MergedCutProfiles.Batch104.valid4192
  · exact MergedCutProfiles.Batch104.valid4193
  · exact MergedCutProfiles.Batch104.valid4194
  · exact MergedCutProfiles.Batch104.valid4195
  · exact MergedCutProfiles.Batch104.valid4196
  · exact MergedCutProfiles.Batch104.valid4197
  · exact MergedCutProfiles.Batch104.valid4198
  · exact MergedCutProfiles.Batch104.valid4177
  · exact MergedCutProfiles.Batch104.valid4199
  · exact MergedCutProfiles.Batch105.valid4200
  · exact MergedCutProfiles.Batch105.valid4201
  · exact MergedCutProfiles.Batch105.valid4202
  · exact MergedCutProfiles.Batch105.valid4203
  · exact MergedCutProfiles.Batch105.valid4204
  · exact MergedCutProfiles.Batch105.valid4205
theorem numericValid626 : retention626.NumericValid := by decide +kernel
def certificate626 : RatCutBinCertificate := ⟨⟨retention626,(2102826811312011789/1000000000000000000),(5622540848385301/62500000000000000),(12034105757834079189/1000000000000000000),(38381348920839597449/125000000000000000),(984716488278314573/500000000000000000)⟩,(993756035613194971/1000000000000000000),(384683226910720291/1000000000000000000),(247813268140614361/1000000000000000000),(17679125226258731/125000000000000000)⟩
theorem valid626 : certificate626.Valid := by decide +kernel
theorem sound626 : certificate626.Sound := rat_cut_bin_certificate_sound certificate626 profilesValid626 numericValid626 valid626

def retention627 : RatCutRetentionCertificate := ⟨(7/160),(11/250),(1465376158658091313/6369984013696635067),(198984459708329077/125000000000000000),(37/20),(3896273906185289695111718968292828209/2487305746354113462500000000000000000),false,MergedCutProfiles.Batch105.profile4206,(fun _ => MergedCutProfiles.Batch105.profile4206)⟩
theorem profilesValid627 : retention627.ProfilesValid := by
  exact MergedCutProfiles.Batch105.valid4206
theorem numericValid627 : retention627.NumericValid := by decide +kernel
def certificate627 : RatCutBinCertificate := ⟨⟨retention627,(2102826811312011789/1000000000000000000),(5622540848385301/62500000000000000),(12034105757834079189/1000000000000000000),(38381348920839597449/125000000000000000),(1537379390681895043/1000000000000000000)⟩,(993756035613194971/1000000000000000000),(414632856872887031/1000000000000000000),(11016967130854011/50000000000000000),(141782043571055281/1000000000000000000)⟩
theorem valid627 : certificate627.Valid := by decide +kernel
theorem sound627 : certificate627.Sound := rat_cut_bin_certificate_sound certificate627 profilesValid627 numericValid627 valid627

def retention628 : RatCutRetentionCertificate := ⟨(7/160),(11/250),(11530882055151454025/25479936054786540268),(1465376158658091313/250000000000000000),1,(67272150105817120273/64000000000000000000),true,MergedCutProfiles.Batch105.profile4207,![MergedCutProfiles.Batch105.profile4207,MergedCutProfiles.Batch105.profile4208,MergedCutProfiles.Batch105.profile4209,MergedCutProfiles.Batch105.profile4210,MergedCutProfiles.Batch105.profile4211,MergedCutProfiles.Batch105.profile4212,MergedCutProfiles.Batch105.profile4213,MergedCutProfiles.Batch105.profile4214,MergedCutProfiles.Batch105.profile4215,MergedCutProfiles.Batch105.profile4216,MergedCutProfiles.Batch105.profile4217,MergedCutProfiles.Batch105.profile4218,MergedCutProfiles.Batch105.profile4219,MergedCutProfiles.Batch105.profile4220,MergedCutProfiles.Batch105.profile4221,MergedCutProfiles.Batch105.profile4222]⟩
theorem profilesValid628 : retention628.ProfilesValid := by
  change ∀ j : Fin 16, (retention628.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch105.valid4207
  · exact MergedCutProfiles.Batch105.valid4208
  · exact MergedCutProfiles.Batch105.valid4209
  · exact MergedCutProfiles.Batch105.valid4210
  · exact MergedCutProfiles.Batch105.valid4211
  · exact MergedCutProfiles.Batch105.valid4212
  · exact MergedCutProfiles.Batch105.valid4213
  · exact MergedCutProfiles.Batch105.valid4214
  · exact MergedCutProfiles.Batch105.valid4215
  · exact MergedCutProfiles.Batch105.valid4216
  · exact MergedCutProfiles.Batch105.valid4217
  · exact MergedCutProfiles.Batch105.valid4218
  · exact MergedCutProfiles.Batch105.valid4219
  · exact MergedCutProfiles.Batch105.valid4220
  · exact MergedCutProfiles.Batch105.valid4221
  · exact MergedCutProfiles.Batch105.valid4222
theorem numericValid628 : retention628.NumericValid := by decide +kernel
def certificate628 : RatCutBinCertificate := ⟨⟨retention628,(2102826811312011789/1000000000000000000),(5622540848385301/62500000000000000),(12034105757834079189/1000000000000000000),(38381348920839597449/125000000000000000),(258851732741322923/250000000000000000)⟩,(993756035613194971/1000000000000000000),(487777451566142067/1000000000000000000),(40512244952742629/250000000000000000),(70816890044332331/500000000000000000)⟩
theorem valid628 : certificate628.Valid := by decide +kernel
theorem sound628 : certificate628.Sound := rat_cut_bin_certificate_sound certificate628 profilesValid628 numericValid628 valid628

def retention629 : RatCutRetentionCertificate := ⟨(7/160),(11/250),(6305577942389760917/12739968027393270134),(461235282206058161/40000000000000000),(21/20),(29742045668832365894266500438625964159/29519058061187722304000000000000000000),false,MergedCutProfiles.Batch105.profile4223,(fun _ => MergedCutProfiles.Batch105.profile4223)⟩
theorem profilesValid629 : retention629.ProfilesValid := by
  exact MergedCutProfiles.Batch105.valid4223
theorem numericValid629 : retention629.NumericValid := by decide +kernel
def certificate629 : RatCutBinCertificate := ⟨⟨retention629,(2102826811312011789/1000000000000000000),(5622540848385301/62500000000000000),(12034105757834079189/1000000000000000000),(38381348920839597449/125000000000000000),(991048012232007933/1000000000000000000)⟩,(993756035613194971/1000000000000000000),(97024082100879653/200000000000000000),(32792740282314071/200000000000000000),(35657655573960907/250000000000000000)⟩
theorem valid629 : certificate629.Valid := by decide +kernel
theorem sound629 : certificate629.Sound := rat_cut_bin_certificate_sound certificate629 profilesValid629 numericValid629 valid629

def retention630 : RatCutRetentionCertificate := ⟨(7/160),(11/250),(12737267443627317053/25479936054786540268),(6305577942389760917/500000000000000000),(21/20),(5039456133258362378276260875946749876071/5044462353911808733600000000000000000000),false,MergedCutProfiles.Batch105.profile4224,(fun _ => MergedCutProfiles.Batch105.profile4224)⟩
theorem profilesValid630 : retention630.ProfilesValid := by
  exact MergedCutProfiles.Batch105.valid4224
theorem numericValid630 : retention630.NumericValid := by decide +kernel
def certificate630 : RatCutBinCertificate := ⟨⟨retention630,(2102826811312011789/1000000000000000000),(5622540848385301/62500000000000000),(12034105757834079189/1000000000000000000),(38381348920839597449/125000000000000000),(982501605588466517/1000000000000000000)⟩,(993756035613194971/1000000000000000000),(487152532324840299/1000000000000000000),(32499601122268579/200000000000000000),(70547094643777023/500000000000000000)⟩
theorem valid630 : certificate630.Valid := by decide +kernel
theorem sound630 : certificate630.Sound := rat_cut_bin_certificate_sound certificate630 profilesValid630 numericValid630 valid630

def retention631 : RatCutRetentionCertificate := ⟨(7/160),(11/250),(1/2),(12737267443627317053/1000000000000000000),(21/20),(20357545672234327253095449400608902017751/20379627909803707284800000000000000000000),false,MergedCutProfiles.Batch105.profile4225,(fun _ => MergedCutProfiles.Batch105.profile4225)⟩
theorem profilesValid631 : retention631.ProfilesValid := by
  exact MergedCutProfiles.Batch105.valid4225
theorem numericValid631 : retention631.NumericValid := by decide +kernel
def certificate631 : RatCutBinCertificate := ⟨⟨retention631,(2102826811312011789/1000000000000000000),(5622540848385301/62500000000000000),(12034105757834079189/1000000000000000000),(38381348920839597449/125000000000000000),(491205241794583537/500000000000000000)⟩,(993756035613194971/1000000000000000000),(9739329725025019/20000000000000000),(813159204333253/5000000000000000),(14129081379786973/100000000000000000)⟩
theorem valid631 : certificate631.Valid := by decide +kernel
theorem sound631 : certificate631.Sound := rat_cut_bin_certificate_sound certificate631 profilesValid631 numericValid631 valid631

def retention632 : RatCutRetentionCertificate := ⟨(7/160),(11/250),(11303083046457493301/25479936054786540268),(468203268992639253/125000000000000000),(6/5),(414400086072406306696664213746582855919/374562615194111402400000000000000000000),false,MergedCutProfiles.Batch105.profile4226,(fun _ => MergedCutProfiles.Batch105.profile4226)⟩
theorem profilesValid632 : retention632.ProfilesValid := by
  exact MergedCutProfiles.Batch105.valid4226
theorem numericValid632 : retention632.NumericValid := by decide +kernel
def certificate632 : RatCutBinCertificate := ⟨⟨retention632,(2482909222312011789/1000000000000000000),(5622540848385301/62500000000000000),(12034105757834079189/1000000000000000000),(38381348920839597449/125000000000000000),(542041372246920483/500000000000000000)⟩,(992626638359231783/1000000000000000000),(373286620679053289/1000000000000000000),(258870508184494241/1000000000000000000),(193162438808379059/1000000000000000000)⟩
theorem valid632 : certificate632.Valid := by decide +kernel
theorem sound632 : certificate632.Sound := rat_cut_bin_certificate_sound certificate632 profilesValid632 numericValid632 valid632

def retention633 : RatCutRetentionCertificate := ⟨(7/160),(11/250),(12610491974662000993/25479936054786540268),(11303083046457493301/1000000000000000000),(21/20),(18216960464838420044562557763529282603079/18084932874331989281600000000000000000000),false,MergedCutProfiles.Batch105.profile4227,(fun _ => MergedCutProfiles.Batch105.profile4227)⟩
theorem profilesValid633 : retention633.ProfilesValid := by
  exact MergedCutProfiles.Batch105.valid4227
theorem numericValid633 : retention633.NumericValid := by decide +kernel
def certificate633 : RatCutBinCertificate := ⟨⟨retention633,(2482909222312011789/1000000000000000000),(5622540848385301/62500000000000000),(12034105757834079189/1000000000000000000),(38381348920839597449/125000000000000000),(987810966627879629/1000000000000000000)⟩,(992626638359231783/1000000000000000000),(81933405864084703/200000000000000000),(224740781484653921/1000000000000000000),(7776100351040681/40000000000000000)⟩
theorem valid633 : certificate633.Valid := by decide +kernel
theorem sound633 : certificate633.Sound := rat_cut_bin_certificate_sound certificate633 profilesValid633 numericValid633 valid633

def retention634 : RatCutRetentionCertificate := ⟨(7/160),(11/250),(12736596894408621003/25479936054786540268),(12610491974662000993/1000000000000000000),(21/20),(20157798541474242323890901749597229505431/20176787159459201588800000000000000000000),false,MergedCutProfiles.Batch105.profile4228,(fun _ => MergedCutProfiles.Batch105.profile4228)⟩
theorem profilesValid634 : retention634.ProfilesValid := by
  exact MergedCutProfiles.Batch105.valid4228
theorem numericValid634 : retention634.NumericValid := by decide +kernel
def certificate634 : RatCutBinCertificate := ⟨⟨retention634,(2482909222312011789/1000000000000000000),(5622540848385301/62500000000000000),(12034105757834079189/1000000000000000000),(38381348920839597449/125000000000000000),(12244618565906439/12500000000000000)⟩,(992626638359231783/1000000000000000000),(206556854982063741/500000000000000000),(221679486643347199/1000000000000000000),(19172494877855057/100000000000000000)⟩
theorem valid634 : certificate634.Valid := by decide +kernel
theorem sound634 : certificate634.Sound := rat_cut_bin_certificate_sound certificate634 profilesValid634 numericValid634 valid634

def retention635 : RatCutRetentionCertificate := ⟨(7/160),(11/250),(1/2),(12736596894408621003/1000000000000000000),(21/20),(20356461374305679343697481450653730640551/20378555031053793604800000000000000000000),false,MergedCutProfiles.Batch105.profile4225,(fun _ => MergedCutProfiles.Batch105.profile4225)⟩
theorem profilesValid635 : retention635.ProfilesValid := by
  exact MergedCutProfiles.Batch105.valid4225
theorem numericValid635 : retention635.NumericValid := by decide +kernel
def certificate635 : RatCutBinCertificate := ⟨⟨retention635,(2482909222312011789/1000000000000000000),(5622540848385301/62500000000000000),(12034105757834079189/1000000000000000000),(38381348920839597449/125000000000000000),(979426439528089039/1000000000000000000)⟩,(992626638359231783/1000000000000000000),(82634809087563701/200000000000000000),(221626154210963547/1000000000000000000),(95889040885270523/500000000000000000)⟩
theorem valid635 : certificate635.Valid := by decide +kernel
theorem sound635 : certificate635.Sound := rat_cut_bin_certificate_sound certificate635 profilesValid635 numericValid635 valid635

def certificates : List RatCutBinCertificate := [certificate624,certificate625,certificate626,certificate627,certificate628,certificate629,certificate630,certificate631,certificate632,certificate633,certificate634,certificate635]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound624,List.forall_mem_cons.mpr ⟨sound625,List.forall_mem_cons.mpr ⟨sound626,List.forall_mem_cons.mpr ⟨sound627,List.forall_mem_cons.mpr ⟨sound628,List.forall_mem_cons.mpr ⟨sound629,List.forall_mem_cons.mpr ⟨sound630,List.forall_mem_cons.mpr ⟨sound631,List.forall_mem_cons.mpr ⟨sound632,List.forall_mem_cons.mpr ⟨sound633,List.forall_mem_cons.mpr ⟨sound634,List.forall_mem_cons.mpr ⟨sound635,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch052
