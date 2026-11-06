import Cycle12.RationalDegreeEnvelope
import Cycle12.MomentCertificates.Batch000

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.DegreeCertificates.Batch000

def certificate0 : RatDegreeEnvelope := ⟨0,Cycle12.MomentCertificates.Batch000.certificate0.inputs,(47/20),(97087378640776699/40000000000000000),(22659999926297011/500000000000),(620226274770631/500000000000000000),(14054327340589968153/500000000000000000),(2481/4000000000000000),(33393/100000000000000000),4,58⟩
theorem valid0 : certificate0.NumericValid := by decide +kernel
theorem sound0 : certificate0.Sound := rat_degree_envelope_sound certificate0 Cycle12.MomentCertificates.Batch000.valid0.1 valid0

def certificate1 : RatDegreeEnvelope := ⟨1,Cycle12.MomentCertificates.Batch000.certificate1.inputs,(47/20),(97087378640776699/40000000000000000),(22659999981574252727111/250000000000000000),(620226274770631/500000000000000000),40,(1/200000000000000000),(1/1000000000000000000),4,48⟩
theorem valid1 : certificate1.NumericValid := by decide +kernel
theorem sound1 : certificate1.Sound := rat_degree_envelope_sound certificate1 Cycle12.MomentCertificates.Batch000.valid1.1 valid1

def certificate2 : RatDegreeEnvelope := ⟨2,Cycle12.MomentCertificates.Batch000.certificate2.inputs,(235759/100000),(1214348195990557559/500000000000000000),(6514935146107861847401/250000000000000000),(52561097602159/50000000000000000),(6848642841726226633/500000000000000000),(1125497178541/1000000000000000000),(39138855945598291/200000000000000000),4,49⟩
theorem valid2 : certificate2.NumericValid := by decide +kernel
theorem sound2 : certificate2.Sound := rat_degree_envelope_sound certificate2 Cycle12.MomentCertificates.Batch000.valid2.1 valid2

def certificate3 : RatDegreeEnvelope := ⟨3,Cycle12.MomentCertificates.Batch000.certificate3.inputs,(234359/100000),(485838384802634719/200000000000000000),(525086275949533264257/31250000000000000),(190786487160853/125000000000000000),(1282295885373257517/100000000000000000),(1349055237887/500000000000000000),(36851799628919687/125000000000000000),4,47⟩
theorem valid3 : certificate3.NumericValid := by decide +kernel
theorem sound3 : certificate3.Sound := rat_degree_envelope_sound certificate3 Cycle12.MomentCertificates.Batch000.valid3.1 valid3

def certificate4 : RatDegreeEnvelope := ⟨4,Cycle12.MomentCertificates.Batch000.certificate4.inputs,(46593/20000),(2429683322440734359/1000000000000000000),(11756323027834685309923/1000000000000000000),(522027583466699/250000000000000000),(12274249801348893393/1000000000000000000),(4670474892789/1000000000000000000),(295844731138597963/1000000000000000000),4,47⟩
theorem valid4 : certificate4.NumericValid := by decide +kernel
theorem sound4 : certificate4.Sound := rat_degree_envelope_sound certificate4 Cycle12.MomentCertificates.Batch000.valid4.1 valid4

def certificate5 : RatDegreeEnvelope := ⟨5,Cycle12.MomentCertificates.Batch000.certificate5.inputs,(115811/50000),(2430170638771211511/1000000000000000000),(8702706377686016146887/1000000000000000000),(2714335314427219/1000000000000000000),(11811031626022068373/1000000000000000000),(1855556351099/250000000000000000),(148149196561373557/500000000000000000),4,46⟩
theorem valid5 : certificate5.NumericValid := by decide +kernel
theorem sound5 : certificate5.Sound := rat_degree_envelope_sound certificate5 Cycle12.MomentCertificates.Batch000.valid5.1 valid5

def certificate6 : RatDegreeEnvelope := ⟨6,Cycle12.MomentCertificates.Batch000.certificate6.inputs,(115163/50000),(2430653923659804141/1000000000000000000),(839228398002528746119/125000000000000000),(424793501466913/125000000000000000),(11407960630974791741/1000000000000000000),(11106715517881/1000000000000000000),(59553957677643301/200000000000000000),4,46⟩
theorem valid6 : certificate6.NumericValid := by decide +kernel
theorem sound6 : certificate6.Sound := rat_degree_envelope_sound certificate6 Cycle12.MomentCertificates.Batch000.valid6.1 valid6

def certificate7 : RatDegreeEnvelope := ⟨7,Cycle12.MomentCertificates.Batch000.certificate7.inputs,(229071/100000),(2431133226927049103/1000000000000000000),(2672750682344156463489/500000000000000000),(4135868643407477/1000000000000000000),(11054145738753134881/1000000000000000000),(15821421599579/1000000000000000000),(2980473111863297/10000000000000000),5,45⟩
theorem valid7 : certificate7.NumericValid := by decide +kernel
theorem sound7 : certificate7.Sound := rat_degree_envelope_sound certificate7 Cycle12.MomentCertificates.Batch000.valid7.1 valid7

def certificate8 : RatDegreeEnvelope := ⟨8,Cycle12.MomentCertificates.Batch000.certificate8.inputs,(113927/50000),(2431608597575941747/1000000000000000000),(545419571159664462953/125000000000000000),(4922197493066899/1000000000000000000),(1342331422915861773/125000000000000000),(54225425657/2500000000000000),(148848747456034121/500000000000000000),5,45⟩
theorem valid8 : certificate8.NumericValid := by decide +kernel
theorem sound8 : certificate8.Sound := rat_degree_envelope_sound certificate8 Cycle12.MomentCertificates.Batch000.valid8.1 valid8

def certificate9 : RatDegreeEnvelope := ⟨9,Cycle12.MomentCertificates.Batch000.certificate9.inputs,(113337/50000),(486416016761727389/200000000000000000),(454272876767597821347/125000000000000000),(2876014678405491/500000000000000000),(326623865396275023/31250000000000000),(28891483562857/1000000000000000000),(298148640462006419/1000000000000000000),5,45⟩
theorem valid9 : certificate9.NumericValid := by decide +kernel
theorem sound9 : certificate9.Sound := rat_degree_envelope_sound certificate9 Cycle12.MomentCertificates.Batch000.valid9.1 valid9

def certificate10 : RatDegreeEnvelope := ⟨10,Cycle12.MomentCertificates.Batch000.certificate10.inputs,(225527/100000),(1216273866521371187/500000000000000000),(307769565671236112583/100000000000000000),(6622674018871219/1000000000000000000),(10191287531850874129/1000000000000000000),(9373894688323/250000000000000000),(297935260234355701/1000000000000000000),5,44⟩
theorem valid10 : certificate10.NumericValid := by decide +kernel
theorem sound10 : certificate10.Sound := rat_degree_envelope_sound certificate10 Cycle12.MomentCertificates.Batch000.valid10.1 valid10

def certificate11 : RatDegreeEnvelope := ⟨11,Cycle12.MomentCertificates.Batch000.certificate11.inputs,(224413/100000),(608252897981803907/250000000000000000),(660788289044395744131/250000000000000000),(7529160334089767/1000000000000000000),(621897621888013523/62500000000000000),(23855181017867/500000000000000000),(14920541072905829/50000000000000000),5,43⟩
theorem valid11 : certificate11.NumericValid := by decide +kernel
theorem sound11 : certificate11.Sound := rat_degree_envelope_sound certificate11 Cycle12.MomentCertificates.Batch000.valid11.1 valid11

def certificate12 : RatDegreeEnvelope := ⟨12,Cycle12.MomentCertificates.Batch000.certificate12.inputs,(223329/100000),(1216735853178938169/500000000000000000),(2297201253456370845709/1000000000000000000),(8469194258000419/1000000000000000000),(9727721832622030573/1000000000000000000),(7450992043013/125000000000000000),(298599596817732173/1000000000000000000),5,43⟩
theorem valid12 : certificate12.NumericValid := by decide +kernel
theorem sound12 : certificate12.Sound := rat_degree_envelope_sound certificate12 Cycle12.MomentCertificates.Batch000.valid12.1 valid12

def certificate13 : RatDegreeEnvelope := ⟨13,Cycle12.MomentCertificates.Batch000.certificate13.inputs,(111137/50000),(48678562429850883/20000000000000000),(252147263830554027219/125000000000000000),(2359840117666199/250000000000000000),(476021782997683791/50000000000000000),(73337707087691/1000000000000000000),(298783326833129313/1000000000000000000),5,42⟩
theorem valid13 : certificate13.NumericValid := by decide +kernel
theorem sound13 : certificate13.Sound := rat_degree_envelope_sound certificate13 Cycle12.MomentCertificates.Batch000.valid13.1 valid13

def certificate14 : RatDegreeEnvelope := ⟨14,Cycle12.MomentCertificates.Batch000.certificate14.inputs,(110623/50000),(1217190440882906519/500000000000000000),(893623095659599263587/500000000000000000),(5218738764941301/500000000000000000),(4663585490565599139/500000000000000000),(86888270851/976562500000000),(298573723457911153/1000000000000000000),5,43⟩
theorem valid14 : certificate14.NumericValid := by decide +kernel
theorem sound14 : certificate14.Sound := rat_degree_envelope_sound certificate14 Cycle12.MomentCertificates.Batch000.valid14.1 valid14

def certificate15 : RatDegreeEnvelope := ⟨15,Cycle12.MomentCertificates.Batch000.certificate15.inputs,(44049/20000),(486966006180694419/200000000000000000),(199508041444546027759/125000000000000000),(2864953974196993/250000000000000000),(9145301699532968487/1000000000000000000),(53360014741449/500000000000000000),(14928549311774671/50000000000000000),5,42⟩
theorem valid15 : certificate15.NumericValid := by decide +kernel
theorem sound15 : certificate15.Sound := rat_degree_envelope_sound certificate15 Cycle12.MomentCertificates.Batch000.valid15.1 valid15

def certificate16 : RatDegreeEnvelope := ⟨16,Cycle12.MomentCertificates.Batch000.certificate16.inputs,(21927/10000),(121763780596829133/50000000000000000),(179417096775373226307/125000000000000000),(125037652124703/10000000000000000),(1121694626591164493/125000000000000000),(63358328405869/500000000000000000),(298731926684488343/1000000000000000000),5,42⟩
theorem valid16 : certificate16.NumericValid := by decide +kernel
theorem sound16 : certificate16.Sound := rat_degree_envelope_sound certificate16 Cycle12.MomentCertificates.Batch000.valid16.1 valid16

def certificate17 : RatDegreeEnvelope := ⟨17,Cycle12.MomentCertificates.Batch000.certificate17.inputs,(2729/1250),(1217858833607610631/500000000000000000),(649440413585474310029/500000000000000000),(423967732017713/31250000000000000),(8810936935311330221/1000000000000000000),(149093499513253/1000000000000000000),(74745504579417517/250000000000000000),6,41⟩
theorem valid17 : certificate17.NumericValid := by decide +kernel
theorem sound17 : certificate17.Sound := rat_degree_envelope_sound certificate17 Cycle12.MomentCertificates.Batch000.valid17.1 valid17

def certificate18 : RatDegreeEnvelope := ⟨18,Cycle12.MomentCertificates.Batch000.certificate18.inputs,(217393/100000),(2436156238421897629/1000000000000000000),(1182011536263273450937/1000000000000000000),(585937892722741/40000000000000000),(2164329214787725633/250000000000000000),(173850146096561/1000000000000000000),(74706675857315771/250000000000000000),6,41⟩
theorem valid18 : certificate18.NumericValid := by decide +kernel
theorem sound18 : certificate18.Sound := rat_degree_envelope_sound certificate18 Cycle12.MomentCertificates.Batch000.valid18.1 valid18

def certificate19 : RatDegreeEnvelope := ⟨19,Cycle12.MomentCertificates.Batch000.certificate19.inputs,(8647/4000),(609147841646164169/250000000000000000),(135140731992612482481/125000000000000000),(16118796920995977/1000000000000000000),(1089153007371832303/125000000000000000),(164397372311823/1000000000000000000),(24924889731549323/125000000000000000),6,45⟩
theorem valid19 : certificate19.NumericValid := by decide +kernel
theorem sound19 : certificate19.Sound := rat_degree_envelope_sound certificate19 Cycle12.MomentCertificates.Batch000.valid19.1 valid19

def configurations : List RatDegreeEnvelope := [certificate0,certificate1,certificate2,certificate3,certificate4,certificate5,certificate6,certificate7,certificate8,certificate9,certificate10,certificate11,certificate12,certificate13,certificate14,certificate15,certificate16,certificate17,certificate18,certificate19]
theorem configurations_sound : ∀ c∈configurations, c.Sound := by
  intro c hc
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sound0
  · exact sound1
  · exact sound2
  · exact sound3
  · exact sound4
  · exact sound5
  · exact sound6
  · exact sound7
  · exact sound8
  · exact sound9
  · exact sound10
  · exact sound11
  · exact sound12
  · exact sound13
  · exact sound14
  · exact sound15
  · exact sound16
  · exact sound17
  · exact sound18
  · exact sound19

end Cycle12.DegreeCertificates.Batch000
