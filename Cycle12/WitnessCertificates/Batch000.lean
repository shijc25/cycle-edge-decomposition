import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs000

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch000

def certificate0 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs000.envelope0,(47/20),(28812461/200000000),(22659999926297011/500000000000),(178231873/100000000),(7/5),(19281647/50000000),0,1,(35401393350581/500000000000000000)⟩
theorem valid0 : certificate0.Valid := by
  refine ⟨MajorityCertificates.Inputs000.inputs_valid0,?_⟩
  decide +kernel
theorem sound0 : certificate0.Sound :=
  rat_witness_certificate_sound certificate0 valid0 MajorityCertificates.Inputs000.envelope_sound0

def certificate1 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs000.envelope1,(47/20),(28812461/200000000),(22659999926297011/500000000000),(1050346269/500000000),(7/5),(254192179/200000000),0,(562515845120066943/500000000000000000),(83003961671269/1000000000000000000)⟩
theorem valid1 : certificate1.Valid := by
  refine ⟨MajorityCertificates.Inputs000.inputs_valid1,?_⟩
  decide +kernel
theorem sound1 : certificate1.Sound :=
  rat_witness_certificate_sound certificate1 valid1 MajorityCertificates.Inputs000.envelope_sound1

def certificate2 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs000.envelope2,(47/20),(147875781/1000000000),(22659999981574252727111/250000000000000000),(350391857/200000000),2,(7999269/20000000),0,1,(607327306281/15625000000000000)⟩
theorem valid2 : certificate2.Valid := by
  refine ⟨MajorityCertificates.Inputs000.inputs_valid2,?_⟩
  decide +kernel
theorem sound2 : certificate2.Sound :=
  rat_witness_certificate_sound certificate2 valid2 MajorityCertificates.Inputs000.envelope_sound2

def certificate3 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs000.envelope3,(47/20),(147875781/1000000000),(22659999981574252727111/250000000000000000),(492589467/250000000),2,(1347438371/1000000000),0,(562507922473226449/500000000000000000),(9082938330563/1000000000000000000)⟩
theorem valid3 : certificate3.Valid := by
  refine ⟨MajorityCertificates.Inputs000.inputs_valid3,?_⟩
  decide +kernel
theorem sound3 : certificate3.Sound :=
  rat_witness_certificate_sound certificate3 valid3 MajorityCertificates.Inputs000.envelope_sound3

def certificate4 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs000.envelope4,(235759/100000),(137875781/1000000000),(6514935146107861847401/250000000000000000),(1795441441/1000000000),(29/20),(366618969/1000000000),0,1,(79939348740341/500000000000000000)⟩
theorem valid4 : certificate4.Valid := by
  refine ⟨MajorityCertificates.Inputs000.inputs_valid4,?_⟩
  decide +kernel
theorem sound4 : certificate4.Sound :=
  rat_witness_certificate_sound certificate4 valid4 MajorityCertificates.Inputs000.envelope_sound4

def certificate5 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs000.envelope5,(235759/100000),(137875781/1000000000),(6514935146107861847401/250000000000000000),(2119162877/1000000000),(29/20),(1264105389/1000000000),0,(1125054935350837039/1000000000000000000),(194407288344551/1000000000000000000)⟩
theorem valid5 : certificate5.Valid := by
  refine ⟨MajorityCertificates.Inputs000.inputs_valid5,?_⟩
  decide +kernel
theorem sound5 : certificate5.Sound :=
  rat_witness_certificate_sound certificate5 valid5 MajorityCertificates.Inputs000.envelope_sound5

def certificate6 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs000.envelope6,(234359/100000),(138520313/1000000000),(525086275949533264257/31250000000000000),(903533439/500000000),(29/20),(92078913/250000000),0,1,(136503168553943/500000000000000000)⟩
theorem valid6 : certificate6.Valid := by
  refine ⟨MajorityCertificates.Inputs000.inputs_valid6,?_⟩
  decide +kernel
theorem sound6 : certificate6.Sound :=
  rat_witness_certificate_sound certificate6 valid6 MajorityCertificates.Inputs000.envelope_sound6

def certificate7 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs000.envelope7,(234359/100000),(138520313/1000000000),(525086275949533264257/31250000000000000),(2134164121/1000000000),(29/20),(1261875159/1000000000),0,(562542855565845857/500000000000000000),(224006804693287/1000000000000000000)⟩
theorem valid7 : certificate7.Valid := by
  refine ⟨MajorityCertificates.Inputs000.inputs_valid7,?_⟩
  decide +kernel
theorem sound7 : certificate7.Sound :=
  rat_witness_certificate_sound certificate7 valid7 MajorityCertificates.Inputs000.envelope_sound7

def certificate8 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs000.envelope8,(46593/20000),(34791211/250000000),(11756323027834685309923/1000000000000000000),(907864891/500000000),(29/20),(370375271/1000000000),0,1,(78097896465881/200000000000000000)⟩
theorem valid8 : certificate8.Valid := by
  refine ⟨MajorityCertificates.Inputs000.inputs_valid8,?_⟩
  decide +kernel
theorem sound8 : certificate8.Sound :=
  rat_witness_certificate_sound certificate8 valid8 MajorityCertificates.Inputs000.envelope_sound8

def certificate9 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs000.envelope9,(46593/20000),(34791211/250000000),(11756323027834685309923/1000000000000000000),(2144979047/1000000000),(29/20),(1261913251/1000000000),0,(1125123239120085581/1000000000000000000),(316298204831381/1000000000000000000)⟩
theorem valid9 : certificate9.Valid := by
  refine ⟨MajorityCertificates.Inputs000.inputs_valid9,?_⟩
  decide +kernel
theorem sound9 : certificate9.Sound :=
  rat_witness_certificate_sound certificate9 valid9 MajorityCertificates.Inputs000.envelope_sound9

def certificate10 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs000.envelope10,(115811/50000),(44739/320000),(8702706377686016146887/1000000000000000000),(114022481/62500000),(3/2),(372420631/1000000000),0,1,(66048167550361/125000000000000000)⟩
theorem valid10 : certificate10.Valid := by
  refine ⟨MajorityCertificates.Inputs000.inputs_valid10,?_⟩
  decide +kernel
theorem sound10 : certificate10.Sound :=
  rat_witness_certificate_sound certificate10 valid10 MajorityCertificates.Inputs000.envelope_sound10

def certificate11 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs000.envelope11,(115811/50000),(44739/320000),(8702706377686016146887/1000000000000000000),(2160730101/1000000000),(3/2),(629756251/500000000),0,(1125167451835881251/1000000000000000000),(425422815297647/1000000000000000000)⟩
theorem valid11 : certificate11.Valid := by
  refine ⟨MajorityCertificates.Inputs000.inputs_valid11,?_⟩
  decide +kernel
theorem sound11 : certificate11.Sound :=
  rat_witness_certificate_sound certificate11 valid11 MajorityCertificates.Inputs000.envelope_sound11

def certificate12 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs000.envelope12,(115163/50000),(70226953/500000000),(839228398002528746119/125000000000000000),(916269821/500000000),(3/2),(374501569/1000000000),0,1,(21417810641833/31250000000000000)⟩
theorem valid12 : certificate12.Valid := by
  refine ⟨MajorityCertificates.Inputs000.inputs_valid12,?_⟩
  decide +kernel
theorem sound12 : certificate12.Sound :=
  rat_witness_certificate_sound certificate12 valid12 MajorityCertificates.Inputs000.envelope_sound12

def certificate13 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs000.envelope13,(115163/50000),(70226953/500000000),(839228398002528746119/125000000000000000),(2172146773/1000000000),(3/2),(1259162797/1000000000),0,(1125218286153914667/1000000000000000000),(139352950232467/250000000000000000)⟩
theorem valid13 : certificate13.Valid := by
  refine ⟨MajorityCertificates.Inputs000.inputs_valid13,?_⟩
  decide +kernel
theorem sound13 : certificate13.Sound :=
  rat_witness_certificate_sound certificate13 valid13 MajorityCertificates.Inputs000.envelope_sound13

def certificate14 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs000.envelope14,(229071/100000),(70549219/500000000),(2672750682344156463489/500000000000000000),(920293809/500000000),(3/2),(376586259/1000000000),0,1,(430825444878177/500000000000000000)⟩
theorem valid14 : certificate14.Valid := by
  refine ⟨MajorityCertificates.Inputs000.inputs_valid14,?_⟩
  decide +kernel
theorem sound14 : certificate14.Sound :=
  rat_witness_certificate_sound certificate14 valid14 MajorityCertificates.Inputs000.envelope_sound14

def certificate15 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs000.envelope15,(229071/100000),(70549219/500000000),(2672750682344156463489/500000000000000000),(1091927519/500000000),(3/2),(1258634977/1000000000),0,(225055135076250427/200000000000000000),(35032887032953/50000000000000000)⟩
theorem valid15 : certificate15.Valid := by
  refine ⟨MajorityCertificates.Inputs000.inputs_valid15,?_⟩
  decide +kernel
theorem sound15 : certificate15.Sound :=
  rat_witness_certificate_sound certificate15 valid15 MajorityCertificates.Inputs000.envelope_sound15

def certificate16 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs000.envelope16,(113927/50000),(141742969/1000000000),(545419571159664462953/125000000000000000),(924397629/500000000),(3/2),(378643821/1000000000),0,1,(211620523762297/200000000000000000)⟩
theorem valid16 : certificate16.Valid := by
  refine ⟨MajorityCertificates.Inputs000.inputs_valid16,?_⟩
  decide +kernel
theorem sound16 : certificate16.Sound :=
  rat_witness_certificate_sound certificate16 valid16 MajorityCertificates.Inputs000.envelope_sound16

def certificate17 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs000.envelope17,(113927/50000),(141742969/1000000000),(545419571159664462953/125000000000000000),(274422689/125000000),(3/2),(31454247/25000000),0,(140667443223867073/125000000000000000),(107380007139111/125000000000000000)⟩
theorem valid17 : certificate17.Valid := by
  refine ⟨MajorityCertificates.Inputs000.inputs_valid17,?_⟩
  decide +kernel
theorem sound17 : certificate17.Sound :=
  rat_witness_certificate_sound certificate17 valid17 MajorityCertificates.Inputs000.envelope_sound17

def certificate18 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs000.envelope18,(113337/50000),(11391/80000),(454272876767597821347/125000000000000000),(185642017/100000000),(3/2),(380757759/1000000000),0,1,(635830324796969/500000000000000000)⟩
theorem valid18 : certificate18.Valid := by
  refine ⟨MajorityCertificates.Inputs000.inputs_valid18,?_⟩
  decide +kernel
theorem sound18 : certificate18.Sound :=
  rat_witness_certificate_sound certificate18 valid18 MajorityCertificates.Inputs000.envelope_sound18

def certificate19 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs000.envelope19,(113337/50000),(11391/80000),(454272876767597821347/125000000000000000),(2206668401/1000000000),(3/2),(251559623/200000000),0,(1125409815426696749/1000000000000000000),(129474791460183/125000000000000000)⟩
theorem valid19 : certificate19.Valid := by
  refine ⟨MajorityCertificates.Inputs000.inputs_valid19,?_⟩
  decide +kernel
theorem sound19 : certificate19.Sound :=
  rat_witness_certificate_sound certificate19 valid19 MajorityCertificates.Inputs000.envelope_sound19

def certificates : List RatWitnessCertificate := [certificate0,certificate1,certificate2,certificate3,certificate4,certificate5,certificate6,certificate7,certificate8,certificate9,certificate10,certificate11,certificate12,certificate13,certificate14,certificate15,certificate16,certificate17,certificate18,certificate19]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_cons.mpr ⟨sound6,List.forall_mem_cons.mpr ⟨sound7,List.forall_mem_cons.mpr ⟨sound8,List.forall_mem_cons.mpr ⟨sound9,List.forall_mem_cons.mpr ⟨sound10,List.forall_mem_cons.mpr ⟨sound11,List.forall_mem_cons.mpr ⟨sound12,List.forall_mem_cons.mpr ⟨sound13,List.forall_mem_cons.mpr ⟨sound14,List.forall_mem_cons.mpr ⟨sound15,List.forall_mem_cons.mpr ⟨sound16,List.forall_mem_cons.mpr ⟨sound17,List.forall_mem_cons.mpr ⟨sound18,List.forall_mem_cons.mpr ⟨sound19,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch000
