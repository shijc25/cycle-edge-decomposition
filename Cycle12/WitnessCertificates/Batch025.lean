import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs025

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch025

def certificate500 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs025.envelope500,(47043/20000),(36402539/250000000),(18170925009373157771189/1000000000000000000),(1817172039/1000000000),(17/5),(385599073/1000000000),0,1,(252937015721341/1000000000000000000)⟩
theorem valid500 : certificate500.Valid := by
  refine ⟨MajorityCertificates.Inputs025.inputs_valid500,?_⟩
  decide +kernel
theorem sound500 : certificate500.Sound :=
  rat_witness_certificate_sound certificate500 valid500 MajorityCertificates.Inputs025.envelope_sound500

def certificate501 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs025.envelope501,(47043/20000),(36402539/250000000),(18170925009373157771189/1000000000000000000),(1967081957/1000000000),(17/5),(135269729/100000000),0,(281269742195386097/250000000000000000),(297399178473507/1000000000000000000)⟩
theorem valid501 : certificate501.Valid := by
  refine ⟨MajorityCertificates.Inputs025.inputs_valid501,?_⟩
  decide +kernel
theorem sound501 : certificate501.Sound :=
  rat_witness_certificate_sound certificate501 valid501 MajorityCertificates.Inputs025.envelope_sound501

def certificate502 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs025.envelope502,(117489/50000),(4570459/31250000),(8377854801191924745717/500000000000000000),(1822151767/1000000000),(17/5),(387021107/1000000000),0,1,(17128193322719/62500000000000000)⟩
theorem valid502 : certificate502.Valid := by
  refine ⟨MajorityCertificates.Inputs025.inputs_valid502,?_⟩
  decide +kernel
theorem sound502 : certificate502.Sound :=
  rat_witness_certificate_sound certificate502 valid502 MajorityCertificates.Inputs025.envelope_sound502

def certificate503 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs025.envelope503,(117489/50000),(4570459/31250000),(8377854801191924745717/500000000000000000),(1968975873/1000000000),(17/5),(1351947309/1000000000),0,(281271431348393869/250000000000000000),(77242331974489/250000000000000000)⟩
theorem valid503 : certificate503.Valid := by
  refine ⟨MajorityCertificates.Inputs025.inputs_valid503,?_⟩
  decide +kernel
theorem sound503 : certificate503.Sound :=
  rat_witness_certificate_sound certificate503 valid503 MajorityCertificates.Inputs025.envelope_sound503

def certificate504 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs025.envelope504,(117353/50000),(146899219/1000000000),(7724553436294398938717/500000000000000000),(456019951/250000000),(69/20),(388823743/1000000000),0,1,(297289647835091/1000000000000000000)⟩
theorem valid504 : certificate504.Valid := by
  refine ⟨MajorityCertificates.Inputs025.inputs_valid504,?_⟩
  decide +kernel
theorem sound504 : certificate504.Sound :=
  rat_witness_certificate_sound certificate504 valid504 MajorityCertificates.Inputs025.envelope_sound504

def certificate505 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs025.envelope505,(117353/50000),(146899219/1000000000),(7724553436294398938717/500000000000000000),(987335043/500000000),(69/20),(1348700519/1000000000),0,(562546541905458161/500000000000000000),(350165888951479/1000000000000000000)⟩
theorem valid505 : certificate505.Valid := by
  refine ⟨MajorityCertificates.Inputs025.inputs_valid505,?_⟩
  decide +kernel
theorem sound505 : certificate505.Sound :=
  rat_witness_certificate_sound certificate505 valid505 MajorityCertificates.Inputs025.envelope_sound505

def certificate506 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs025.envelope506,(58533/25000),(23607/160000),(1651972473570312641507/125000000000000000),(1826832391/1000000000),(69/20),(390828311/1000000000),0,1,(87099234409761/250000000000000000)⟩
theorem valid506 : certificate506.Valid := by
  refine ⟨MajorityCertificates.Inputs025.inputs_valid506,?_⟩
  decide +kernel
theorem sound506 : certificate506.Sound :=
  rat_witness_certificate_sound certificate506 valid506 MajorityCertificates.Inputs025.envelope_sound506

def certificate507 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs025.envelope507,(58533/25000),(23607/160000),(1651972473570312641507/125000000000000000),(395642737/200000000),(69/20),(674409821/500000000),0,(22502181639333893/20000000000000000),(418572847478011/1000000000000000000)⟩
theorem valid507 : certificate507.Valid := by
  refine ⟨MajorityCertificates.Inputs025.inputs_valid507,?_⟩
  decide +kernel
theorem sound507 : certificate507.Sound :=
  rat_witness_certificate_sound certificate507 valid507 MajorityCertificates.Inputs025.envelope_sound507

def certificate508 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs025.envelope508,(23361/10000),(148832813/1000000000),(5743011293647465710453/500000000000000000),(915289451/500000000),(69/20),(394449527/1000000000),0,1,(401042486355189/1000000000000000000)⟩
theorem valid508 : certificate508.Valid := by
  refine ⟨MajorityCertificates.Inputs025.inputs_valid508,?_⟩
  decide +kernel
theorem sound508 : certificate508.Sound :=
  rat_witness_certificate_sound certificate508 valid508 MajorityCertificates.Inputs025.envelope_sound508

def certificate509 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs025.envelope509,(23361/10000),(148832813/1000000000),(5743011293647465710453/500000000000000000),(39623989/20000000),(69/20),(269669543/200000000),0,(562562895627357787/500000000000000000),(95184799412647/200000000000000000)⟩
theorem valid509 : certificate509.Valid := by
  refine ⟨MajorityCertificates.Inputs025.inputs_valid509,?_⟩
  decide +kernel
theorem sound509 : certificate509.Sound :=
  rat_witness_certificate_sound certificate509 valid509 MajorityCertificates.Inputs025.envelope_sound509

def certificate510 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs025.envelope510,(2331/1000),(4671167/31250000),(10085909374252406242401/1000000000000000000),(1833436949/1000000000),(7/2),(396400931/1000000000),0,1,(45607371564731/100000000000000000)⟩
theorem valid510 : certificate510.Valid := by
  refine ⟨MajorityCertificates.Inputs025.inputs_valid510,?_⟩
  decide +kernel
theorem sound510 : certificate510.Sound :=
  rat_witness_certificate_sound certificate510 valid510 MajorityCertificates.Inputs025.envelope_sound510

def certificate511 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs025.envelope511,(2331/1000),(4671167/31250000),(10085909374252406242401/1000000000000000000),(497168541/250000000),(7/2),(336351847/250000000),0,(1125143568626815921/1000000000000000000),(16883759583789/31250000000000000)⟩
theorem valid511 : certificate511.Valid := by
  refine ⟨MajorityCertificates.Inputs025.inputs_valid511,?_⟩
  decide +kernel
theorem sound511 : certificate511.Sound :=
  rat_witness_certificate_sound certificate511 valid511 MajorityCertificates.Inputs025.envelope_sound511

def certificate512 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs025.envelope512,(116301/50000),(75383203/500000000),(446812623498984896617/50000000000000000),(45994493/25000000),(7/2),(399736103/1000000000),0,1,(258055280903953/500000000000000000)⟩
theorem valid512 : certificate512.Valid := by
  refine ⟨MajorityCertificates.Inputs025.inputs_valid512,?_⟩
  decide +kernel
theorem sound512 : certificate512.Sound :=
  rat_witness_certificate_sound certificate512 valid512 MajorityCertificates.Inputs025.envelope_sound512

def certificate513 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs025.envelope513,(116301/50000),(75383203/500000000),(446812623498984896617/50000000000000000),(1991911711/1000000000),(7/2),(1344753857/1000000000),0,(1125162387896683797/1000000000000000000),(6145002159917/10000000000000000)⟩
theorem valid513 : certificate513.Valid := by
  refine ⟨MajorityCertificates.Inputs025.inputs_valid513,?_⟩
  decide +kernel
theorem sound513 : certificate513.Sound :=
  rat_witness_certificate_sound certificate513 valid513 MajorityCertificates.Inputs025.envelope_sound513

def certificate514 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs025.envelope514,(46423/20000),(75705469/500000000),(1596069211513529826833/200000000000000000),(1845287271/1000000000),(7/2),(100347263/250000000),0,1,(289244442196573/500000000000000000)⟩
theorem valid514 : certificate514.Valid := by
  refine ⟨MajorityCertificates.Inputs025.inputs_valid514,?_⟩
  decide +kernel
theorem sound514 : certificate514.Sound :=
  rat_witness_certificate_sound certificate514 valid514 MajorityCertificates.Inputs025.envelope_sound514

def certificate515 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs025.envelope515,(46423/20000),(75705469/500000000),(1596069211513529826833/200000000000000000),(998936697/500000000),(7/2),(134301591/100000000),0,(1125182223152174117/1000000000000000000),(395000950175737/500000000000000000)⟩
theorem valid515 : certificate515.Valid := by
  refine ⟨MajorityCertificates.Inputs025.inputs_valid515,?_⟩
  decide +kernel
theorem sound515 : certificate515.Sound :=
  rat_witness_certificate_sound certificate515 valid515 MajorityCertificates.Inputs025.envelope_sound515

def certificate516 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs025.envelope516,(5791/2500),(1527/10000),(179417783850497030531/25000000000000000),(462228523/250000000),(71/20),(202516893/500000000),0,1,(643686999672567/1000000000000000000)⟩
theorem valid516 : certificate516.Valid := by
  refine ⟨MajorityCertificates.Inputs025.inputs_valid516,?_⟩
  decide +kernel
theorem sound516 : certificate516.Sound :=
  rat_witness_certificate_sound certificate516 valid516 MajorityCertificates.Inputs025.envelope_sound516

def certificate517 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs025.envelope517,(5791/2500),(1527/10000),(179417783850497030531/25000000000000000),(400483891/200000000),(71/20),(335331707/250000000),0,(1125203046590776383/1000000000000000000),(30798111126737/40000000000000000)⟩
theorem valid517 : certificate517.Valid := by
  refine ⟨MajorityCertificates.Inputs025.inputs_valid517,?_⟩
  decide +kernel
theorem sound517 : certificate517.Sound :=
  rat_witness_certificate_sound certificate517 valid517 MajorityCertificates.Inputs025.envelope_sound517

def certificate518 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs025.envelope518,(9247/4000),(153344531/1000000000),(259777396068867272681/40000000000000000),(1854578929/1000000000),(71/20),(20333421/50000000),0,1,(71274531141571/100000000000000000)⟩
theorem valid518 : certificate518.Valid := by
  refine ⟨MajorityCertificates.Inputs025.inputs_valid518,?_⟩
  decide +kernel
theorem sound518 : certificate518.Sound :=
  rat_witness_certificate_sound certificate518 valid518 MajorityCertificates.Inputs025.envelope_sound518

def certificate519 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs025.envelope519,(9247/4000),(153344531/1000000000),(259777396068867272681/40000000000000000),(1003105573/500000000),(71/20),(670472579/500000000),0,(1125224832476118051/1000000000000000000),(171254361321583/200000000000000000)⟩
theorem valid519 : certificate519.Valid := by
  refine ⟨MajorityCertificates.Inputs025.inputs_valid519,?_⟩
  decide +kernel
theorem sound519 : certificate519.Sound :=
  rat_witness_certificate_sound certificate519 valid519 MajorityCertificates.Inputs025.envelope_sound519

def certificates : List RatWitnessCertificate := [certificate500,certificate501,certificate502,certificate503,certificate504,certificate505,certificate506,certificate507,certificate508,certificate509,certificate510,certificate511,certificate512,certificate513,certificate514,certificate515,certificate516,certificate517,certificate518,certificate519]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound500,List.forall_mem_cons.mpr ⟨sound501,List.forall_mem_cons.mpr ⟨sound502,List.forall_mem_cons.mpr ⟨sound503,List.forall_mem_cons.mpr ⟨sound504,List.forall_mem_cons.mpr ⟨sound505,List.forall_mem_cons.mpr ⟨sound506,List.forall_mem_cons.mpr ⟨sound507,List.forall_mem_cons.mpr ⟨sound508,List.forall_mem_cons.mpr ⟨sound509,List.forall_mem_cons.mpr ⟨sound510,List.forall_mem_cons.mpr ⟨sound511,List.forall_mem_cons.mpr ⟨sound512,List.forall_mem_cons.mpr ⟨sound513,List.forall_mem_cons.mpr ⟨sound514,List.forall_mem_cons.mpr ⟨sound515,List.forall_mem_cons.mpr ⟨sound516,List.forall_mem_cons.mpr ⟨sound517,List.forall_mem_cons.mpr ⟨sound518,List.forall_mem_cons.mpr ⟨sound519,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch025
