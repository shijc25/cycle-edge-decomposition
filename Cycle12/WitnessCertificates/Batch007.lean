import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs007

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch007

def certificate140 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs007.envelope140,(99713/50000),(144079961/1000000000),(134543316774886799319/500000000000000000),(1047486957/500000000),(39/20),(395663277/1000000000),0,1,(10063275870719433/500000000000000000)⟩
theorem valid140 : certificate140.Valid := by
  refine ⟨MajorityCertificates.Inputs007.inputs_valid140,?_⟩
  decide +kernel
theorem sound140 : certificate140.Sound :=
  rat_witness_certificate_sound certificate140 valid140 MajorityCertificates.Inputs007.envelope_sound140

def certificate141 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs007.envelope141,(99713/50000),(144079961/1000000000),(134543316774886799319/500000000000000000),(617739437/250000000),(39/20),(332665779/250000000),0,(113131672088210401/100000000000000000),(8888823291350397/500000000000000000)⟩
theorem valid141 : certificate141.Valid := by
  refine ⟨MajorityCertificates.Inputs007.inputs_valid141,?_⟩
  decide +kernel
theorem sound141 : certificate141.Sound :=
  rat_witness_certificate_sound certificate141 valid141 MajorityCertificates.Inputs007.envelope_sound141

def certificate142 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs007.envelope142,(99661/50000),(71919131/500000000),(66755191438671498179/250000000000000000),(2099471913/1000000000),(39/20),(394627583/1000000000),0,1,(20050049664025817/1000000000000000000)⟩
theorem valid142 : certificate142.Valid := by
  refine ⟨MajorityCertificates.Inputs007.inputs_valid142,?_⟩
  decide +kernel
theorem sound142 : certificate142.Sound :=
  rat_witness_certificate_sound certificate142 valid142 MajorityCertificates.Inputs007.envelope_sound142

def certificate143 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs007.envelope143,(99661/50000),(71919131/500000000),(66755191438671498179/250000000000000000),(2472224233/1000000000),(39/20),(332884179/250000000),0,(7071057141718877/6250000000000000),(1796332227833843/100000000000000000)⟩
theorem valid143 : certificate143.Valid := by
  refine ⟨MajorityCertificates.Inputs007.inputs_valid143,?_⟩
  decide +kernel
theorem sound143 : certificate143.Sound :=
  rat_witness_certificate_sound certificate143 valid143 MajorityCertificates.Inputs007.envelope_sound143

def certificate144 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs007.envelope144,(199219/100000),(143596563/1000000000),(132493373275799381101/500000000000000000),(1035534827/500000000),2,(198410301/500000000),0,1,(3982775620357481/200000000000000000)⟩
theorem valid144 : certificate144.Valid := by
  refine ⟨MajorityCertificates.Inputs007.inputs_valid144,?_⟩
  decide +kernel
theorem sound144 : certificate144.Sound :=
  rat_witness_certificate_sound certificate144 valid144 MajorityCertificates.Inputs007.envelope_sound144

def certificate145 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs007.envelope145,(199219/100000),(143596563/1000000000),(132493373275799381101/500000000000000000),(2475297771/1000000000),2,(1332851297/1000000000),0,(226284316322691789/200000000000000000),(18117614217914161/1000000000000000000)⟩
theorem valid145 : certificate145.Valid := by
  refine ⟨MajorityCertificates.Inputs007.inputs_valid145,?_⟩
  decide +kernel
theorem sound145 : certificate145.Sound :=
  rat_witness_certificate_sound certificate145 valid145 MajorityCertificates.Inputs007.envelope_sound145

def certificate146 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs007.envelope146,(49779/25000),(143354863/1000000000),(131491975698769558831/500000000000000000),(1051942197/500000000),2,(78631773/200000000),0,1,(20425738723373657/1000000000000000000)⟩
theorem valid146 : certificate146.Valid := by
  refine ⟨MajorityCertificates.Inputs007.inputs_valid146,?_⟩
  decide +kernel
theorem sound146 : certificate146.Sound :=
  rat_witness_certificate_sound certificate146 valid146 MajorityCertificates.Inputs007.envelope_sound146

def certificate147 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs007.envelope147,(49779/25000),(143354863/1000000000),(131491975698769558831/500000000000000000),(154786801/62500000),2,(83357859/62500000),0,(1131474066964064787/1000000000000000000),(732152288714979/40000000000000000)⟩
theorem valid147 : certificate147.Valid := by
  refine ⟨MajorityCertificates.Inputs007.inputs_valid147,?_⟩
  decide +kernel
theorem sound147 : certificate147.Sound :=
  rat_witness_certificate_sound certificate147 valid147 MajorityCertificates.Inputs007.envelope_sound147

def certificate148 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs007.envelope148,(39803/20000),(14319373/100000000),(130505885730980550373/500000000000000000),(524679177/250000000),2,(39333641/100000000),0,1,(5129546907215903/250000000000000000)⟩
theorem valid148 : certificate148.Valid := by
  refine ⟨MajorityCertificates.Inputs007.inputs_valid148,?_⟩
  decide +kernel
theorem sound148 : certificate148.Sound :=
  rat_witness_certificate_sound certificate148 valid148 MajorityCertificates.Inputs007.envelope_sound148

def certificate149 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs007.envelope149,(39803/20000),(14319373/100000000),(130505885730980550373/500000000000000000),(154916679/62500000),2,(1334130999/1000000000),0,(565763265146493993/500000000000000000),(184548598738167/10000000000000000)⟩
theorem valid149 : certificate149.Valid := by
  refine ⟨MajorityCertificates.Inputs007.inputs_valid149,?_⟩
  decide +kernel
theorem sound149 : certificate149.Sound :=
  rat_witness_certificate_sound certificate149 valid149 MajorityCertificates.Inputs007.envelope_sound149

def certificate150 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs007.envelope150,(99457/50000),(142952031/1000000000),(259069613155146490359/1000000000000000000),(263432897/125000000),2,(391986389/1000000000),0,1,(10374564181944717/500000000000000000)⟩
theorem valid150 : certificate150.Valid := by
  refine ⟨MajorityCertificates.Inputs007.inputs_valid150,?_⟩
  decide +kernel
theorem sound150 : certificate150.Sound :=
  rat_witness_certificate_sound certificate150 valid150 MajorityCertificates.Inputs007.envelope_sound150

def certificate151 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs007.envelope151,(99457/50000),(142952031/1000000000),(259069613155146490359/1000000000000000000),(2479933633/1000000000),2,(333753189/250000000),0,(141447379224921497/125000000000000000),(1864303341249787/100000000000000000)⟩
theorem valid151 : certificate151.Valid := by
  refine ⟨MajorityCertificates.Inputs007.inputs_valid151,?_⟩
  decide +kernel
theorem sound151 : certificate151.Sound :=
  rat_witness_certificate_sound certificate151 valid151 MajorityCertificates.Inputs007.envelope_sound151

def certificate152 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs007.envelope152,(99407/50000),(35677583/250000000),(128578448836555681817/500000000000000000),(65784253/31250000),2,(391652737/1000000000),0,1,(5207208264857873/250000000000000000)⟩
theorem valid152 : certificate152.Valid := by
  refine ⟨MajorityCertificates.Inputs007.inputs_valid152,?_⟩
  decide +kernel
theorem sound152 : certificate152.Sound :=
  rat_witness_certificate_sound certificate152 valid152 MajorityCertificates.Inputs007.envelope_sound152

def certificate153 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs007.envelope153,(99407/50000),(35677583/250000000),(128578448836555681817/500000000000000000),(155133559/62500000),2,(1335427813/1000000000),0,(565815770708490281/500000000000000000),(9397822403960629/500000000000000000)⟩
theorem valid153 : certificate153.Valid := by
  refine ⟨MajorityCertificates.Inputs007.inputs_valid153,?_⟩
  decide +kernel
theorem sound153 : certificate153.Sound :=
  rat_witness_certificate_sound certificate153 valid153 MajorityCertificates.Inputs007.envelope_sound153

def certificate154 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs007.envelope154,(39743/20000),(142468633/1000000000),(255273060558360408829/1000000000000000000),(2090553989/1000000000),2,(392736393/1000000000),0,1,(10841327163949979/500000000000000000)⟩
theorem valid154 : certificate154.Valid := by
  refine ⟨MajorityCertificates.Inputs007.inputs_valid154,?_⟩
  decide +kernel
theorem sound154 : certificate154.Sound :=
  rat_witness_certificate_sound certificate154 valid154 MajorityCertificates.Inputs007.envelope_sound154

def certificate155 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs007.envelope155,(39743/20000),(142468633/1000000000),(255273060558360408829/1000000000000000000),(620844493/250000000),2,(267263501/200000000),0,(56584202486716493/50000000000000000),(3797154904345189/200000000000000000)⟩
theorem valid155 : certificate155.Valid := by
  refine ⟨MajorityCertificates.Inputs007.inputs_valid155,?_⟩
  decide +kernel
theorem sound155 : certificate155.Sound :=
  rat_witness_certificate_sound certificate155 valid155 MajorityCertificates.Inputs007.envelope_sound155

def certificate156 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs007.envelope156,(198617/100000),(71113467/500000000),(6335438781896511673/25000000000000000),(1055750243/500000000),2,(15598717/40000000),0,1,(10569345984730369/500000000000000000)⟩
theorem valid156 : certificate156.Valid := by
  refine ⟨MajorityCertificates.Inputs007.inputs_valid156,?_⟩
  decide +kernel
theorem sound156 : certificate156.Sound :=
  rat_witness_certificate_sound certificate156 valid156 MajorityCertificates.Inputs007.envelope_sound156

def certificate157 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs007.envelope157,(198617/100000),(71113467/500000000),(6335438781896511673/25000000000000000),(2485573541/1000000000),2,(1336730511/1000000000),0,(35366767354237763/31250000000000000),(3827789131151949/200000000000000000)⟩
theorem valid157 : certificate157.Valid := by
  refine ⟨MajorityCertificates.Inputs007.inputs_valid157,?_⟩
  decide +kernel
theorem sound157 : certificate157.Sound :=
  rat_witness_certificate_sound certificate157 valid157 MajorityCertificates.Inputs007.envelope_sound157

def certificate158 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs007.envelope158,(197759/100000),(46389/320000),(251589832803632728293/1000000000000000000),(421844301/200000000),2,(399235059/1000000000),0,1,(10622878262812281/500000000000000000)⟩
theorem valid158 : certificate158.Valid := by
  refine ⟨MajorityCertificates.Inputs007.inputs_valid158,?_⟩
  decide +kernel
theorem sound158 : certificate158.Sound :=
  rat_witness_certificate_sound certificate158 valid158 MajorityCertificates.Inputs007.envelope_sound158

def certificate159 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs007.envelope159,(197759/100000),(46389/320000),(251589832803632728293/1000000000000000000),(622202601/250000000),2,(1338330767/1000000000),0,(282953825722073039/250000000000000000),(4823179329440131/250000000000000000)⟩
theorem valid159 : certificate159.Valid := by
  refine ⟨MajorityCertificates.Inputs007.inputs_valid159,?_⟩
  decide +kernel
theorem sound159 : certificate159.Sound :=
  rat_witness_certificate_sound certificate159 valid159 MajorityCertificates.Inputs007.envelope_sound159

def certificates : List RatWitnessCertificate := [certificate140,certificate141,certificate142,certificate143,certificate144,certificate145,certificate146,certificate147,certificate148,certificate149,certificate150,certificate151,certificate152,certificate153,certificate154,certificate155,certificate156,certificate157,certificate158,certificate159]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound140,List.forall_mem_cons.mpr ⟨sound141,List.forall_mem_cons.mpr ⟨sound142,List.forall_mem_cons.mpr ⟨sound143,List.forall_mem_cons.mpr ⟨sound144,List.forall_mem_cons.mpr ⟨sound145,List.forall_mem_cons.mpr ⟨sound146,List.forall_mem_cons.mpr ⟨sound147,List.forall_mem_cons.mpr ⟨sound148,List.forall_mem_cons.mpr ⟨sound149,List.forall_mem_cons.mpr ⟨sound150,List.forall_mem_cons.mpr ⟨sound151,List.forall_mem_cons.mpr ⟨sound152,List.forall_mem_cons.mpr ⟨sound153,List.forall_mem_cons.mpr ⟨sound154,List.forall_mem_cons.mpr ⟨sound155,List.forall_mem_cons.mpr ⟨sound156,List.forall_mem_cons.mpr ⟨sound157,List.forall_mem_cons.mpr ⟨sound158,List.forall_mem_cons.mpr ⟨sound159,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch007
