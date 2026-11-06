import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs035

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch035

def certificate700 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs035.envelope700,(118473/50000),(80861719/500000000),(12988872207026718218203/500000000000000000),(452383993/250000000),(143/20),(53662239/125000000),0,1,(88856288188663/500000000000000000)⟩
theorem valid700 : certificate700.Valid := by
  refine ⟨MajorityCertificates.Inputs035.inputs_valid700,?_⟩
  decide +kernel
theorem sound700 : certificate700.Sound :=
  rat_witness_certificate_sound certificate700 valid700 MajorityCertificates.Inputs035.envelope_sound700

def certificate701 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs035.envelope701,(118473/50000),(80861719/500000000),(12988872207026718218203/500000000000000000),(1782606223/1000000000),(143/20),(298050817/200000000),0,(1125054832673224833/1000000000000000000),(76343013102401/250000000000000000)⟩
theorem valid701 : certificate701.Valid := by
  refine ⟨MajorityCertificates.Inputs035.inputs_valid701,?_⟩
  decide +kernel
theorem sound701 : certificate701.Sound :=
  rat_witness_certificate_sound certificate701 valid701 MajorityCertificates.Inputs035.envelope_sound701

def certificate702 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs035.envelope702,(118433/50000),(13041/80000),(24868242594516611726429/1000000000000000000),(72483509/40000000),(36/5),(216346597/500000000),0,1,(185364740715821/1000000000000000000)⟩
theorem valid702 : certificate702.Valid := by
  refine ⟨MajorityCertificates.Inputs035.inputs_valid702,?_⟩
  decide +kernel
theorem sound702 : certificate702.Sound :=
  rat_witness_certificate_sound certificate702 valid702 MajorityCertificates.Inputs035.envelope_sound702

def certificate703 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs035.envelope703,(118433/50000),(13041/80000),(24868242594516611726429/1000000000000000000),(89223563/50000000),(36/5),(148693861/100000000),0,(562528649243833069/500000000000000000),(320017295161393/1000000000000000000)⟩
theorem valid703 : certificate703.Valid := by
  refine ⟨MajorityCertificates.Inputs035.inputs_valid703,?_⟩
  decide +kernel
theorem sound703 : certificate703.Sound :=
  rat_witness_certificate_sound certificate703 valid703 MajorityCertificates.Inputs035.envelope_sound703

def certificate704 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs035.envelope704,(14797/6250),(163657031/1000000000),(23739285423009214710321/1000000000000000000),(906727109/500000000),(36/5),(217229831/500000000),0,1,(48579594412121/250000000000000000)⟩
theorem valid704 : certificate704.Valid := by
  refine ⟨MajorityCertificates.Inputs035.inputs_valid704,?_⟩
  decide +kernel
theorem sound704 : certificate704.Sound :=
  rat_witness_certificate_sound certificate704 valid704 MajorityCertificates.Inputs035.envelope_sound704

def certificate705 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs035.envelope705,(14797/6250),(163657031/1000000000),(23739285423009214710321/1000000000000000000),(1784835283/1000000000),(36/5),(743276569/500000000),0,(1125060052419410727/1000000000000000000),(84158587321201/250000000000000000)⟩
theorem valid705 : certificate705.Valid := by
  refine ⟨MajorityCertificates.Inputs035.inputs_valid705,?_⟩
  decide +kernel
theorem sound705 : certificate705.Sound :=
  rat_witness_certificate_sound certificate705 valid705 MajorityCertificates.Inputs035.envelope_sound705

def certificate706 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs035.envelope706,(236491/100000),(82473047/500000000),(21622674815746229464277/1000000000000000000),(1813132307/1000000000),(29/4),(438392577/1000000000),0,1,(53345441254391/250000000000000000)⟩
theorem valid706 : certificate706.Valid := by
  refine ⟨MajorityCertificates.Inputs035.inputs_valid706,?_⟩
  decide +kernel
theorem sound706 : certificate706.Sound :=
  rat_witness_certificate_sound certificate706 valid706 MajorityCertificates.Inputs035.envelope_sound706

def certificate707 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs035.envelope707,(236491/100000),(82473047/500000000),(21622674815746229464277/1000000000000000000),(178670039/100000000),(29/4),(92800181/62500000),0,(1125066003894251761/1000000000000000000),(370419341827881/1000000000000000000)⟩
theorem valid707 : certificate707.Valid := by
  refine ⟨MajorityCertificates.Inputs035.inputs_valid707,?_⟩
  decide +kernel
theorem sound707 : certificate707.Sound :=
  rat_witness_certificate_sound certificate707 valid707 MajorityCertificates.Inputs035.envelope_sound707

def certificate708 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs035.envelope708,(236271/100000),(41558789/250000000),(19868486828763672939793/1000000000000000000),(1815759801/1000000000),(29/4),(441949981/1000000000),0,1,(58322161078741/250000000000000000)⟩
theorem valid708 : certificate708.Valid := by
  refine ⟨MajorityCertificates.Inputs035.inputs_valid708,?_⟩
  decide +kernel
theorem sound708 : certificate708.Sound :=
  rat_witness_certificate_sound certificate708 valid708 MajorityCertificates.Inputs035.envelope_sound708

def certificate709 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs035.envelope709,(236271/100000),(41558789/250000000),(19868486828763672939793/1000000000000000000),(1787290161/1000000000),(29/4),(1484195441/1000000000),0,(1125071898553340263/1000000000000000000),(406405393300349/1000000000000000000)⟩
theorem valid709 : certificate709.Valid := by
  refine ⟨MajorityCertificates.Inputs035.inputs_valid709,?_⟩
  decide +kernel
theorem sound709 : certificate709.Sound :=
  rat_witness_certificate_sound certificate709 valid709 MajorityCertificates.Inputs035.envelope_sound709

def certificate710 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs035.envelope710,(236199/100000),(167524219/1000000000),(3831476627723406824789/200000000000000000),(1818349307/1000000000),(73/10),(44536701/100000000),0,1,(12081685705001/50000000000000000)⟩
theorem valid710 : certificate710.Valid := by
  refine ⟨MajorityCertificates.Inputs035.inputs_valid710,?_⟩
  decide +kernel
theorem sound710 : certificate710.Sound :=
  rat_witness_certificate_sound certificate710 valid710 MajorityCertificates.Inputs035.envelope_sound710

def certificate711 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs035.envelope711,(236199/100000),(167524219/1000000000),(3831476627723406824789/200000000000000000),(357836381/200000000),(73/10),(370235597/250000000),0,(562537295113841991/500000000000000000),(422813313714339/1000000000000000000)⟩
theorem valid711 : certificate711.Valid := by
  refine ⟨MajorityCertificates.Inputs035.inputs_valid711,?_⟩
  decide +kernel
theorem sound711 : certificate711.Sound :=
  rat_witness_certificate_sound certificate711 valid711 MajorityCertificates.Inputs035.envelope_sound711

def certificate712 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs035.envelope712,(59023/25000),(26907/160000),(4603011735212441710691/250000000000000000),(909846951/500000000),(147/20),(447148343/1000000000),0,1,(62895053658621/250000000000000000)⟩
theorem valid712 : certificate712.Valid := by
  refine ⟨MajorityCertificates.Inputs035.inputs_valid712,?_⟩
  decide +kernel
theorem sound712 : certificate712.Sound :=
  rat_witness_certificate_sound certificate712 valid712 MajorityCertificates.Inputs035.envelope_sound712

def certificate713 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs035.envelope713,(59023/25000),(26907/160000),(4603011735212441710691/250000000000000000),(1791211773/1000000000),(147/20),(29574907/20000000),0,(1125077645044811297/1000000000000000000),(1376606941423/3125000000000000)⟩
theorem valid713 : certificate713.Valid := by
  refine ⟨MajorityCertificates.Inputs035.inputs_valid713,?_⟩
  decide +kernel
theorem sound713 : certificate713.Sound :=
  rat_witness_certificate_sound certificate713 valid713 MajorityCertificates.Inputs035.envelope_sound713

def certificate714 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs035.envelope714,(117993/50000),(168813281/1000000000),(8856374180019400121829/500000000000000000),(455258373/250000000),(147/20),(89786423/200000000),0,1,(130851003573427/500000000000000000)⟩
theorem valid714 : certificate714.Valid := by
  refine ⟨MajorityCertificates.Inputs035.inputs_valid714,?_⟩
  decide +kernel
theorem sound714 : certificate714.Sound :=
  rat_witness_certificate_sound certificate714 valid714 MajorityCertificates.Inputs035.envelope_sound714

def certificate715 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs035.envelope715,(117993/50000),(168813281/1000000000),(8856374180019400121829/500000000000000000),(179153139/100000000),(147/20),(73921313/50000000),0,(1125080746894616923/1000000000000000000),(92025523631917/200000000000000000)⟩
theorem valid715 : certificate715.Valid := by
  refine ⟨MajorityCertificates.Inputs035.inputs_valid715,?_⟩
  decide +kernel
theorem sound715 : certificate715.Sound :=
  rat_witness_certificate_sound certificate715 valid715 MajorityCertificates.Inputs035.envelope_sound715

def certificate716 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs035.envelope716,(117941/50000),(169457813/1000000000),(2131967635031285304207/125000000000000000),(1822369779/1000000000),(37/5),(14084909/31250000),0,1,(271977473087317/1000000000000000000)⟩
theorem valid716 : certificate716.Valid := by
  refine ⟨MajorityCertificates.Inputs035.inputs_valid716,?_⟩
  decide +kernel
theorem sound716 : certificate716.Sound :=
  rat_witness_certificate_sound certificate716 valid716 MajorityCertificates.Inputs035.envelope_sound716

def certificate717 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs035.envelope717,(117941/50000),(169457813/1000000000),(2131967635031285304207/125000000000000000),(896706787/500000000),(37/5),(59056127/40000000),0,(4394858962950959/3906250000000000),(47809234986011/100000000000000000)⟩
theorem valid717 : certificate717.Valid := by
  refine ⟨MajorityCertificates.Inputs035.inputs_valid717,?_⟩
  decide +kernel
theorem sound717 : certificate717.Sound :=
  rat_witness_certificate_sound certificate717 valid717 MajorityCertificates.Inputs035.envelope_sound717

def certificate718 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs035.envelope718,(235637/100000),(54639/320000),(15786723066698804416633/1000000000000000000),(455456759/250000000),(37/5),(9094247/20000000),0,1,(1475097735959/5000000000000000)⟩
theorem valid718 : certificate718.Valid := by
  refine ⟨MajorityCertificates.Inputs035.inputs_valid718,?_⟩
  decide +kernel
theorem sound718 : certificate718.Sound :=
  rat_witness_certificate_sound certificate718 valid718 MajorityCertificates.Inputs035.envelope_sound718

def certificate719 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs035.envelope719,(235637/100000),(54639/320000),(15786723066698804416633/1000000000000000000),(1793451121/1000000000),(37/5),(73836249/50000000),0,(562545366528509867/500000000000000000),(519299603495117/1000000000000000000)⟩
theorem valid719 : certificate719.Valid := by
  refine ⟨MajorityCertificates.Inputs035.inputs_valid719,?_⟩
  decide +kernel
theorem sound719 : certificate719.Sound :=
  rat_witness_certificate_sound certificate719 valid719 MajorityCertificates.Inputs035.envelope_sound719

def certificates : List RatWitnessCertificate := [certificate700,certificate701,certificate702,certificate703,certificate704,certificate705,certificate706,certificate707,certificate708,certificate709,certificate710,certificate711,certificate712,certificate713,certificate714,certificate715,certificate716,certificate717,certificate718,certificate719]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound700,List.forall_mem_cons.mpr ⟨sound701,List.forall_mem_cons.mpr ⟨sound702,List.forall_mem_cons.mpr ⟨sound703,List.forall_mem_cons.mpr ⟨sound704,List.forall_mem_cons.mpr ⟨sound705,List.forall_mem_cons.mpr ⟨sound706,List.forall_mem_cons.mpr ⟨sound707,List.forall_mem_cons.mpr ⟨sound708,List.forall_mem_cons.mpr ⟨sound709,List.forall_mem_cons.mpr ⟨sound710,List.forall_mem_cons.mpr ⟨sound711,List.forall_mem_cons.mpr ⟨sound712,List.forall_mem_cons.mpr ⟨sound713,List.forall_mem_cons.mpr ⟨sound714,List.forall_mem_cons.mpr ⟨sound715,List.forall_mem_cons.mpr ⟨sound716,List.forall_mem_cons.mpr ⟨sound717,List.forall_mem_cons.mpr ⟨sound718,List.forall_mem_cons.mpr ⟨sound719,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch035
