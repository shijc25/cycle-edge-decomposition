import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch691
import Cycle12.MergedCutProfiles.Batch692
import Cycle12.MergedCutProfiles.Batch693

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch411

def retention4932 : RatCutRetentionCertificate := ⟨(23/500),(93/2000),(1/40),(2624053134903339001/50000000000000000),(21/20),(1105137029352375627/500000000000000000),false,MergedCutProfiles.Batch691.profile27672,(fun _ => MergedCutProfiles.Batch691.profile27672)⟩
theorem profilesValid4932 : retention4932.ProfilesValid := by
  exact MergedCutProfiles.Batch691.valid27672
theorem numericValid4932 : retention4932.NumericValid := by decide +kernel
def certificate4932 : RatCutBinCertificate := ⟨⟨retention4932,(935022573639322461/500000000000000000),(50858016999050421/500000000000000000),(12476149680667381057/1000000000000000000),(3518599610248635872887/125000000000000000),(1097132786345661313/500000000000000000)⟩,(999940161761240739/1000000000000000000),(348462834573225413/500000000000000000),(25715418501910453/500000000000000000),(103545652227390213/1000000000000000000)⟩
theorem valid4932 : certificate4932.Valid := by decide +kernel
theorem sound4932 : certificate4932.Sound := rat_cut_bin_certificate_sound certificate4932 profilesValid4932 numericValid4932 valid4932

def retention4933 : RatCutRetentionCertificate := ⟨(93/2000),(47/1000),(300106780108946353/1098063006495144911542),(594270851700883867/1000000000000000000),4,(580535381097292476091/256000000000000000000),true,MergedCutProfiles.Batch691.profile27673,![MergedCutProfiles.Batch691.profile27673,MergedCutProfiles.Batch691.profile27674,MergedCutProfiles.Batch691.profile27675,MergedCutProfiles.Batch691.profile27676,MergedCutProfiles.Batch691.profile27677,MergedCutProfiles.Batch691.profile27678,MergedCutProfiles.Batch691.profile27679,MergedCutProfiles.Batch692.profile27680,MergedCutProfiles.Batch692.profile27681,MergedCutProfiles.Batch692.profile27682,MergedCutProfiles.Batch692.profile27683,MergedCutProfiles.Batch692.profile27684,MergedCutProfiles.Batch692.profile27685,MergedCutProfiles.Batch692.profile27686,MergedCutProfiles.Batch692.profile27687,MergedCutProfiles.Batch692.profile27688]⟩
theorem profilesValid4933 : retention4933.ProfilesValid := by
  change ∀ j : Fin 16, (retention4933.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch691.valid27673
  · exact MergedCutProfiles.Batch691.valid27674
  · exact MergedCutProfiles.Batch691.valid27675
  · exact MergedCutProfiles.Batch691.valid27676
  · exact MergedCutProfiles.Batch691.valid27677
  · exact MergedCutProfiles.Batch691.valid27678
  · exact MergedCutProfiles.Batch691.valid27679
  · exact MergedCutProfiles.Batch692.valid27680
  · exact MergedCutProfiles.Batch692.valid27681
  · exact MergedCutProfiles.Batch692.valid27682
  · exact MergedCutProfiles.Batch692.valid27683
  · exact MergedCutProfiles.Batch692.valid27684
  · exact MergedCutProfiles.Batch692.valid27685
  · exact MergedCutProfiles.Batch692.valid27686
  · exact MergedCutProfiles.Batch692.valid27687
  · exact MergedCutProfiles.Batch692.valid27688
theorem numericValid4933 : retention4933.NumericValid := by decide +kernel
def certificate4933 : RatCutBinCertificate := ⟨⟨retention4933,(382016406455403279/200000000000000000),(6511012982960937/62500000000000000),(12577396975114151283/1000000000000000000),(27699124992646009937571/1000000000000000000),(137777052184045967/62500000000000000)⟩,(999938055512514283/1000000000000000000),(701160379043371403/1000000000000000000),(1996584893867133/40000000000000000),(22329386016763299/1000000000000000000)⟩
theorem valid4933 : certificate4933.Valid := by decide +kernel
theorem sound4933 : certificate4933.Sound := rat_cut_bin_certificate_sound certificate4933 profilesValid4933 numericValid4933 valid4933

def retention4934 : RatCutRetentionCertificate := ⟨(93/2000),(47/1000),(281847608500000000/549031503247572455771),(300106780108946353/500000000000000000),4,(5336819693784205484364562048495599/2344584219601143382812500000000000),true,MergedCutProfiles.Batch691.profile27674,![MergedCutProfiles.Batch691.profile27674,MergedCutProfiles.Batch691.profile27676,MergedCutProfiles.Batch691.profile27678,MergedCutProfiles.Batch692.profile27680,MergedCutProfiles.Batch692.profile27681,MergedCutProfiles.Batch692.profile27683,MergedCutProfiles.Batch692.profile27685,MergedCutProfiles.Batch692.profile27687,MergedCutProfiles.Batch692.profile27689,MergedCutProfiles.Batch692.profile27690,MergedCutProfiles.Batch692.profile27691,MergedCutProfiles.Batch692.profile27692,MergedCutProfiles.Batch692.profile27693,MergedCutProfiles.Batch692.profile27694,MergedCutProfiles.Batch692.profile27695,MergedCutProfiles.Batch692.profile27696]⟩
theorem profilesValid4934 : retention4934.ProfilesValid := by
  change ∀ j : Fin 16, (retention4934.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch691.valid27674
  · exact MergedCutProfiles.Batch691.valid27676
  · exact MergedCutProfiles.Batch691.valid27678
  · exact MergedCutProfiles.Batch692.valid27680
  · exact MergedCutProfiles.Batch692.valid27681
  · exact MergedCutProfiles.Batch692.valid27683
  · exact MergedCutProfiles.Batch692.valid27685
  · exact MergedCutProfiles.Batch692.valid27687
  · exact MergedCutProfiles.Batch692.valid27689
  · exact MergedCutProfiles.Batch692.valid27690
  · exact MergedCutProfiles.Batch692.valid27691
  · exact MergedCutProfiles.Batch692.valid27692
  · exact MergedCutProfiles.Batch692.valid27693
  · exact MergedCutProfiles.Batch692.valid27694
  · exact MergedCutProfiles.Batch692.valid27695
  · exact MergedCutProfiles.Batch692.valid27696
theorem numericValid4934 : retention4934.NumericValid := by decide +kernel
def certificate4934 : RatCutBinCertificate := ⟨⟨retention4934,(382016406455403279/200000000000000000),(6511012982960937/62500000000000000),(12577396975114151283/1000000000000000000),(27699124992646009937571/1000000000000000000),(276618673111147751/125000000000000000)⟩,(999938055512514283/1000000000000000000),(346935585392892687/500000000000000000),(1313511202250137/25000000000000000),(5905468334205833/250000000000000000)⟩
theorem valid4934 : certificate4934.Valid := by decide +kernel
theorem sound4934 : certificate4934.Sound := rat_cut_bin_certificate_sound certificate4934 profilesValid4934 numericValid4934 valid4934

def retention4935 : RatCutRetentionCertificate := ⟨(93/2000),(47/1000),(4095726451734635661/2196126012990289823084),(563695217/500000000),(14/5),(429420936858680567301030176700829839/180382469440000000000000000000000000),true,MergedCutProfiles.Batch691.profile27679,![MergedCutProfiles.Batch691.profile27679,MergedCutProfiles.Batch692.profile27686,MergedCutProfiles.Batch692.profile27691,MergedCutProfiles.Batch692.profile27695,MergedCutProfiles.Batch692.profile27697,MergedCutProfiles.Batch692.profile27698,MergedCutProfiles.Batch692.profile27699,MergedCutProfiles.Batch692.profile27700,MergedCutProfiles.Batch692.profile27701,MergedCutProfiles.Batch692.profile27702,MergedCutProfiles.Batch692.profile27703,MergedCutProfiles.Batch692.profile27704,MergedCutProfiles.Batch692.profile27705,MergedCutProfiles.Batch692.profile27706,MergedCutProfiles.Batch692.profile27707,MergedCutProfiles.Batch692.profile27708]⟩
theorem profilesValid4935 : retention4935.ProfilesValid := by
  change ∀ j : Fin 16, (retention4935.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch691.valid27679
  · exact MergedCutProfiles.Batch692.valid27686
  · exact MergedCutProfiles.Batch692.valid27691
  · exact MergedCutProfiles.Batch692.valid27695
  · exact MergedCutProfiles.Batch692.valid27697
  · exact MergedCutProfiles.Batch692.valid27698
  · exact MergedCutProfiles.Batch692.valid27699
  · exact MergedCutProfiles.Batch692.valid27700
  · exact MergedCutProfiles.Batch692.valid27701
  · exact MergedCutProfiles.Batch692.valid27702
  · exact MergedCutProfiles.Batch692.valid27703
  · exact MergedCutProfiles.Batch692.valid27704
  · exact MergedCutProfiles.Batch692.valid27705
  · exact MergedCutProfiles.Batch692.valid27706
  · exact MergedCutProfiles.Batch692.valid27707
  · exact MergedCutProfiles.Batch692.valid27708
theorem numericValid4935 : retention4935.NumericValid := by decide +kernel
def certificate4935 : RatCutBinCertificate := ⟨⟨retention4935,(382016406455403279/200000000000000000),(6511012982960937/62500000000000000),(12577396975114151283/1000000000000000000),(27699124992646009937571/1000000000000000000),(292039380133446123/125000000000000000)⟩,(999938055512514283/1000000000000000000),(453898650914179393/1000000000000000000),(187575028215963077/1000000000000000000),(123782101449156167/1000000000000000000)⟩
theorem valid4935 : certificate4935.Valid := by decide +kernel
theorem sound4935 : certificate4935.Sound := rat_cut_bin_certificate_sound certificate4935 profilesValid4935 numericValid4935 valid4935

def retention4936 : RatCutRetentionCertificate := ⟨(93/2000),(47/1000),(16000000000000000000/549031503247572455771),(4095726451734635661/1000000000000000000),(13/10),(1168929359495163880371701017429979671317/546096860231284754800000000000000000000),true,MergedCutProfiles.Batch692.profile27709,![MergedCutProfiles.Batch692.profile27709,MergedCutProfiles.Batch692.profile27710,MergedCutProfiles.Batch692.profile27711,MergedCutProfiles.Batch692.profile27712,MergedCutProfiles.Batch692.profile27713,MergedCutProfiles.Batch692.profile27714,MergedCutProfiles.Batch692.profile27715,MergedCutProfiles.Batch692.profile27716,MergedCutProfiles.Batch692.profile27717,MergedCutProfiles.Batch692.profile27718,MergedCutProfiles.Batch692.profile27719,MergedCutProfiles.Batch693.profile27720,MergedCutProfiles.Batch693.profile27721,MergedCutProfiles.Batch693.profile27722,MergedCutProfiles.Batch693.profile27723,MergedCutProfiles.Batch693.profile27724]⟩
theorem profilesValid4936 : retention4936.ProfilesValid := by
  change ∀ j : Fin 16, (retention4936.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch692.valid27709
  · exact MergedCutProfiles.Batch692.valid27710
  · exact MergedCutProfiles.Batch692.valid27711
  · exact MergedCutProfiles.Batch692.valid27712
  · exact MergedCutProfiles.Batch692.valid27713
  · exact MergedCutProfiles.Batch692.valid27714
  · exact MergedCutProfiles.Batch692.valid27715
  · exact MergedCutProfiles.Batch692.valid27716
  · exact MergedCutProfiles.Batch692.valid27717
  · exact MergedCutProfiles.Batch692.valid27718
  · exact MergedCutProfiles.Batch692.valid27719
  · exact MergedCutProfiles.Batch693.valid27720
  · exact MergedCutProfiles.Batch693.valid27721
  · exact MergedCutProfiles.Batch693.valid27722
  · exact MergedCutProfiles.Batch693.valid27723
  · exact MergedCutProfiles.Batch693.valid27724
theorem numericValid4936 : retention4936.NumericValid := by decide +kernel
def certificate4936 : RatCutBinCertificate := ⟨⟨retention4936,(382016406455403279/200000000000000000),(6511012982960937/62500000000000000),(12577396975114151283/1000000000000000000),(27699124992646009937571/1000000000000000000),(423989883435232677/200000000000000000)⟩,(999938055512514283/1000000000000000000),(63064021077361529/200000000000000000),(40091578941589777/125000000000000000),(50046322054204573/125000000000000000)⟩
theorem valid4936 : certificate4936.Valid := by decide +kernel
theorem sound4936 : certificate4936.Sound := rat_cut_bin_certificate_sound certificate4936 profilesValid4936 numericValid4936 valid4936

def retention4937 : RatCutRetentionCertificate := ⟨(93/2000),(47/1000),(1/2),64,1,(255390584390425659150229438137492986359/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch693.profile27725,(fun _ => MergedCutProfiles.Batch693.profile27725)⟩
theorem profilesValid4937 : retention4937.ProfilesValid := by
  exact MergedCutProfiles.Batch693.valid27725
theorem numericValid4937 : retention4937.NumericValid := by decide +kernel
def certificate4937 : RatCutBinCertificate := ⟨⟨retention4937,(382016406455403279/200000000000000000),(6511012982960937/62500000000000000),(12577396975114151283/1000000000000000000),(27699124992646009937571/1000000000000000000),(981798620010296341/1000000000000000000)⟩,(999938055512514283/1000000000000000000),(269460171472058869/500000000000000000),(127925822436802397/1000000000000000000),(24738405692261933/200000000000000000)⟩
theorem valid4937 : certificate4937.Valid := by decide +kernel
theorem sound4937 : certificate4937.Sound := rat_cut_bin_certificate_sound certificate4937 profilesValid4937 numericValid4937 valid4937

def retention4938 : RatCutRetentionCertificate := ⟨(93/2000),(47/1000),(16000000000000000000/549031503247572455771),(17363563446128046143/500000000000000000),1,(18701722913590679954146765361429426049/8681781723064023071500000000000000000),false,MergedCutProfiles.Batch693.profile27726,(fun _ => MergedCutProfiles.Batch693.profile27726)⟩
theorem profilesValid4938 : retention4938.ProfilesValid := by
  exact MergedCutProfiles.Batch693.valid27726
theorem numericValid4938 : retention4938.NumericValid := by decide +kernel
def certificate4938 : RatCutBinCertificate := ⟨⟨retention4938,(349160254455403279/200000000000000000),(6511012982960937/62500000000000000),(12577396975114151283/1000000000000000000),(27699124992646009937571/1000000000000000000),(2139674054162488393/1000000000000000000)⟩,(249985845804264393/250000000000000000),(19102099297892551/1000000000000000000),(876734438386669109/1000000000000000000),(1766949053808885509/1000000000000000000)⟩
theorem valid4938 : certificate4938.Valid := by decide +kernel
theorem sound4938 : certificate4938.Sound := rat_cut_bin_certificate_sound certificate4938 profilesValid4938 numericValid4938 valid4938

def retention4939 : RatCutRetentionCertificate := ⟨(93/2000),(47/1000),(1/2),64,1,(255390584390425659150229438137492986359/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch693.profile27725,(fun _ => MergedCutProfiles.Batch693.profile27725)⟩
theorem profilesValid4939 : retention4939.ProfilesValid := by
  exact MergedCutProfiles.Batch693.valid27725
theorem numericValid4939 : retention4939.NumericValid := by decide +kernel
def certificate4939 : RatCutBinCertificate := ⟨⟨retention4939,(349160254455403279/200000000000000000),(6511012982960937/62500000000000000),(12577396975114151283/1000000000000000000),(27699124992646009937571/1000000000000000000),(15361864478919749/15625000000000000)⟩,(249985845804264393/250000000000000000),(41572373001808069/1000000000000000000),(202840811019018619/250000000000000000),(785585628249789067/1000000000000000000)⟩
theorem valid4939 : certificate4939.Valid := by decide +kernel
theorem sound4939 : certificate4939.Sound := rat_cut_bin_certificate_sound certificate4939 profilesValid4939 numericValid4939 valid4939

def retention4940 : RatCutRetentionCertificate := ⟨(93/2000),(47/1000),(354033348477305463/1098063006495144911542),(701056135598624679/1000000000000000000),4,(422012264541730077616927744173641057/175264033899656169750000000000000000),false,MergedCutProfiles.Batch693.profile27727,(fun _ => MergedCutProfiles.Batch693.profile27727)⟩
theorem profilesValid4940 : retention4940.ProfilesValid := by
  exact MergedCutProfiles.Batch693.valid27727
theorem numericValid4940 : retention4940.NumericValid := by decide +kernel
def certificate4940 : RatCutBinCertificate := ⟨⟨retention4940,(374833516855403279/200000000000000000),(6511012982960937/62500000000000000),(12577396975114151283/1000000000000000000),(27699124992646009937571/1000000000000000000),(2345772160401322529/1000000000000000000)⟩,(62496201264749449/62500000000000000),(170983076542773807/200000000000000000),(11074252218793313/1000000000000000000),(268538352271609/50000000000000000)⟩
theorem valid4940 : certificate4940.Valid := by decide +kernel
theorem sound4940 : certificate4940.Sound := rat_cut_bin_certificate_sound certificate4940 profilesValid4940 numericValid4940 valid4940

def retention4941 : RatCutRetentionCertificate := ⟨(93/2000),(47/1000),(436307845277650177/1098063006495144911542),(354033348477305463/500000000000000000),4,(1706984210607459225592778772797294279/708066696954610926000000000000000000),false,MergedCutProfiles.Batch693.profile27728,(fun _ => MergedCutProfiles.Batch693.profile27728)⟩
theorem profilesValid4941 : retention4941.ProfilesValid := by
  exact MergedCutProfiles.Batch693.valid27728
theorem numericValid4941 : retention4941.NumericValid := by decide +kernel
def certificate4941 : RatCutBinCertificate := ⟨⟨retention4941,(374833516855403279/200000000000000000),(6511012982960937/62500000000000000),(12577396975114151283/1000000000000000000),(27699124992646009937571/1000000000000000000),(2348673952635782741/1000000000000000000)⟩,(62496201264749449/62500000000000000),(851813184122817111/1000000000000000000),(5783082857272811/500000000000000000),(5624714224792541/1000000000000000000)⟩
theorem valid4941 : certificate4941.Valid := by decide +kernel
theorem sound4941 : certificate4941.Sound := rat_cut_bin_certificate_sound certificate4941 profilesValid4941 numericValid4941 valid4941

def retention4942 : RatCutRetentionCertificate := ⟨(93/2000),(47/1000),(4161776002631480533/2196126012990289823084),(436307845277650177/500000000000000000),(73/20),(839679661674057931526409867845788631599/349046276222120141600000000000000000000),false,MergedCutProfiles.Batch693.profile27729,(fun _ => MergedCutProfiles.Batch693.profile27729)⟩
theorem profilesValid4942 : retention4942.ProfilesValid := by
  exact MergedCutProfiles.Batch693.valid27729
theorem numericValid4942 : retention4942.NumericValid := by decide +kernel
def certificate4942 : RatCutBinCertificate := ⟨⟨retention4942,(374833516855403279/200000000000000000),(6511012982960937/62500000000000000),(12577396975114151283/1000000000000000000),(27699124992646009937571/1000000000000000000),(2348979544250485133/1000000000000000000)⟩,(62496201264749449/62500000000000000),(20328174194753151/25000000000000000),(1866307476248221/100000000000000000),(9991119621906179/1000000000000000000)⟩
theorem valid4942 : certificate4942.Valid := by decide +kernel
theorem sound4942 : certificate4942.Sound := rat_cut_bin_certificate_sound certificate4942 profilesValid4942 numericValid4942 valid4942

def retention4943 : RatCutRetentionCertificate := ⟨(93/2000),(47/1000),(51592463866795013737/2196126012990289823084),(4161776002631480533/1000000000000000000),(3/2),(147719809375087857124977656278238016911/66588416042103688528000000000000000000),false,MergedCutProfiles.Batch693.profile27730,(fun _ => MergedCutProfiles.Batch693.profile27730)⟩
theorem profilesValid4943 : retention4943.ProfilesValid := by
  exact MergedCutProfiles.Batch693.valid27730
theorem numericValid4943 : retention4943.NumericValid := by decide +kernel
def certificate4943 : RatCutBinCertificate := ⟨⟨retention4943,(374833516855403279/200000000000000000),(6511012982960937/62500000000000000),(12577396975114151283/1000000000000000000),(27699124992646009937571/1000000000000000000),(1097557965232550297/500000000000000000)⟩,(62496201264749449/62500000000000000),(364869010046216259/500000000000000000),(10085912793163537/250000000000000000),(47824397690025607/1000000000000000000)⟩
theorem valid4943 : certificate4943.Valid := by decide +kernel
theorem sound4943 : certificate4943.Sound := rat_cut_bin_certificate_sound certificate4943 profilesValid4943 numericValid4943 valid4943

def certificates : List RatCutBinCertificate := [certificate4932,certificate4933,certificate4934,certificate4935,certificate4936,certificate4937,certificate4938,certificate4939,certificate4940,certificate4941,certificate4942,certificate4943]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4932,List.forall_mem_cons.mpr ⟨sound4933,List.forall_mem_cons.mpr ⟨sound4934,List.forall_mem_cons.mpr ⟨sound4935,List.forall_mem_cons.mpr ⟨sound4936,List.forall_mem_cons.mpr ⟨sound4937,List.forall_mem_cons.mpr ⟨sound4938,List.forall_mem_cons.mpr ⟨sound4939,List.forall_mem_cons.mpr ⟨sound4940,List.forall_mem_cons.mpr ⟨sound4941,List.forall_mem_cons.mpr ⟨sound4942,List.forall_mem_cons.mpr ⟨sound4943,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch411
