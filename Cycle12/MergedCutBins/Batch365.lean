import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch012
import Cycle12.MergedCutProfiles.Batch013
import Cycle12.MergedCutProfiles.Batch313
import Cycle12.MergedCutProfiles.Batch568
import Cycle12.MergedCutProfiles.Batch569
import Cycle12.MergedCutProfiles.Batch646

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch365

def retention4380 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(1/2),64,1,(63842289268809469711650675485864946351/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch012.profile509,(fun _ => MergedCutProfiles.Batch012.profile509)⟩
theorem profilesValid4380 : retention4380.ProfilesValid := by
  exact MergedCutProfiles.Batch012.valid509
theorem numericValid4380 : retention4380.NumericValid := by decide +kernel
def certificate4380 : RatCutBinCertificate := ⟨⟨retention4380,(113439164896524909/62500000000000000),(246507623072377/50000000000000000),(1881196017164384497/250000000000000000),(45427313556122745628759/125000000000000000),(249086646282440779/250000000000000000)⟩,(999995025966853767/1000000000000000000),(207395827436690249/500000000000000000),(22019957753329787/100000000000000000),(108015423284138237/500000000000000000)⟩
theorem valid4380 : certificate4380.Valid := by decide +kernel
theorem sound4380 : certificate4380.Sound := rat_cut_bin_certificate_sound certificate4380 profilesValid4380 numericValid4380 valid4380

def retention4381 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(12800000000000000000/9615687695137442862049),(8032331799323036389/500000000000000000),1,(146963961049689477531042457800860972647/64258654394584291112000000000000000000),false,MergedCutProfiles.Batch646.profile25844,(fun _ => MergedCutProfiles.Batch646.profile25844)⟩
theorem profilesValid4381 : retention4381.ProfilesValid := by
  exact MergedCutProfiles.Batch646.valid25844
theorem numericValid4381 : retention4381.NumericValid := by decide +kernel
def certificate4381 : RatCutBinCertificate := ⟨⟨retention4381,(102259621021524909/62500000000000000),(246507623072377/50000000000000000),(1881196017164384497/250000000000000000),(45427313556122745628759/125000000000000000),(1142998385514573941/500000000000000000)⟩,(249998879040708891/250000000000000000),(33091974411650111/1000000000000000000),(417657529426812897/500000000000000000),(1671644211852558417/1000000000000000000)⟩
theorem valid4381 : certificate4381.Valid := by decide +kernel
theorem sound4381 : certificate4381.Sound := rat_cut_bin_certificate_sound certificate4381 profilesValid4381 numericValid4381 valid4381

def retention4382 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(1/2),64,1,(63842289268809469711650675485864946351/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch012.profile509,(fun _ => MergedCutProfiles.Batch012.profile509)⟩
theorem profilesValid4382 : retention4382.ProfilesValid := by
  exact MergedCutProfiles.Batch012.valid509
theorem numericValid4382 : retention4382.NumericValid := by decide +kernel
def certificate4382 : RatCutBinCertificate := ⟨⟨retention4382,(102259621021524909/62500000000000000),(246507623072377/50000000000000000),(1881196017164384497/250000000000000000),(45427313556122745628759/125000000000000000),(62278986279899123/62500000000000000)⟩,(249998879040708891/250000000000000000),(3036664177224541/40000000000000000),(28890574877221537/40000000000000000),(708673167260426743/1000000000000000000)⟩
theorem valid4382 : certificate4382.Valid := by decide +kernel
theorem sound4382 : certificate4382.Sound := rat_cut_bin_certificate_sound certificate4382 profilesValid4382 numericValid4382 valid4382

def retention4383 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(690985546291581551/48078438475687214310245),(342072052619594827/500000000000000000),4,(1300659653389033330437964082302048307/547315284191351723200000000000000000),false,MergedCutProfiles.Batch646.profile25845,(fun _ => MergedCutProfiles.Batch646.profile25845)⟩
theorem profilesValid4383 : retention4383.ProfilesValid := by
  exact MergedCutProfiles.Batch646.valid25845
theorem numericValid4383 : retention4383.NumericValid := by decide +kernel
def certificate4383 : RatCutBinCertificate := ⟨⟨retention4383,(110193037146524909/62500000000000000),(246507623072377/50000000000000000),(1881196017164384497/250000000000000000),(45427313556122745628759/125000000000000000),(2371815211207249967/1000000000000000000)⟩,(99999516830171103/100000000000000000),(731192471132725331/1000000000000000000),(7977369244349963/200000000000000000),(2429868273455427/125000000000000000)⟩
theorem valid4383 : certificate4383.Valid := by decide +kernel
theorem sound4383 : certificate4383.Sound := rat_cut_bin_certificate_sound certificate4383 profilesValid4383 numericValid4383 valid4383

def retention4384 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(3463630185750525702/48078438475687214310245),(690985546291581551/1000000000000000000),4,(410563678268067957870471862234229217/172746386572895387750000000000000000),false,MergedCutProfiles.Batch646.profile25846,(fun _ => MergedCutProfiles.Batch646.profile25846)⟩
theorem profilesValid4384 : retention4384.ProfilesValid := by
  exact MergedCutProfiles.Batch646.valid25846
theorem numericValid4384 : retention4384.NumericValid := by decide +kernel
def certificate4384 : RatCutBinCertificate := ⟨⟨retention4384,(110193037146524909/62500000000000000),(246507623072377/50000000000000000),(1881196017164384497/250000000000000000),(45427313556122745628759/125000000000000000),(2372063987277453643/1000000000000000000)⟩,(99999516830171103/100000000000000000),(728772093210876393/1000000000000000000),(20324312507282869/500000000000000000),(19846907040195227/1000000000000000000)⟩
theorem valid4384 : certificate4384.Valid := by decide +kernel
theorem sound4384 : certificate4384.Sound := rat_cut_bin_certificate_sound certificate4384 profilesValid4384 numericValid4384 valid4384

def retention4385 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(1/40),(1731815092875262851/500000000000000000),(31/20),(3004468974755030637787321372640911410599/1385452074300210280800000000000000000000),false,MergedCutProfiles.Batch646.profile25847,(fun _ => MergedCutProfiles.Batch646.profile25847)⟩
theorem profilesValid4385 : retention4385.ProfilesValid := by
  exact MergedCutProfiles.Batch646.valid25847
theorem numericValid4385 : retention4385.NumericValid := by decide +kernel
def certificate4385 : RatCutBinCertificate := ⟨⟨retention4385,(110193037146524909/62500000000000000),(246507623072377/50000000000000000),(1881196017164384497/250000000000000000),(45427313556122745628759/125000000000000000),(86671733825150993/40000000000000000)⟩,(99999516830171103/100000000000000000),(29621274883856079/50000000000000000),(12177735953017437/125000000000000000),(54026330406898707/500000000000000000)⟩
theorem valid4385 : certificate4385.Valid := by decide +kernel
theorem sound4385 : certificate4385.Sound := rat_cut_bin_certificate_sound certificate4385 profilesValid4385 numericValid4385 valid4385

def retention4386 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(391779635426963255/20108024706910554078163),(116268116098219351/200000000000000000),4,(5180240657952370689991134322373543311/2325362321964387020000000000000000000),true,MergedCutProfiles.Batch646.profile25848,![MergedCutProfiles.Batch646.profile25848,MergedCutProfiles.Batch646.profile25849,MergedCutProfiles.Batch646.profile25849,MergedCutProfiles.Batch568.profile22756,MergedCutProfiles.Batch646.profile25850,MergedCutProfiles.Batch646.profile25850,MergedCutProfiles.Batch646.profile25850,MergedCutProfiles.Batch568.profile22757,MergedCutProfiles.Batch568.profile22757,MergedCutProfiles.Batch568.profile22758,MergedCutProfiles.Batch568.profile22758,MergedCutProfiles.Batch568.profile22758,MergedCutProfiles.Batch568.profile22759,MergedCutProfiles.Batch568.profile22759,MergedCutProfiles.Batch568.profile22759,MergedCutProfiles.Batch569.profile22760]⟩
theorem profilesValid4386 : retention4386.ProfilesValid := by
  change ∀ j : Fin 16, (retention4386.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch646.valid25848
  · exact MergedCutProfiles.Batch646.valid25849
  · exact MergedCutProfiles.Batch646.valid25849
  · exact MergedCutProfiles.Batch568.valid22756
  · exact MergedCutProfiles.Batch646.valid25850
  · exact MergedCutProfiles.Batch646.valid25850
  · exact MergedCutProfiles.Batch646.valid25850
  · exact MergedCutProfiles.Batch568.valid22757
  · exact MergedCutProfiles.Batch568.valid22757
  · exact MergedCutProfiles.Batch568.valid22758
  · exact MergedCutProfiles.Batch568.valid22758
  · exact MergedCutProfiles.Batch568.valid22758
  · exact MergedCutProfiles.Batch568.valid22759
  · exact MergedCutProfiles.Batch568.valid22759
  · exact MergedCutProfiles.Batch568.valid22759
  · exact MergedCutProfiles.Batch569.valid22760
theorem numericValid4386 : retention4386.NumericValid := by decide +kernel
def certificate4386 : RatCutBinCertificate := ⟨⟨retention4386,(463444486923632951/250000000000000000),(5886872707676009/1000000000000000000),(7618207346444008837/1000000000000000000),(76942453293967764291679/250000000000000000),(444396680746005739/200000000000000000)⟩,(19999880128686077/20000000000000000),(562883225429744223/1000000000000000000),(56818650076658763/500000000000000000),(50952721307307073/1000000000000000000)⟩
theorem valid4386 : certificate4386.Valid := by decide +kernel
theorem sound4386 : certificate4386.Sound := rat_cut_bin_certificate_sound certificate4386 profilesValid4386 numericValid4386 valid4386

def retention4387 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(638960235000000000/20108024706910554078163),(78355927085392651/100000000000000000),(37/10),(1501574573175900353448061954565530971/626847416683141208000000000000000000),true,MergedCutProfiles.Batch646.profile25848,![MergedCutProfiles.Batch646.profile25848,MergedCutProfiles.Batch568.profile22756,MergedCutProfiles.Batch568.profile22756,MergedCutProfiles.Batch646.profile25850,MergedCutProfiles.Batch568.profile22757,MergedCutProfiles.Batch568.profile22758,MergedCutProfiles.Batch568.profile22758,MergedCutProfiles.Batch568.profile22759,MergedCutProfiles.Batch568.profile22759,MergedCutProfiles.Batch569.profile22760,MergedCutProfiles.Batch569.profile22760,MergedCutProfiles.Batch569.profile22760,MergedCutProfiles.Batch569.profile22761,MergedCutProfiles.Batch569.profile22761,MergedCutProfiles.Batch569.profile22762,MergedCutProfiles.Batch569.profile22762]⟩
theorem profilesValid4387 : retention4387.ProfilesValid := by
  change ∀ j : Fin 16, (retention4387.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch646.valid25848
  · exact MergedCutProfiles.Batch568.valid22756
  · exact MergedCutProfiles.Batch568.valid22756
  · exact MergedCutProfiles.Batch646.valid25850
  · exact MergedCutProfiles.Batch568.valid22757
  · exact MergedCutProfiles.Batch568.valid22758
  · exact MergedCutProfiles.Batch568.valid22758
  · exact MergedCutProfiles.Batch568.valid22759
  · exact MergedCutProfiles.Batch568.valid22759
  · exact MergedCutProfiles.Batch569.valid22760
  · exact MergedCutProfiles.Batch569.valid22760
  · exact MergedCutProfiles.Batch569.valid22760
  · exact MergedCutProfiles.Batch569.valid22761
  · exact MergedCutProfiles.Batch569.valid22761
  · exact MergedCutProfiles.Batch569.valid22762
  · exact MergedCutProfiles.Batch569.valid22762
theorem numericValid4387 : retention4387.NumericValid := by decide +kernel
def certificate4387 : RatCutBinCertificate := ⟨⟨retention4387,(463444486923632951/250000000000000000),(5886872707676009/1000000000000000000),(7618207346444008837/1000000000000000000),(76942453293967764291679/250000000000000000),(298767316413365207/125000000000000000)⟩,(19999880128686077/20000000000000000),(107906308546587959/250000000000000000),(51430946023764787/250000000000000000),(54338980607526187/500000000000000000)⟩
theorem valid4387 : certificate4387.Valid := by decide +kernel
theorem sound4387 : certificate4387.Sound := rat_cut_bin_certificate_sound certificate4387 profilesValid4387 numericValid4387 valid4387

def retention4388 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(3134793794145196212/20108024706910554078163),(127792047/100000000),(5/2),(6453515174670859977913725845768037/2726230336000000000000000000000000),true,MergedCutProfiles.Batch568.profile22757,![MergedCutProfiles.Batch568.profile22757,MergedCutProfiles.Batch569.profile22760,MergedCutProfiles.Batch569.profile22762,MergedCutProfiles.Batch569.profile22763,MergedCutProfiles.Batch313.profile12522,MergedCutProfiles.Batch569.profile22765,MergedCutProfiles.Batch569.profile22766,MergedCutProfiles.Batch569.profile22768,MergedCutProfiles.Batch012.profile510,MergedCutProfiles.Batch313.profile12530,MergedCutProfiles.Batch569.profile22769,MergedCutProfiles.Batch313.profile12540,MergedCutProfiles.Batch569.profile22770,MergedCutProfiles.Batch569.profile22770,MergedCutProfiles.Batch313.profile12523,MergedCutProfiles.Batch569.profile22771]⟩
theorem profilesValid4388 : retention4388.ProfilesValid := by
  change ∀ j : Fin 16, (retention4388.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch568.valid22757
  · exact MergedCutProfiles.Batch569.valid22760
  · exact MergedCutProfiles.Batch569.valid22762
  · exact MergedCutProfiles.Batch569.valid22763
  · exact MergedCutProfiles.Batch313.valid12522
  · exact MergedCutProfiles.Batch569.valid22765
  · exact MergedCutProfiles.Batch569.valid22766
  · exact MergedCutProfiles.Batch569.valid22768
  · exact MergedCutProfiles.Batch012.valid510
  · exact MergedCutProfiles.Batch313.valid12530
  · exact MergedCutProfiles.Batch569.valid22769
  · exact MergedCutProfiles.Batch313.valid12540
  · exact MergedCutProfiles.Batch569.valid22770
  · exact MergedCutProfiles.Batch569.valid22770
  · exact MergedCutProfiles.Batch313.valid12523
  · exact MergedCutProfiles.Batch569.valid22771
theorem numericValid4388 : retention4388.NumericValid := by decide +kernel
def certificate4388 : RatCutBinCertificate := ⟨⟨retention4388,(463444486923632951/250000000000000000),(5886872707676009/1000000000000000000),(7618207346444008837/1000000000000000000),(76942453293967764291679/250000000000000000),(2363612454511168841/1000000000000000000)⟩,(19999880128686077/20000000000000000),(41674002552376241/125000000000000000),(150194420028100581/500000000000000000),(219146622612945181/1000000000000000000)⟩
theorem valid4388 : certificate4388.Valid := by decide +kernel
theorem sound4388 : certificate4388.Sound := rat_cut_bin_certificate_sound certificate4388 profilesValid4388 numericValid4388 valid4388

def retention4389 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(32000000000000000000/20108024706910554078163),(783698448536299053/125000000000000000),(23/20),(1435595638593938082898414036820864984831/626958758829039242400000000000000000000),true,MergedCutProfiles.Batch313.profile12530,![MergedCutProfiles.Batch313.profile12530,MergedCutProfiles.Batch012.profile511,MergedCutProfiles.Batch313.profile12531,MergedCutProfiles.Batch013.profile526,MergedCutProfiles.Batch313.profile12532,MergedCutProfiles.Batch313.profile12528,MergedCutProfiles.Batch313.profile12529,MergedCutProfiles.Batch013.profile528,MergedCutProfiles.Batch646.profile25851,MergedCutProfiles.Batch313.profile12535,MergedCutProfiles.Batch013.profile542,MergedCutProfiles.Batch313.profile12536,MergedCutProfiles.Batch313.profile12537,MergedCutProfiles.Batch313.profile12546,MergedCutProfiles.Batch013.profile525,MergedCutProfiles.Batch313.profile12539]⟩
theorem profilesValid4389 : retention4389.ProfilesValid := by
  change ∀ j : Fin 16, (retention4389.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch313.valid12530
  · exact MergedCutProfiles.Batch012.valid511
  · exact MergedCutProfiles.Batch313.valid12531
  · exact MergedCutProfiles.Batch013.valid526
  · exact MergedCutProfiles.Batch313.valid12532
  · exact MergedCutProfiles.Batch313.valid12528
  · exact MergedCutProfiles.Batch313.valid12529
  · exact MergedCutProfiles.Batch013.valid528
  · exact MergedCutProfiles.Batch646.valid25851
  · exact MergedCutProfiles.Batch313.valid12535
  · exact MergedCutProfiles.Batch013.valid542
  · exact MergedCutProfiles.Batch313.valid12536
  · exact MergedCutProfiles.Batch313.valid12537
  · exact MergedCutProfiles.Batch313.valid12546
  · exact MergedCutProfiles.Batch013.valid525
  · exact MergedCutProfiles.Batch313.valid12539
theorem numericValid4389 : retention4389.NumericValid := by decide +kernel
def certificate4389 : RatCutBinCertificate := ⟨⟨retention4389,(463444486923632951/250000000000000000),(5886872707676009/1000000000000000000),(7618207346444008837/1000000000000000000),(76942453293967764291679/250000000000000000),(2288129473021949537/1000000000000000000)⟩,(19999880128686077/20000000000000000),(105011664410937087/500000000000000000),(57749472638427833/125000000000000000),(9005151064719837/12500000000000000)⟩
theorem valid4389 : certificate4389.Valid := by decide +kernel
theorem sound4389 : certificate4389.Sound := rat_cut_bin_certificate_sound certificate4389 profilesValid4389 numericValid4389 valid4389

def retention4390 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(1/2),64,1,(63842322836766415695342227016481542439/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch013.profile555,(fun _ => MergedCutProfiles.Batch013.profile555)⟩
theorem profilesValid4390 : retention4390.ProfilesValid := by
  exact MergedCutProfiles.Batch013.valid555
theorem numericValid4390 : retention4390.NumericValid := by decide +kernel
def certificate4390 : RatCutBinCertificate := ⟨⟨retention4390,(463444486923632951/250000000000000000),(5886872707676009/1000000000000000000),(7618207346444008837/1000000000000000000),(76942453293967764291679/250000000000000000),(249025952755793349/250000000000000000)⟩,(19999880128686077/20000000000000000),(102790733161947577/250000000000000000),(223408594375270547/1000000000000000000),(109563149413272267/500000000000000000)⟩
theorem valid4390 : certificate4390.Valid := by decide +kernel
theorem sound4390 : certificate4390.Sound := rat_cut_bin_certificate_sound certificate4390 profilesValid4390 numericValid4390 valid4390

def retention4391 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(32000000000000000000/20108024706910554078163),(8122098535421185937/500000000000000000),1,(7419139305857231253520039293165468351/3248839414168474374800000000000000000),false,MergedCutProfiles.Batch646.profile25852,(fun _ => MergedCutProfiles.Batch646.profile25852)⟩
theorem profilesValid4391 : retention4391.ProfilesValid := by
  exact MergedCutProfiles.Batch646.valid25852
theorem numericValid4391 : retention4391.NumericValid := by decide +kernel
def certificate4391 : RatCutBinCertificate := ⟨⟨retention4391,(442724114423632951/250000000000000000),(5886872707676009/1000000000000000000),(7618207346444008837/1000000000000000000),(76942453293967764291679/250000000000000000),(2282259147444790721/1000000000000000000)⟩,(999994274403652617/1000000000000000000),(30090180789884913/1000000000000000000),(843997229796627447/1000000000000000000),(1688920898146167523/1000000000000000000)⟩
theorem valid4391 : certificate4391.Valid := by decide +kernel
theorem sound4391 : certificate4391.Sound := rat_cut_bin_certificate_sound certificate4391 profilesValid4391 numericValid4391 valid4391

def certificates : List RatCutBinCertificate := [certificate4380,certificate4381,certificate4382,certificate4383,certificate4384,certificate4385,certificate4386,certificate4387,certificate4388,certificate4389,certificate4390,certificate4391]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4380,List.forall_mem_cons.mpr ⟨sound4381,List.forall_mem_cons.mpr ⟨sound4382,List.forall_mem_cons.mpr ⟨sound4383,List.forall_mem_cons.mpr ⟨sound4384,List.forall_mem_cons.mpr ⟨sound4385,List.forall_mem_cons.mpr ⟨sound4386,List.forall_mem_cons.mpr ⟨sound4387,List.forall_mem_cons.mpr ⟨sound4388,List.forall_mem_cons.mpr ⟨sound4389,List.forall_mem_cons.mpr ⟨sound4390,List.forall_mem_cons.mpr ⟨sound4391,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch365
