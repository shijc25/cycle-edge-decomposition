import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch670
import Cycle12.MergedCutProfiles.Batch671
import Cycle12.MergedCutProfiles.Batch672

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch396

def retention4752 : RatCutRetentionCertificate := ⟨(311/8000),(39/1000),(1148544894000000000/3332425821775927600291),(29364921896406147/50000000000000000),4,(143813055005775415903/64000000000000000000),true,MergedCutProfiles.Batch670.profile26819,![MergedCutProfiles.Batch670.profile26819,MergedCutProfiles.Batch670.profile26821,MergedCutProfiles.Batch670.profile26823,MergedCutProfiles.Batch670.profile26825,MergedCutProfiles.Batch670.profile26827,MergedCutProfiles.Batch670.profile26829,MergedCutProfiles.Batch670.profile26831,MergedCutProfiles.Batch670.profile26832,MergedCutProfiles.Batch670.profile26834,MergedCutProfiles.Batch670.profile26835,MergedCutProfiles.Batch670.profile26836,MergedCutProfiles.Batch670.profile26837,MergedCutProfiles.Batch670.profile26838,MergedCutProfiles.Batch670.profile26839,MergedCutProfiles.Batch671.profile26840,MergedCutProfiles.Batch671.profile26841]⟩
theorem profilesValid4752 : retention4752.ProfilesValid := by
  change ∀ j : Fin 16, (retention4752.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch670.valid26819
  · exact MergedCutProfiles.Batch670.valid26821
  · exact MergedCutProfiles.Batch670.valid26823
  · exact MergedCutProfiles.Batch670.valid26825
  · exact MergedCutProfiles.Batch670.valid26827
  · exact MergedCutProfiles.Batch670.valid26829
  · exact MergedCutProfiles.Batch670.valid26831
  · exact MergedCutProfiles.Batch670.valid26832
  · exact MergedCutProfiles.Batch670.valid26834
  · exact MergedCutProfiles.Batch670.valid26835
  · exact MergedCutProfiles.Batch670.valid26836
  · exact MergedCutProfiles.Batch670.valid26837
  · exact MergedCutProfiles.Batch670.valid26838
  · exact MergedCutProfiles.Batch670.valid26839
  · exact MergedCutProfiles.Batch671.valid26840
  · exact MergedCutProfiles.Batch671.valid26841
theorem numericValid4752 : retention4752.NumericValid := by decide +kernel
def certificate4752 : RatCutBinCertificate := ⟨⟨retention4752,(235126540587285351/125000000000000000),(69043717129131353/1000000000000000000),(2231872470360797053/200000000000000000),(4651573464116167766979/125000000000000000),(440105430845872787/200000000000000000)⟩,(999952917802806253/1000000000000000000),(350129824574145641/500000000000000000),(6279372130078333/125000000000000000),(22390822812783589/1000000000000000000)⟩
theorem valid4752 : certificate4752.Valid := by decide +kernel
theorem sound4752 : certificate4752.Sound := rat_cut_bin_certificate_sound certificate4752 profilesValid4752 numericValid4752 valid4752

def retention4753 : RatCutRetentionCertificate := ⟨(311/8000),(39/1000),(3251884682387950183/3332425821775927600291),(574272447/500000000),(11/4),(10691252038486428406260729929102519/4486503492187500000000000000000000),true,MergedCutProfiles.Batch670.profile26822,![MergedCutProfiles.Batch670.profile26822,MergedCutProfiles.Batch670.profile26828,MergedCutProfiles.Batch670.profile26833,MergedCutProfiles.Batch670.profile26836,MergedCutProfiles.Batch670.profile26839,MergedCutProfiles.Batch671.profile26842,MergedCutProfiles.Batch671.profile26843,MergedCutProfiles.Batch671.profile26844,MergedCutProfiles.Batch671.profile26845,MergedCutProfiles.Batch671.profile26846,MergedCutProfiles.Batch671.profile26847,MergedCutProfiles.Batch671.profile26848,MergedCutProfiles.Batch671.profile26849,MergedCutProfiles.Batch671.profile26850,MergedCutProfiles.Batch671.profile26851,MergedCutProfiles.Batch671.profile26852]⟩
theorem profilesValid4753 : retention4753.ProfilesValid := by
  change ∀ j : Fin 16, (retention4753.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch670.valid26822
  · exact MergedCutProfiles.Batch670.valid26828
  · exact MergedCutProfiles.Batch670.valid26833
  · exact MergedCutProfiles.Batch670.valid26836
  · exact MergedCutProfiles.Batch670.valid26839
  · exact MergedCutProfiles.Batch671.valid26842
  · exact MergedCutProfiles.Batch671.valid26843
  · exact MergedCutProfiles.Batch671.valid26844
  · exact MergedCutProfiles.Batch671.valid26845
  · exact MergedCutProfiles.Batch671.valid26846
  · exact MergedCutProfiles.Batch671.valid26847
  · exact MergedCutProfiles.Batch671.valid26848
  · exact MergedCutProfiles.Batch671.valid26849
  · exact MergedCutProfiles.Batch671.valid26850
  · exact MergedCutProfiles.Batch671.valid26851
  · exact MergedCutProfiles.Batch671.valid26852
theorem numericValid4753 : retention4753.NumericValid := by decide +kernel
def certificate4753 : RatCutBinCertificate := ⟨⟨retention4753,(235126540587285351/125000000000000000),(69043717129131353/1000000000000000000),(2231872470360797053/200000000000000000),(4651573464116167766979/125000000000000000),(2350976502866461903/1000000000000000000)⟩,(999952917802806253/1000000000000000000),(44058199907681991/100000000000000000),(49572688319008237/250000000000000000),(133402150628378333/1000000000000000000)⟩
theorem valid4753 : certificate4753.Valid := by decide +kernel
theorem sound4753 : certificate4753.Sound := rat_cut_bin_certificate_sound certificate4753 profilesValid4753 numericValid4753 valid4753

def retention4754 : RatCutRetentionCertificate := ⟨(311/8000),(39/1000),(64000000000000000000/3332425821775927600291),(3251884682387950183/1000000000000000000),(29/20),(11423165997123260856565507453320992353831/5203015491820720292800000000000000000000),true,MergedCutProfiles.Batch671.profile26853,![MergedCutProfiles.Batch671.profile26853,MergedCutProfiles.Batch671.profile26854,MergedCutProfiles.Batch671.profile26855,MergedCutProfiles.Batch671.profile26856,MergedCutProfiles.Batch671.profile26857,MergedCutProfiles.Batch671.profile26858,MergedCutProfiles.Batch671.profile26859,MergedCutProfiles.Batch671.profile26860,MergedCutProfiles.Batch671.profile26861,MergedCutProfiles.Batch671.profile26862,MergedCutProfiles.Batch671.profile26863,MergedCutProfiles.Batch671.profile26864,MergedCutProfiles.Batch671.profile26865,MergedCutProfiles.Batch671.profile26866,MergedCutProfiles.Batch671.profile26867,MergedCutProfiles.Batch671.profile26868]⟩
theorem profilesValid4754 : retention4754.ProfilesValid := by
  change ∀ j : Fin 16, (retention4754.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch671.valid26853
  · exact MergedCutProfiles.Batch671.valid26854
  · exact MergedCutProfiles.Batch671.valid26855
  · exact MergedCutProfiles.Batch671.valid26856
  · exact MergedCutProfiles.Batch671.valid26857
  · exact MergedCutProfiles.Batch671.valid26858
  · exact MergedCutProfiles.Batch671.valid26859
  · exact MergedCutProfiles.Batch671.valid26860
  · exact MergedCutProfiles.Batch671.valid26861
  · exact MergedCutProfiles.Batch671.valid26862
  · exact MergedCutProfiles.Batch671.valid26863
  · exact MergedCutProfiles.Batch671.valid26864
  · exact MergedCutProfiles.Batch671.valid26865
  · exact MergedCutProfiles.Batch671.valid26866
  · exact MergedCutProfiles.Batch671.valid26867
  · exact MergedCutProfiles.Batch671.valid26868
theorem numericValid4754 : retention4754.NumericValid := by decide +kernel
def certificate4754 : RatCutBinCertificate := ⟨⟨retention4754,(235126540587285351/125000000000000000),(69043717129131353/1000000000000000000),(2231872470360797053/200000000000000000),(4651573464116167766979/125000000000000000),(435722898123368441/200000000000000000)⟩,(999952917802806253/1000000000000000000),(318506289354584573/1000000000000000000),(79268138180180853/250000000000000000),(361260243951381287/1000000000000000000)⟩
theorem valid4754 : certificate4754.Valid := by decide +kernel
theorem sound4754 : certificate4754.Sound := rat_cut_bin_certificate_sound certificate4754 profilesValid4754 numericValid4754 valid4754

def retention4755 : RatCutRetentionCertificate := ⟨(311/8000),(39/1000),(1/2),64,1,(3990362285233170126659738410853128231/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch671.profile26869,(fun _ => MergedCutProfiles.Batch671.profile26869)⟩
theorem profilesValid4755 : retention4755.ProfilesValid := by
  exact MergedCutProfiles.Batch671.valid26869
theorem numericValid4755 : retention4755.NumericValid := by decide +kernel
def certificate4755 : RatCutBinCertificate := ⟨⟨retention4755,(235126540587285351/125000000000000000),(69043717129131353/1000000000000000000),(2231872470360797053/200000000000000000),(4651573464116167766979/125000000000000000),(12324407782544383/12500000000000000)⟩,(999952917802806253/1000000000000000000),(524055431663596779/1000000000000000000),(137322034766470039/1000000000000000000),(133332530273855609/1000000000000000000)⟩
theorem valid4755 : certificate4755.Valid := by decide +kernel
theorem sound4755 : certificate4755.Sound := rat_cut_bin_certificate_sound certificate4755 profilesValid4755 numericValid4755 valid4755

def retention4756 : RatCutRetentionCertificate := ⟨(311/8000),(39/1000),(64000000000000000000/3332425821775927600291),(30017682955219351027/1000000000000000000),1,(1645780452914819370984691923173575401/750442073880483775675000000000000000),false,MergedCutProfiles.Batch671.profile26870,(fun _ => MergedCutProfiles.Batch671.profile26870)⟩
theorem profilesValid4756 : retention4756.ProfilesValid := by
  exact MergedCutProfiles.Batch671.valid26870
theorem numericValid4756 : retention4756.NumericValid := by decide +kernel
def certificate4756 : RatCutBinCertificate := ⟨⟨retention4756,(219198316962285351/125000000000000000),(69043717129131353/1000000000000000000),(2231872470360797053/200000000000000000),(4651573464116167766979/125000000000000000),(272778963510888417/125000000000000000)⟩,(499978053655842127/500000000000000000),(4231035619450977/200000000000000000),(54406278970498727/62500000000000000),(354162732337646753/200000000000000000)⟩
theorem valid4756 : certificate4756.Valid := by decide +kernel
theorem sound4756 : certificate4756.Sound := rat_cut_bin_certificate_sound certificate4756 profilesValid4756 numericValid4756 valid4756

def retention4757 : RatCutRetentionCertificate := ⟨(311/8000),(39/1000),(1/2),64,1,(3990362285233170126659738410853128231/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch671.profile26869,(fun _ => MergedCutProfiles.Batch671.profile26869)⟩
theorem profilesValid4757 : retention4757.ProfilesValid := by
  exact MergedCutProfiles.Batch671.valid26869
theorem numericValid4757 : retention4757.NumericValid := by decide +kernel
def certificate4757 : RatCutBinCertificate := ⟨⟨retention4757,(219198316962285351/125000000000000000),(69043717129131353/1000000000000000000),(2231872470360797053/200000000000000000),(4651573464116167766979/125000000000000000),(493370507229300977/500000000000000000)⟩,(499978053655842127/500000000000000000),(2924114569932849/62500000000000000),(797045936733585797/1000000000000000000),(774501910372009651/1000000000000000000)⟩
theorem valid4757 : certificate4757.Valid := by decide +kernel
theorem sound4757 : certificate4757.Sound := rat_cut_bin_certificate_sound certificate4757 profilesValid4757 numericValid4757 valid4757

def retention4758 : RatCutRetentionCertificate := ⟨(311/8000),(39/1000),(696322743983337944/3332425821775927600291),(172357114847360877/250000000000000000),4,(2111609752459735566506019112191163/882468428018487690240000000000000),false,MergedCutProfiles.Batch671.profile26871,(fun _ => MergedCutProfiles.Batch671.profile26871)⟩
theorem profilesValid4758 : retention4758.ProfilesValid := by
  exact MergedCutProfiles.Batch671.valid26871
theorem numericValid4758 : retention4758.NumericValid := by decide +kernel
def certificate4758 : RatCutBinCertificate := ⟨⟨retention4758,(230094191962285351/125000000000000000),(69043717129131353/1000000000000000000),(2231872470360797053/200000000000000000),(4651573464116167766979/125000000000000000),(293411130361304331/125000000000000000)⟩,(99995392549353011/100000000000000000),(425182191426023901/500000000000000000),(11799768907551503/1000000000000000000),(2854563156586121/500000000000000000)⟩
theorem valid4758 : certificate4758.Valid := by decide +kernel
theorem sound4758 : certificate4758.Sound := rat_cut_bin_certificate_sound certificate4758 profilesValid4758 numericValid4758 valid4758

def retention4759 : RatCutRetentionCertificate := ⟨(311/8000),(39/1000),(938537855199574617/3332425821775927600291),(87040342997917243/125000000000000000),4,(1334661149626664649337004627533758051/557058195186670355200000000000000000),false,MergedCutProfiles.Batch671.profile26872,(fun _ => MergedCutProfiles.Batch671.profile26872)⟩
theorem profilesValid4759 : retention4759.ProfilesValid := by
  exact MergedCutProfiles.Batch671.valid26872
theorem numericValid4759 : retention4759.NumericValid := by decide +kernel
def certificate4759 : RatCutBinCertificate := ⟨⟨retention4759,(230094191962285351/125000000000000000),(69043717129131353/1000000000000000000),(2231872470360797053/200000000000000000),(4651573464116167766979/125000000000000000),(146897140043280557/62500000000000000)⟩,(99995392549353011/100000000000000000),(847057170166561287/1000000000000000000),(3085568908386619/250000000000000000),(1497113110923639/250000000000000000)⟩
theorem valid4759 : certificate4759.Valid := by decide +kernel
theorem sound4759 : certificate4759.Sound := rat_cut_bin_certificate_sound certificate4759 profilesValid4759 numericValid4759 valid4759

def retention4760 : RatCutRetentionCertificate := ⟨(311/8000),(39/1000),(8295310614471109346/3332425821775927600291),(938537855199574617/1000000000000000000),(69/20),(3578860107686469507843693280402860540311/1501660568319319387200000000000000000000),false,MergedCutProfiles.Batch671.profile26873,(fun _ => MergedCutProfiles.Batch671.profile26873)⟩
theorem profilesValid4760 : retention4760.ProfilesValid := by
  exact MergedCutProfiles.Batch671.valid26873
theorem numericValid4760 : retention4760.NumericValid := by decide +kernel
def certificate4760 : RatCutBinCertificate := ⟨⟨retention4760,(230094191962285351/125000000000000000),(69043717129131353/1000000000000000000),(2231872470360797053/200000000000000000),(4651573464116167766979/125000000000000000),(2343976746589806791/1000000000000000000)⟩,(99995392549353011/100000000000000000),(49529785822051009/62500000000000000),(23199450773467519/1000000000000000000),(6513810302642821/500000000000000000)⟩
theorem valid4760 : certificate4760.Valid := by decide +kernel
theorem sound4760 : certificate4760.Sound := rat_cut_bin_certificate_sound certificate4760 profilesValid4760 numericValid4760 valid4760

def retention4761 : RatCutRetentionCertificate := ⟨(311/8000),(39/1000),(1/40),(4147655307235554673/500000000000000000),(6/5),(454555459508669348344729067171641235871/207382765361777733650000000000000000000),false,MergedCutProfiles.Batch671.profile26874,(fun _ => MergedCutProfiles.Batch671.profile26874)⟩
theorem profilesValid4761 : retention4761.ProfilesValid := by
  exact MergedCutProfiles.Batch671.valid26874
theorem numericValid4761 : retention4761.NumericValid := by decide +kernel
def certificate4761 : RatCutBinCertificate := ⟨⟨retention4761,(230094191962285351/125000000000000000),(69043717129131353/1000000000000000000),(2231872470360797053/200000000000000000),(4651573464116167766979/125000000000000000),(217820045518118853/100000000000000000)⟩,(99995392549353011/100000000000000000),(43544976449857599/62500000000000000),(51505265819147069/1000000000000000000),(79068150147294197/1000000000000000000)⟩
theorem valid4761 : certificate4761.Valid := by decide +kernel
theorem sound4761 : certificate4761.Sound := rat_cut_bin_certificate_sound certificate4761 profilesValid4761 numericValid4761 valid4761

def retention4762 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(634263522357221173/3239912467432955022712),(36245774847118113/62500000000000000),4,(143929038179218640735577353264427023/64436933061543312000000000000000000),true,MergedCutProfiles.Batch671.profile26875,![MergedCutProfiles.Batch671.profile26875,MergedCutProfiles.Batch671.profile26876,MergedCutProfiles.Batch671.profile26877,MergedCutProfiles.Batch671.profile26878,MergedCutProfiles.Batch671.profile26879,MergedCutProfiles.Batch672.profile26880,MergedCutProfiles.Batch672.profile26881,MergedCutProfiles.Batch672.profile26882,MergedCutProfiles.Batch672.profile26883,MergedCutProfiles.Batch672.profile26884,MergedCutProfiles.Batch672.profile26885,MergedCutProfiles.Batch672.profile26886,MergedCutProfiles.Batch672.profile26887,MergedCutProfiles.Batch672.profile26888,MergedCutProfiles.Batch672.profile26889,MergedCutProfiles.Batch672.profile26890]⟩
theorem profilesValid4762 : retention4762.ProfilesValid := by
  change ∀ j : Fin 16, (retention4762.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch671.valid26875
  · exact MergedCutProfiles.Batch671.valid26876
  · exact MergedCutProfiles.Batch671.valid26877
  · exact MergedCutProfiles.Batch671.valid26878
  · exact MergedCutProfiles.Batch671.valid26879
  · exact MergedCutProfiles.Batch672.valid26880
  · exact MergedCutProfiles.Batch672.valid26881
  · exact MergedCutProfiles.Batch672.valid26882
  · exact MergedCutProfiles.Batch672.valid26883
  · exact MergedCutProfiles.Batch672.valid26884
  · exact MergedCutProfiles.Batch672.valid26885
  · exact MergedCutProfiles.Batch672.valid26886
  · exact MergedCutProfiles.Batch672.valid26887
  · exact MergedCutProfiles.Batch672.valid26888
  · exact MergedCutProfiles.Batch672.valid26889
  · exact MergedCutProfiles.Batch672.valid26890
theorem numericValid4762 : retention4762.NumericValid := by decide +kernel
def certificate4762 : RatCutBinCertificate := ⟨⟨retention4762,(941217283656937391/500000000000000000),(70986334890534179/1000000000000000000),(11180591871833216343/1000000000000000000),(36321210023289684453751/1000000000000000000),(1092917556367336617/500000000000000000)⟩,(99995175076605437/100000000000000000),(706309314001331351/1000000000000000000),(24052756931907901/500000000000000000),(2659313192694733/125000000000000000)⟩
theorem valid4762 : certificate4762.Valid := by decide +kernel
theorem sound4762 : certificate4762.Sound := rat_cut_bin_certificate_sound certificate4762 profilesValid4762 numericValid4762 valid4762

def retention4763 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(144462733625000000/404989058429119377839),(634263522357221173/1000000000000000000),4,(46143455442738468453674782438343561/19820735073663161656250000000000000),true,MergedCutProfiles.Batch672.profile26891,![MergedCutProfiles.Batch672.profile26891,MergedCutProfiles.Batch672.profile26892,MergedCutProfiles.Batch671.profile26879,MergedCutProfiles.Batch672.profile26893,MergedCutProfiles.Batch672.profile26883,MergedCutProfiles.Batch672.profile26885,MergedCutProfiles.Batch672.profile26887,MergedCutProfiles.Batch672.profile26889,MergedCutProfiles.Batch672.profile26894,MergedCutProfiles.Batch672.profile26895,MergedCutProfiles.Batch672.profile26896,MergedCutProfiles.Batch672.profile26897,MergedCutProfiles.Batch672.profile26898,MergedCutProfiles.Batch672.profile26899,MergedCutProfiles.Batch672.profile26900,MergedCutProfiles.Batch672.profile26901]⟩
theorem profilesValid4763 : retention4763.ProfilesValid := by
  change ∀ j : Fin 16, (retention4763.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch672.valid26891
  · exact MergedCutProfiles.Batch672.valid26892
  · exact MergedCutProfiles.Batch671.valid26879
  · exact MergedCutProfiles.Batch672.valid26893
  · exact MergedCutProfiles.Batch672.valid26883
  · exact MergedCutProfiles.Batch672.valid26885
  · exact MergedCutProfiles.Batch672.valid26887
  · exact MergedCutProfiles.Batch672.valid26889
  · exact MergedCutProfiles.Batch672.valid26894
  · exact MergedCutProfiles.Batch672.valid26895
  · exact MergedCutProfiles.Batch672.valid26896
  · exact MergedCutProfiles.Batch672.valid26897
  · exact MergedCutProfiles.Batch672.valid26898
  · exact MergedCutProfiles.Batch672.valid26899
  · exact MergedCutProfiles.Batch672.valid26900
  · exact MergedCutProfiles.Batch672.valid26901
theorem numericValid4763 : retention4763.NumericValid := by decide +kernel
def certificate4763 : RatCutBinCertificate := ⟨⟨retention4763,(941217283656937391/500000000000000000),(70986334890534179/1000000000000000000),(11180591871833216343/1000000000000000000),(36321210023289684453751/1000000000000000000),(456046541841795031/200000000000000000)⟩,(99995175076605437/100000000000000000),(127606095854304833/200000000000000000),(75258259438126961/1000000000000000000),(218927879888003/6250000000000000)⟩
theorem valid4763 : certificate4763.Valid := by decide +kernel
theorem sound4763 : certificate4763.Sound := rat_cut_bin_certificate_sound certificate4763 profilesValid4763 numericValid4763 valid4763

def certificates : List RatCutBinCertificate := [certificate4752,certificate4753,certificate4754,certificate4755,certificate4756,certificate4757,certificate4758,certificate4759,certificate4760,certificate4761,certificate4762,certificate4763]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4752,List.forall_mem_cons.mpr ⟨sound4753,List.forall_mem_cons.mpr ⟨sound4754,List.forall_mem_cons.mpr ⟨sound4755,List.forall_mem_cons.mpr ⟨sound4756,List.forall_mem_cons.mpr ⟨sound4757,List.forall_mem_cons.mpr ⟨sound4758,List.forall_mem_cons.mpr ⟨sound4759,List.forall_mem_cons.mpr ⟨sound4760,List.forall_mem_cons.mpr ⟨sound4761,List.forall_mem_cons.mpr ⟨sound4762,List.forall_mem_cons.mpr ⟨sound4763,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch396
