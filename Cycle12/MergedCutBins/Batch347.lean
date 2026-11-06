import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch397
import Cycle12.MergedCutProfiles.Batch398
import Cycle12.MergedCutProfiles.Batch399
import Cycle12.MergedCutProfiles.Batch520
import Cycle12.MergedCutProfiles.Batch521
import Cycle12.MergedCutProfiles.Batch624
import Cycle12.MergedCutProfiles.Batch625
import Cycle12.MergedCutProfiles.Batch626

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch347

def retention4164 : RatCutRetentionCertificate := ⟨(117/2000),(59/1000),(40015033987434044765/259856146211192519276),(184892243081129769/100000000000000000),(19/10),(654522448401854166222187892623682113/369784486162259538000000000000000000),false,MergedCutProfiles.Batch624.profile24999,(fun _ => MergedCutProfiles.Batch624.profile24999)⟩
theorem profilesValid4164 : retention4164.ProfilesValid := by
  exact MergedCutProfiles.Batch624.valid24999
theorem numericValid4164 : retention4164.NumericValid := by decide +kernel
def certificate4164 : RatCutBinCertificate := ⟨⟨retention4164,(2048786597038828997/1000000000000000000),(175338961017292427/1000000000000000000),(15441190913345225551/1000000000000000000),(4024676736448661465887/1000000000000000000),(1725807404974181467/1000000000000000000)⟩,(999578396734357809/1000000000000000000),(426481351441496307/1000000000000000000),(105038173201484839/500000000000000000),(2367822283238213/15625000000000000)⟩
theorem valid4164 : certificate4164.Valid := by decide +kernel
theorem sound4164 : certificate4164.Sound := rat_cut_bin_certificate_sound certificate4164 profilesValid4164 numericValid4164 valid4164

def retention4165 : RatCutRetentionCertificate := ⟨(117/2000),(59/1000),(16000000000000000000/64964036552798129819),(8003006797486808953/200000000000000000),1,(244304355605899573822611175571700333579/160060135949736179060000000000000000000),false,MergedCutProfiles.Batch625.profile25000,(fun _ => MergedCutProfiles.Batch625.profile25000)⟩
theorem profilesValid4165 : retention4165.ProfilesValid := by
  exact MergedCutProfiles.Batch625.valid25000
theorem numericValid4165 : retention4165.NumericValid := by decide +kernel
def certificate4165 : RatCutBinCertificate := ⟨⟨retention4165,(2048786597038828997/1000000000000000000),(175338961017292427/1000000000000000000),(15441190913345225551/1000000000000000000),(4024676736448661465887/1000000000000000000),(1503063992954093109/1000000000000000000)⟩,(999578396734357809/1000000000000000000),(323591418634784029/1000000000000000000),(31129678265884493/100000000000000000),(450766517301869239/1000000000000000000)⟩
theorem valid4165 : certificate4165.Valid := by decide +kernel
theorem sound4165 : certificate4165.Sound := rat_cut_bin_certificate_sound certificate4165 profilesValid4165 numericValid4165 valid4165

def retention4166 : RatCutRetentionCertificate := ⟨(117/2000),(59/1000),(1/2),64,1,(63851486112046193934926044147505160399/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch520.profile20832,(fun _ => MergedCutProfiles.Batch520.profile20832)⟩
theorem profilesValid4166 : retention4166.ProfilesValid := by
  exact MergedCutProfiles.Batch520.valid20832
theorem numericValid4166 : retention4166.NumericValid := by decide +kernel
def certificate4166 : RatCutBinCertificate := ⟨⟨retention4166,(2048786597038828997/1000000000000000000),(175338961017292427/1000000000000000000),(15441190913345225551/1000000000000000000),(4024676736448661465887/1000000000000000000),(30450466266166127/31250000000000000)⟩,(999578396734357809/1000000000000000000),(494498018426110973/1000000000000000000),(157270414581815831/1000000000000000000),(9430255936570201/62500000000000000)⟩
theorem valid4166 : certificate4166.Valid := by decide +kernel
theorem sound4166 : certificate4166.Sound := rat_cut_bin_certificate_sound certificate4166 profilesValid4166 numericValid4166 valid4166

def retention4167 : RatCutRetentionCertificate := ⟨(117/2000),(59/1000),(16000000000000000000/64964036552798129819),(773103615574589829/31250000000000000),1,(150134564810195988809081067839118123911/98957262793547498112000000000000000000),false,MergedCutProfiles.Batch625.profile25000,(fun _ => MergedCutProfiles.Batch625.profile25000)⟩
theorem profilesValid4167 : retention4167.ProfilesValid := by
  exact MergedCutProfiles.Batch625.valid25000
theorem numericValid4167 : retention4167.NumericValid := by decide +kernel
def certificate4167 : RatCutBinCertificate := ⟨⟨retention4167,(1907610327038828997/1000000000000000000),(175338961017292427/1000000000000000000),(15441190913345225551/1000000000000000000),(4024676736448661465887/1000000000000000000),(1495504222334777659/1000000000000000000)⟩,(15618866416043961/15625000000000000),(34883935989184253/1000000000000000000),(830183702041191951/1000000000000000000),(1170296996480453041/1000000000000000000)⟩
theorem valid4167 : certificate4167.Valid := by decide +kernel
theorem sound4167 : certificate4167.Sound := rat_cut_bin_certificate_sound certificate4167 profilesValid4167 numericValid4167 valid4167

def retention4168 : RatCutRetentionCertificate := ⟨(117/2000),(59/1000),(1/2),64,1,(63851486112046193934926044147505160399/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch520.profile20832,(fun _ => MergedCutProfiles.Batch520.profile20832)⟩
theorem profilesValid4168 : retention4168.ProfilesValid := by
  exact MergedCutProfiles.Batch520.valid20832
theorem numericValid4168 : retention4168.NumericValid := by decide +kernel
def certificate4168 : RatCutBinCertificate := ⟨⟨retention4168,(1907610327038828997/1000000000000000000),(175338961017292427/1000000000000000000),(15441190913345225551/1000000000000000000),(4024676736448661465887/1000000000000000000),(122002252112944257/125000000000000000)⟩,(15618866416043961/15625000000000000),(53450932933583627/1000000000000000000),(389587287939529939/500000000000000000),(74876756123810891/100000000000000000)⟩
theorem valid4168 : certificate4168.Valid := by decide +kernel
theorem sound4168 : certificate4168.Sound := rat_cut_bin_certificate_sound certificate4168 profilesValid4168 numericValid4168 valid4168

def retention4169 : RatCutRetentionCertificate := ⟨(59/1000),(119/2000),(82970855439465827/28303420528530076023),(369672128195639823/500000000000000000),(19/5),(1523807789808522808931/640000000000000000000),true,MergedCutProfiles.Batch625.profile25001,![MergedCutProfiles.Batch625.profile25001,MergedCutProfiles.Batch625.profile25002,MergedCutProfiles.Batch625.profile25003,MergedCutProfiles.Batch625.profile25004,MergedCutProfiles.Batch625.profile25005,MergedCutProfiles.Batch521.profile20876,MergedCutProfiles.Batch625.profile25006,MergedCutProfiles.Batch625.profile25007,MergedCutProfiles.Batch625.profile25008,MergedCutProfiles.Batch625.profile25009,MergedCutProfiles.Batch625.profile25010,MergedCutProfiles.Batch625.profile25011,MergedCutProfiles.Batch625.profile25012,MergedCutProfiles.Batch625.profile25013,MergedCutProfiles.Batch625.profile25014,MergedCutProfiles.Batch625.profile25015]⟩
theorem profilesValid4169 : retention4169.ProfilesValid := by
  change ∀ j : Fin 16, (retention4169.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch625.valid25001
  · exact MergedCutProfiles.Batch625.valid25002
  · exact MergedCutProfiles.Batch625.valid25003
  · exact MergedCutProfiles.Batch625.valid25004
  · exact MergedCutProfiles.Batch625.valid25005
  · exact MergedCutProfiles.Batch521.valid20876
  · exact MergedCutProfiles.Batch625.valid25006
  · exact MergedCutProfiles.Batch625.valid25007
  · exact MergedCutProfiles.Batch625.valid25008
  · exact MergedCutProfiles.Batch625.valid25009
  · exact MergedCutProfiles.Batch625.valid25010
  · exact MergedCutProfiles.Batch625.valid25011
  · exact MergedCutProfiles.Batch625.valid25012
  · exact MergedCutProfiles.Batch625.valid25013
  · exact MergedCutProfiles.Batch625.valid25014
  · exact MergedCutProfiles.Batch625.valid25015
theorem numericValid4169 : retention4169.NumericValid := by decide +kernel
def certificate4169 : RatCutBinCertificate := ⟨⟨retention4169,(2056230266183645427/1000000000000000000),(178859476136284067/1000000000000000000),(15581497503419628473/1000000000000000000),(995296067866497899553/250000000000000000),(2291255329498196951/1000000000000000000)⟩,(49978701727893423/50000000000000000),(487262438856760073/1000000000000000000),(162418975953306867/1000000000000000000),(16117414291905241/200000000000000000)⟩
theorem valid4169 : certificate4169.Valid := by decide +kernel
theorem sound4169 : certificate4169.Sound := rat_cut_bin_certificate_sound certificate4169 profilesValid4169 numericValid4169 valid4169

def retention4170 : RatCutRetentionCertificate := ⟨(59/1000),(119/2000),(1096737475000000000/254730784756770684207),(746737698955192443/1000000000000000000),(15/4),(604953860492853747567/256000000000000000000),true,MergedCutProfiles.Batch625.profile25016,![MergedCutProfiles.Batch625.profile25016,MergedCutProfiles.Batch625.profile25017,MergedCutProfiles.Batch625.profile25018,MergedCutProfiles.Batch521.profile20876,MergedCutProfiles.Batch625.profile25019,MergedCutProfiles.Batch625.profile25020,MergedCutProfiles.Batch625.profile25021,MergedCutProfiles.Batch625.profile25022,MergedCutProfiles.Batch397.profile15911,MergedCutProfiles.Batch625.profile25023,MergedCutProfiles.Batch625.profile25024,MergedCutProfiles.Batch521.profile20877,MergedCutProfiles.Batch625.profile25025,MergedCutProfiles.Batch625.profile25026,MergedCutProfiles.Batch625.profile25027,MergedCutProfiles.Batch520.profile20839]⟩
theorem profilesValid4170 : retention4170.ProfilesValid := by
  change ∀ j : Fin 16, (retention4170.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch625.valid25016
  · exact MergedCutProfiles.Batch625.valid25017
  · exact MergedCutProfiles.Batch625.valid25018
  · exact MergedCutProfiles.Batch521.valid20876
  · exact MergedCutProfiles.Batch625.valid25019
  · exact MergedCutProfiles.Batch625.valid25020
  · exact MergedCutProfiles.Batch625.valid25021
  · exact MergedCutProfiles.Batch625.valid25022
  · exact MergedCutProfiles.Batch397.valid15911
  · exact MergedCutProfiles.Batch625.valid25023
  · exact MergedCutProfiles.Batch625.valid25024
  · exact MergedCutProfiles.Batch521.valid20877
  · exact MergedCutProfiles.Batch625.valid25025
  · exact MergedCutProfiles.Batch625.valid25026
  · exact MergedCutProfiles.Batch625.valid25027
  · exact MergedCutProfiles.Batch520.valid20839
theorem numericValid4170 : retention4170.NumericValid := by decide +kernel
def certificate4170 : RatCutBinCertificate := ⟨⟨retention4170,(2056230266183645427/1000000000000000000),(178859476136284067/1000000000000000000),(15581497503419628473/1000000000000000000),(995296067866497899553/250000000000000000),(454917371902578797/200000000000000000)⟩,(49978701727893423/50000000000000000),(488020706788965489/1000000000000000000),(6474976366362377/40000000000000000),(10082923348684933/125000000000000000)⟩
theorem valid4170 : certificate4170.Valid := by decide +kernel
theorem sound4170 : certificate4170.Sound := rat_cut_bin_certificate_sound certificate4170 profilesValid4170 numericValid4170 valid4170

def retention4171 : RatCutRetentionCertificate := ⟨(59/1000),(119/2000),(401303330481386270/84910261585590228069),(43869499/40000000),(11/4),(3753813861603031927/1600000000000000000),true,MergedCutProfiles.Batch625.profile25028,![MergedCutProfiles.Batch625.profile25028,MergedCutProfiles.Batch625.profile25029,MergedCutProfiles.Batch520.profile20835,MergedCutProfiles.Batch625.profile25030,MergedCutProfiles.Batch625.profile25007,MergedCutProfiles.Batch625.profile25031,MergedCutProfiles.Batch625.profile25032,MergedCutProfiles.Batch625.profile25012,MergedCutProfiles.Batch625.profile25033,MergedCutProfiles.Batch625.profile25024,MergedCutProfiles.Batch521.profile20877,MergedCutProfiles.Batch625.profile25025,MergedCutProfiles.Batch625.profile25034,MergedCutProfiles.Batch521.profile20853,MergedCutProfiles.Batch625.profile25035,MergedCutProfiles.Batch625.profile25036]⟩
theorem profilesValid4171 : retention4171.ProfilesValid := by
  change ∀ j : Fin 16, (retention4171.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch625.valid25028
  · exact MergedCutProfiles.Batch625.valid25029
  · exact MergedCutProfiles.Batch520.valid20835
  · exact MergedCutProfiles.Batch625.valid25030
  · exact MergedCutProfiles.Batch625.valid25007
  · exact MergedCutProfiles.Batch625.valid25031
  · exact MergedCutProfiles.Batch625.valid25032
  · exact MergedCutProfiles.Batch625.valid25012
  · exact MergedCutProfiles.Batch625.valid25033
  · exact MergedCutProfiles.Batch625.valid25024
  · exact MergedCutProfiles.Batch521.valid20877
  · exact MergedCutProfiles.Batch625.valid25025
  · exact MergedCutProfiles.Batch625.valid25034
  · exact MergedCutProfiles.Batch521.valid20853
  · exact MergedCutProfiles.Batch625.valid25035
  · exact MergedCutProfiles.Batch625.valid25036
theorem numericValid4171 : retention4171.NumericValid := by decide +kernel
def certificate4171 : RatCutBinCertificate := ⟨⟨retention4171,(2056230266183645427/1000000000000000000),(178859476136284067/1000000000000000000),(15581497503419628473/1000000000000000000),(995296067866497899553/250000000000000000),(2281223355439516601/1000000000000000000)⟩,(49978701727893423/50000000000000000),(79421745267971203/200000000000000000),(7379436317505751/31250000000000000),(38388855120565921/250000000000000000)⟩
theorem valid4171 : certificate4171.Valid := by decide +kernel
theorem sound4171 : certificate4171.Sound := rat_cut_bin_certificate_sound certificate4171 profilesValid4171 numericValid4171 valid4171

def retention4172 : RatCutRetentionCertificate := ⟨(59/1000),(119/2000),(6095059440488448443/254730784756770684207),(120390999144415881/100000000000000000),(51/20),(70964176966524389107/32000000000000000000),true,MergedCutProfiles.Batch625.profile25037,![MergedCutProfiles.Batch625.profile25037,MergedCutProfiles.Batch625.profile25038,MergedCutProfiles.Batch397.profile15896,MergedCutProfiles.Batch625.profile25039,MergedCutProfiles.Batch398.profile15928,MergedCutProfiles.Batch626.profile25040,MergedCutProfiles.Batch626.profile25041,MergedCutProfiles.Batch397.profile15915,MergedCutProfiles.Batch397.profile15900,MergedCutProfiles.Batch521.profile20873,MergedCutProfiles.Batch626.profile25042,MergedCutProfiles.Batch397.profile15902,MergedCutProfiles.Batch626.profile25043,MergedCutProfiles.Batch626.profile25044,MergedCutProfiles.Batch626.profile25045,MergedCutProfiles.Batch626.profile25046]⟩
theorem profilesValid4172 : retention4172.ProfilesValid := by
  change ∀ j : Fin 16, (retention4172.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch625.valid25037
  · exact MergedCutProfiles.Batch625.valid25038
  · exact MergedCutProfiles.Batch397.valid15896
  · exact MergedCutProfiles.Batch625.valid25039
  · exact MergedCutProfiles.Batch398.valid15928
  · exact MergedCutProfiles.Batch626.valid25040
  · exact MergedCutProfiles.Batch626.valid25041
  · exact MergedCutProfiles.Batch397.valid15915
  · exact MergedCutProfiles.Batch397.valid15900
  · exact MergedCutProfiles.Batch521.valid20873
  · exact MergedCutProfiles.Batch626.valid25042
  · exact MergedCutProfiles.Batch397.valid15902
  · exact MergedCutProfiles.Batch626.valid25043
  · exact MergedCutProfiles.Batch626.valid25044
  · exact MergedCutProfiles.Batch626.valid25045
  · exact MergedCutProfiles.Batch626.valid25046
theorem numericValid4172 : retention4172.NumericValid := by decide +kernel
def certificate4172 : RatCutBinCertificate := ⟨⟨retention4172,(2056230266183645427/1000000000000000000),(178859476136284067/1000000000000000000),(15581497503419628473/1000000000000000000),(995296067866497899553/250000000000000000),(2157440987572206327/1000000000000000000)⟩,(49978701727893423/50000000000000000),(401920377465956881/1000000000000000000),(46345483505475639/200000000000000000),(76809855114431739/500000000000000000)⟩
theorem valid4172 : certificate4172.Valid := by decide +kernel
theorem sound4172 : certificate4172.Sound := rat_cut_bin_certificate_sound certificate4172 profilesValid4172 numericValid4172 valid4172

def retention4173 : RatCutRetentionCertificate := ⟨(59/1000),(119/2000),(64000000000000000000/254730784756770684207),(6095059440488448443/1000000000000000000),(23/20),(14767241425360990567438377675283763704359/9752095104781517508800000000000000000000),false,MergedCutProfiles.Batch626.profile25047,(fun _ => MergedCutProfiles.Batch626.profile25047)⟩
theorem profilesValid4173 : retention4173.ProfilesValid := by
  exact MergedCutProfiles.Batch626.valid25047
theorem numericValid4173 : retention4173.NumericValid := by decide +kernel
def certificate4173 : RatCutBinCertificate := ⟨⟨retention4173,(2056230266183645427/1000000000000000000),(178859476136284067/1000000000000000000),(15581497503419628473/1000000000000000000),(995296067866497899553/250000000000000000),(297423879012562587/200000000000000000)⟩,(49978701727893423/50000000000000000),(1844852890548491/5000000000000000),(16446764016438757/62500000000000000),(287155150737587467/1000000000000000000)⟩
theorem valid4173 : certificate4173.Valid := by decide +kernel
theorem sound4173 : certificate4173.Sound := rat_cut_bin_certificate_sound certificate4173 profilesValid4173 numericValid4173 valid4173

def retention4174 : RatCutRetentionCertificate := ⟨(59/1000),(119/2000),(1/2),64,1,(102162675905069115123294709018435311/102400000000000000000000000000000000),false,MergedCutProfiles.Batch399.profile15991,(fun _ => MergedCutProfiles.Batch399.profile15991)⟩
theorem profilesValid4174 : retention4174.ProfilesValid := by
  exact MergedCutProfiles.Batch399.valid15991
theorem numericValid4174 : retention4174.NumericValid := by decide +kernel
def certificate4174 : RatCutBinCertificate := ⟨⟨retention4174,(2056230266183645427/1000000000000000000),(178859476136284067/1000000000000000000),(15581497503419628473/1000000000000000000),(995296067866497899553/250000000000000000),(487039484261027669/500000000000000000)⟩,(49978701727893423/50000000000000000),(490506698746227159/1000000000000000000),(32019458491001007/200000000000000000),(153543339486633371/1000000000000000000)⟩
theorem valid4174 : certificate4174.Valid := by decide +kernel
theorem sound4174 : certificate4174.Sound := rat_cut_bin_certificate_sound certificate4174 profilesValid4174 numericValid4174 valid4174

def retention4175 : RatCutRetentionCertificate := ⟨(59/1000),(119/2000),(64000000000000000000/254730784756770684207),(4929728520984475523/200000000000000000),1,(1187921007771175356865699099718288607/788756563357516083680000000000000000),false,MergedCutProfiles.Batch626.profile25047,(fun _ => MergedCutProfiles.Batch626.profile25047)⟩
theorem profilesValid4175 : retention4175.ProfilesValid := by
  exact MergedCutProfiles.Batch626.valid25047
theorem numericValid4175 : retention4175.NumericValid := by decide +kernel
def certificate4175 : RatCutBinCertificate := ⟨⟨retention4175,(1910495617183645427/1000000000000000000),(178859476136284067/1000000000000000000),(15581497503419628473/1000000000000000000),(995296067866497899553/250000000000000000),(742068715473887087/500000000000000000)⟩,(999604227260020369/1000000000000000000),(17507069311340421/500000000000000000),(829812348017557807/1000000000000000000),(290284987645622159/250000000000000000)⟩
theorem valid4175 : certificate4175.Valid := by decide +kernel
theorem sound4175 : certificate4175.Sound := rat_cut_bin_certificate_sound certificate4175 profilesValid4175 numericValid4175 valid4175

def certificates : List RatCutBinCertificate := [certificate4164,certificate4165,certificate4166,certificate4167,certificate4168,certificate4169,certificate4170,certificate4171,certificate4172,certificate4173,certificate4174,certificate4175]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4164,List.forall_mem_cons.mpr ⟨sound4165,List.forall_mem_cons.mpr ⟨sound4166,List.forall_mem_cons.mpr ⟨sound4167,List.forall_mem_cons.mpr ⟨sound4168,List.forall_mem_cons.mpr ⟨sound4169,List.forall_mem_cons.mpr ⟨sound4170,List.forall_mem_cons.mpr ⟨sound4171,List.forall_mem_cons.mpr ⟨sound4172,List.forall_mem_cons.mpr ⟨sound4173,List.forall_mem_cons.mpr ⟨sound4174,List.forall_mem_cons.mpr ⟨sound4175,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch347
