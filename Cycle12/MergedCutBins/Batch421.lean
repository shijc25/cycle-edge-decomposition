import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch390
import Cycle12.MergedCutProfiles.Batch391
import Cycle12.MergedCutProfiles.Batch392
import Cycle12.MergedCutProfiles.Batch619
import Cycle12.MergedCutProfiles.Batch620
import Cycle12.MergedCutProfiles.Batch703
import Cycle12.MergedCutProfiles.Batch704

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch421

def retention5052 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(8309542237151316358/367120525546659461781),(747833032207518783/250000000000000000),(17/10),(668988450430286440446975987710269330391/299133212883007513200000000000000000000),false,MergedCutProfiles.Batch703.profile28154,(fun _ => MergedCutProfiles.Batch703.profile28154)⟩
theorem profilesValid5052 : retention5052.ProfilesValid := by
  exact MergedCutProfiles.Batch703.valid28154
theorem numericValid5052 : retention5052.NumericValid := by decide +kernel
def certificate5052 : RatCutBinCertificate := ⟨⟨retention5052,(194291503027270571/100000000000000000),(155212952940275013/1000000000000000000),(2902141146764401583/200000000000000000),(10717789802044865406831/500000000000000000),(550273311913615469/250000000000000000)⟩,(199984570572496951/200000000000000000),(143571218771379771/200000000000000000),(44184548736254817/1000000000000000000),(569933171652697/12500000000000000)⟩
theorem valid5052 : certificate5052.Valid := by decide +kernel
theorem sound5052 : certificate5052.Sound := rat_cut_bin_certificate_sound certificate5052 profilesValid5052 numericValid5052 valid5052

def retention5053 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(1/40),(4154771118575658179/125000000000000000),(21/20),(461596952586784294939003650356594943491/207738555928782908950000000000000000000),false,MergedCutProfiles.Batch703.profile28155,(fun _ => MergedCutProfiles.Batch703.profile28155)⟩
theorem profilesValid5053 : retention5053.ProfilesValid := by
  exact MergedCutProfiles.Batch703.valid28155
theorem numericValid5053 : retention5053.NumericValid := by decide +kernel
def certificate5053 : RatCutBinCertificate := ⟨⟨retention5053,(194291503027270571/100000000000000000),(155212952940275013/1000000000000000000),(2902141146764401583/200000000000000000),(10717789802044865406831/500000000000000000),(1100093827743889381/500000000000000000)⟩,(199984570572496951/200000000000000000),(84445687094185867/125000000000000000),(5947422550599991/100000000000000000),(117555414739417721/1000000000000000000)⟩
theorem valid5053 : certificate5053.Valid := by decide +kernel
theorem sound5053 : certificate5053.Sound := rat_cut_bin_certificate_sound certificate5053 profilesValid5053 numericValid5053 valid5053

def retention5054 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(644010091828889553/1408963791382908709094),(61275350484765983/100000000000000000),4,(923501076285767181/400000000000000000),true,MergedCutProfiles.Batch703.profile28156,![MergedCutProfiles.Batch703.profile28156,MergedCutProfiles.Batch703.profile28157,MergedCutProfiles.Batch703.profile28158,MergedCutProfiles.Batch703.profile28159,MergedCutProfiles.Batch704.profile28160,MergedCutProfiles.Batch704.profile28161,MergedCutProfiles.Batch704.profile28162,MergedCutProfiles.Batch704.profile28163,MergedCutProfiles.Batch704.profile28164,MergedCutProfiles.Batch704.profile28165,MergedCutProfiles.Batch619.profile24776,MergedCutProfiles.Batch704.profile28166,MergedCutProfiles.Batch704.profile28167,MergedCutProfiles.Batch704.profile28168,MergedCutProfiles.Batch704.profile28169,MergedCutProfiles.Batch704.profile28170]⟩
theorem profilesValid5054 : retention5054.ProfilesValid := by
  change ∀ j : Fin 16, (retention5054.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch703.valid28156
  · exact MergedCutProfiles.Batch703.valid28157
  · exact MergedCutProfiles.Batch703.valid28158
  · exact MergedCutProfiles.Batch703.valid28159
  · exact MergedCutProfiles.Batch704.valid28160
  · exact MergedCutProfiles.Batch704.valid28161
  · exact MergedCutProfiles.Batch704.valid28162
  · exact MergedCutProfiles.Batch704.valid28163
  · exact MergedCutProfiles.Batch704.valid28164
  · exact MergedCutProfiles.Batch704.valid28165
  · exact MergedCutProfiles.Batch619.valid24776
  · exact MergedCutProfiles.Batch704.valid28166
  · exact MergedCutProfiles.Batch704.valid28167
  · exact MergedCutProfiles.Batch704.valid28168
  · exact MergedCutProfiles.Batch704.valid28169
  · exact MergedCutProfiles.Batch704.valid28170
theorem numericValid5054 : retention5054.NumericValid := by decide +kernel
def certificate5054 : RatCutBinCertificate := ⟨⟨retention5054,(486197701111738163/250000000000000000),(161735409484216873/1000000000000000000),(3691915359570146133/250000000000000000),(10465903641982879244853/500000000000000000),(2223555036361511957/1000000000000000000)⟩,(249980377258378263/250000000000000000),(86957300568009771/125000000000000000),(51889569366315191/1000000000000000000),(23509980090875743/1000000000000000000)⟩
theorem valid5054 : certificate5054.Valid := by decide +kernel
theorem sound5054 : certificate5054.Sound := rat_cut_bin_certificate_sound certificate5054 profilesValid5054 numericValid5054 valid5054

def retention5055 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(539437758500000000/704481895691454354547),(644010091828889553/1000000000000000000),4,(150619968909210980113/64000000000000000000),true,MergedCutProfiles.Batch704.profile28171,![MergedCutProfiles.Batch704.profile28171,MergedCutProfiles.Batch704.profile28172,MergedCutProfiles.Batch704.profile28160,MergedCutProfiles.Batch704.profile28162,MergedCutProfiles.Batch619.profile24791,MergedCutProfiles.Batch704.profile28165,MergedCutProfiles.Batch704.profile28166,MergedCutProfiles.Batch704.profile28168,MergedCutProfiles.Batch704.profile28169,MergedCutProfiles.Batch619.profile24777,MergedCutProfiles.Batch704.profile28173,MergedCutProfiles.Batch704.profile28174,MergedCutProfiles.Batch619.profile24778,MergedCutProfiles.Batch704.profile28175,MergedCutProfiles.Batch619.profile24792,MergedCutProfiles.Batch704.profile28176]⟩
theorem profilesValid5055 : retention5055.ProfilesValid := by
  change ∀ j : Fin 16, (retention5055.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch704.valid28171
  · exact MergedCutProfiles.Batch704.valid28172
  · exact MergedCutProfiles.Batch704.valid28160
  · exact MergedCutProfiles.Batch704.valid28162
  · exact MergedCutProfiles.Batch619.valid24791
  · exact MergedCutProfiles.Batch704.valid28165
  · exact MergedCutProfiles.Batch704.valid28166
  · exact MergedCutProfiles.Batch704.valid28168
  · exact MergedCutProfiles.Batch704.valid28169
  · exact MergedCutProfiles.Batch619.valid24777
  · exact MergedCutProfiles.Batch704.valid28173
  · exact MergedCutProfiles.Batch704.valid28174
  · exact MergedCutProfiles.Batch619.valid24778
  · exact MergedCutProfiles.Batch704.valid28175
  · exact MergedCutProfiles.Batch619.valid24792
  · exact MergedCutProfiles.Batch704.valid28176
theorem numericValid5055 : retention5055.NumericValid := by decide +kernel
def certificate5055 : RatCutBinCertificate := ⟨⟨retention5055,(486197701111738163/250000000000000000),(161735409484216873/1000000000000000000),(3691915359570146133/250000000000000000),(10465903641982879244853/500000000000000000),(283529921611127117/125000000000000000)⟩,(249980377258378263/250000000000000000),(330191158185434271/500000000000000000),(16400264820734197/250000000000000000),(30485436894661731/1000000000000000000)⟩
theorem valid5055 : certificate5055.Valid := by decide +kernel
theorem sound5055 : certificate5055.Sound := rat_cut_bin_certificate_sound certificate5055 profilesValid5055 numericValid5055 valid5055

def retention5056 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(1128121234258829283/704481895691454354547),(1078875517/1000000000),(29/10),(647857894988501818402971310859817431/269718879250000000000000000000000000),true,MergedCutProfiles.Batch704.profile28172,![MergedCutProfiles.Batch704.profile28172,MergedCutProfiles.Batch704.profile28162,MergedCutProfiles.Batch620.profile24813,MergedCutProfiles.Batch704.profile28168,MergedCutProfiles.Batch620.profile24802,MergedCutProfiles.Batch620.profile24814,MergedCutProfiles.Batch619.profile24792,MergedCutProfiles.Batch619.profile24779,MergedCutProfiles.Batch620.profile24815,MergedCutProfiles.Batch704.profile28177,MergedCutProfiles.Batch704.profile28178,MergedCutProfiles.Batch619.profile24793,MergedCutProfiles.Batch704.profile28179,MergedCutProfiles.Batch704.profile28180,MergedCutProfiles.Batch620.profile24816,MergedCutProfiles.Batch619.profile24784]⟩
theorem profilesValid5056 : retention5056.ProfilesValid := by
  change ∀ j : Fin 16, (retention5056.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch704.valid28172
  · exact MergedCutProfiles.Batch704.valid28162
  · exact MergedCutProfiles.Batch620.valid24813
  · exact MergedCutProfiles.Batch704.valid28168
  · exact MergedCutProfiles.Batch620.valid24802
  · exact MergedCutProfiles.Batch620.valid24814
  · exact MergedCutProfiles.Batch619.valid24792
  · exact MergedCutProfiles.Batch619.valid24779
  · exact MergedCutProfiles.Batch620.valid24815
  · exact MergedCutProfiles.Batch704.valid28177
  · exact MergedCutProfiles.Batch704.valid28178
  · exact MergedCutProfiles.Batch619.valid24793
  · exact MergedCutProfiles.Batch704.valid28179
  · exact MergedCutProfiles.Batch704.valid28180
  · exact MergedCutProfiles.Batch620.valid24816
  · exact MergedCutProfiles.Batch619.valid24784
theorem numericValid5056 : retention5056.NumericValid := by decide +kernel
def certificate5056 : RatCutBinCertificate := ⟨⟨retention5056,(486197701111738163/250000000000000000),(161735409484216873/1000000000000000000),(3691915359570146133/250000000000000000),(10465903641982879244853/500000000000000000),(2340206334948918997/1000000000000000000)⟩,(249980377258378263/250000000000000000),(474860635418202423/1000000000000000000),(42873605447754351/250000000000000000),(13750628824677253/125000000000000000)⟩
theorem valid5056 : certificate5056.Valid := by decide +kernel
theorem sound5056 : certificate5056.Sound := rat_cut_bin_certificate_sound certificate5056 profilesValid5056 numericValid5056 valid5056

def retention5057 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(32000000000000000000/704481895691454354547),(1128121234258829283/500000000000000000),(7/4),(269635633312669554639/128000000000000000000),true,MergedCutProfiles.Batch619.profile24797,![MergedCutProfiles.Batch619.profile24797,MergedCutProfiles.Batch704.profile28181,MergedCutProfiles.Batch704.profile28182,MergedCutProfiles.Batch704.profile28183,MergedCutProfiles.Batch704.profile28184,MergedCutProfiles.Batch704.profile28185,MergedCutProfiles.Batch390.profile15626,MergedCutProfiles.Batch704.profile28186,MergedCutProfiles.Batch704.profile28187,MergedCutProfiles.Batch391.profile15670,MergedCutProfiles.Batch704.profile28188,MergedCutProfiles.Batch704.profile28189,MergedCutProfiles.Batch704.profile28190,MergedCutProfiles.Batch704.profile28191,MergedCutProfiles.Batch704.profile28192,MergedCutProfiles.Batch704.profile28193]⟩
theorem profilesValid5057 : retention5057.ProfilesValid := by
  change ∀ j : Fin 16, (retention5057.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch619.valid24797
  · exact MergedCutProfiles.Batch704.valid28181
  · exact MergedCutProfiles.Batch704.valid28182
  · exact MergedCutProfiles.Batch704.valid28183
  · exact MergedCutProfiles.Batch704.valid28184
  · exact MergedCutProfiles.Batch704.valid28185
  · exact MergedCutProfiles.Batch390.valid15626
  · exact MergedCutProfiles.Batch704.valid28186
  · exact MergedCutProfiles.Batch704.valid28187
  · exact MergedCutProfiles.Batch391.valid15670
  · exact MergedCutProfiles.Batch704.valid28188
  · exact MergedCutProfiles.Batch704.valid28189
  · exact MergedCutProfiles.Batch704.valid28190
  · exact MergedCutProfiles.Batch704.valid28191
  · exact MergedCutProfiles.Batch704.valid28192
  · exact MergedCutProfiles.Batch704.valid28193
theorem numericValid5057 : retention5057.NumericValid := by decide +kernel
def certificate5057 : RatCutBinCertificate := ⟨⟨retention5057,(486197701111738163/250000000000000000),(161735409484216873/1000000000000000000),(3691915359570146133/250000000000000000),(10465903641982879244853/500000000000000000),(1034627228019391287/500000000000000000)⟩,(249980377258378263/250000000000000000),(196322854962245801/500000000000000000),(120144361290560391/500000000000000000),(218627350214577411/1000000000000000000)⟩
theorem valid5057 : certificate5057.Valid := by decide +kernel
theorem sound5057 : certificate5057.Sound := rat_cut_bin_certificate_sound certificate5057 profilesValid5057 numericValid5057 valid5057

def retention5058 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(1/2),64,1,(255402311029323201614710967138024893231/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch392.profile15710,(fun _ => MergedCutProfiles.Batch392.profile15710)⟩
theorem profilesValid5058 : retention5058.ProfilesValid := by
  exact MergedCutProfiles.Batch392.valid15710
theorem numericValid5058 : retention5058.NumericValid := by decide +kernel
def certificate5058 : RatCutBinCertificate := ⟨⟨retention5058,(486197701111738163/250000000000000000),(161735409484216873/1000000000000000000),(3691915359570146133/250000000000000000),(10465903641982879244853/500000000000000000),(976365928444380397/1000000000000000000)⟩,(249980377258378263/250000000000000000),(35101014518095103/62500000000000000),(57183423222539937/500000000000000000),(21995450069904683/200000000000000000)⟩
theorem valid5058 : certificate5058.Valid := by decide +kernel
theorem sound5058 : certificate5058.Sound := rat_cut_bin_certificate_sound certificate5058 profilesValid5058 numericValid5058 valid5058

def retention5059 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(32000000000000000000/704481895691454354547),(8490301818705650677/200000000000000000),1,(356358424603073949740554223975000096859/169806036374113013540000000000000000000),false,MergedCutProfiles.Batch704.profile28194,(fun _ => MergedCutProfiles.Batch704.profile28194)⟩
theorem profilesValid5059 : retention5059.ProfilesValid := by
  exact MergedCutProfiles.Batch704.valid28194
theorem numericValid5059 : retention5059.NumericValid := by decide +kernel
def certificate5059 : RatCutBinCertificate := ⟨⟨retention5059,(432807588861738163/250000000000000000),(161735409484216873/1000000000000000000),(3691915359570146133/250000000000000000),(10465903641982879244853/500000000000000000),(207966003822597239/100000000000000000)⟩,(999930128357091249/1000000000000000000),(16658376833629589/1000000000000000000),(221056722278344797/250000000000000000),(219111022789211157/125000000000000000)⟩
theorem valid5059 : certificate5059.Valid := by decide +kernel
theorem sound5059 : certificate5059.Sound := rat_cut_bin_certificate_sound certificate5059 profilesValid5059 numericValid5059 valid5059

def retention5060 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(1/2),64,1,(255402311029323201614710967138024893231/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch392.profile15710,(fun _ => MergedCutProfiles.Batch392.profile15710)⟩
theorem profilesValid5060 : retention5060.ProfilesValid := by
  exact MergedCutProfiles.Batch392.valid15710
theorem numericValid5060 : retention5060.NumericValid := by decide +kernel
def certificate5060 : RatCutBinCertificate := ⟨⟨retention5060,(432807588861738163/250000000000000000),(161735409484216873/1000000000000000000),(3691915359570146133/250000000000000000),(10465903641982879244853/500000000000000000),(244676210623850559/250000000000000000)⟩,(999930128357091249/1000000000000000000),(1769877857877847/50000000000000000),(414359977409743107/500000000000000000),(399399709111865041/500000000000000000)⟩
theorem valid5060 : certificate5060.Valid := by decide +kernel
theorem sound5060 : certificate5060.Sound := rat_cut_bin_certificate_sound certificate5060 profilesValid5060 numericValid5060 valid5060

def retention5061 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(746882705227720139/1408963791382908709094),(739487826958138751/1000000000000000000),4,(1444264107880100525242946835158306331/591590261566511000800000000000000000),false,MergedCutProfiles.Batch704.profile28195,(fun _ => MergedCutProfiles.Batch704.profile28195)⟩
theorem profilesValid5061 : retention5061.ProfilesValid := by
  exact MergedCutProfiles.Batch704.valid28195
theorem numericValid5061 : retention5061.NumericValid := by decide +kernel
def certificate5061 : RatCutBinCertificate := ⟨⟨retention5061,(488053306861738163/250000000000000000),(161735409484216873/1000000000000000000),(3691915359570146133/250000000000000000),(10465903641982879244853/500000000000000000),(1177901125295705703/500000000000000000)⟩,(999921209463200733/1000000000000000000),(79955392409713183/100000000000000000),(10792411148844379/500000000000000000),(2120108785706547/200000000000000000)⟩
theorem valid5061 : certificate5061.Valid := by decide +kernel
theorem sound5061 : certificate5061.Sound := rat_cut_bin_certificate_sound certificate5061 profilesValid5061 numericValid5061 valid5061

def retention5062 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(437889355206433125/704481895691454354547),(746882705227720139/1000000000000000000),4,(1824053182614729199413115984749643059/746882705227720139000000000000000000),false,MergedCutProfiles.Batch704.profile28196,(fun _ => MergedCutProfiles.Batch704.profile28196)⟩
theorem profilesValid5062 : retention5062.ProfilesValid := by
  exact MergedCutProfiles.Batch704.valid28196
theorem numericValid5062 : retention5062.NumericValid := by decide +kernel
def certificate5062 : RatCutBinCertificate := ⟨⟨retention5062,(488053306861738163/250000000000000000),(161735409484216873/1000000000000000000),(3691915359570146133/250000000000000000),(10465903641982879244853/500000000000000000),(920585537170047/390625000000000)⟩,(999921209463200733/1000000000000000000),(15950490331526227/20000000000000000),(881655243158541/40000000000000000),(2169207839968091/200000000000000000)⟩
theorem valid5062 : certificate5062.Valid := by decide +kernel
theorem sound5062 : certificate5062.Sound := rat_cut_bin_certificate_sound certificate5062 profilesValid5062 numericValid5062 valid5062

def retention5063 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(1474252895409476582/704481895691454354547),(700622968330293/800000000000000),(73/20),(33907854966276832206704350175682447839/14012459366605860000000000000000000000),false,MergedCutProfiles.Batch704.profile28197,(fun _ => MergedCutProfiles.Batch704.profile28197)⟩
theorem profilesValid5063 : retention5063.ProfilesValid := by
  exact MergedCutProfiles.Batch704.valid28197
theorem numericValid5063 : retention5063.NumericValid := by decide +kernel
def certificate5063 : RatCutBinCertificate := ⟨⟨retention5063,(488053306861738163/250000000000000000),(161735409484216873/1000000000000000000),(3691915359570146133/250000000000000000),(10465903641982879244853/500000000000000000),(1170898291405326291/500000000000000000)⟩,(999921209463200733/1000000000000000000),(777047172492896609/1000000000000000000),(26939399574242701/1000000000000000000),(14393472431881357/1000000000000000000)⟩
theorem valid5063 : certificate5063.Valid := by decide +kernel
theorem sound5063 : certificate5063.Sound := rat_cut_bin_certificate_sound certificate5063 profilesValid5063 numericValid5063 valid5063

def certificates : List RatCutBinCertificate := [certificate5052,certificate5053,certificate5054,certificate5055,certificate5056,certificate5057,certificate5058,certificate5059,certificate5060,certificate5061,certificate5062,certificate5063]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound5052,List.forall_mem_cons.mpr ⟨sound5053,List.forall_mem_cons.mpr ⟨sound5054,List.forall_mem_cons.mpr ⟨sound5055,List.forall_mem_cons.mpr ⟨sound5056,List.forall_mem_cons.mpr ⟨sound5057,List.forall_mem_cons.mpr ⟨sound5058,List.forall_mem_cons.mpr ⟨sound5059,List.forall_mem_cons.mpr ⟨sound5060,List.forall_mem_cons.mpr ⟨sound5061,List.forall_mem_cons.mpr ⟨sound5062,List.forall_mem_cons.mpr ⟨sound5063,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch421
