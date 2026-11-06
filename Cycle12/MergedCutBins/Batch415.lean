import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch376
import Cycle12.MergedCutProfiles.Batch378
import Cycle12.MergedCutProfiles.Batch611
import Cycle12.MergedCutProfiles.Batch612
import Cycle12.MergedCutProfiles.Batch696
import Cycle12.MergedCutProfiles.Batch697

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch415

def retention4980 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(1/40),(563549553956992949/12500000000000000),(21/20),(1107356453623259557/500000000000000000),false,MergedCutProfiles.Batch696.profile27865,(fun _ => MergedCutProfiles.Batch696.profile27865)⟩
theorem profilesValid4980 : retention4980.ProfilesValid := by
  exact MergedCutProfiles.Batch696.valid27865
theorem numericValid4980 : retention4980.NumericValid := by decide +kernel
def certificate4980 : RatCutBinCertificate := ⟨⟨retention4980,(1893292060239611651/1000000000000000000),(59865971199444307/500000000000000000),(13103032017811620311/1000000000000000000),(12570243598073477431933/500000000000000000),(1098273749088963141/500000000000000000)⟩,(499966652841521559/500000000000000000),(137917389076766857/200000000000000000),(54119453053188091/1000000000000000000),(108416439034100119/1000000000000000000)⟩
theorem valid4980 : certificate4980.Valid := by decide +kernel
theorem sound4980 : certificate4980.Sound := rat_cut_bin_certificate_sound certificate4980 profilesValid4980 numericValid4980 valid4980

def retention4981 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(646430680470346565/1823169683104305214804),(615056611883816811/1000000000000000000),4,(9233121448588273849/4000000000000000000),true,MergedCutProfiles.Batch696.profile27866,![MergedCutProfiles.Batch696.profile27866,MergedCutProfiles.Batch696.profile27867,MergedCutProfiles.Batch696.profile27868,MergedCutProfiles.Batch696.profile27869,MergedCutProfiles.Batch611.profile24454,MergedCutProfiles.Batch696.profile27870,MergedCutProfiles.Batch696.profile27871,MergedCutProfiles.Batch696.profile27872,MergedCutProfiles.Batch611.profile24470,MergedCutProfiles.Batch611.profile24455,MergedCutProfiles.Batch696.profile27873,MergedCutProfiles.Batch696.profile27874,MergedCutProfiles.Batch696.profile27875,MergedCutProfiles.Batch696.profile27876,MergedCutProfiles.Batch611.profile24456,MergedCutProfiles.Batch696.profile27877]⟩
theorem profilesValid4981 : retention4981.ProfilesValid := by
  change ∀ j : Fin 16, (retention4981.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch696.valid27866
  · exact MergedCutProfiles.Batch696.valid27867
  · exact MergedCutProfiles.Batch696.valid27868
  · exact MergedCutProfiles.Batch696.valid27869
  · exact MergedCutProfiles.Batch611.valid24454
  · exact MergedCutProfiles.Batch696.valid27870
  · exact MergedCutProfiles.Batch696.valid27871
  · exact MergedCutProfiles.Batch696.valid27872
  · exact MergedCutProfiles.Batch611.valid24470
  · exact MergedCutProfiles.Batch611.valid24455
  · exact MergedCutProfiles.Batch696.valid27873
  · exact MergedCutProfiles.Batch696.valid27874
  · exact MergedCutProfiles.Batch696.valid27875
  · exact MergedCutProfiles.Batch696.valid27876
  · exact MergedCutProfiles.Batch611.valid24456
  · exact MergedCutProfiles.Batch696.valid27877
theorem numericValid4981 : retention4981.NumericValid := by decide +kernel
def certificate4981 : RatCutBinCertificate := ⟨⟨retention4981,(1922243345298746579/1000000000000000000),(31307344283847009/250000000000000000),(3330687757480619411/250000000000000000),(48859186672234238561/2000000000000000),(1118003224395237519/500000000000000000)⟩,(999930735426530723/1000000000000000000),(5212793225393061/7812500000000000),(62792039249462209/1000000000000000000),(5719921906113931/200000000000000000)⟩
theorem valid4981 : certificate4981.Valid := by decide +kernel
theorem sound4981 : certificate4981.Sound := rat_cut_bin_certificate_sound certificate4981 profilesValid4981 numericValid4981 valid4981

def retention4982 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(277342049000000000/455792420776076303701),(129286136094069313/200000000000000000),4,(30098336628570385433/12800000000000000000),true,MergedCutProfiles.Batch696.profile27878,![MergedCutProfiles.Batch696.profile27878,MergedCutProfiles.Batch696.profile27879,MergedCutProfiles.Batch611.profile24454,MergedCutProfiles.Batch696.profile27871,MergedCutProfiles.Batch611.profile24470,MergedCutProfiles.Batch611.profile24455,MergedCutProfiles.Batch696.profile27874,MergedCutProfiles.Batch612.profile24483,MergedCutProfiles.Batch611.profile24456,MergedCutProfiles.Batch611.profile24471,MergedCutProfiles.Batch697.profile27880,MergedCutProfiles.Batch611.profile24457,MergedCutProfiles.Batch697.profile27881,MergedCutProfiles.Batch697.profile27882,MergedCutProfiles.Batch611.profile24458,MergedCutProfiles.Batch612.profile24484]⟩
theorem profilesValid4982 : retention4982.ProfilesValid := by
  change ∀ j : Fin 16, (retention4982.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch696.valid27878
  · exact MergedCutProfiles.Batch696.valid27879
  · exact MergedCutProfiles.Batch611.valid24454
  · exact MergedCutProfiles.Batch696.valid27871
  · exact MergedCutProfiles.Batch611.valid24470
  · exact MergedCutProfiles.Batch611.valid24455
  · exact MergedCutProfiles.Batch696.valid27874
  · exact MergedCutProfiles.Batch612.valid24483
  · exact MergedCutProfiles.Batch611.valid24456
  · exact MergedCutProfiles.Batch611.valid24471
  · exact MergedCutProfiles.Batch697.valid27880
  · exact MergedCutProfiles.Batch611.valid24457
  · exact MergedCutProfiles.Batch697.valid27881
  · exact MergedCutProfiles.Batch697.valid27882
  · exact MergedCutProfiles.Batch611.valid24458
  · exact MergedCutProfiles.Batch612.valid24484
theorem numericValid4982 : retention4982.NumericValid := by decide +kernel
def certificate4982 : RatCutBinCertificate := ⟨⟨retention4982,(1922243345298746579/1000000000000000000),(31307344283847009/250000000000000000),(3330687757480619411/250000000000000000),(48859186672234238561/2000000000000000),(2279158643059240491/1000000000000000000)⟩,(999930735426530723/1000000000000000000),(633877810785428159/1000000000000000000),(19284471050865137/250000000000000000),(9003221538227931/250000000000000000)⟩
theorem valid4982 : certificate4982.Valid := by decide +kernel
theorem sound4982 : certificate4982.Sound := rat_cut_bin_certificate_sound certificate4982 profilesValid4982 numericValid4982 valid4982

def retention4983 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(718899259925143985/455792420776076303701),(277342049/250000000),(57/20),(2655148686079831301597724403979241359/1109368196000000000000000000000000000),true,MergedCutProfiles.Batch697.profile27883,![MergedCutProfiles.Batch697.profile27883,MergedCutProfiles.Batch611.profile24470,MergedCutProfiles.Batch612.profile24483,MergedCutProfiles.Batch697.profile27884,MergedCutProfiles.Batch697.profile27881,MergedCutProfiles.Batch697.profile27885,MergedCutProfiles.Batch611.profile24459,MergedCutProfiles.Batch611.profile24460,MergedCutProfiles.Batch611.profile24461,MergedCutProfiles.Batch611.profile24462,MergedCutProfiles.Batch697.profile27886,MergedCutProfiles.Batch697.profile27887,MergedCutProfiles.Batch697.profile27888,MergedCutProfiles.Batch697.profile27889,MergedCutProfiles.Batch611.profile24466,MergedCutProfiles.Batch611.profile24467]⟩
theorem profilesValid4983 : retention4983.ProfilesValid := by
  change ∀ j : Fin 16, (retention4983.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch697.valid27883
  · exact MergedCutProfiles.Batch611.valid24470
  · exact MergedCutProfiles.Batch612.valid24483
  · exact MergedCutProfiles.Batch697.valid27884
  · exact MergedCutProfiles.Batch697.valid27881
  · exact MergedCutProfiles.Batch697.valid27885
  · exact MergedCutProfiles.Batch611.valid24459
  · exact MergedCutProfiles.Batch611.valid24460
  · exact MergedCutProfiles.Batch611.valid24461
  · exact MergedCutProfiles.Batch611.valid24462
  · exact MergedCutProfiles.Batch697.valid27886
  · exact MergedCutProfiles.Batch697.valid27887
  · exact MergedCutProfiles.Batch697.valid27888
  · exact MergedCutProfiles.Batch697.valid27889
  · exact MergedCutProfiles.Batch611.valid24466
  · exact MergedCutProfiles.Batch611.valid24467
theorem numericValid4983 : retention4983.NumericValid := by decide +kernel
def certificate4983 : RatCutBinCertificate := ⟨⟨retention4983,(1922243345298746579/1000000000000000000),(31307344283847009/250000000000000000),(3330687757480619411/250000000000000000),(48859186672234238561/2000000000000000),(146368312695928349/62500000000000000)⟩,(999930735426530723/1000000000000000000),(451880961532828051/1000000000000000000),(189173237813422333/1000000000000000000),(15421324669411537/125000000000000000)⟩
theorem valid4983 : certificate4983.Valid := by decide +kernel
theorem sound4983 : certificate4983.Sound := rat_cut_bin_certificate_sound certificate4983 profilesValid4983 numericValid4983 valid4983

def retention4984 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(16000000000000000000/455792420776076303701),(143779851985028797/50000000000000000),(31/20),(136851830880209894353/64000000000000000000),true,MergedCutProfiles.Batch697.profile27890,![MergedCutProfiles.Batch697.profile27890,MergedCutProfiles.Batch697.profile27891,MergedCutProfiles.Batch697.profile27892,MergedCutProfiles.Batch376.profile15069,MergedCutProfiles.Batch697.profile27893,MergedCutProfiles.Batch697.profile27894,MergedCutProfiles.Batch376.profile15058,MergedCutProfiles.Batch697.profile27895,MergedCutProfiles.Batch697.profile27896,MergedCutProfiles.Batch697.profile27897,MergedCutProfiles.Batch376.profile15049,MergedCutProfiles.Batch697.profile27898,MergedCutProfiles.Batch697.profile27899,MergedCutProfiles.Batch697.profile27900,MergedCutProfiles.Batch697.profile27901,MergedCutProfiles.Batch697.profile27902]⟩
theorem profilesValid4984 : retention4984.ProfilesValid := by
  change ∀ j : Fin 16, (retention4984.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch697.valid27890
  · exact MergedCutProfiles.Batch697.valid27891
  · exact MergedCutProfiles.Batch697.valid27892
  · exact MergedCutProfiles.Batch376.valid15069
  · exact MergedCutProfiles.Batch697.valid27893
  · exact MergedCutProfiles.Batch697.valid27894
  · exact MergedCutProfiles.Batch376.valid15058
  · exact MergedCutProfiles.Batch697.valid27895
  · exact MergedCutProfiles.Batch697.valid27896
  · exact MergedCutProfiles.Batch697.valid27897
  · exact MergedCutProfiles.Batch376.valid15049
  · exact MergedCutProfiles.Batch697.valid27898
  · exact MergedCutProfiles.Batch697.valid27899
  · exact MergedCutProfiles.Batch697.valid27900
  · exact MergedCutProfiles.Batch697.valid27901
  · exact MergedCutProfiles.Batch697.valid27902
theorem numericValid4984 : retention4984.NumericValid := by decide +kernel
def certificate4984 : RatCutBinCertificate := ⟨⟨retention4984,(1922243345298746579/1000000000000000000),(31307344283847009/250000000000000000),(3330687757480619411/250000000000000000),(48859186672234238561/2000000000000000),(422060748444349759/200000000000000000)⟩,(999930735426530723/1000000000000000000),(43051298262610341/125000000000000000),(57693684885670013/200000000000000000),(150412751496900399/500000000000000000)⟩
theorem valid4984 : certificate4984.Valid := by decide +kernel
theorem sound4984 : certificate4984.Sound := rat_cut_bin_certificate_sound certificate4984 profilesValid4984 numericValid4984 valid4984

def retention4985 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(1/2),64,1,(63848635416822846544693585750381821951/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch378.profile15126,(fun _ => MergedCutProfiles.Batch378.profile15126)⟩
theorem profilesValid4985 : retention4985.ProfilesValid := by
  exact MergedCutProfiles.Batch378.valid15126
theorem numericValid4985 : retention4985.NumericValid := by decide +kernel
def certificate4985 : RatCutBinCertificate := ⟨⟨retention4985,(1922243345298746579/1000000000000000000),(31307344283847009/250000000000000000),(3330687757480619411/250000000000000000),(48859186672234238561/2000000000000000),(61222905390559521/62500000000000000)⟩,(999930735426530723/1000000000000000000),(67374568093685091/125000000000000000),(127878720855044423/1000000000000000000),(123368696477360539/1000000000000000000)⟩
theorem valid4985 : certificate4985.Valid := by decide +kernel
theorem sound4985 : certificate4985.Sound := rat_cut_bin_certificate_sound certificate4985 profilesValid4985 numericValid4985 valid4985

def retention4986 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(16000000000000000000/455792420776076303701),(36742461105914029177/1000000000000000000),1,(78329180758660049681684782762102381473/36742461105914029177000000000000000000),false,MergedCutProfiles.Batch697.profile27903,(fun _ => MergedCutProfiles.Batch697.profile27903)⟩
theorem profilesValid4986 : retention4986.ProfilesValid := by
  exact MergedCutProfiles.Batch697.valid27903
theorem numericValid4986 : retention4986.NumericValid := by decide +kernel
def certificate4986 : RatCutBinCertificate := ⟨⟨retention4986,(1740942262298746579/1000000000000000000),(31307344283847009/250000000000000000),(3330687757480619411/250000000000000000),(48859186672234238561/2000000000000000),(2115479331696661291/1000000000000000000)⟩,(499968634169971931/500000000000000000),(18245543622553377/1000000000000000000),(879351630812935233/1000000000000000000),(879431605531760013/500000000000000000)⟩
theorem valid4986 : certificate4986.Valid := by decide +kernel
theorem sound4986 : certificate4986.Sound := rat_cut_bin_certificate_sound certificate4986 profilesValid4986 numericValid4986 valid4986

def retention4987 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(1/2),64,1,(63848635416822846544693585750381821951/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch378.profile15126,(fun _ => MergedCutProfiles.Batch378.profile15126)⟩
theorem profilesValid4987 : retention4987.ProfilesValid := by
  exact MergedCutProfiles.Batch378.valid15126
theorem numericValid4987 : retention4987.NumericValid := by decide +kernel
def certificate4987 : RatCutBinCertificate := ⟨⟨retention4987,(1740942262298746579/1000000000000000000),(31307344283847009/250000000000000000),(3330687757480619411/250000000000000000),(48859186672234238561/2000000000000000),(981270655565453277/1000000000000000000)⟩,(499968634169971931/500000000000000000),(1966739258438311/50000000000000000),(817602015571145117/1000000000000000000),(79012351479662789/100000000000000000)⟩
theorem valid4987 : certificate4987.Valid := by decide +kernel
theorem sound4987 : certificate4987.Sound := rat_cut_bin_certificate_sound certificate4987 profilesValid4987 numericValid4987 valid4987

def retention4988 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(180572338777805821/455792420776076303701),(143027595071529363/200000000000000000),4,(30778638904453961719247758704827231/12713564006358165600000000000000000),false,MergedCutProfiles.Batch697.profile27904,(fun _ => MergedCutProfiles.Batch697.profile27904)⟩
theorem profilesValid4988 : retention4988.ProfilesValid := by
  exact MergedCutProfiles.Batch697.valid27904
theorem numericValid4988 : retention4988.NumericValid := by decide +kernel
def certificate4988 : RatCutBinCertificate := ⟨⟨retention4988,(1903256209298746579/1000000000000000000),(31307344283847009/250000000000000000),(3330687757480619411/250000000000000000),(48859186672234238561/2000000000000000),(587342311057247221/250000000000000000)⟩,(999931419600127907/1000000000000000000),(833749118542198711/1000000000000000000),(14656333107622419/1000000000000000000),(7141294234399299/1000000000000000000)⟩
theorem valid4988 : certificate4988.Valid := by decide +kernel
theorem sound4988 : certificate4988.Sound := rat_cut_bin_certificate_sound certificate4988 profilesValid4988 numericValid4988 valid4988

def retention4989 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(872604234719955193/1823169683104305214804),(180572338777805821/250000000000000000),4,(437534386469791201119878263827591447/180572338777805821000000000000000000),false,MergedCutProfiles.Batch697.profile27905,(fun _ => MergedCutProfiles.Batch697.profile27905)⟩
theorem profilesValid4989 : retention4989.ProfilesValid := by
  exact MergedCutProfiles.Batch697.valid27905
theorem numericValid4989 : retention4989.NumericValid := by decide +kernel
def certificate4989 : RatCutBinCertificate := ⟨⟨retention4989,(1903256209298746579/1000000000000000000),(31307344283847009/250000000000000000),(3330687757480619411/250000000000000000),(48859186672234238561/2000000000000000),(587870535662157427/250000000000000000)⟩,(999931419600127907/1000000000000000000),(831076730325732647/1000000000000000000),(3786630373589583/250000000000000000),(3699066068211861/500000000000000000)⟩
theorem valid4989 : certificate4989.Valid := by decide +kernel
theorem sound4989 : certificate4989.Sound := rat_cut_bin_certificate_sound certificate4989 profilesValid4989 numericValid4989 valid4989

def retention4990 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(3620543478276794573/1823169683104305214804),(872604234719955193/1000000000000000000),(73/20),(3364758094546032044355625502136174674719/1396166775551928308800000000000000000000),false,MergedCutProfiles.Batch697.profile27906,(fun _ => MergedCutProfiles.Batch697.profile27906)⟩
theorem profilesValid4990 : retention4990.ProfilesValid := by
  exact MergedCutProfiles.Batch697.valid27906
theorem numericValid4990 : retention4990.NumericValid := by decide +kernel
def certificate4990 : RatCutBinCertificate := ⟨⟨retention4990,(1903256209298746579/1000000000000000000),(31307344283847009/250000000000000000),(3330687757480619411/250000000000000000),(48859186672234238561/2000000000000000),(293087345653253563/125000000000000000)⟩,(999931419600127907/1000000000000000000),(800255634362993809/1000000000000000000),(1339259789235007/62500000000000000),(2863463238273203/250000000000000000)⟩
theorem valid4990 : certificate4990.Valid := by decide +kernel
theorem sound4990 : certificate4990.Sound := rat_cut_bin_certificate_sound certificate4990 profilesValid4990 numericValid4990 valid4990

def retention4991 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(42704581018056862051/1823169683104305214804),(3620543478276794573/1000000000000000000),(31/20),(12868790636457991313871174442104141467431/5792869565242871316800000000000000000000),false,MergedCutProfiles.Batch697.profile27907,(fun _ => MergedCutProfiles.Batch697.profile27907)⟩
theorem profilesValid4991 : retention4991.ProfilesValid := by
  exact MergedCutProfiles.Batch697.valid27907
theorem numericValid4991 : retention4991.NumericValid := by decide +kernel
def certificate4991 : RatCutBinCertificate := ⟨⟨retention4991,(1903256209298746579/1000000000000000000),(31307344283847009/250000000000000000),(3330687757480619411/250000000000000000),(48859186672234238561/2000000000000000),(548439648834770047/250000000000000000)⟩,(999931419600127907/1000000000000000000),(725804179585329903/1000000000000000000),(41593707359229703/1000000000000000000),(47008577628753543/1000000000000000000)⟩
theorem valid4991 : certificate4991.Valid := by decide +kernel
theorem sound4991 : certificate4991.Sound := rat_cut_bin_certificate_sound certificate4991 profilesValid4991 numericValid4991 valid4991

def certificates : List RatCutBinCertificate := [certificate4980,certificate4981,certificate4982,certificate4983,certificate4984,certificate4985,certificate4986,certificate4987,certificate4988,certificate4989,certificate4990,certificate4991]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4980,List.forall_mem_cons.mpr ⟨sound4981,List.forall_mem_cons.mpr ⟨sound4982,List.forall_mem_cons.mpr ⟨sound4983,List.forall_mem_cons.mpr ⟨sound4984,List.forall_mem_cons.mpr ⟨sound4985,List.forall_mem_cons.mpr ⟨sound4986,List.forall_mem_cons.mpr ⟨sound4987,List.forall_mem_cons.mpr ⟨sound4988,List.forall_mem_cons.mpr ⟨sound4989,List.forall_mem_cons.mpr ⟨sound4990,List.forall_mem_cons.mpr ⟨sound4991,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch415
