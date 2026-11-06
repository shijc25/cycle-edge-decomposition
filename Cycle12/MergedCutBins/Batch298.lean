import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch427
import Cycle12.MergedCutProfiles.Batch428
import Cycle12.MergedCutProfiles.Batch429
import Cycle12.MergedCutProfiles.Batch549
import Cycle12.MergedCutProfiles.Batch550
import Cycle12.MergedCutProfiles.Batch551

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch298

def retention3576 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(11847735524442363743/25784585687379593828),(8673743889299722513/1000000000000000000),1,(1820609721005817932189855072196005049/1734748777859944502600000000000000000),false,MergedCutProfiles.Batch549.profile21990,(fun _ => MergedCutProfiles.Batch549.profile21990)⟩
theorem profilesValid3576 : retention3576.ProfilesValid := by
  exact MergedCutProfiles.Batch549.valid21990
theorem numericValid3576 : retention3576.NumericValid := by decide +kernel
def certificate3576 : RatCutBinCertificate := ⟨⟨retention3576,(1163569897224245929/500000000000000000),(55239130418189853/250000000000000000),(17261006915229141307/1000000000000000000),(446476391738544410619/500000000000000000),(509852197547507341/500000000000000000)⟩,(997957884591768599/1000000000000000000),(29365455871216131/250000000000000000),(314387392070283829/500000000000000000),(286232250050017043/500000000000000000)⟩
theorem valid3576 : certificate3576.Valid := by decide +kernel
theorem sound3576 : certificate3576.Sound := rat_cut_bin_certificate_sound certificate3576 profilesValid3576 numericValid3576 valid3576

def retention3577 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(3207349964787607970/6446146421844898457),(11847735524442363743/500000000000000000),1,(23596785370843591200672105386268040347/23695471048884727486000000000000000000),false,MergedCutProfiles.Batch549.profile21991,(fun _ => MergedCutProfiles.Batch549.profile21991)⟩
theorem profilesValid3577 : retention3577.ProfilesValid := by
  exact MergedCutProfiles.Batch549.valid21991
theorem numericValid3577 : retention3577.NumericValid := by decide +kernel
def certificate3577 : RatCutBinCertificate := ⟨⟨retention3577,(1163569897224245929/500000000000000000),(55239130418189853/250000000000000000),(17261006915229141307/1000000000000000000),(446476391738544410619/500000000000000000),(60377840209592269/62500000000000000)⟩,(997957884591768599/1000000000000000000),(123986235313740797/1000000000000000000),(615301286951672143/1000000000000000000),(569926751746527511/1000000000000000000)⟩
theorem valid3577 : certificate3577.Valid := by decide +kernel
theorem sound3577 : certificate3577.Sound := rat_cut_bin_certificate_sound certificate3577 profilesValid3577 numericValid3577 valid3577

def retention3578 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(1/2),(320734996478760797/12500000000000000),1,(101799815200682753157867310140123145231/102635198873203455040000000000000000000),false,MergedCutProfiles.Batch427.profile17083,(fun _ => MergedCutProfiles.Batch427.profile17083)⟩
theorem profilesValid3578 : retention3578.ProfilesValid := by
  exact MergedCutProfiles.Batch427.valid17083
theorem numericValid3578 : retention3578.NumericValid := by decide +kernel
def certificate3578 : RatCutBinCertificate := ⟨⟨retention3578,(1163569897224245929/500000000000000000),(55239130418189853/250000000000000000),(17261006915229141307/1000000000000000000),(446476391738544410619/500000000000000000),(962070866979073933/1000000000000000000)⟩,(997957884591768599/1000000000000000000),(60790261800927/488281250000000),(614256180280719841/1000000000000000000),(142102120999652623/250000000000000000)⟩
theorem valid3578 : certificate3578.Valid := by decide +kernel
theorem sound3578 : certificate3578.Sound := rat_cut_bin_certificate_sound certificate3578 profilesValid3578 numericValid3578 valid3578

def retention3579 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(943337210345610415/50624096366191786564),(186799447593190181/200000000000000000),(14/5),(565289386163643387297/256000000000000000000),true,MergedCutProfiles.Batch549.profile21992,![MergedCutProfiles.Batch549.profile21992,MergedCutProfiles.Batch549.profile21993,MergedCutProfiles.Batch549.profile21994,MergedCutProfiles.Batch549.profile21995,MergedCutProfiles.Batch549.profile21996,MergedCutProfiles.Batch549.profile21997,MergedCutProfiles.Batch549.profile21998,MergedCutProfiles.Batch549.profile21999,MergedCutProfiles.Batch550.profile22000,MergedCutProfiles.Batch550.profile22001,MergedCutProfiles.Batch550.profile22002,MergedCutProfiles.Batch550.profile22003,MergedCutProfiles.Batch550.profile22004,MergedCutProfiles.Batch550.profile22005,MergedCutProfiles.Batch550.profile22006,MergedCutProfiles.Batch550.profile22007]⟩
theorem profilesValid3579 : retention3579.ProfilesValid := by
  change ∀ j : Fin 16, (retention3579.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch549.valid21992
  · exact MergedCutProfiles.Batch549.valid21993
  · exact MergedCutProfiles.Batch549.valid21994
  · exact MergedCutProfiles.Batch549.valid21995
  · exact MergedCutProfiles.Batch549.valid21996
  · exact MergedCutProfiles.Batch549.valid21997
  · exact MergedCutProfiles.Batch549.valid21998
  · exact MergedCutProfiles.Batch549.valid21999
  · exact MergedCutProfiles.Batch550.valid22000
  · exact MergedCutProfiles.Batch550.valid22001
  · exact MergedCutProfiles.Batch550.valid22002
  · exact MergedCutProfiles.Batch550.valid22003
  · exact MergedCutProfiles.Batch550.valid22004
  · exact MergedCutProfiles.Batch550.valid22005
  · exact MergedCutProfiles.Batch550.valid22006
  · exact MergedCutProfiles.Batch550.valid22007
theorem numericValid3579 : retention3579.NumericValid := by decide +kernel
def certificate3579 : RatCutBinCertificate := ⟨⟨retention3579,(2281222050009882821/1000000000000000000),(225107070921290071/1000000000000000000),(17427134482546462459/1000000000000000000),(885034598884324527611/1000000000000000000),(132852939354652491/62500000000000000)⟩,(49899540928438097/50000000000000000),(289219550072611491/1000000000000000000),(175976467019658143/500000000000000000),(41315126257085863/200000000000000000)⟩
theorem valid3579 : certificate3579.Valid := by decide +kernel
theorem sound3579 : certificate3579.Sound := rat_cut_bin_certificate_sound certificate3579 profilesValid3579 numericValid3579 valid3579

def retention3580 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(78227515404042279/3616006883299413326),(188667442069122083/200000000000000000),(14/5),(35208577889549069347/16000000000000000000),true,MergedCutProfiles.Batch550.profile22008,![MergedCutProfiles.Batch550.profile22008,MergedCutProfiles.Batch550.profile22009,MergedCutProfiles.Batch550.profile22010,MergedCutProfiles.Batch550.profile22011,MergedCutProfiles.Batch550.profile22012,MergedCutProfiles.Batch549.profile21998,MergedCutProfiles.Batch550.profile22013,MergedCutProfiles.Batch550.profile22014,MergedCutProfiles.Batch550.profile22015,MergedCutProfiles.Batch550.profile22016,MergedCutProfiles.Batch427.profile17091,MergedCutProfiles.Batch550.profile22017,MergedCutProfiles.Batch550.profile22018,MergedCutProfiles.Batch550.profile22019,MergedCutProfiles.Batch550.profile22020,MergedCutProfiles.Batch550.profile22021]⟩
theorem profilesValid3580 : retention3580.ProfilesValid := by
  change ∀ j : Fin 16, (retention3580.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch550.valid22008
  · exact MergedCutProfiles.Batch550.valid22009
  · exact MergedCutProfiles.Batch550.valid22010
  · exact MergedCutProfiles.Batch550.valid22011
  · exact MergedCutProfiles.Batch550.valid22012
  · exact MergedCutProfiles.Batch549.valid21998
  · exact MergedCutProfiles.Batch550.valid22013
  · exact MergedCutProfiles.Batch550.valid22014
  · exact MergedCutProfiles.Batch550.valid22015
  · exact MergedCutProfiles.Batch550.valid22016
  · exact MergedCutProfiles.Batch427.valid17091
  · exact MergedCutProfiles.Batch550.valid22017
  · exact MergedCutProfiles.Batch550.valid22018
  · exact MergedCutProfiles.Batch550.valid22019
  · exact MergedCutProfiles.Batch550.valid22020
  · exact MergedCutProfiles.Batch550.valid22021
theorem numericValid3580 : retention3580.NumericValid := by decide +kernel
def certificate3580 : RatCutBinCertificate := ⟨⟨retention3580,(2281222050009882821/1000000000000000000),(225107070921290071/1000000000000000000),(17427134482546462459/1000000000000000000),(885034598884324527611/1000000000000000000),(1059010781259646727/500000000000000000)⟩,(49899540928438097/50000000000000000),(288999899402473769/1000000000000000000),(176112665329968477/500000000000000000),(51654954469072807/250000000000000000)⟩
theorem valid3580 : certificate3580.Valid := by decide +kernel
theorem sound3580 : certificate3580.Sound := rat_cut_bin_certificate_sound certificate3580 profilesValid3580 numericValid3580 valid3580

def retention3581 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(277331876750000000/12656024091547946641),(547592607828295953/500000000000000000),(49/20),(10905999946993430289/5000000000000000000),true,MergedCutProfiles.Batch550.profile22008,![MergedCutProfiles.Batch550.profile22008,MergedCutProfiles.Batch550.profile22022,MergedCutProfiles.Batch550.profile22023,MergedCutProfiles.Batch550.profile22024,MergedCutProfiles.Batch550.profile22025,MergedCutProfiles.Batch550.profile22026,MergedCutProfiles.Batch550.profile22027,MergedCutProfiles.Batch428.profile17121,MergedCutProfiles.Batch427.profile17106,MergedCutProfiles.Batch550.profile22028,MergedCutProfiles.Batch550.profile22004,MergedCutProfiles.Batch550.profile22029,MergedCutProfiles.Batch427.profile17092,MergedCutProfiles.Batch550.profile22030,MergedCutProfiles.Batch550.profile22031,MergedCutProfiles.Batch428.profile17124]⟩
theorem profilesValid3581 : retention3581.ProfilesValid := by
  change ∀ j : Fin 16, (retention3581.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch550.valid22008
  · exact MergedCutProfiles.Batch550.valid22022
  · exact MergedCutProfiles.Batch550.valid22023
  · exact MergedCutProfiles.Batch550.valid22024
  · exact MergedCutProfiles.Batch550.valid22025
  · exact MergedCutProfiles.Batch550.valid22026
  · exact MergedCutProfiles.Batch550.valid22027
  · exact MergedCutProfiles.Batch428.valid17121
  · exact MergedCutProfiles.Batch427.valid17106
  · exact MergedCutProfiles.Batch550.valid22028
  · exact MergedCutProfiles.Batch550.valid22004
  · exact MergedCutProfiles.Batch550.valid22029
  · exact MergedCutProfiles.Batch427.valid17092
  · exact MergedCutProfiles.Batch550.valid22030
  · exact MergedCutProfiles.Batch550.valid22031
  · exact MergedCutProfiles.Batch428.valid17124
theorem numericValid3581 : retention3581.NumericValid := by decide +kernel
def certificate3581 : RatCutBinCertificate := ⟨⟨retention3581,(2281222050009882821/1000000000000000000),(225107070921290071/1000000000000000000),(17427134482546462459/1000000000000000000),(885034598884324527611/1000000000000000000),(527249965430364979/250000000000000000)⟩,(49899540928438097/50000000000000000),(34084828617021099/125000000000000000),(372938711938000521/1000000000000000000),(121236138490431397/500000000000000000)⟩
theorem valid3581 : certificate3581.Valid := by decide +kernel
theorem sound3581 : certificate3581.Sound := rat_cut_bin_certificate_sound certificate3581 profilesValid3581 numericValid3581 valid3581

def retention3582 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(314721791029084178/12656024091547946641),(1109327507/1000000000),(12/5),(4322685518345215293/2000000000000000000),true,MergedCutProfiles.Batch550.profile22032,![MergedCutProfiles.Batch550.profile22032,MergedCutProfiles.Batch550.profile22033,MergedCutProfiles.Batch549.profile21995,MergedCutProfiles.Batch550.profile22034,MergedCutProfiles.Batch428.profile17133,MergedCutProfiles.Batch549.profile21999,MergedCutProfiles.Batch550.profile22014,MergedCutProfiles.Batch550.profile22035,MergedCutProfiles.Batch550.profile22003,MergedCutProfiles.Batch428.profile17134,MergedCutProfiles.Batch550.profile22036,MergedCutProfiles.Batch550.profile22007,MergedCutProfiles.Batch550.profile22020,MergedCutProfiles.Batch550.profile22037,MergedCutProfiles.Batch428.profile17135,MergedCutProfiles.Batch550.profile22038]⟩
theorem profilesValid3582 : retention3582.ProfilesValid := by
  change ∀ j : Fin 16, (retention3582.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch550.valid22032
  · exact MergedCutProfiles.Batch550.valid22033
  · exact MergedCutProfiles.Batch549.valid21995
  · exact MergedCutProfiles.Batch550.valid22034
  · exact MergedCutProfiles.Batch428.valid17133
  · exact MergedCutProfiles.Batch549.valid21999
  · exact MergedCutProfiles.Batch550.valid22014
  · exact MergedCutProfiles.Batch550.valid22035
  · exact MergedCutProfiles.Batch550.valid22003
  · exact MergedCutProfiles.Batch428.valid17134
  · exact MergedCutProfiles.Batch550.valid22036
  · exact MergedCutProfiles.Batch550.valid22007
  · exact MergedCutProfiles.Batch550.valid22020
  · exact MergedCutProfiles.Batch550.valid22037
  · exact MergedCutProfiles.Batch428.valid17135
  · exact MergedCutProfiles.Batch550.valid22038
theorem numericValid3582 : retention3582.NumericValid := by decide +kernel
def certificate3582 : RatCutBinCertificate := ⟨⟨retention3582,(2281222050009882821/1000000000000000000),(225107070921290071/1000000000000000000),(17427134482546462459/1000000000000000000),(885034598884324527611/1000000000000000000),(2090616051070824717/1000000000000000000)⟩,(49899540928438097/50000000000000000),(68418416263625857/250000000000000000),(371648724983897441/1000000000000000000),(24334404497990197/100000000000000000)⟩
theorem valid3582 : certificate3582.Valid := by decide +kernel
theorem sound3582 : certificate3582.Sound := rat_cut_bin_certificate_sound certificate3582 profilesValid3582 numericValid3582 valid3582

def retention3583 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(834490591898616305/12656024091547946641),(157360895514542089/125000000000000000),(9/4),(4056600537602951589/2000000000000000000),true,MergedCutProfiles.Batch550.profile22023,![MergedCutProfiles.Batch550.profile22023,MergedCutProfiles.Batch550.profile22026,MergedCutProfiles.Batch427.profile17106,MergedCutProfiles.Batch550.profile22029,MergedCutProfiles.Batch550.profile22031,MergedCutProfiles.Batch550.profile22038,MergedCutProfiles.Batch550.profile22039,MergedCutProfiles.Batch428.profile17127,MergedCutProfiles.Batch551.profile22040,MergedCutProfiles.Batch551.profile22041,MergedCutProfiles.Batch551.profile22042,MergedCutProfiles.Batch551.profile22043,MergedCutProfiles.Batch551.profile22044,MergedCutProfiles.Batch551.profile22045,MergedCutProfiles.Batch551.profile22046,MergedCutProfiles.Batch428.profile17149]⟩
theorem profilesValid3583 : retention3583.ProfilesValid := by
  change ∀ j : Fin 16, (retention3583.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch550.valid22023
  · exact MergedCutProfiles.Batch550.valid22026
  · exact MergedCutProfiles.Batch427.valid17106
  · exact MergedCutProfiles.Batch550.valid22029
  · exact MergedCutProfiles.Batch550.valid22031
  · exact MergedCutProfiles.Batch550.valid22038
  · exact MergedCutProfiles.Batch550.valid22039
  · exact MergedCutProfiles.Batch428.valid17127
  · exact MergedCutProfiles.Batch551.valid22040
  · exact MergedCutProfiles.Batch551.valid22041
  · exact MergedCutProfiles.Batch551.valid22042
  · exact MergedCutProfiles.Batch551.valid22043
  · exact MergedCutProfiles.Batch551.valid22044
  · exact MergedCutProfiles.Batch551.valid22045
  · exact MergedCutProfiles.Batch551.valid22046
  · exact MergedCutProfiles.Batch428.valid17149
theorem numericValid3583 : retention3583.NumericValid := by decide +kernel
def certificate3583 : RatCutBinCertificate := ⟨⟨retention3583,(2281222050009882821/1000000000000000000),(225107070921290071/1000000000000000000),(17427134482546462459/1000000000000000000),(885034598884324527611/1000000000000000000),(490498590087124271/250000000000000000)⟩,(49899540928438097/50000000000000000),(277863108845210427/1000000000000000000),(7325132933680139/20000000000000000),(24361568838709857/100000000000000000)⟩
theorem valid3583 : certificate3583.Valid := by decide +kernel
theorem sound3583 : certificate3583.Sound := rat_cut_bin_certificate_sound certificate3583 profilesValid3583 numericValid3583 valid3583

def retention3584 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(2512191939344612963/7232013766598826652),(166898118379723261/50000000000000000),(5/4),(17351419480109972026112549339217784591/13351849470377860880000000000000000000),false,MergedCutProfiles.Batch551.profile22047,(fun _ => MergedCutProfiles.Batch551.profile22047)⟩
theorem profilesValid3584 : retention3584.ProfilesValid := by
  exact MergedCutProfiles.Batch551.valid22047
theorem numericValid3584 : retention3584.NumericValid := by decide +kernel
def certificate3584 : RatCutBinCertificate := ⟨⟨retention3584,(2281222050009882821/1000000000000000000),(225107070921290071/1000000000000000000),(17427134482546462459/1000000000000000000),(885034598884324527611/1000000000000000000),(631358103249136791/500000000000000000)⟩,(49899540928438097/50000000000000000),(66605189830944963/200000000000000000),(300791052427798471/1000000000000000000),(61017248918642313/250000000000000000)⟩
theorem valid3584 : certificate3584.Valid := by decide +kernel
theorem sound3584 : certificate3584.Sound := rat_cut_bin_certificate_sound certificate3584 profilesValid3584 numericValid3584 valid3584

def retention3585 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(24664798192758218197/50624096366191786564),(17585343575412290741/1000000000000000000),1,(71206500528883516584838136729238454683/70341374301649162964000000000000000000),false,MergedCutProfiles.Batch551.profile22048,(fun _ => MergedCutProfiles.Batch551.profile22048)⟩
theorem profilesValid3585 : retention3585.ProfilesValid := by
  exact MergedCutProfiles.Batch551.valid22048
theorem numericValid3585 : retention3585.NumericValid := by decide +kernel
def certificate3585 : RatCutBinCertificate := ⟨⟨retention3585,(2281222050009882821/1000000000000000000),(225107070921290071/1000000000000000000),(17427134482546462459/1000000000000000000),(885034598884324527611/1000000000000000000),(245707973490494613/250000000000000000)⟩,(49899540928438097/50000000000000000),(365645879071500381/1000000000000000000),(266477759930743857/1000000000000000000),(7735100765411859/31250000000000000)⟩
theorem valid3585 : certificate3585.Valid := by decide +kernel
theorem sound3585 : certificate3585.Sound := rat_cut_bin_certificate_sound certificate3585 profilesValid3585 numericValid3585 valid3585

def retention3586 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(25160560636432658383/50624096366191786564),(24664798192758218197/1000000000000000000),1,(98397270869150791879160390004628030227/98659192771032872788000000000000000000),false,MergedCutProfiles.Batch551.profile22049,(fun _ => MergedCutProfiles.Batch551.profile22049)⟩
theorem profilesValid3586 : retention3586.ProfilesValid := by
  exact MergedCutProfiles.Batch551.valid22049
theorem numericValid3586 : retention3586.NumericValid := by decide +kernel
def certificate3586 : RatCutBinCertificate := ⟨⟨retention3586,(2281222050009882821/1000000000000000000),(225107070921290071/1000000000000000000),(17427134482546462459/1000000000000000000),(885034598884324527611/1000000000000000000),(967878234521109409/1000000000000000000)⟩,(49899540928438097/50000000000000000),(367046581181076997/1000000000000000000),(53014270915954469/200000000000000000),(61589998783711403/250000000000000000)⟩
theorem valid3586 : certificate3586.Valid := by decide +kernel
theorem sound3586 : certificate3586.Sound := rat_cut_bin_certificate_sound certificate3586 profilesValid3586 numericValid3586 valid3586

def retention3587 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(1/2),(25160560636432658383/1000000000000000000),1,(4990196571502931464449384209152718813/5032112127286531676600000000000000000),false,MergedCutProfiles.Batch429.profile17180,(fun _ => MergedCutProfiles.Batch429.profile17180)⟩
theorem profilesValid3587 : retention3587.ProfilesValid := by
  exact MergedCutProfiles.Batch429.valid17180
theorem numericValid3587 : retention3587.NumericValid := by decide +kernel
def certificate3587 : RatCutBinCertificate := ⟨⟨retention3587,(2281222050009882821/1000000000000000000),(225107070921290071/1000000000000000000),(17427134482546462459/1000000000000000000),(885034598884324527611/1000000000000000000),(120275430081489/125000000000000)⟩,(49899540928438097/50000000000000000),(18450107340707627/50000000000000000),(65779188373499321/250000000000000000),(243343689575713271/1000000000000000000)⟩
theorem valid3587 : certificate3587.Valid := by decide +kernel
theorem sound3587 : certificate3587.Sound := rat_cut_bin_certificate_sound certificate3587 profilesValid3587 numericValid3587 valid3587

def certificates : List RatCutBinCertificate := [certificate3576,certificate3577,certificate3578,certificate3579,certificate3580,certificate3581,certificate3582,certificate3583,certificate3584,certificate3585,certificate3586,certificate3587]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3576,List.forall_mem_cons.mpr ⟨sound3577,List.forall_mem_cons.mpr ⟨sound3578,List.forall_mem_cons.mpr ⟨sound3579,List.forall_mem_cons.mpr ⟨sound3580,List.forall_mem_cons.mpr ⟨sound3581,List.forall_mem_cons.mpr ⟨sound3582,List.forall_mem_cons.mpr ⟨sound3583,List.forall_mem_cons.mpr ⟨sound3584,List.forall_mem_cons.mpr ⟨sound3585,List.forall_mem_cons.mpr ⟨sound3586,List.forall_mem_cons.mpr ⟨sound3587,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch298
