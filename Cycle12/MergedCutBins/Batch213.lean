import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch398
import Cycle12.MergedCutProfiles.Batch399
import Cycle12.MergedCutProfiles.Batch400
import Cycle12.MergedCutProfiles.Batch401

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch213

def retention2556 : RatCutRetentionCertificate := ⟨(59/1000),(119/2000),(4831383016676152553/25473078475677068420),(739261335521885813/500000000000000000),(37/20),(1061102026251937342949/640000000000000000000),true,MergedCutProfiles.Batch398.profile15957,![MergedCutProfiles.Batch398.profile15957,MergedCutProfiles.Batch398.profile15958,MergedCutProfiles.Batch398.profile15959,MergedCutProfiles.Batch399.profile15960,MergedCutProfiles.Batch399.profile15961,MergedCutProfiles.Batch399.profile15962,MergedCutProfiles.Batch399.profile15963,MergedCutProfiles.Batch399.profile15964,MergedCutProfiles.Batch399.profile15965,MergedCutProfiles.Batch399.profile15966,MergedCutProfiles.Batch399.profile15967,MergedCutProfiles.Batch399.profile15968,MergedCutProfiles.Batch399.profile15969,MergedCutProfiles.Batch399.profile15970,MergedCutProfiles.Batch399.profile15971,MergedCutProfiles.Batch399.profile15972]⟩
theorem profilesValid2556 : retention2556.ProfilesValid := by
  change ∀ j : Fin 16, (retention2556.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch398.valid15957
  · exact MergedCutProfiles.Batch398.valid15958
  · exact MergedCutProfiles.Batch398.valid15959
  · exact MergedCutProfiles.Batch399.valid15960
  · exact MergedCutProfiles.Batch399.valid15961
  · exact MergedCutProfiles.Batch399.valid15962
  · exact MergedCutProfiles.Batch399.valid15963
  · exact MergedCutProfiles.Batch399.valid15964
  · exact MergedCutProfiles.Batch399.valid15965
  · exact MergedCutProfiles.Batch399.valid15966
  · exact MergedCutProfiles.Batch399.valid15967
  · exact MergedCutProfiles.Batch399.valid15968
  · exact MergedCutProfiles.Batch399.valid15969
  · exact MergedCutProfiles.Batch399.valid15970
  · exact MergedCutProfiles.Batch399.valid15971
  · exact MergedCutProfiles.Batch399.valid15972
theorem numericValid2556 : retention2556.NumericValid := by decide +kernel
def certificate2556 : RatCutBinCertificate := ⟨⟨retention2556,(2269928936836454261/1000000000000000000),(178859476136284067/1000000000000000000),(7789990525088299483/500000000000000000),(398079680679526674123/1000000000000000000),(201219362193501811/125000000000000000)⟩,(995292815782194811/1000000000000000000),(20669763173391663/62500000000000000),(303338099892825719/1000000000000000000),(99568864911821017/500000000000000000)⟩
theorem valid2556 : certificate2556.Valid := by decide +kernel
theorem sound2556 : certificate2556.Sound := rat_cut_bin_certificate_sound certificate2556 profilesValid2556 numericValid2556 valid2556

def retention2557 : RatCutRetentionCertificate := ⟨(59/1000),(119/2000),(11144661089737228881/25473078475677068420),(4831383016676152553/1000000000000000000),(21/20),(1396525787535786362577/1280000000000000000000),true,MergedCutProfiles.Batch399.profile15973,![MergedCutProfiles.Batch399.profile15973,MergedCutProfiles.Batch399.profile15974,MergedCutProfiles.Batch399.profile15975,MergedCutProfiles.Batch399.profile15976,MergedCutProfiles.Batch399.profile15977,MergedCutProfiles.Batch399.profile15978,MergedCutProfiles.Batch399.profile15979,MergedCutProfiles.Batch399.profile15980,MergedCutProfiles.Batch399.profile15981,MergedCutProfiles.Batch399.profile15982,MergedCutProfiles.Batch399.profile15983,MergedCutProfiles.Batch399.profile15984,MergedCutProfiles.Batch399.profile15985,MergedCutProfiles.Batch399.profile15986,MergedCutProfiles.Batch399.profile15987,MergedCutProfiles.Batch399.profile15988]⟩
theorem profilesValid2557 : retention2557.ProfilesValid := by
  change ∀ j : Fin 16, (retention2557.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch399.valid15973
  · exact MergedCutProfiles.Batch399.valid15974
  · exact MergedCutProfiles.Batch399.valid15975
  · exact MergedCutProfiles.Batch399.valid15976
  · exact MergedCutProfiles.Batch399.valid15977
  · exact MergedCutProfiles.Batch399.valid15978
  · exact MergedCutProfiles.Batch399.valid15979
  · exact MergedCutProfiles.Batch399.valid15980
  · exact MergedCutProfiles.Batch399.valid15981
  · exact MergedCutProfiles.Batch399.valid15982
  · exact MergedCutProfiles.Batch399.valid15983
  · exact MergedCutProfiles.Batch399.valid15984
  · exact MergedCutProfiles.Batch399.valid15985
  · exact MergedCutProfiles.Batch399.valid15986
  · exact MergedCutProfiles.Batch399.valid15987
  · exact MergedCutProfiles.Batch399.valid15988
theorem numericValid2557 : retention2557.NumericValid := by decide +kernel
def certificate2557 : RatCutBinCertificate := ⟨⟨retention2557,(2269928936836454261/1000000000000000000),(178859476136284067/1000000000000000000),(7789990525088299483/500000000000000000),(398079680679526674123/1000000000000000000),(531835713392826069/500000000000000000)⟩,(995292815782194811/1000000000000000000),(396460055036356311/1000000000000000000),(236741540515755283/1000000000000000000),(198866756382412669/1000000000000000000)⟩
theorem valid2557 : certificate2557.Valid := by decide +kernel
theorem sound2557 : certificate2557.Sound := rat_cut_bin_certificate_sound certificate2557 profilesValid2557 numericValid2557 valid2557

def retention2558 : RatCutRetentionCertificate := ⟨(59/1000),(119/2000),(6279041534126871721/12736539237838534210),(11144661089737228881/1000000000000000000),(21/20),(18026440102493866312319776022049574790519/17831457743579566209600000000000000000000),false,MergedCutProfiles.Batch399.profile15989,(fun _ => MergedCutProfiles.Batch399.profile15989)⟩
theorem profilesValid2558 : retention2558.ProfilesValid := by
  exact MergedCutProfiles.Batch399.valid15989
theorem numericValid2558 : retention2558.NumericValid := by decide +kernel
def certificate2558 : RatCutBinCertificate := ⟨⟨retention2558,(2269928936836454261/1000000000000000000),(178859476136284067/1000000000000000000),(7789990525088299483/500000000000000000),(398079680679526674123/1000000000000000000),(122946471045260503/125000000000000000)⟩,(995292815782194811/1000000000000000000),(400639443551473669/1000000000000000000),(116448491759377773/500000000000000000),(200995126078967907/1000000000000000000)⟩
theorem valid2558 : certificate2558.Valid := by decide +kernel
theorem sound2558 : certificate2558.Sound := rat_cut_bin_certificate_sound certificate2558 profilesValid2558 numericValid2558 valid2558

def retention2559 : RatCutRetentionCertificate := ⟨(59/1000),(119/2000),(12683663898936280877/25473078475677068420),(6279041534126871721/500000000000000000),1,(386797968075557340722187826804559139/392440095882929482562500000000000000),false,MergedCutProfiles.Batch399.profile15990,(fun _ => MergedCutProfiles.Batch399.profile15990)⟩
theorem profilesValid2559 : retention2559.ProfilesValid := by
  exact MergedCutProfiles.Batch399.valid15990
theorem numericValid2559 : retention2559.NumericValid := by decide +kernel
def certificate2559 : RatCutBinCertificate := ⟨⟨retention2559,(2269928936836454261/1000000000000000000),(178859476136284067/1000000000000000000),(7789990525088299483/500000000000000000),(398079680679526674123/1000000000000000000),(479781526404783391/500000000000000000)⟩,(995292815782194811/1000000000000000000),(81636422409791043/200000000000000000),(226068585138293871/1000000000000000000),(100267773682157101/500000000000000000)⟩
theorem valid2559 : certificate2559.Valid := by decide +kernel
theorem sound2559 : certificate2559.Sound := rat_cut_bin_certificate_sound certificate2559 profilesValid2559 numericValid2559 valid2559

def retention2560 : RatCutRetentionCertificate := ⟨(59/1000),(119/2000),(1/2),(12683663898936280877/1000000000000000000),1,(498126845692988961235445320793576557/507346555957451235080000000000000000),false,MergedCutProfiles.Batch399.profile15991,(fun _ => MergedCutProfiles.Batch399.profile15991)⟩
theorem profilesValid2560 : retention2560.ProfilesValid := by
  exact MergedCutProfiles.Batch399.valid15991
theorem numericValid2560 : retention2560.NumericValid := by decide +kernel
def certificate2560 : RatCutBinCertificate := ⟨⟨retention2560,(2269928936836454261/1000000000000000000),(178859476136284067/1000000000000000000),(7789990525088299483/500000000000000000),(398079680679526674123/1000000000000000000),(119470961619158239/125000000000000000)⟩,(995292815782194811/1000000000000000000),(6400132957269959/15625000000000000),(224793007779698309/1000000000000000000),(24851340455147987/125000000000000000)⟩
theorem valid2560 : certificate2560.Valid := by decide +kernel
theorem sound2560 : certificate2560.Sound := rat_cut_bin_certificate_sound certificate2560 profilesValid2560 numericValid2560 valid2560

def retention2561 : RatCutRetentionCertificate := ⟨(59/1000),(119/2000),(11520202999477092007/25473078475677068420),(5145515082482123857/1000000000000000000),(21/20),(8756541809352984272987545534535806046391/8232824131971398171200000000000000000000),false,MergedCutProfiles.Batch399.profile15992,(fun _ => MergedCutProfiles.Batch399.profile15992)⟩
theorem profilesValid2561 : retention2561.ProfilesValid := by
  exact MergedCutProfiles.Batch399.valid15992
theorem numericValid2561 : retention2561.NumericValid := by decide +kernel
def certificate2561 : RatCutBinCertificate := ⟨⟨retention2561,(2517441534836454261/1000000000000000000),(178859476136284067/1000000000000000000),(7789990525088299483/500000000000000000),(398079680679526674123/1000000000000000000),(1033265385422101907/1000000000000000000)⟩,(994778975645965487/1000000000000000000),(226550866260136629/1000000000000000000),(109229016756611873/250000000000000000),(36163978719137603/100000000000000000)⟩
theorem valid2561 : certificate2561.Valid := by decide +kernel
theorem sound2561 : certificate2561.Sound := rat_cut_bin_certificate_sound certificate2561 profilesValid2561 numericValid2561 valid2561

def retention2562 : RatCutRetentionCertificate := ⟨(59/1000),(119/2000),(12599476358862295739/25473078475677068420),(11520202999477092007/1000000000000000000),1,(45626727367529616148831795476481530027/46080811997908368028000000000000000000),false,MergedCutProfiles.Batch399.profile15993,(fun _ => MergedCutProfiles.Batch399.profile15993)⟩
theorem profilesValid2562 : retention2562.ProfilesValid := by
  exact MergedCutProfiles.Batch399.valid15993
theorem numericValid2562 : retention2562.NumericValid := by decide +kernel
def certificate2562 : RatCutBinCertificate := ⟨⟨retention2562,(2517441534836454261/1000000000000000000),(178859476136284067/1000000000000000000),(7789990525088299483/500000000000000000),(398079680679526674123/1000000000000000000),(480622170737284697/500000000000000000)⟩,(994778975645965487/1000000000000000000),(243525145526366803/1000000000000000000),(51548368831591807/125000000000000000),(181939504782244751/500000000000000000)⟩
theorem valid2562 : certificate2562.Valid := by decide +kernel
theorem sound2562 : certificate2562.Sound := rat_cut_bin_certificate_sound certificate2562 profilesValid2562 numericValid2562 valid2562

def retention2563 : RatCutRetentionCertificate := ⟨(59/1000),(119/2000),(12725471122450918697/25473078475677068420),(12599476358862295739/1000000000000000000),1,(2475875978822308961592096801004915253/2519895271772459147800000000000000000),false,MergedCutProfiles.Batch399.profile15994,(fun _ => MergedCutProfiles.Batch399.profile15994)⟩
theorem profilesValid2563 : retention2563.ProfilesValid := by
  exact MergedCutProfiles.Batch399.valid15994
theorem numericValid2563 : retention2563.NumericValid := by decide +kernel
def certificate2563 : RatCutBinCertificate := ⟨⟨retention2563,(2517441534836454261/1000000000000000000),(178859476136284067/1000000000000000000),(7789990525088299483/500000000000000000),(398079680679526674123/1000000000000000000),(119203729020570657/125000000000000000)⟩,(994778975645965487/1000000000000000000),(49093927276300929/200000000000000000),(409652855484972897/1000000000000000000),(45149274402348433/125000000000000000)⟩
theorem valid2563 : certificate2563.Valid := by decide +kernel
theorem sound2563 : certificate2563.Sound := rat_cut_bin_certificate_sound certificate2563 profilesValid2563 numericValid2563 valid2563

def retention2564 : RatCutRetentionCertificate := ⟨(59/1000),(119/2000),(1/2),(12725471122450918697/1000000000000000000),1,(499801812220501984843001032737866677/509018844898036747880000000000000000),false,MergedCutProfiles.Batch399.profile15991,(fun _ => MergedCutProfiles.Batch399.profile15991)⟩
theorem profilesValid2564 : retention2564.ProfilesValid := by
  exact MergedCutProfiles.Batch399.valid15991
theorem numericValid2564 : retention2564.NumericValid := by decide +kernel
def certificate2564 : RatCutBinCertificate := ⟨⟨retention2564,(2517441534836454261/1000000000000000000),(178859476136284067/1000000000000000000),(7789990525088299483/500000000000000000),(398079680679526674123/1000000000000000000),(5956194330810263/6250000000000000)⟩,(994778975645965487/1000000000000000000),(49126832324186989/200000000000000000),(204711109537638569/500000000000000000),(180509063891093121/500000000000000000)⟩
theorem valid2564 : certificate2564.Valid := by decide +kernel
theorem sound2564 : certificate2564.Sound := rat_cut_bin_certificate_sound certificate2564 profilesValid2564 numericValid2564 valid2564

def retention2565 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(921674091206567042/24973922070982979467),(912548605155016873/1000000000000000000),(27/10),(21485242420080042081/10240000000000000000),true,MergedCutProfiles.Batch399.profile15995,![MergedCutProfiles.Batch399.profile15995,MergedCutProfiles.Batch399.profile15996,MergedCutProfiles.Batch399.profile15997,MergedCutProfiles.Batch399.profile15998,MergedCutProfiles.Batch399.profile15999,MergedCutProfiles.Batch400.profile16000,MergedCutProfiles.Batch400.profile16001,MergedCutProfiles.Batch400.profile16002,MergedCutProfiles.Batch400.profile16003,MergedCutProfiles.Batch400.profile16004,MergedCutProfiles.Batch400.profile16005,MergedCutProfiles.Batch400.profile16006,MergedCutProfiles.Batch400.profile16007,MergedCutProfiles.Batch400.profile16008,MergedCutProfiles.Batch400.profile16009,MergedCutProfiles.Batch400.profile16010]⟩
theorem profilesValid2565 : retention2565.ProfilesValid := by
  change ∀ j : Fin 16, (retention2565.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch399.valid15995
  · exact MergedCutProfiles.Batch399.valid15996
  · exact MergedCutProfiles.Batch399.valid15997
  · exact MergedCutProfiles.Batch399.valid15998
  · exact MergedCutProfiles.Batch399.valid15999
  · exact MergedCutProfiles.Batch400.valid16000
  · exact MergedCutProfiles.Batch400.valid16001
  · exact MergedCutProfiles.Batch400.valid16002
  · exact MergedCutProfiles.Batch400.valid16003
  · exact MergedCutProfiles.Batch400.valid16004
  · exact MergedCutProfiles.Batch400.valid16005
  · exact MergedCutProfiles.Batch400.valid16006
  · exact MergedCutProfiles.Batch400.valid16007
  · exact MergedCutProfiles.Batch400.valid16008
  · exact MergedCutProfiles.Batch400.valid16009
  · exact MergedCutProfiles.Batch400.valid16010
theorem numericValid2565 : retention2565.NumericValid := by decide +kernel
def certificate2565 : RatCutBinCertificate := ⟨⟨retention2565,(2277826033255611433/1000000000000000000),(182428996879551849/1000000000000000000),(15722171334757975717/1000000000000000000),(393845047766373384873/1000000000000000000),(126674563213693897/62500000000000000)⟩,(124405732897495927/125000000000000000),(307422470667726091/1000000000000000000),(8248598254823353/25000000000000000),(188759714996628979/1000000000000000000)⟩
theorem valid2565 : certificate2565.Valid := by decide +kernel
theorem sound2565 : certificate2565.Sound := rat_cut_bin_certificate_sound certificate2565 profilesValid2565 numericValid2565 valid2565

def retention2566 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(23959756000000000/609120050511779987),(460837045603283521/500000000000000000),(27/10),(83787161991082590399/40000000000000000000),true,MergedCutProfiles.Batch400.profile16011,![MergedCutProfiles.Batch400.profile16011,MergedCutProfiles.Batch400.profile16012,MergedCutProfiles.Batch400.profile16013,MergedCutProfiles.Batch400.profile16014,MergedCutProfiles.Batch400.profile16015,MergedCutProfiles.Batch400.profile16016,MergedCutProfiles.Batch400.profile16017,MergedCutProfiles.Batch400.profile16018,MergedCutProfiles.Batch400.profile16019,MergedCutProfiles.Batch400.profile16020,MergedCutProfiles.Batch400.profile16021,MergedCutProfiles.Batch400.profile16022,MergedCutProfiles.Batch400.profile16023,MergedCutProfiles.Batch400.profile16024,MergedCutProfiles.Batch400.profile16010,MergedCutProfiles.Batch400.profile16025]⟩
theorem profilesValid2566 : retention2566.ProfilesValid := by
  change ∀ j : Fin 16, (retention2566.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch400.valid16011
  · exact MergedCutProfiles.Batch400.valid16012
  · exact MergedCutProfiles.Batch400.valid16013
  · exact MergedCutProfiles.Batch400.valid16014
  · exact MergedCutProfiles.Batch400.valid16015
  · exact MergedCutProfiles.Batch400.valid16016
  · exact MergedCutProfiles.Batch400.valid16017
  · exact MergedCutProfiles.Batch400.valid16018
  · exact MergedCutProfiles.Batch400.valid16019
  · exact MergedCutProfiles.Batch400.valid16020
  · exact MergedCutProfiles.Batch400.valid16021
  · exact MergedCutProfiles.Batch400.valid16022
  · exact MergedCutProfiles.Batch400.valid16023
  · exact MergedCutProfiles.Batch400.valid16024
  · exact MergedCutProfiles.Batch400.valid16010
  · exact MergedCutProfiles.Batch400.valid16025
theorem numericValid2566 : retention2566.NumericValid := by decide +kernel
def certificate2566 : RatCutBinCertificate := ⟨⟨retention2566,(2277826033255611433/1000000000000000000),(182428996879551849/1000000000000000000),(15722171334757975717/1000000000000000000),(393845047766373384873/1000000000000000000),(2023303988939254909/1000000000000000000)⟩,(124405732897495927/125000000000000000),(153354919512383139/500000000000000000),(8269624080840751/25000000000000000),(1515437990730819/8000000000000000)⟩
theorem valid2566 : certificate2566.Valid := by decide +kernel
theorem sound2566 : certificate2566.Sound := rat_cut_bin_certificate_sound certificate2566 profilesValid2566 numericValid2566 valid2566

def retention2567 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(1070035006859680902/24973922070982979467),(245587499/250000000),(51/20),(2076604913491487991/1000000000000000000),true,MergedCutProfiles.Batch400.profile16026,![MergedCutProfiles.Batch400.profile16026,MergedCutProfiles.Batch400.profile16027,MergedCutProfiles.Batch400.profile16028,MergedCutProfiles.Batch400.profile16029,MergedCutProfiles.Batch400.profile16030,MergedCutProfiles.Batch400.profile16031,MergedCutProfiles.Batch400.profile16032,MergedCutProfiles.Batch400.profile16033,MergedCutProfiles.Batch400.profile16034,MergedCutProfiles.Batch400.profile16035,MergedCutProfiles.Batch400.profile16022,MergedCutProfiles.Batch400.profile16036,MergedCutProfiles.Batch400.profile16037,MergedCutProfiles.Batch400.profile16038,MergedCutProfiles.Batch400.profile16039,MergedCutProfiles.Batch401.profile16040]⟩
theorem profilesValid2567 : retention2567.ProfilesValid := by
  change ∀ j : Fin 16, (retention2567.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch400.valid16026
  · exact MergedCutProfiles.Batch400.valid16027
  · exact MergedCutProfiles.Batch400.valid16028
  · exact MergedCutProfiles.Batch400.valid16029
  · exact MergedCutProfiles.Batch400.valid16030
  · exact MergedCutProfiles.Batch400.valid16031
  · exact MergedCutProfiles.Batch400.valid16032
  · exact MergedCutProfiles.Batch400.valid16033
  · exact MergedCutProfiles.Batch400.valid16034
  · exact MergedCutProfiles.Batch400.valid16035
  · exact MergedCutProfiles.Batch400.valid16022
  · exact MergedCutProfiles.Batch400.valid16036
  · exact MergedCutProfiles.Batch400.valid16037
  · exact MergedCutProfiles.Batch400.valid16038
  · exact MergedCutProfiles.Batch400.valid16039
  · exact MergedCutProfiles.Batch401.valid16040
theorem numericValid2567 : retention2567.NumericValid := by decide +kernel
def certificate2567 : RatCutBinCertificate := ⟨⟨retention2567,(2277826033255611433/1000000000000000000),(182428996879551849/1000000000000000000),(15722171334757975717/1000000000000000000),(393845047766373384873/1000000000000000000),(2009195216305078329/1000000000000000000)⟩,(124405732897495927/125000000000000000),(150566832516137477/500000000000000000),(337423075255689273/1000000000000000000),(50275456571406293/250000000000000000)⟩
theorem valid2567 : certificate2567.Valid := by decide +kernel
theorem sound2567 : certificate2567.Sound := rat_cut_bin_certificate_sound certificate2567 profilesValid2567 numericValid2567 valid2567

def certificates : List RatCutBinCertificate := [certificate2556,certificate2557,certificate2558,certificate2559,certificate2560,certificate2561,certificate2562,certificate2563,certificate2564,certificate2565,certificate2566,certificate2567]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2556,List.forall_mem_cons.mpr ⟨sound2557,List.forall_mem_cons.mpr ⟨sound2558,List.forall_mem_cons.mpr ⟨sound2559,List.forall_mem_cons.mpr ⟨sound2560,List.forall_mem_cons.mpr ⟨sound2561,List.forall_mem_cons.mpr ⟨sound2562,List.forall_mem_cons.mpr ⟨sound2563,List.forall_mem_cons.mpr ⟨sound2564,List.forall_mem_cons.mpr ⟨sound2565,List.forall_mem_cons.mpr ⟨sound2566,List.forall_mem_cons.mpr ⟨sound2567,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch213
