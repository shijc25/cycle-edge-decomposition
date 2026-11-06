import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch380
import Cycle12.MergedCutProfiles.Batch612
import Cycle12.MergedCutProfiles.Batch697
import Cycle12.MergedCutProfiles.Batch698

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch416

def retention4992 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(1/40),(42704581018056862051/1000000000000000000),(21/20),(151427816977055450961751422473071136567679/68327329628890979281600000000000000000000),false,MergedCutProfiles.Batch697.profile27908,(fun _ => MergedCutProfiles.Batch697.profile27908)⟩
theorem profilesValid4992 : retention4992.ProfilesValid := by
  exact MergedCutProfiles.Batch697.valid27908
theorem numericValid4992 : retention4992.NumericValid := by decide +kernel
def certificate4992 : RatCutBinCertificate := ⟨⟨retention4992,(1903256209298746579/1000000000000000000),(31307344283847009/250000000000000000),(3330687757480619411/250000000000000000),(48859186672234238561/2000000000000000),(549356769897472757/250000000000000000)⟩,(999931419600127907/1000000000000000000),(687015557223124533/1000000000000000000),(55079941750585121/1000000000000000000),(27530722795565993/250000000000000000)⟩
theorem valid4992 : certificate4992.Valid := by decide +kernel
theorem sound4992 : certificate4992.Sound := rat_cut_bin_certificate_sound certificate4992 profilesValid4992 numericValid4992 valid4992

def retention4993 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(161625103660680408/435902475717329878669),(75375326139114467/125000000000000000),4,(5517067629705686498484637035782792967/2412010436451662944000000000000000000),true,MergedCutProfiles.Batch697.profile27909,![MergedCutProfiles.Batch697.profile27909,MergedCutProfiles.Batch697.profile27910,MergedCutProfiles.Batch697.profile27911,MergedCutProfiles.Batch697.profile27912,MergedCutProfiles.Batch612.profile24496,MergedCutProfiles.Batch697.profile27913,MergedCutProfiles.Batch697.profile27914,MergedCutProfiles.Batch697.profile27915,MergedCutProfiles.Batch697.profile27916,MergedCutProfiles.Batch612.profile24497,MergedCutProfiles.Batch697.profile27917,MergedCutProfiles.Batch697.profile27918,MergedCutProfiles.Batch697.profile27919,MergedCutProfiles.Batch698.profile27920,MergedCutProfiles.Batch612.profile24498,MergedCutProfiles.Batch698.profile27921]⟩
theorem profilesValid4993 : retention4993.ProfilesValid := by
  change ∀ j : Fin 16, (retention4993.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch697.valid27909
  · exact MergedCutProfiles.Batch697.valid27910
  · exact MergedCutProfiles.Batch697.valid27911
  · exact MergedCutProfiles.Batch697.valid27912
  · exact MergedCutProfiles.Batch612.valid24496
  · exact MergedCutProfiles.Batch697.valid27913
  · exact MergedCutProfiles.Batch697.valid27914
  · exact MergedCutProfiles.Batch697.valid27915
  · exact MergedCutProfiles.Batch697.valid27916
  · exact MergedCutProfiles.Batch612.valid24497
  · exact MergedCutProfiles.Batch697.valid27917
  · exact MergedCutProfiles.Batch697.valid27918
  · exact MergedCutProfiles.Batch697.valid27919
  · exact MergedCutProfiles.Batch698.valid27920
  · exact MergedCutProfiles.Batch612.valid24498
  · exact MergedCutProfiles.Batch698.valid27921
theorem numericValid4993 : retention4993.NumericValid := by decide +kernel
def certificate4993 : RatCutBinCertificate := ⟨⟨retention4993,(962806368890364433/500000000000000000),(65444215677591123/500000000000000000),(3387039325050602467/250000000000000000),(11879850903099233585143/500000000000000000),(276614775738015641/125000000000000000)⟩,(999929103211402413/1000000000000000000),(139772745878022359/200000000000000000),(12683435303380523/250000000000000000),(22828839327131679/1000000000000000000)⟩
theorem valid4993 : certificate4993.Valid := by decide +kernel
theorem sound4993 : certificate4993.Sound := rat_cut_bin_certificate_sound certificate4993 profilesValid4993 numericValid4993 valid4993

def retention4994 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(272590906000000000/435902475717329878669),(20203137957585051/31250000000000000),4,(4704445668624096391/2000000000000000000),true,MergedCutProfiles.Batch698.profile27922,![MergedCutProfiles.Batch698.profile27922,MergedCutProfiles.Batch698.profile27923,MergedCutProfiles.Batch612.profile24496,MergedCutProfiles.Batch698.profile27924,MergedCutProfiles.Batch612.profile24511,MergedCutProfiles.Batch612.profile24497,MergedCutProfiles.Batch698.profile27925,MergedCutProfiles.Batch698.profile27920,MergedCutProfiles.Batch612.profile24498,MergedCutProfiles.Batch612.profile24512,MergedCutProfiles.Batch698.profile27926,MergedCutProfiles.Batch612.profile24499,MergedCutProfiles.Batch698.profile27927,MergedCutProfiles.Batch698.profile27928,MergedCutProfiles.Batch612.profile24513,MergedCutProfiles.Batch698.profile27929]⟩
theorem profilesValid4994 : retention4994.ProfilesValid := by
  change ∀ j : Fin 16, (retention4994.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch698.valid27922
  · exact MergedCutProfiles.Batch698.valid27923
  · exact MergedCutProfiles.Batch612.valid24496
  · exact MergedCutProfiles.Batch698.valid27924
  · exact MergedCutProfiles.Batch612.valid24511
  · exact MergedCutProfiles.Batch612.valid24497
  · exact MergedCutProfiles.Batch698.valid27925
  · exact MergedCutProfiles.Batch698.valid27920
  · exact MergedCutProfiles.Batch612.valid24498
  · exact MergedCutProfiles.Batch612.valid24512
  · exact MergedCutProfiles.Batch698.valid27926
  · exact MergedCutProfiles.Batch612.valid24499
  · exact MergedCutProfiles.Batch698.valid27927
  · exact MergedCutProfiles.Batch698.valid27928
  · exact MergedCutProfiles.Batch612.valid24513
  · exact MergedCutProfiles.Batch698.valid27929
theorem numericValid4994 : retention4994.NumericValid := by decide +kernel
def certificate4994 : RatCutBinCertificate := ⟨⟨retention4994,(962806368890364433/500000000000000000),(65444215677591123/500000000000000000),(3387039325050602467/250000000000000000),(11879850903099233585143/500000000000000000),(284726184623856911/125000000000000000)⟩,(999929103211402413/1000000000000000000),(648888699590333977/1000000000000000000),(70470784203889159/1000000000000000000),(16442434190249601/500000000000000000)⟩
theorem valid4994 : certificate4994.Valid := by decide +kernel
theorem sound4994 : certificate4994.Sound := rat_cut_bin_certificate_sound certificate4994 profilesValid4994 numericValid4994 valid4994

def retention4995 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(1323450554087564917/1743609902869319514676),(136295453/125000000),(29/10),(10528796341442571077495098400669612959/4361454496000000000000000000000000000),true,MergedCutProfiles.Batch698.profile27930,![MergedCutProfiles.Batch698.profile27930,MergedCutProfiles.Batch697.profile27912,MergedCutProfiles.Batch697.profile27913,MergedCutProfiles.Batch612.profile24511,MergedCutProfiles.Batch612.profile24497,MergedCutProfiles.Batch697.profile27918,MergedCutProfiles.Batch698.profile27931,MergedCutProfiles.Batch698.profile27921,MergedCutProfiles.Batch698.profile27926,MergedCutProfiles.Batch612.profile24499,MergedCutProfiles.Batch698.profile27927,MergedCutProfiles.Batch698.profile27932,MergedCutProfiles.Batch612.profile24500,MergedCutProfiles.Batch698.profile27933,MergedCutProfiles.Batch698.profile27934,MergedCutProfiles.Batch698.profile27935]⟩
theorem profilesValid4995 : retention4995.ProfilesValid := by
  change ∀ j : Fin 16, (retention4995.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch698.valid27930
  · exact MergedCutProfiles.Batch697.valid27912
  · exact MergedCutProfiles.Batch697.valid27913
  · exact MergedCutProfiles.Batch612.valid24511
  · exact MergedCutProfiles.Batch612.valid24497
  · exact MergedCutProfiles.Batch697.valid27918
  · exact MergedCutProfiles.Batch698.valid27931
  · exact MergedCutProfiles.Batch698.valid27921
  · exact MergedCutProfiles.Batch698.valid27926
  · exact MergedCutProfiles.Batch612.valid24499
  · exact MergedCutProfiles.Batch698.valid27927
  · exact MergedCutProfiles.Batch698.valid27932
  · exact MergedCutProfiles.Batch612.valid24500
  · exact MergedCutProfiles.Batch698.valid27933
  · exact MergedCutProfiles.Batch698.valid27934
  · exact MergedCutProfiles.Batch698.valid27935
theorem numericValid4995 : retention4995.NumericValid := by decide +kernel
def certificate4995 : RatCutBinCertificate := ⟨⟨retention4995,(962806368890364433/500000000000000000),(65444215677591123/500000000000000000),(3387039325050602467/250000000000000000),(11879850903099233585143/500000000000000000),(2360106553927455141/1000000000000000000)⟩,(999929103211402413/1000000000000000000),(115627760589089911/250000000000000000),(5651672399845497/31250000000000000),(117046973665057563/1000000000000000000)⟩
theorem valid4995 : certificate4995.Valid := by decide +kernel
theorem sound4995 : certificate4995.Sound := rat_cut_bin_certificate_sound certificate4995 profilesValid4995 numericValid4995 valid4995

def retention4996 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(15873113812920345637/435902475717329878669),(1323450554087564917/1000000000000000000),(5/2),(45593626178223716812323881600341557511/21175208865401038672000000000000000000),false,MergedCutProfiles.Batch698.profile27936,(fun _ => MergedCutProfiles.Batch698.profile27936)⟩
theorem profilesValid4996 : retention4996.ProfilesValid := by
  exact MergedCutProfiles.Batch698.valid27936
theorem numericValid4996 : retention4996.NumericValid := by decide +kernel
def certificate4996 : RatCutBinCertificate := ⟨⟨retention4996,(962806368890364433/500000000000000000),(65444215677591123/500000000000000000),(3387039325050602467/250000000000000000),(11879850903099233585143/500000000000000000),(2106652308848218387/1000000000000000000)⟩,(999929103211402413/1000000000000000000),(235548176476266237/500000000000000000),(34862550716463229/200000000000000000),(117060718258180349/1000000000000000000)⟩
theorem valid4996 : certificate4996.Valid := by decide +kernel
theorem sound4996 : certificate4996.Sound := rat_cut_bin_certificate_sound certificate4996 profilesValid4996 numericValid4996 valid4996

def retention4997 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(16000000000000000000/435902475717329878669),(15873113812920345637/250000000000000000),1,(108655701556702585669257256989244811139/50793964201345106038400000000000000000),false,MergedCutProfiles.Batch698.profile27937,(fun _ => MergedCutProfiles.Batch698.profile27937)⟩
theorem profilesValid4997 : retention4997.ProfilesValid := by
  exact MergedCutProfiles.Batch698.valid27937
theorem numericValid4997 : retention4997.NumericValid := by decide +kernel
def certificate4997 : RatCutBinCertificate := ⟨⟨retention4997,(962806368890364433/500000000000000000),(65444215677591123/500000000000000000),(3387039325050602467/250000000000000000),(11879850903099233585143/500000000000000000),(1060271312047428069/500000000000000000)⟩,(999929103211402413/1000000000000000000),(126933897374990521/500000000000000000),(398017376293957293/1000000000000000000),(408338357355272311/500000000000000000)⟩
theorem valid4997 : certificate4997.Valid := by decide +kernel
theorem sound4997 : certificate4997.Sound := rat_cut_bin_certificate_sound certificate4997 profilesValid4997 numericValid4997 valid4997

def retention4998 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(1/2),64,1,(63848938712576751324224913430591766799/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch380.profile15211,(fun _ => MergedCutProfiles.Batch380.profile15211)⟩
theorem profilesValid4998 : retention4998.ProfilesValid := by
  exact MergedCutProfiles.Batch380.valid15211
theorem numericValid4998 : retention4998.NumericValid := by decide +kernel
def certificate4998 : RatCutBinCertificate := ⟨⟨retention4998,(962806368890364433/500000000000000000),(65444215677591123/500000000000000000),(3387039325050602467/250000000000000000),(11879850903099233585143/500000000000000000),(97903636608218411/100000000000000000)⟩,(999929103211402413/1000000000000000000),(274893168730046643/500000000000000000),(6065870928968729/50000000000000000),(58488109919808779/500000000000000000)⟩
theorem valid4998 : certificate4998.Valid := by decide +kernel
theorem sound4998 : certificate4998.Sound := rat_cut_bin_certificate_sound certificate4998 profilesValid4998 numericValid4998 valid4998

def retention4999 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(16000000000000000000/435902475717329878669),(38121104132082364829/1000000000000000000),1,(324326420291570368051545726786635219763/152484416528329459316000000000000000000),false,MergedCutProfiles.Batch698.profile27937,(fun _ => MergedCutProfiles.Batch698.profile27937)⟩
theorem profilesValid4999 : retention4999.ProfilesValid := by
  exact MergedCutProfiles.Batch698.valid27937
theorem numericValid4999 : retention4999.NumericValid := by decide +kernel
def certificate4999 : RatCutBinCertificate := ⟨⟨retention4999,(869373182890364433/500000000000000000),(65444215677591123/500000000000000000),(3387039325050602467/250000000000000000),(11879850903099233585143/500000000000000000),(65942186880774529/31250000000000000)⟩,(199987196655933091/200000000000000000),(4488574341204333/250000000000000000),(880243737331978499/1000000000000000000),(1759907537312795491/1000000000000000000)⟩
theorem valid4999 : certificate4999.Valid := by decide +kernel
theorem sound4999 : certificate4999.Sound := rat_cut_bin_certificate_sound certificate4999 profilesValid4999 numericValid4999 valid4999

def retention5000 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(1/2),64,1,(63848938712576751324224913430591766799/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch380.profile15211,(fun _ => MergedCutProfiles.Batch380.profile15211)⟩
theorem profilesValid5000 : retention5000.ProfilesValid := by
  exact MergedCutProfiles.Batch380.valid15211
theorem numericValid5000 : retention5000.NumericValid := by decide +kernel
def certificate5000 : RatCutBinCertificate := ⟨⟨retention5000,(869373182890364433/500000000000000000),(65444215677591123/500000000000000000),(3387039325050602467/250000000000000000),(11879850903099233585143/500000000000000000),(980841677894517613/1000000000000000000)⟩,(199987196655933091/200000000000000000),(1207071088868541/31250000000000000),(819589421604063917/1000000000000000000),(395851031363521947/500000000000000000)⟩
theorem valid5000 : certificate5000.Valid := by decide +kernel
theorem sound5000 : certificate5000.Sound := rat_cut_bin_certificate_sound certificate5000 profilesValid5000 numericValid5000 valid5000

def retention5001 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(726422510769800999/1743609902869319514676),(359615104341485643/500000000000000000),4,(13950590399076385126659024345724483/5753841669463770288000000000000000),false,MergedCutProfiles.Batch698.profile27938,(fun _ => MergedCutProfiles.Batch698.profile27938)⟩
theorem profilesValid5001 : retention5001.ProfilesValid := by
  exact MergedCutProfiles.Batch698.valid27938
theorem numericValid5001 : retention5001.NumericValid := by decide +kernel
def certificate5001 : RatCutBinCertificate := ⟨⟨retention5001,(954973606390364433/500000000000000000),(65444215677591123/500000000000000000),(3387039325050602467/250000000000000000),(11879850903099233585143/500000000000000000),(470152355339929463/200000000000000000)⟩,(499964839993540811/500000000000000000),(827844031273964081/1000000000000000000),(3937743348297701/250000000000000000),(480366744229057/62500000000000000)⟩
theorem valid5001 : certificate5001.Valid := by decide +kernel
theorem sound5001 : certificate5001.Sound := rat_cut_bin_certificate_sound certificate5001 profilesValid5001 numericValid5001 valid5001

def retention5002 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(877597537064659259/1743609902869319514676),(726422510769800999/1000000000000000000),4,(19638817668839600647827007107370473/8093844131139844000000000000000000),false,MergedCutProfiles.Batch698.profile27939,(fun _ => MergedCutProfiles.Batch698.profile27939)⟩
theorem profilesValid5002 : retention5002.ProfilesValid := by
  exact MergedCutProfiles.Batch698.valid27939
theorem numericValid5002 : retention5002.NumericValid := by decide +kernel
def certificate5002 : RatCutBinCertificate := ⟨⟨retention5002,(954973606390364433/500000000000000000),(65444215677591123/500000000000000000),(3387039325050602467/250000000000000000),(11879850903099233585143/500000000000000000),(2352581446233358117/1000000000000000000)⟩,(499964839993540811/500000000000000000),(206328755621748433/250000000000000000),(4058161807773667/250000000000000000),(1984835056591497/250000000000000000)⟩
theorem valid5002 : certificate5002.Valid := by decide +kernel
theorem sound5002 : certificate5002.Sound := rat_cut_bin_certificate_sound certificate5002 profilesValid5002 numericValid5002 valid5002

def retention5003 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(3569514077661618261/1743609902869319514676),(877597537064659259/1000000000000000000),(73/20),(3386016607275223733433965155741613160991/1404156059303454814400000000000000000000),false,MergedCutProfiles.Batch698.profile27940,(fun _ => MergedCutProfiles.Batch698.profile27940)⟩
theorem profilesValid5003 : retention5003.ProfilesValid := by
  exact MergedCutProfiles.Batch698.valid27940
theorem numericValid5003 : retention5003.NumericValid := by decide +kernel
def certificate5003 : RatCutBinCertificate := ⟨⟨retention5003,(954973606390364433/500000000000000000),(65444215677591123/500000000000000000),(3387039325050602467/250000000000000000),(11879850903099233585143/500000000000000000),(1172037474573665741/500000000000000000)⟩,(499964839993540811/500000000000000000),(24864293283338979/31250000000000000),(22465993291810987/1000000000000000000),(375543461058767/31250000000000000)⟩
theorem valid5003 : certificate5003.Valid := by decide +kernel
theorem sound5003 : certificate5003.Sound := rat_cut_bin_certificate_sound certificate5003 profilesValid5003 numericValid5003 valid5003

def certificates : List RatCutBinCertificate := [certificate4992,certificate4993,certificate4994,certificate4995,certificate4996,certificate4997,certificate4998,certificate4999,certificate5000,certificate5001,certificate5002,certificate5003]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4992,List.forall_mem_cons.mpr ⟨sound4993,List.forall_mem_cons.mpr ⟨sound4994,List.forall_mem_cons.mpr ⟨sound4995,List.forall_mem_cons.mpr ⟨sound4996,List.forall_mem_cons.mpr ⟨sound4997,List.forall_mem_cons.mpr ⟨sound4998,List.forall_mem_cons.mpr ⟨sound4999,List.forall_mem_cons.mpr ⟨sound5000,List.forall_mem_cons.mpr ⟨sound5001,List.forall_mem_cons.mpr ⟨sound5002,List.forall_mem_cons.mpr ⟨sound5003,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch416
