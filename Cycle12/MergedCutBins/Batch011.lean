import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch022
import Cycle12.MergedCutProfiles.Batch023
import Cycle12.MergedCutProfiles.Batch024

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch011

def retention132 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(997363062522567069/155280714373951182740),(650180900073611281/1000000000000000000),4,(36329454625914830329/16000000000000000000),true,MergedCutProfiles.Batch022.profile905,![MergedCutProfiles.Batch022.profile905,MergedCutProfiles.Batch022.profile906,MergedCutProfiles.Batch022.profile907,MergedCutProfiles.Batch022.profile908,MergedCutProfiles.Batch022.profile909,MergedCutProfiles.Batch022.profile910,MergedCutProfiles.Batch022.profile911,MergedCutProfiles.Batch022.profile912,MergedCutProfiles.Batch022.profile902,MergedCutProfiles.Batch022.profile913,MergedCutProfiles.Batch022.profile914,MergedCutProfiles.Batch022.profile915,MergedCutProfiles.Batch022.profile916,MergedCutProfiles.Batch022.profile917,MergedCutProfiles.Batch022.profile918,MergedCutProfiles.Batch022.profile919]⟩
theorem profilesValid132 : retention132.ProfilesValid := by
  change ∀ j : Fin 16, (retention132.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch022.valid905
  · exact MergedCutProfiles.Batch022.valid906
  · exact MergedCutProfiles.Batch022.valid907
  · exact MergedCutProfiles.Batch022.valid908
  · exact MergedCutProfiles.Batch022.valid909
  · exact MergedCutProfiles.Batch022.valid910
  · exact MergedCutProfiles.Batch022.valid911
  · exact MergedCutProfiles.Batch022.valid912
  · exact MergedCutProfiles.Batch022.valid902
  · exact MergedCutProfiles.Batch022.valid913
  · exact MergedCutProfiles.Batch022.valid914
  · exact MergedCutProfiles.Batch022.valid915
  · exact MergedCutProfiles.Batch022.valid916
  · exact MergedCutProfiles.Batch022.valid917
  · exact MergedCutProfiles.Batch022.valid918
  · exact MergedCutProfiles.Batch022.valid919
theorem numericValid132 : retention132.NumericValid := by decide +kernel
def certificate132 : RatCutBinCertificate := ⟨⟨retention132,(958950628382366181/500000000000000000),(15120529320228081/1000000000000000000),(4162624447707471869/500000000000000000),(649440413585474310029/500000000000000000),(451331497418407537/200000000000000000)⟩,(499271678933108497/500000000000000000),(30592013126108451/62500000000000000),(160835264717106081/1000000000000000000),(74435881031437059/1000000000000000000)⟩
theorem valid132 : certificate132.Valid := by decide +kernel
theorem sound132 : certificate132.Sound := rat_cut_bin_certificate_sound certificate132 profilesValid132 numericValid132 valid132

def retention133 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(59528357450000000/7764035718697559137),(997363062522567069/1000000000000000000),(57/20),(2886963402387395004901/1280000000000000000000),true,MergedCutProfiles.Batch023.profile920,![MergedCutProfiles.Batch023.profile920,MergedCutProfiles.Batch023.profile921,MergedCutProfiles.Batch023.profile922,MergedCutProfiles.Batch023.profile923,MergedCutProfiles.Batch022.profile910,MergedCutProfiles.Batch022.profile899,MergedCutProfiles.Batch023.profile924,MergedCutProfiles.Batch023.profile925,MergedCutProfiles.Batch023.profile926,MergedCutProfiles.Batch023.profile927,MergedCutProfiles.Batch023.profile928,MergedCutProfiles.Batch023.profile929,MergedCutProfiles.Batch023.profile930,MergedCutProfiles.Batch023.profile931,MergedCutProfiles.Batch023.profile932,MergedCutProfiles.Batch023.profile933]⟩
theorem profilesValid133 : retention133.ProfilesValid := by
  change ∀ j : Fin 16, (retention133.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch023.valid920
  · exact MergedCutProfiles.Batch023.valid921
  · exact MergedCutProfiles.Batch023.valid922
  · exact MergedCutProfiles.Batch023.valid923
  · exact MergedCutProfiles.Batch022.valid910
  · exact MergedCutProfiles.Batch022.valid899
  · exact MergedCutProfiles.Batch023.valid924
  · exact MergedCutProfiles.Batch023.valid925
  · exact MergedCutProfiles.Batch023.valid926
  · exact MergedCutProfiles.Batch023.valid927
  · exact MergedCutProfiles.Batch023.valid928
  · exact MergedCutProfiles.Batch023.valid929
  · exact MergedCutProfiles.Batch023.valid930
  · exact MergedCutProfiles.Batch023.valid931
  · exact MergedCutProfiles.Batch023.valid932
  · exact MergedCutProfiles.Batch023.valid933
theorem numericValid133 : retention133.NumericValid := by decide +kernel
def certificate133 : RatCutBinCertificate := ⟨⟨retention133,(958950628382366181/500000000000000000),(15120529320228081/1000000000000000000),(4162624447707471869/500000000000000000),(649440413585474310029/500000000000000000),(224551259513744501/100000000000000000)⟩,(499271678933108497/500000000000000000),(48654776818452847/125000000000000000),(1947910879661701/8000000000000000),(14995765164398757/100000000000000000)⟩
theorem valid133 : certificate133.Valid := by decide +kernel
theorem sound133 : certificate133.Sound := rat_cut_bin_certificate_sound certificate133 profilesValid133 numericValid133 valid133

def retention134 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(812027242849645051/77640357186975591370),(1190567149/1000000000),(49/20),(35544969811879939163/16000000000000000000),true,MergedCutProfiles.Batch023.profile934,![MergedCutProfiles.Batch023.profile934,MergedCutProfiles.Batch022.profile893,MergedCutProfiles.Batch023.profile935,MergedCutProfiles.Batch022.profile898,MergedCutProfiles.Batch023.profile936,MergedCutProfiles.Batch022.profile903,MergedCutProfiles.Batch023.profile937,MergedCutProfiles.Batch023.profile928,MergedCutProfiles.Batch023.profile938,MergedCutProfiles.Batch023.profile939,MergedCutProfiles.Batch023.profile932,MergedCutProfiles.Batch023.profile940,MergedCutProfiles.Batch023.profile941,MergedCutProfiles.Batch023.profile942,MergedCutProfiles.Batch023.profile943,MergedCutProfiles.Batch023.profile944]⟩
theorem profilesValid134 : retention134.ProfilesValid := by
  change ∀ j : Fin 16, (retention134.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch023.valid934
  · exact MergedCutProfiles.Batch022.valid893
  · exact MergedCutProfiles.Batch023.valid935
  · exact MergedCutProfiles.Batch022.valid898
  · exact MergedCutProfiles.Batch023.valid936
  · exact MergedCutProfiles.Batch022.valid903
  · exact MergedCutProfiles.Batch023.valid937
  · exact MergedCutProfiles.Batch023.valid928
  · exact MergedCutProfiles.Batch023.valid938
  · exact MergedCutProfiles.Batch023.valid939
  · exact MergedCutProfiles.Batch023.valid932
  · exact MergedCutProfiles.Batch023.valid940
  · exact MergedCutProfiles.Batch023.valid941
  · exact MergedCutProfiles.Batch023.valid942
  · exact MergedCutProfiles.Batch023.valid943
  · exact MergedCutProfiles.Batch023.valid944
theorem numericValid134 : retention134.NumericValid := by decide +kernel
def certificate134 : RatCutBinCertificate := ⟨⟨retention134,(958950628382366181/500000000000000000),(15120529320228081/1000000000000000000),(4162624447707471869/500000000000000000),(649440413585474310029/500000000000000000),(2213026393328642171/1000000000000000000)⟩,(499271678933108497/500000000000000000),(363294049960050623/1000000000000000000),(67212807609392917/250000000000000000),(185117845956541203/1000000000000000000)⟩
theorem valid134 : certificate134.Valid := by decide +kernel
theorem sound134 : certificate134.Sound := rat_cut_bin_certificate_sound certificate134 profilesValid134 numericValid134 valid134

def retention135 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(7694866234740261223/77640357186975591370),(812027242849645051/500000000000000000),(41/20),(1230891872569088074796518190409756123439/649621794279716040800000000000000000000),false,MergedCutProfiles.Batch023.profile945,(fun _ => MergedCutProfiles.Batch023.profile945)⟩
theorem profilesValid135 : retention135.ProfilesValid := by
  exact MergedCutProfiles.Batch023.valid945
theorem numericValid135 : retention135.NumericValid := by decide +kernel
def certificate135 : RatCutBinCertificate := ⟨⟨retention135,(958950628382366181/500000000000000000),(15120529320228081/1000000000000000000),(4162624447707471869/500000000000000000),(649440413585474310029/500000000000000000),(943820709029899913/500000000000000000)⟩,(499271678933108497/500000000000000000),(74955417077018813/200000000000000000),(51480977935183891/200000000000000000),(185363162609409223/1000000000000000000)⟩
theorem valid135 : certificate135.Valid := by decide +kernel
theorem sound135 : certificate135.Sound := rat_cut_bin_certificate_sound certificate135 profilesValid135 numericValid135 valid135

def retention136 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(3200000000000000000/7764035718697559137),(7694866234740261223/500000000000000000),1,(71190481552543739504906622044479526439/61558929877922089784000000000000000000),false,MergedCutProfiles.Batch023.profile946,(fun _ => MergedCutProfiles.Batch023.profile946)⟩
theorem profilesValid136 : retention136.ProfilesValid := by
  exact MergedCutProfiles.Batch023.valid946
theorem numericValid136 : retention136.NumericValid := by decide +kernel
def certificate136 : RatCutBinCertificate := ⟨⟨retention136,(958950628382366181/500000000000000000),(15120529320228081/1000000000000000000),(4162624447707471869/500000000000000000),(649440413585474310029/500000000000000000),(288244332611771527/250000000000000000)⟩,(499271678933108497/500000000000000000),(407894137814323561/1000000000000000000),(353635491290811/1562500000000000),(242397081674589077/1000000000000000000)⟩
theorem valid136 : certificate136.Valid := by decide +kernel
theorem sound136 : certificate136.Sound := rat_cut_bin_certificate_sound certificate136 profilesValid136 numericValid136 valid136

def retention137 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(1/2),64,1,(255370911039032911357452645744173379951/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch023.profile947,(fun _ => MergedCutProfiles.Batch023.profile947)⟩
theorem profilesValid137 : retention137.ProfilesValid := by
  exact MergedCutProfiles.Batch023.valid947
theorem numericValid137 : retention137.NumericValid := by decide +kernel
def certificate137 : RatCutBinCertificate := ⟨⟨retention137,(958950628382366181/500000000000000000),(15120529320228081/1000000000000000000),(4162624447707471869/500000000000000000),(649440413585474310029/500000000000000000),(15532176241369237/15625000000000000)⟩,(499271678933108497/500000000000000000),(451725339214758421/1000000000000000000),(23662109969819757/125000000000000000),(92511080357364559/500000000000000000)⟩
theorem valid137 : certificate137.Valid := by decide +kernel
theorem sound137 : certificate137.Sound := rat_cut_bin_certificate_sound certificate137 profilesValid137 numericValid137 valid137

def retention138 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(15652840548789310693/38820178593487795685),(692091280134315691/200000000000000000),(13/10),(66192500316084163400069288242960154671/55367302410745255280000000000000000000),false,MergedCutProfiles.Batch023.profile948,(fun _ => MergedCutProfiles.Batch023.profile948)⟩
theorem profilesValid138 : retention138.ProfilesValid := by
  exact MergedCutProfiles.Batch023.valid948
theorem numericValid138 : retention138.NumericValid := by decide +kernel
def certificate138 : RatCutBinCertificate := ⟨⟨retention138,(1143405267882366181/500000000000000000),(15120529320228081/1000000000000000000),(4162624447707471869/500000000000000000),(649440413585474310029/500000000000000000),(148764586617754297/125000000000000000)⟩,(998263165342690911/1000000000000000000),(169108515803125267/500000000000000000),(5902495705700777/20000000000000000),(44814357908972867/200000000000000000)⟩
theorem valid138 : certificate138.Valid := by decide +kernel
theorem sound138 : certificate138.Sound := rat_cut_bin_certificate_sound certificate138 profilesValid138 numericValid138 valid138

def retention139 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(3200000000000000000/7764035718697559137),(15652840548789310693/250000000000000000),1,(293895804955091392211720977153502497167/250445448780628971088000000000000000000),false,MergedCutProfiles.Batch023.profile946,(fun _ => MergedCutProfiles.Batch023.profile946)⟩
theorem profilesValid139 : retention139.ProfilesValid := by
  exact MergedCutProfiles.Batch023.valid946
theorem numericValid139 : retention139.NumericValid := by decide +kernel
def certificate139 : RatCutBinCertificate := ⟨⟨retention139,(1143405267882366181/500000000000000000),(15120529320228081/1000000000000000000),(4162624447707471869/500000000000000000),(649440413585474310029/500000000000000000),(1169338932593164091/1000000000000000000)⟩,(998263165342690911/1000000000000000000),(86056686374767743/250000000000000000),(72166046142762357/250000000000000000),(82694552341567443/250000000000000000)⟩
theorem valid139 : certificate139.Valid := by decide +kernel
theorem sound139 : certificate139.Sound := rat_cut_bin_certificate_sound certificate139 profilesValid139 numericValid139 valid139

def retention140 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(1/2),64,1,(255370911039032911357452645744173379951/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch023.profile947,(fun _ => MergedCutProfiles.Batch023.profile947)⟩
theorem profilesValid140 : retention140.ProfilesValid := by
  exact MergedCutProfiles.Batch023.valid947
theorem numericValid140 : retention140.NumericValid := by decide +kernel
def certificate140 : RatCutBinCertificate := ⟨⟨retention140,(1143405267882366181/500000000000000000),(15120529320228081/1000000000000000000),(4162624447707471869/500000000000000000),(649440413585474310029/500000000000000000),(99338925688682607/100000000000000000)⟩,(998263165342690911/1000000000000000000),(81039276871857709/200000000000000000),(28594346062779973/125000000000000000),(8935116314933817/40000000000000000)⟩
theorem valid140 : certificate140.Valid := by decide +kernel
theorem sound140 : certificate140.Sound := rat_cut_bin_certificate_sound certificate140 profilesValid140 numericValid140 valid140

def retention141 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(219229312086453050/46491869449741093531),(32558808725710849/50000000000000000),4,(4569542183781198853/2000000000000000000),true,MergedCutProfiles.Batch023.profile949,![MergedCutProfiles.Batch023.profile949,MergedCutProfiles.Batch023.profile950,MergedCutProfiles.Batch023.profile951,MergedCutProfiles.Batch023.profile952,MergedCutProfiles.Batch023.profile953,MergedCutProfiles.Batch023.profile954,MergedCutProfiles.Batch023.profile955,MergedCutProfiles.Batch023.profile956,MergedCutProfiles.Batch023.profile957,MergedCutProfiles.Batch023.profile958,MergedCutProfiles.Batch023.profile959,MergedCutProfiles.Batch024.profile960,MergedCutProfiles.Batch024.profile961,MergedCutProfiles.Batch024.profile962,MergedCutProfiles.Batch024.profile963,MergedCutProfiles.Batch024.profile964]⟩
theorem profilesValid141 : retention141.ProfilesValid := by
  change ∀ j : Fin 16, (retention141.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch023.valid949
  · exact MergedCutProfiles.Batch023.valid950
  · exact MergedCutProfiles.Batch023.valid951
  · exact MergedCutProfiles.Batch023.valid952
  · exact MergedCutProfiles.Batch023.valid953
  · exact MergedCutProfiles.Batch023.valid954
  · exact MergedCutProfiles.Batch023.valid955
  · exact MergedCutProfiles.Batch023.valid956
  · exact MergedCutProfiles.Batch023.valid957
  · exact MergedCutProfiles.Batch023.valid958
  · exact MergedCutProfiles.Batch023.valid959
  · exact MergedCutProfiles.Batch024.valid960
  · exact MergedCutProfiles.Batch024.valid961
  · exact MergedCutProfiles.Batch024.valid962
  · exact MergedCutProfiles.Batch024.valid963
  · exact MergedCutProfiles.Batch024.valid964
theorem numericValid141 : retention141.NumericValid := by decide +kernel
def certificate141 : RatCutBinCertificate := ⟨⟨retention141,(120338172838091963/62500000000000000),(16814618099358171/1000000000000000000),(4217227099650750953/500000000000000000),(1182011536263273450937/1000000000000000000),(2269417295306270463/1000000000000000000)⟩,(199679132671688709/200000000000000000),(483706928954708893/1000000000000000000),(32997642346262403/200000000000000000),(76720116961756727/1000000000000000000)⟩
theorem valid141 : certificate141.Valid := by decide +kernel
theorem sound141 : certificate141.Sound := rat_cut_bin_certificate_sound certificate141 profilesValid141 numericValid141 valid141

def retention142 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(316803120743368949/46491869449741093531),(13153758725187183/20000000000000000),4,(11643600432191862007/5120000000000000000),true,MergedCutProfiles.Batch024.profile965,![MergedCutProfiles.Batch024.profile965,MergedCutProfiles.Batch024.profile966,MergedCutProfiles.Batch024.profile967,MergedCutProfiles.Batch024.profile968,MergedCutProfiles.Batch024.profile969,MergedCutProfiles.Batch024.profile970,MergedCutProfiles.Batch023.profile958,MergedCutProfiles.Batch024.profile971,MergedCutProfiles.Batch024.profile961,MergedCutProfiles.Batch024.profile972,MergedCutProfiles.Batch024.profile964,MergedCutProfiles.Batch024.profile973,MergedCutProfiles.Batch024.profile974,MergedCutProfiles.Batch024.profile975,MergedCutProfiles.Batch024.profile976,MergedCutProfiles.Batch024.profile977]⟩
theorem profilesValid142 : retention142.ProfilesValid := by
  change ∀ j : Fin 16, (retention142.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch024.valid965
  · exact MergedCutProfiles.Batch024.valid966
  · exact MergedCutProfiles.Batch024.valid967
  · exact MergedCutProfiles.Batch024.valid968
  · exact MergedCutProfiles.Batch024.valid969
  · exact MergedCutProfiles.Batch024.valid970
  · exact MergedCutProfiles.Batch023.valid958
  · exact MergedCutProfiles.Batch024.valid971
  · exact MergedCutProfiles.Batch024.valid961
  · exact MergedCutProfiles.Batch024.valid972
  · exact MergedCutProfiles.Batch024.valid964
  · exact MergedCutProfiles.Batch024.valid973
  · exact MergedCutProfiles.Batch024.valid974
  · exact MergedCutProfiles.Batch024.valid975
  · exact MergedCutProfiles.Batch024.valid976
  · exact MergedCutProfiles.Batch024.valid977
theorem numericValid142 : retention142.NumericValid := by decide +kernel
def certificate142 : RatCutBinCertificate := ⟨⟨retention142,(120338172838091963/62500000000000000),(16814618099358171/1000000000000000000),(4217227099650750953/500000000000000000),(1182011536263273450937/1000000000000000000),(564696728414593719/250000000000000000)⟩,(199679132671688709/200000000000000000),(483122794438560943/1000000000000000000),(165412805670317381/1000000000000000000),(38378505033577483/500000000000000000)⟩
theorem valid142 : certificate142.Valid := by decide +kernel
theorem sound142 : certificate142.Sound := rat_cut_bin_certificate_sound certificate142 profilesValid142 numericValid142 valid142

def retention143 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(1177044509000000000/139475608349223280593),(950409362230106847/1000000000000000000),(59/20),(2881050307039720182671/1280000000000000000000),true,MergedCutProfiles.Batch024.profile978,![MergedCutProfiles.Batch024.profile978,MergedCutProfiles.Batch024.profile979,MergedCutProfiles.Batch024.profile980,MergedCutProfiles.Batch024.profile969,MergedCutProfiles.Batch023.profile957,MergedCutProfiles.Batch024.profile981,MergedCutProfiles.Batch024.profile982,MergedCutProfiles.Batch024.profile972,MergedCutProfiles.Batch024.profile983,MergedCutProfiles.Batch024.profile984,MergedCutProfiles.Batch024.profile985,MergedCutProfiles.Batch024.profile986,MergedCutProfiles.Batch024.profile977,MergedCutProfiles.Batch024.profile987,MergedCutProfiles.Batch024.profile988,MergedCutProfiles.Batch024.profile989]⟩
theorem profilesValid143 : retention143.ProfilesValid := by
  change ∀ j : Fin 16, (retention143.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch024.valid978
  · exact MergedCutProfiles.Batch024.valid979
  · exact MergedCutProfiles.Batch024.valid980
  · exact MergedCutProfiles.Batch024.valid969
  · exact MergedCutProfiles.Batch023.valid957
  · exact MergedCutProfiles.Batch024.valid981
  · exact MergedCutProfiles.Batch024.valid982
  · exact MergedCutProfiles.Batch024.valid972
  · exact MergedCutProfiles.Batch024.valid983
  · exact MergedCutProfiles.Batch024.valid984
  · exact MergedCutProfiles.Batch024.valid985
  · exact MergedCutProfiles.Batch024.valid986
  · exact MergedCutProfiles.Batch024.valid977
  · exact MergedCutProfiles.Batch024.valid987
  · exact MergedCutProfiles.Batch024.valid988
  · exact MergedCutProfiles.Batch024.valid989
theorem numericValid143 : retention143.NumericValid := by decide +kernel
def certificate143 : RatCutBinCertificate := ⟨⟨retention143,(120338172838091963/62500000000000000),(16814618099358171/1000000000000000000),(4217227099650750953/500000000000000000),(1182011536263273450937/1000000000000000000),(89579885271331089/40000000000000000)⟩,(199679132671688709/200000000000000000),(9960525512989779/25000000000000000),(234932222142643147/1000000000000000000),(140088607481149917/1000000000000000000)⟩
theorem valid143 : certificate143.Valid := by decide +kernel
theorem sound143 : certificate143.Sound := rat_cut_bin_certificate_sound certificate143 profilesValid143 numericValid143 valid143

def certificates : List RatCutBinCertificate := [certificate132,certificate133,certificate134,certificate135,certificate136,certificate137,certificate138,certificate139,certificate140,certificate141,certificate142,certificate143]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound132,List.forall_mem_cons.mpr ⟨sound133,List.forall_mem_cons.mpr ⟨sound134,List.forall_mem_cons.mpr ⟨sound135,List.forall_mem_cons.mpr ⟨sound136,List.forall_mem_cons.mpr ⟨sound137,List.forall_mem_cons.mpr ⟨sound138,List.forall_mem_cons.mpr ⟨sound139,List.forall_mem_cons.mpr ⟨sound140,List.forall_mem_cons.mpr ⟨sound141,List.forall_mem_cons.mpr ⟨sound142,List.forall_mem_cons.mpr ⟨sound143,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch011
