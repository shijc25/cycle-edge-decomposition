import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch718
import Cycle12.MergedCutProfiles.Batch719

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch432

def retention5184 : RatCutRetentionCertificate := ⟨(33/500),(67/1000),(1/2),64,1,(255418053332003062582561760940652564719/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch718.profile28723,(fun _ => MergedCutProfiles.Batch718.profile28723)⟩
theorem profilesValid5184 : retention5184.ProfilesValid := by
  exact MergedCutProfiles.Batch718.valid28723
theorem numericValid5184 : retention5184.NumericValid := by decide +kernel
def certificate5184 : RatCutBinCertificate := ⟨⟨retention5184,(211514256617338783/125000000000000000),(11895173549139047/50000000000000000),(17767111311624607767/1000000000000000000),(17137809829215648313311/1000000000000000000),(48753459125196151/50000000000000000)⟩,(499961952046509939/500000000000000000),(14731175197127073/500000000000000000),(422913484613458937/500000000000000000),(32492014749972177/40000000000000000)⟩
theorem valid5184 : certificate5184.Valid := by decide +kernel
theorem sound5184 : certificate5184.Sound := rat_cut_bin_certificate_sound certificate5184 profilesValid5184 numericValid5184 valid5184

def retention5185 : RatCutRetentionCertificate := ⟨(33/500),(67/1000),(789389664041259822/958430071261117944869),(195393481198331639/250000000000000000),(79/20),(12046247419279874536052804109483322219/4884837029958290975000000000000000000),false,MergedCutProfiles.Batch718.profile28724,(fun _ => MergedCutProfiles.Batch718.profile28724)⟩
theorem profilesValid5185 : retention5185.ProfilesValid := by
  exact MergedCutProfiles.Batch718.valid28724
theorem numericValid5185 : retention5185.NumericValid := by decide +kernel
def certificate5185 : RatCutBinCertificate := ⟨⟨retention5185,(254652143367338783/125000000000000000),(11895173549139047/50000000000000000),(17767111311624607767/1000000000000000000),(17137809829215648313311/1000000000000000000),(2358298232881432929/1000000000000000000)⟩,(49995419203507147/50000000000000000),(149856716368592923/200000000000000000),(8611222150004663/250000000000000000),(4307602785065581/250000000000000000)⟩
theorem valid5185 : certificate5185.Valid := by decide +kernel
theorem sound5185 : certificate5185.Sound := rat_cut_bin_certificate_sound certificate5185 profilesValid5185 numericValid5185 valid5185

def retention5186 : RatCutRetentionCertificate := ⟨(33/500),(67/1000),(889504031969158061/958430071261117944869),(394694832020629911/500000000000000000),(39/10),(24289750750905966552967231170263791153/9867370800515747775000000000000000000),false,MergedCutProfiles.Batch718.profile28725,(fun _ => MergedCutProfiles.Batch718.profile28725)⟩
theorem profilesValid5186 : retention5186.ProfilesValid := by
  exact MergedCutProfiles.Batch718.valid28725
theorem numericValid5186 : retention5186.NumericValid := by decide +kernel
def certificate5186 : RatCutBinCertificate := ⟨⟨retention5186,(254652143367338783/125000000000000000),(11895173549139047/50000000000000000),(17767111311624607767/1000000000000000000),(17137809829215648313311/1000000000000000000),(1177618282592692549/500000000000000000)⟩,(49995419203507147/50000000000000000),(74882999852252021/100000000000000000),(1383037887516323/40000000000000000),(4363609468069727/250000000000000000)⟩
theorem valid5186 : certificate5186.Valid := by decide +kernel
theorem sound5186 : certificate5186.Sound := rat_cut_bin_certificate_sound certificate5186 profilesValid5186 numericValid5186 valid5186

def retention5187 : RatCutRetentionCertificate := ⟨(33/500),(67/1000),(2335184384948074459/958430071261117944869),(889504031969158061/1000000000000000000),(71/20),(3460437495545483662656683724870856391199/1423206451150652897600000000000000000000),false,MergedCutProfiles.Batch718.profile28726,(fun _ => MergedCutProfiles.Batch718.profile28726)⟩
theorem profilesValid5187 : retention5187.ProfilesValid := by
  exact MergedCutProfiles.Batch718.valid28726
theorem numericValid5187 : retention5187.NumericValid := by decide +kernel
def certificate5187 : RatCutBinCertificate := ⟨⟨retention5187,(254652143367338783/125000000000000000),(11895173549139047/50000000000000000),(17767111311624607767/1000000000000000000),(17137809829215648313311/1000000000000000000),(2334598194435355071/1000000000000000000)⟩,(49995419203507147/50000000000000000),(73923994723740973/100000000000000000),(37411477555091159/1000000000000000000),(1018005118122363/50000000000000000)⟩
theorem valid5187 : certificate5187.Valid := by decide +kernel
theorem sound5187 : certificate5187.Sound := rat_cut_bin_certificate_sound certificate5187 profilesValid5187 numericValid5187 valid5187

def retention5188 : RatCutRetentionCertificate := ⟨(33/500),(67/1000),(21909389641369250206/958430071261117944869),(2335184384948074459/1000000000000000000),(19/10),(2106697816084308408844320946416698484039/934073753979229783600000000000000000000),false,MergedCutProfiles.Batch718.profile28727,(fun _ => MergedCutProfiles.Batch718.profile28727)⟩
theorem profilesValid5188 : retention5188.ProfilesValid := by
  exact MergedCutProfiles.Batch718.valid28727
theorem numericValid5188 : retention5188.NumericValid := by decide +kernel
def certificate5188 : RatCutBinCertificate := ⟨⟨retention5188,(254652143367338783/125000000000000000),(11895173549139047/50000000000000000),(17767111311624607767/1000000000000000000),(17137809829215648313311/1000000000000000000),(220355760858182577/100000000000000000)⟩,(49995419203507147/50000000000000000),(2797472616412501/4000000000000000),(3159574255349481/62500000000000000),(23237698842563839/500000000000000000)⟩
theorem valid5188 : certificate5188.Valid := by decide +kernel
theorem sound5188 : certificate5188.Sound := rat_cut_bin_certificate_sound certificate5188 profilesValid5188 numericValid5188 valid5188

def retention5189 : RatCutRetentionCertificate := ⟨(33/500),(67/1000),(1/40),(10954694820684625103/500000000000000000),(21/20),(19544590473824202315024378431983418135511/8763755856547700082400000000000000000000),false,MergedCutProfiles.Batch718.profile28728,(fun _ => MergedCutProfiles.Batch718.profile28728)⟩
theorem profilesValid5189 : retention5189.ProfilesValid := by
  exact MergedCutProfiles.Batch718.valid28728
theorem numericValid5189 : retention5189.NumericValid := by decide +kernel
def certificate5189 : RatCutBinCertificate := ⟨⟨retention5189,(254652143367338783/125000000000000000),(11895173549139047/50000000000000000),(17767111311624607767/1000000000000000000),(17137809829215648313311/1000000000000000000),(440303791210833499/200000000000000000)⟩,(49995419203507147/50000000000000000),(653889863749607801/1000000000000000000),(3416351686267233/50000000000000000),(131281582266399779/1000000000000000000)⟩
theorem valid5189 : certificate5189.Valid := by decide +kernel
theorem sound5189 : certificate5189.Sound := rat_cut_bin_certificate_sound certificate5189 profilesValid5189 numericValid5189 valid5189

def retention5190 : RatCutRetentionCertificate := ⟨(67/1000),(17/250),(632011875660177049/924473784126809255932),(607350989989147791/1000000000000000000),4,(5608709131396855308200298367405667447/2429403959956591164000000000000000000),true,MergedCutProfiles.Batch718.profile28729,![MergedCutProfiles.Batch718.profile28729,MergedCutProfiles.Batch718.profile28730,MergedCutProfiles.Batch718.profile28731,MergedCutProfiles.Batch718.profile28732,MergedCutProfiles.Batch718.profile28733,MergedCutProfiles.Batch718.profile28734,MergedCutProfiles.Batch718.profile28735,MergedCutProfiles.Batch718.profile28736,MergedCutProfiles.Batch718.profile28737,MergedCutProfiles.Batch718.profile28738,MergedCutProfiles.Batch718.profile28739,MergedCutProfiles.Batch718.profile28740,MergedCutProfiles.Batch718.profile28741,MergedCutProfiles.Batch718.profile28742,MergedCutProfiles.Batch718.profile28743,MergedCutProfiles.Batch718.profile28744]⟩
theorem profilesValid5190 : retention5190.ProfilesValid := by
  change ∀ j : Fin 16, (retention5190.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch718.valid28729
  · exact MergedCutProfiles.Batch718.valid28730
  · exact MergedCutProfiles.Batch718.valid28731
  · exact MergedCutProfiles.Batch718.valid28732
  · exact MergedCutProfiles.Batch718.valid28733
  · exact MergedCutProfiles.Batch718.valid28734
  · exact MergedCutProfiles.Batch718.valid28735
  · exact MergedCutProfiles.Batch718.valid28736
  · exact MergedCutProfiles.Batch718.valid28737
  · exact MergedCutProfiles.Batch718.valid28738
  · exact MergedCutProfiles.Batch718.valid28739
  · exact MergedCutProfiles.Batch718.valid28740
  · exact MergedCutProfiles.Batch718.valid28741
  · exact MergedCutProfiles.Batch718.valid28742
  · exact MergedCutProfiles.Batch718.valid28743
  · exact MergedCutProfiles.Batch718.valid28744
theorem numericValid5190 : retention5190.NumericValid := by decide +kernel
def certificate5190 : RatCutBinCertificate := ⟨⟨retention5190,(393527463087748333/200000000000000000),(123364672097640231/500000000000000000),(18116751585365979149/1000000000000000000),(2107087418192514216281/125000000000000000),(110074427500955557/50000000000000000)⟩,(249977760010865573/250000000000000000),(5899981321276971/7812500000000000),(1023786104051629/31250000000000000),(7349407684671209/500000000000000000)⟩
theorem valid5190 : certificate5190.Valid := by decide +kernel
theorem sound5190 : certificate5190.Sound := rat_cut_bin_certificate_sound certificate5190 profilesValid5190 numericValid5190 valid5190

def retention5191 : RatCutRetentionCertificate := ⟨(67/1000),(17/250),(254758490500000000/231118446031702313983),(632011875660177049/1000000000000000000),4,(120142352419466269973/51200000000000000000),true,MergedCutProfiles.Batch718.profile28745,![MergedCutProfiles.Batch718.profile28745,MergedCutProfiles.Batch718.profile28746,MergedCutProfiles.Batch718.profile28733,MergedCutProfiles.Batch718.profile28747,MergedCutProfiles.Batch718.profile28748,MergedCutProfiles.Batch718.profile28749,MergedCutProfiles.Batch718.profile28739,MergedCutProfiles.Batch718.profile28741,MergedCutProfiles.Batch718.profile28742,MergedCutProfiles.Batch718.profile28744,MergedCutProfiles.Batch718.profile28750,MergedCutProfiles.Batch718.profile28751,MergedCutProfiles.Batch718.profile28752,MergedCutProfiles.Batch718.profile28753,MergedCutProfiles.Batch718.profile28754,MergedCutProfiles.Batch718.profile28755]⟩
theorem profilesValid5191 : retention5191.ProfilesValid := by
  change ∀ j : Fin 16, (retention5191.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch718.valid28745
  · exact MergedCutProfiles.Batch718.valid28746
  · exact MergedCutProfiles.Batch718.valid28733
  · exact MergedCutProfiles.Batch718.valid28747
  · exact MergedCutProfiles.Batch718.valid28748
  · exact MergedCutProfiles.Batch718.valid28749
  · exact MergedCutProfiles.Batch718.valid28739
  · exact MergedCutProfiles.Batch718.valid28741
  · exact MergedCutProfiles.Batch718.valid28742
  · exact MergedCutProfiles.Batch718.valid28744
  · exact MergedCutProfiles.Batch718.valid28750
  · exact MergedCutProfiles.Batch718.valid28751
  · exact MergedCutProfiles.Batch718.valid28752
  · exact MergedCutProfiles.Batch718.valid28753
  · exact MergedCutProfiles.Batch718.valid28754
  · exact MergedCutProfiles.Batch718.valid28755
theorem numericValid5191 : retention5191.NumericValid := by decide +kernel
def certificate5191 : RatCutBinCertificate := ⟨⟨retention5191,(393527463087748333/200000000000000000),(123364672097640231/500000000000000000),(18116751585365979149/1000000000000000000),(2107087418192514216281/125000000000000000),(111967093039204967/50000000000000000)⟩,(249977760010865573/250000000000000000),(723612184640129013/1000000000000000000),(42299500345008431/1000000000000000000),(3877046404945771/200000000000000000)⟩
theorem valid5191 : certificate5191.Valid := by decide +kernel
theorem sound5191 : certificate5191.Sound := rat_cut_bin_certificate_sound certificate5191 profilesValid5191 numericValid5191 valid5191

def retention5192 : RatCutRetentionCertificate := ⟨(67/1000),(17/250),(472080828289421167/231118446031702313983),(509516981/500000000),(61/20),(9870169998172737177164702979458429231/4076135848000000000000000000000000000),true,MergedCutProfiles.Batch718.profile28731,![MergedCutProfiles.Batch718.profile28731,MergedCutProfiles.Batch718.profile28734,MergedCutProfiles.Batch718.profile28737,MergedCutProfiles.Batch718.profile28740,MergedCutProfiles.Batch718.profile28743,MergedCutProfiles.Batch718.profile28750,MergedCutProfiles.Batch718.profile28752,MergedCutProfiles.Batch718.profile28754,MergedCutProfiles.Batch718.profile28756,MergedCutProfiles.Batch718.profile28757,MergedCutProfiles.Batch718.profile28758,MergedCutProfiles.Batch718.profile28759,MergedCutProfiles.Batch719.profile28760,MergedCutProfiles.Batch719.profile28761,MergedCutProfiles.Batch719.profile28762,MergedCutProfiles.Batch719.profile28763]⟩
theorem profilesValid5192 : retention5192.ProfilesValid := by
  change ∀ j : Fin 16, (retention5192.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch718.valid28731
  · exact MergedCutProfiles.Batch718.valid28734
  · exact MergedCutProfiles.Batch718.valid28737
  · exact MergedCutProfiles.Batch718.valid28740
  · exact MergedCutProfiles.Batch718.valid28743
  · exact MergedCutProfiles.Batch718.valid28750
  · exact MergedCutProfiles.Batch718.valid28752
  · exact MergedCutProfiles.Batch718.valid28754
  · exact MergedCutProfiles.Batch718.valid28756
  · exact MergedCutProfiles.Batch718.valid28757
  · exact MergedCutProfiles.Batch718.valid28758
  · exact MergedCutProfiles.Batch718.valid28759
  · exact MergedCutProfiles.Batch719.valid28760
  · exact MergedCutProfiles.Batch719.valid28761
  · exact MergedCutProfiles.Batch719.valid28762
  · exact MergedCutProfiles.Batch719.valid28763
theorem numericValid5192 : retention5192.NumericValid := by decide +kernel
def certificate5192 : RatCutBinCertificate := ⟨⟨retention5192,(393527463087748333/200000000000000000),(123364672097640231/500000000000000000),(18116751585365979149/1000000000000000000),(2107087418192514216281/125000000000000000),(2339721549223683809/1000000000000000000)⟩,(249977760010865573/250000000000000000),(262043803057037953/500000000000000000),(137301246006810779/1000000000000000000),(84467379504564917/1000000000000000000)⟩
theorem valid5192 : certificate5192.Valid := by decide +kernel
theorem sound5192 : certificate5192.Sound := rat_cut_bin_certificate_sound certificate5192 profilesValid5192 numericValid5192 valid5192

def retention5193 : RatCutRetentionCertificate := ⟨(67/1000),(17/250),(16000000000000000000/231118446031702313983),(472080828289421167/250000000000000000),(39/20),(384807067810030150550250762023040317351/188832331315768466800000000000000000000),false,MergedCutProfiles.Batch719.profile28764,(fun _ => MergedCutProfiles.Batch719.profile28764)⟩
theorem profilesValid5193 : retention5193.ProfilesValid := by
  exact MergedCutProfiles.Batch719.valid28764
theorem numericValid5193 : retention5193.NumericValid := by decide +kernel
def certificate5193 : RatCutBinCertificate := ⟨⟨retention5193,(393527463087748333/200000000000000000),(123364672097640231/500000000000000000),(18116751585365979149/1000000000000000000),(2107087418192514216281/125000000000000000),(19855697792948667/10000000000000000)⟩,(249977760010865573/250000000000000000),(18732748080266617/40000000000000000),(35282332448855813/200000000000000000),(140702533913569073/1000000000000000000)⟩
theorem valid5193 : certificate5193.Valid := by decide +kernel
theorem sound5193 : certificate5193.Sound := rat_cut_bin_certificate_sound certificate5193 profilesValid5193 numericValid5193 valid5193

def retention5194 : RatCutRetentionCertificate := ⟨(67/1000),(17/250),(1/2),64,1,(3990934927282774089530076300593022831/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch719.profile28765,(fun _ => MergedCutProfiles.Batch719.profile28765)⟩
theorem profilesValid5194 : retention5194.ProfilesValid := by
  exact MergedCutProfiles.Batch719.valid28765
theorem numericValid5194 : retention5194.NumericValid := by decide +kernel
def certificate5194 : RatCutBinCertificate := ⟨⟨retention5194,(393527463087748333/200000000000000000),(123364672097640231/500000000000000000),(18116751585365979149/1000000000000000000),(2107087418192514216281/125000000000000000),(194187353172779539/200000000000000000)⟩,(249977760010865573/250000000000000000),(610484449824327631/1000000000000000000),(88239973629829479/1000000000000000000),(4219374122382637/50000000000000000)⟩
theorem valid5194 : certificate5194.Valid := by decide +kernel
theorem sound5194 : certificate5194.Sound := rat_cut_bin_certificate_sound certificate5194 profilesValid5194 numericValid5194 valid5194

def retention5195 : RatCutRetentionCertificate := ⟨(67/1000),(17/250),(16000000000000000000/231118446031702313983),(56572755757340626393/1000000000000000000),1,(114715479212386958211891228696937722849/56572755757340626393000000000000000000),false,MergedCutProfiles.Batch719.profile28764,(fun _ => MergedCutProfiles.Batch719.profile28764)⟩
theorem profilesValid5195 : retention5195.ProfilesValid := by
  exact MergedCutProfiles.Batch719.valid28764
theorem numericValid5195 : retention5195.NumericValid := by decide +kernel
def certificate5195 : RatCutBinCertificate := ⟨⟨retention5195,(330625660887748333/200000000000000000),(123364672097640231/500000000000000000),(18116751585365979149/1000000000000000000),(2107087418192514216281/125000000000000000),(2005237588967767907/1000000000000000000)⟩,(99992525981888449/100000000000000000),(14328737623124973/1000000000000000000),(891443887976116393/1000000000000000000),(863117035280596907/500000000000000000)⟩
theorem valid5195 : certificate5195.Valid := by decide +kernel
theorem sound5195 : certificate5195.Sound := rat_cut_bin_certificate_sound certificate5195 profilesValid5195 numericValid5195 valid5195

def certificates : List RatCutBinCertificate := [certificate5184,certificate5185,certificate5186,certificate5187,certificate5188,certificate5189,certificate5190,certificate5191,certificate5192,certificate5193,certificate5194,certificate5195]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound5184,List.forall_mem_cons.mpr ⟨sound5185,List.forall_mem_cons.mpr ⟨sound5186,List.forall_mem_cons.mpr ⟨sound5187,List.forall_mem_cons.mpr ⟨sound5188,List.forall_mem_cons.mpr ⟨sound5189,List.forall_mem_cons.mpr ⟨sound5190,List.forall_mem_cons.mpr ⟨sound5191,List.forall_mem_cons.mpr ⟨sound5192,List.forall_mem_cons.mpr ⟨sound5193,List.forall_mem_cons.mpr ⟨sound5194,List.forall_mem_cons.mpr ⟨sound5195,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch432
