import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch431
import Cycle12.MergedCutProfiles.Batch432
import Cycle12.MergedCutProfiles.Batch434
import Cycle12.MergedCutProfiles.Batch553
import Cycle12.MergedCutProfiles.Batch554
import Cycle12.MergedCutProfiles.Batch555
import Cycle12.MergedCutProfiles.Batch556
import Cycle12.MergedCutProfiles.Batch639
import Cycle12.MergedCutProfiles.Batch640
import Cycle12.MergedCutProfiles.Batch641

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch356

def retention4272 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(1/2),64,1,(10216688527079369933560363522793860999/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch431.profile17278,(fun _ => MergedCutProfiles.Batch431.profile17278)⟩
theorem profilesValid4272 : retention4272.ProfilesValid := by
  exact MergedCutProfiles.Batch431.valid17278
theorem numericValid4272 : retention4272.NumericValid := by decide +kernel
def certificate4272 : RatCutBinCertificate := ⟨⟨retention4272,(215303782971840637/100000000000000000),(229314578619222081/1000000000000000000),(879802960495445129/50000000000000000),(1754677969578086812537/500000000000000000),(193932947335251011/200000000000000000)⟩,(999524526734776649/1000000000000000000),(432607265991437211/1000000000000000000),(5122495378718517/25000000000000000),(19562467348902743/100000000000000000)⟩
theorem valid4272 : certificate4272.Valid := by decide +kernel
theorem sound4272 : certificate4272.Sound := rat_cut_bin_certificate_sound certificate4272 profilesValid4272 numericValid4272 valid4272

def retention4273 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(64000000000000000000/198806338180814466443),(22838287855339009149/1000000000000000000),1,(4939212729155319820850506892756998379/3654126056854241463840000000000000000),false,MergedCutProfiles.Batch639.profile25592,(fun _ => MergedCutProfiles.Batch639.profile25592)⟩
theorem profilesValid4273 : retention4273.ProfilesValid := by
  exact MergedCutProfiles.Batch639.valid25592
theorem numericValid4273 : retention4273.NumericValid := by decide +kernel
def certificate4273 : RatCutBinCertificate := ⟨⟨retention4273,(195541685871840637/100000000000000000),(229314578619222081/1000000000000000000),(879802960495445129/50000000000000000),(1754677969578086812537/500000000000000000),(663098810741574411/500000000000000000)⟩,(499784087246735297/500000000000000000),(18755329117978889/500000000000000000),(822730544072673101/1000000000000000000),(128845124942836241/125000000000000000)⟩
theorem valid4273 : certificate4273.Valid := by decide +kernel
theorem sound4273 : certificate4273.Sound := rat_cut_bin_certificate_sound certificate4273 profilesValid4273 numericValid4273 valid4273

def retention4274 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(1/2),64,1,(10216688527079369933560363522793860999/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch431.profile17278,(fun _ => MergedCutProfiles.Batch431.profile17278)⟩
theorem profilesValid4274 : retention4274.ProfilesValid := by
  exact MergedCutProfiles.Batch431.valid17278
theorem numericValid4274 : retention4274.NumericValid := by decide +kernel
def certificate4274 : RatCutBinCertificate := ⟨⟨retention4274,(195541685871840637/100000000000000000),(229314578619222081/1000000000000000000),(879802960495445129/50000000000000000),(1754677969578086812537/500000000000000000),(972240166516508419/1000000000000000000)⟩,(499784087246735297/500000000000000000),(25583465611708919/500000000000000000),(785245199626853699/1000000000000000000),(187923489805074939/250000000000000000)⟩
theorem valid4274 : certificate4274.Valid := by decide +kernel
theorem sound4274 : certificate4274.Sound := rat_cut_bin_certificate_sound certificate4274 profilesValid4274 numericValid4274 valid4274

def retention4275 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(846233986305102865/195203770590307810072),(837855431985250361/1000000000000000000),(33/10),(188049181678647720171/80000000000000000000),true,MergedCutProfiles.Batch639.profile25593,![MergedCutProfiles.Batch639.profile25593,MergedCutProfiles.Batch639.profile25594,MergedCutProfiles.Batch639.profile25595,MergedCutProfiles.Batch639.profile25596,MergedCutProfiles.Batch639.profile25597,MergedCutProfiles.Batch639.profile25598,MergedCutProfiles.Batch639.profile25599,MergedCutProfiles.Batch640.profile25600,MergedCutProfiles.Batch553.profile22121,MergedCutProfiles.Batch640.profile25601,MergedCutProfiles.Batch640.profile25602,MergedCutProfiles.Batch640.profile25603,MergedCutProfiles.Batch554.profile22163,MergedCutProfiles.Batch640.profile25604,MergedCutProfiles.Batch640.profile25605,MergedCutProfiles.Batch553.profile22149]⟩
theorem profilesValid4275 : retention4275.ProfilesValid := by
  change ∀ j : Fin 16, (retention4275.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch639.valid25593
  · exact MergedCutProfiles.Batch639.valid25594
  · exact MergedCutProfiles.Batch639.valid25595
  · exact MergedCutProfiles.Batch639.valid25596
  · exact MergedCutProfiles.Batch639.valid25597
  · exact MergedCutProfiles.Batch639.valid25598
  · exact MergedCutProfiles.Batch639.valid25599
  · exact MergedCutProfiles.Batch640.valid25600
  · exact MergedCutProfiles.Batch553.valid22121
  · exact MergedCutProfiles.Batch640.valid25601
  · exact MergedCutProfiles.Batch640.valid25602
  · exact MergedCutProfiles.Batch640.valid25603
  · exact MergedCutProfiles.Batch554.valid22163
  · exact MergedCutProfiles.Batch640.valid25604
  · exact MergedCutProfiles.Batch640.valid25605
  · exact MergedCutProfiles.Batch553.valid22149
theorem numericValid4275 : retention4275.NumericValid := by decide +kernel
def certificate4275 : RatCutBinCertificate := ⟨⟨retention4275,(2161654806863854579/1000000000000000000),(233579791654726571/1000000000000000000),(8883543154923914067/500000000000000000),(1739646561492553482501/500000000000000000),(70525953965211683/31250000000000000)⟩,(199904222271674371/200000000000000000),(384178450705505809/1000000000000000000),(248295797810250467/1000000000000000000),(136055256647584951/1000000000000000000)⟩
theorem valid4275 : certificate4275.Valid := by decide +kernel
theorem sound4275 : certificate4275.Sound := rat_cut_bin_certificate_sound certificate4275 profilesValid4275 numericValid4275 valid4275

def retention4276 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(140755770500000000/24400471323788476259),(169246797261020573/200000000000000000),(33/10),(37500919582715886627/16000000000000000000),true,MergedCutProfiles.Batch640.profile25606,![MergedCutProfiles.Batch640.profile25606,MergedCutProfiles.Batch640.profile25607,MergedCutProfiles.Batch639.profile25596,MergedCutProfiles.Batch553.profile22135,MergedCutProfiles.Batch554.profile22162,MergedCutProfiles.Batch640.profile25600,MergedCutProfiles.Batch640.profile25608,MergedCutProfiles.Batch553.profile22136,MergedCutProfiles.Batch640.profile25603,MergedCutProfiles.Batch640.profile25609,MergedCutProfiles.Batch640.profile25610,MergedCutProfiles.Batch553.profile22149,MergedCutProfiles.Batch640.profile25611,MergedCutProfiles.Batch640.profile25612,MergedCutProfiles.Batch640.profile25613,MergedCutProfiles.Batch553.profile22150]⟩
theorem profilesValid4276 : retention4276.ProfilesValid := by
  change ∀ j : Fin 16, (retention4276.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch640.valid25606
  · exact MergedCutProfiles.Batch640.valid25607
  · exact MergedCutProfiles.Batch639.valid25596
  · exact MergedCutProfiles.Batch553.valid22135
  · exact MergedCutProfiles.Batch554.valid22162
  · exact MergedCutProfiles.Batch640.valid25600
  · exact MergedCutProfiles.Batch640.valid25608
  · exact MergedCutProfiles.Batch553.valid22136
  · exact MergedCutProfiles.Batch640.valid25603
  · exact MergedCutProfiles.Batch640.valid25609
  · exact MergedCutProfiles.Batch640.valid25610
  · exact MergedCutProfiles.Batch553.valid22149
  · exact MergedCutProfiles.Batch640.valid25611
  · exact MergedCutProfiles.Batch640.valid25612
  · exact MergedCutProfiles.Batch640.valid25613
  · exact MergedCutProfiles.Batch553.valid22150
theorem numericValid4276 : retention4276.NumericValid := by decide +kernel
def certificate4276 : RatCutBinCertificate := ⟨⟨retention4276,(2161654806863854579/1000000000000000000),(233579791654726571/1000000000000000000),(8883543154923914067/500000000000000000),(1739646561492553482501/500000000000000000),(2250023252368884501/1000000000000000000)⟩,(199904222271674371/200000000000000000),(76664028547605587/200000000000000000),(249117800429612671/1000000000000000000),(27288544693613833/200000000000000000)⟩
theorem valid4276 : certificate4276.Valid := by decide +kernel
theorem sound4276 : certificate4276.Sound := rat_cut_bin_certificate_sound certificate4276 profilesValid4276 numericValid4276 valid4276

def retention4277 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(1235101551161120327/195203770590307810072),(281511541/250000000),(53/20),(583575801943917187/250000000000000000),true,MergedCutProfiles.Batch640.profile25614,![MergedCutProfiles.Batch640.profile25614,MergedCutProfiles.Batch640.profile25615,MergedCutProfiles.Batch640.profile25616,MergedCutProfiles.Batch640.profile25617,MergedCutProfiles.Batch640.profile25618,MergedCutProfiles.Batch640.profile25619,MergedCutProfiles.Batch640.profile25620,MergedCutProfiles.Batch432.profile17298,MergedCutProfiles.Batch640.profile25609,MergedCutProfiles.Batch640.profile25610,MergedCutProfiles.Batch640.profile25621,MergedCutProfiles.Batch640.profile25622,MergedCutProfiles.Batch640.profile25623,MergedCutProfiles.Batch640.profile25624,MergedCutProfiles.Batch640.profile25625,MergedCutProfiles.Batch432.profile17299]⟩
theorem profilesValid4277 : retention4277.ProfilesValid := by
  change ∀ j : Fin 16, (retention4277.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch640.valid25614
  · exact MergedCutProfiles.Batch640.valid25615
  · exact MergedCutProfiles.Batch640.valid25616
  · exact MergedCutProfiles.Batch640.valid25617
  · exact MergedCutProfiles.Batch640.valid25618
  · exact MergedCutProfiles.Batch640.valid25619
  · exact MergedCutProfiles.Batch640.valid25620
  · exact MergedCutProfiles.Batch432.valid17298
  · exact MergedCutProfiles.Batch640.valid25609
  · exact MergedCutProfiles.Batch640.valid25610
  · exact MergedCutProfiles.Batch640.valid25621
  · exact MergedCutProfiles.Batch640.valid25622
  · exact MergedCutProfiles.Batch640.valid25623
  · exact MergedCutProfiles.Batch640.valid25624
  · exact MergedCutProfiles.Batch640.valid25625
  · exact MergedCutProfiles.Batch432.valid17299
theorem numericValid4277 : retention4277.NumericValid := by decide +kernel
def certificate4277 : RatCutBinCertificate := ⟨⟨retention4277,(2161654806863854579/1000000000000000000),(233579791654726571/1000000000000000000),(8883543154923914067/500000000000000000),(1739646561492553482501/500000000000000000),(2258991752081071671/1000000000000000000)⟩,(199904222271674371/200000000000000000),(66357464688199413/200000000000000000),(75538735946434909/250000000000000000),(200225934183878133/1000000000000000000)⟩
theorem valid4277 : certificate4277.Valid := by decide +kernel
theorem sound4277 : certificate4277.Sound := rat_cut_bin_certificate_sound certificate4277 profilesValid4277 numericValid4277 valid4277

def retention4278 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(1346498877342260461/48800942647576952518),(1235101551161120327/1000000000000000000),(49/20),(704917107777549207681/320000000000000000000),true,MergedCutProfiles.Batch640.profile25626,![MergedCutProfiles.Batch640.profile25626,MergedCutProfiles.Batch432.profile17314,MergedCutProfiles.Batch640.profile25627,MergedCutProfiles.Batch640.profile25628,MergedCutProfiles.Batch553.profile22152,MergedCutProfiles.Batch640.profile25629,MergedCutProfiles.Batch640.profile25630,MergedCutProfiles.Batch432.profile17317,MergedCutProfiles.Batch432.profile17286,MergedCutProfiles.Batch432.profile17318,MergedCutProfiles.Batch640.profile25631,MergedCutProfiles.Batch432.profile17319,MergedCutProfiles.Batch640.profile25632,MergedCutProfiles.Batch640.profile25633,MergedCutProfiles.Batch640.profile25634,MergedCutProfiles.Batch640.profile25635]⟩
theorem profilesValid4278 : retention4278.ProfilesValid := by
  change ∀ j : Fin 16, (retention4278.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch640.valid25626
  · exact MergedCutProfiles.Batch432.valid17314
  · exact MergedCutProfiles.Batch640.valid25627
  · exact MergedCutProfiles.Batch640.valid25628
  · exact MergedCutProfiles.Batch553.valid22152
  · exact MergedCutProfiles.Batch640.valid25629
  · exact MergedCutProfiles.Batch640.valid25630
  · exact MergedCutProfiles.Batch432.valid17317
  · exact MergedCutProfiles.Batch432.valid17286
  · exact MergedCutProfiles.Batch432.valid17318
  · exact MergedCutProfiles.Batch640.valid25631
  · exact MergedCutProfiles.Batch432.valid17319
  · exact MergedCutProfiles.Batch640.valid25632
  · exact MergedCutProfiles.Batch640.valid25633
  · exact MergedCutProfiles.Batch640.valid25634
  · exact MergedCutProfiles.Batch640.valid25635
theorem numericValid4278 : retention4278.NumericValid := by decide +kernel
def certificate4278 : RatCutBinCertificate := ⟨⟨retention4278,(2161654806863854579/1000000000000000000),(233579791654726571/1000000000000000000),(8883543154923914067/500000000000000000),(1739646561492553482501/500000000000000000),(1066619205644222679/500000000000000000)⟩,(199904222271674371/200000000000000000),(337204080925009029/1000000000000000000),(296224178346794323/1000000000000000000),(200178350268115833/1000000000000000000)⟩
theorem valid4278 : certificate4278.Valid := by decide +kernel
theorem sound4278 : certificate4278.Sound := rat_cut_bin_certificate_sound certificate4278 profilesValid4278 numericValid4278 valid4278

def retention4279 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(8000000000000000000/24400471323788476259),(1346498877342260461/250000000000000000),(23/20),(724563437610894241459846364324660478951/538599550936904184400000000000000000000),false,MergedCutProfiles.Batch640.profile25636,(fun _ => MergedCutProfiles.Batch640.profile25636)⟩
theorem profilesValid4279 : retention4279.ProfilesValid := by
  exact MergedCutProfiles.Batch640.valid25636
theorem numericValid4279 : retention4279.NumericValid := by decide +kernel
def certificate4279 : RatCutBinCertificate := ⟨⟨retention4279,(2161654806863854579/1000000000000000000),(233579791654726571/1000000000000000000),(8883543154923914067/500000000000000000),(1739646561492553482501/500000000000000000),(262518211698715541/200000000000000000)⟩,(199904222271674371/200000000000000000),(365132264373606343/1000000000000000000),(266994807883067853/1000000000000000000),(257189134688695191/1000000000000000000)⟩
theorem valid4279 : certificate4279.Valid := by decide +kernel
theorem sound4279 : certificate4279.Sound := rat_cut_bin_certificate_sound certificate4279 profilesValid4279 numericValid4279 valid4279

def retention4280 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(1/2),64,1,(63854522306255662397114747532457634191/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch434.profile17377,(fun _ => MergedCutProfiles.Batch434.profile17377)⟩
theorem profilesValid4280 : retention4280.ProfilesValid := by
  exact MergedCutProfiles.Batch434.valid17377
theorem numericValid4280 : retention4280.NumericValid := by decide +kernel
def certificate4280 : RatCutBinCertificate := ⟨⟨retention4280,(2161654806863854579/1000000000000000000),(233579791654726571/1000000000000000000),(8883543154923914067/500000000000000000),(1739646561492553482501/500000000000000000),(242327025836146153/250000000000000000)⟩,(199904222271674371/200000000000000000),(426952574863219457/1000000000000000000),(13104690317359411/62500000000000000),(100055260179382579/500000000000000000)⟩
theorem valid4280 : certificate4280.Valid := by decide +kernel
theorem sound4280 : certificate4280.Sound := rat_cut_bin_certificate_sound certificate4280 profilesValid4280 numericValid4280 valid4280

def retention4281 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(8000000000000000000/24400471323788476259),(22559071014967306293/1000000000000000000),1,(3356066264719637458268837219919875697/2506563446107478477000000000000000000),false,MergedCutProfiles.Batch640.profile25636,(fun _ => MergedCutProfiles.Batch640.profile25636)⟩
theorem profilesValid4281 : retention4281.ProfilesValid := by
  exact MergedCutProfiles.Batch640.valid25636
theorem numericValid4281 : retention4281.NumericValid := by decide +kernel
def certificate4281 : RatCutBinCertificate := ⟨⟨retention4281,(1960538064863854579/1000000000000000000),(233579791654726571/1000000000000000000),(8883543154923914067/500000000000000000),(1739646561492553482501/500000000000000000),(164142067222113083/125000000000000000)⟩,(99956567211329801/100000000000000000),(591621806637341/15625000000000000),(205433672856087151/250000000000000000),(12740457719080077/12500000000000000)⟩
theorem valid4281 : certificate4281.Valid := by decide +kernel
theorem sound4281 : certificate4281.Sound := rat_cut_bin_certificate_sound certificate4281 profilesValid4281 numericValid4281 valid4281

def retention4282 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(1/2),64,1,(63854522306255662397114747532457634191/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch434.profile17377,(fun _ => MergedCutProfiles.Batch434.profile17377)⟩
theorem profilesValid4282 : retention4282.ProfilesValid := by
  exact MergedCutProfiles.Batch434.valid17377
theorem numericValid4282 : retention4282.NumericValid := by decide +kernel
def certificate4282 : RatCutBinCertificate := ⟨⟨retention4282,(1960538064863854579/1000000000000000000),(233579791654726571/1000000000000000000),(8883543154923914067/500000000000000000),(1739646561492553482501/500000000000000000),(242988035401147213/250000000000000000)⟩,(99956567211329801/100000000000000000),(10231025040337043/200000000000000000),(785276722429633753/1000000000000000000),(93937854836579271/125000000000000000)⟩
theorem valid4282 : certificate4282.Valid := by decide +kernel
theorem sound4282 : certificate4282.Sound := rat_cut_bin_certificate_sound certificate4282 profilesValid4282 numericValid4282 valid4282

def retention4283 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(860920711132466143/191686014252223588973),(843957171975753497/1000000000000000000),(13/4),(126582859092519475992181536379392188511/54013259006448223808000000000000000000),true,MergedCutProfiles.Batch640.profile25637,![MergedCutProfiles.Batch640.profile25637,MergedCutProfiles.Batch640.profile25638,MergedCutProfiles.Batch640.profile25639,MergedCutProfiles.Batch641.profile25640,MergedCutProfiles.Batch641.profile25641,MergedCutProfiles.Batch556.profile22243,MergedCutProfiles.Batch641.profile25642,MergedCutProfiles.Batch641.profile25643,MergedCutProfiles.Batch555.profile22207,MergedCutProfiles.Batch641.profile25644,MergedCutProfiles.Batch641.profile25645,MergedCutProfiles.Batch641.profile25646,MergedCutProfiles.Batch641.profile25647,MergedCutProfiles.Batch641.profile25648,MergedCutProfiles.Batch641.profile25649,MergedCutProfiles.Batch641.profile25650]⟩
theorem profilesValid4283 : retention4283.ProfilesValid := by
  change ∀ j : Fin 16, (retention4283.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch640.valid25637
  · exact MergedCutProfiles.Batch640.valid25638
  · exact MergedCutProfiles.Batch640.valid25639
  · exact MergedCutProfiles.Batch641.valid25640
  · exact MergedCutProfiles.Batch641.valid25641
  · exact MergedCutProfiles.Batch556.valid22243
  · exact MergedCutProfiles.Batch641.valid25642
  · exact MergedCutProfiles.Batch641.valid25643
  · exact MergedCutProfiles.Batch555.valid22207
  · exact MergedCutProfiles.Batch641.valid25644
  · exact MergedCutProfiles.Batch641.valid25645
  · exact MergedCutProfiles.Batch641.valid25646
  · exact MergedCutProfiles.Batch641.valid25647
  · exact MergedCutProfiles.Batch641.valid25648
  · exact MergedCutProfiles.Batch641.valid25649
  · exact MergedCutProfiles.Batch641.valid25650
theorem numericValid4283 : retention4283.NumericValid := by decide +kernel
def certificate4283 : RatCutBinCertificate := ⟨⟨retention4283,(2168398067693551319/1000000000000000000),(11895173549139047/50000000000000000),(8970312836421882251/500000000000000000),(3450002997137746146889/1000000000000000000),(1125048947350235253/500000000000000000)⟩,(499759109067024997/500000000000000000),(94836912282682511/250000000000000000),(252947344169781423/1000000000000000000),(34936986122447819/250000000000000000)⟩
theorem valid4283 : certificate4283.Valid := by decide +kernel
theorem sound4283 : certificate4283.Sound := rat_cut_bin_certificate_sound certificate4283 profilesValid4283 numericValid4283 valid4283

def certificates : List RatCutBinCertificate := [certificate4272,certificate4273,certificate4274,certificate4275,certificate4276,certificate4277,certificate4278,certificate4279,certificate4280,certificate4281,certificate4282,certificate4283]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4272,List.forall_mem_cons.mpr ⟨sound4273,List.forall_mem_cons.mpr ⟨sound4274,List.forall_mem_cons.mpr ⟨sound4275,List.forall_mem_cons.mpr ⟨sound4276,List.forall_mem_cons.mpr ⟨sound4277,List.forall_mem_cons.mpr ⟨sound4278,List.forall_mem_cons.mpr ⟨sound4279,List.forall_mem_cons.mpr ⟨sound4280,List.forall_mem_cons.mpr ⟨sound4281,List.forall_mem_cons.mpr ⟨sound4282,List.forall_mem_cons.mpr ⟨sound4283,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch356
