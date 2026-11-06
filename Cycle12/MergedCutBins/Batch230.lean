import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch305
import Cycle12.MergedCutProfiles.Batch306
import Cycle12.MergedCutProfiles.Batch307
import Cycle12.MergedCutProfiles.Batch438
import Cycle12.MergedCutProfiles.Batch439
import Cycle12.MergedCutProfiles.Batch440

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch230

def retention2760 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(1/2),64,1,(255419871002463909042457265882361431119/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch305.profile12226,(fun _ => MergedCutProfiles.Batch305.profile12226)⟩
theorem profilesValid2760 : retention2760.ProfilesValid := by
  exact MergedCutProfiles.Batch305.valid12226
theorem numericValid2760 : retention2760.NumericValid := by decide +kernel
def certificate2760 : RatCutBinCertificate := ⟨⟨retention2760,(2364970645655384873/1000000000000000000),(121143195939341811/500000000000000000),(4528487254489889107/250000000000000000),(171047067277992696389/500000000000000000),(241525107413986479/250000000000000000)⟩,(994722529154146931/1000000000000000000),(169341529144911257/500000000000000000),(294620006579063151/1000000000000000000),(55780866470032569/200000000000000000)⟩
theorem valid2760 : certificate2760.Valid := by decide +kernel
theorem sound2760 : certificate2760.Sound := rat_cut_bin_certificate_sound certificate2760 profilesValid2760 numericValid2760 valid2760

def retention2761 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(8545967777643656317/18825050066394954038),(4704124681020422783/1000000000000000000),(21/20),(7943088107611199444956591041530865498111/7526599489632676452800000000000000000000),false,MergedCutProfiles.Batch438.profile17559,(fun _ => MergedCutProfiles.Batch438.profile17559)⟩
theorem profilesValid2761 : retention2761.ProfilesValid := by
  exact MergedCutProfiles.Batch438.valid17559
theorem numericValid2761 : retention2761.NumericValid := by decide +kernel
def certificate2761 : RatCutBinCertificate := ⟨⟨retention2761,(2604714752655384873/1000000000000000000),(121143195939341811/500000000000000000),(4528487254489889107/250000000000000000),(171047067277992696389/500000000000000000),(1018748493754165229/1000000000000000000)⟩,(994186565544654639/1000000000000000000),(111036831359342621/500000000000000000),(221795046311853737/500000000000000000),(178707091404355533/500000000000000000)⟩
theorem valid2761 : certificate2761.Valid := by decide +kernel
theorem sound2761 : certificate2761.Sound := rat_cut_bin_certificate_sound certificate2761 profilesValid2761 numericValid2761 valid2761

def retention2762 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(9254058514102934645/18825050066394954038),(8545967777643656317/1000000000000000000),1,(33780176943764502752388654289836755731/34183871110574625268000000000000000000),false,MergedCutProfiles.Batch439.profile17560,(fun _ => MergedCutProfiles.Batch439.profile17560)⟩
theorem profilesValid2762 : retention2762.ProfilesValid := by
  exact MergedCutProfiles.Batch439.valid17560
theorem numericValid2762 : retention2762.NumericValid := by decide +kernel
def certificate2762 : RatCutBinCertificate := ⟨⟨retention2762,(2604714752655384873/1000000000000000000),(121143195939341811/500000000000000000),(4528487254489889107/250000000000000000),(171047067277992696389/500000000000000000),(476673894155689731/500000000000000000)⟩,(994186565544654639/1000000000000000000),(23730815990862531/100000000000000000),(421231639209285471/1000000000000000000),(359039641167857141/1000000000000000000)⟩
theorem valid2762 : certificate2762.Valid := by decide +kernel
theorem sound2762 : certificate2762.Sound := rat_cut_bin_certificate_sound certificate2762 profilesValid2762 numericValid2762 valid2762

def retention2763 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(4673299549621981996/9412525033197477019),(1850811702820586929/200000000000000000),1,(45399796063281048489781007266289369/46270292570514673225000000000000000),false,MergedCutProfiles.Batch439.profile17561,(fun _ => MergedCutProfiles.Batch439.profile17561)⟩
theorem profilesValid2763 : retention2763.ProfilesValid := by
  exact MergedCutProfiles.Batch439.valid17561
theorem numericValid2763 : retention2763.NumericValid := by decide +kernel
def certificate2763 : RatCutBinCertificate := ⟨⟨retention2763,(2604714752655384873/1000000000000000000),(121143195939341811/500000000000000000),(4528487254489889107/250000000000000000),(171047067277992696389/500000000000000000),(5914651312799307/6250000000000000)⟩,(994186565544654639/1000000000000000000),(47812879710160117/200000000000000000),(418717042228343257/1000000000000000000),(44658823814540297/125000000000000000)⟩
theorem valid2763 : certificate2763.Valid := by decide +kernel
theorem sound2763 : certificate2763.Sound := rat_cut_bin_certificate_sound certificate2763 profilesValid2763 numericValid2763 valid2763

def retention2764 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(1/2),(1168324887405495499/125000000000000000),1,(36444889012541265282738421381620698607/37386396396975855968000000000000000000),false,MergedCutProfiles.Batch305.profile12226,(fun _ => MergedCutProfiles.Batch305.profile12226)⟩
theorem profilesValid2764 : retention2764.ProfilesValid := by
  exact MergedCutProfiles.Batch305.valid12226
theorem numericValid2764 : retention2764.NumericValid := by decide +kernel
def certificate2764 : RatCutBinCertificate := ⟨⟨retention2764,(2604714752655384873/1000000000000000000),(121143195939341811/500000000000000000),(4528487254489889107/250000000000000000),(171047067277992696389/500000000000000000),(2937419918406083/3125000000000000)⟩,(994186565544654639/1000000000000000000),(48136888766633389/200000000000000000),(416408699983364779/1000000000000000000),(353453730760339783/1000000000000000000)⟩
theorem valid2764 : certificate2764.Valid := by decide +kernel
theorem sound2764 : certificate2764.Sound := rat_cut_bin_certificate_sound certificate2764 profilesValid2764 numericValid2764 valid2764

def retention2765 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(985054357722747703/18489475682536185118),(48765067213997411/50000000000000000),(49/20),(129830614024979933947/64000000000000000000),true,MergedCutProfiles.Batch439.profile17562,![MergedCutProfiles.Batch439.profile17562,MergedCutProfiles.Batch439.profile17563,MergedCutProfiles.Batch439.profile17564,MergedCutProfiles.Batch439.profile17565,MergedCutProfiles.Batch439.profile17566,MergedCutProfiles.Batch439.profile17567,MergedCutProfiles.Batch439.profile17568,MergedCutProfiles.Batch439.profile17569,MergedCutProfiles.Batch439.profile17570,MergedCutProfiles.Batch439.profile17571,MergedCutProfiles.Batch305.profile12233,MergedCutProfiles.Batch439.profile17572,MergedCutProfiles.Batch439.profile17573,MergedCutProfiles.Batch439.profile17574,MergedCutProfiles.Batch439.profile17575,MergedCutProfiles.Batch439.profile17576]⟩
theorem profilesValid2765 : retention2765.ProfilesValid := by
  change ∀ j : Fin 16, (retention2765.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch439.valid17562
  · exact MergedCutProfiles.Batch439.valid17563
  · exact MergedCutProfiles.Batch439.valid17564
  · exact MergedCutProfiles.Batch439.valid17565
  · exact MergedCutProfiles.Batch439.valid17566
  · exact MergedCutProfiles.Batch439.valid17567
  · exact MergedCutProfiles.Batch439.valid17568
  · exact MergedCutProfiles.Batch439.valid17569
  · exact MergedCutProfiles.Batch439.valid17570
  · exact MergedCutProfiles.Batch439.valid17571
  · exact MergedCutProfiles.Batch305.valid12233
  · exact MergedCutProfiles.Batch439.valid17572
  · exact MergedCutProfiles.Batch439.valid17573
  · exact MergedCutProfiles.Batch439.valid17574
  · exact MergedCutProfiles.Batch439.valid17575
  · exact MergedCutProfiles.Batch439.valid17576
theorem numericValid2765 : retention2765.NumericValid := by decide +kernel
def certificate2765 : RatCutBinCertificate := ⟨⟨retention2765,(2375668480937083231/1000000000000000000),(123364672097640231/500000000000000000),(4573138638309731967/250000000000000000),(13572511252097274473/40000000000000000),(243759283109142847/125000000000000000)⟩,(994685652049364679/1000000000000000000),(129960146819258301/500000000000000000),(389802401022902513/1000000000000000000),(46246462573974673/200000000000000000)⟩
theorem valid2765 : certificate2765.Valid := by decide +kernel
theorem sound2765 : certificate2765.Sound := rat_cut_bin_certificate_sound certificate2765 profilesValid2765 numericValid2765 valid2765

def retention2766 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(533336358334119462/9244737841268092559),(985054357722747703/1000000000000000000),(49/20),(80872651511859650411/40000000000000000000),true,MergedCutProfiles.Batch439.profile17577,![MergedCutProfiles.Batch439.profile17577,MergedCutProfiles.Batch439.profile17578,MergedCutProfiles.Batch439.profile17579,MergedCutProfiles.Batch439.profile17580,MergedCutProfiles.Batch306.profile12246,MergedCutProfiles.Batch439.profile17581,MergedCutProfiles.Batch439.profile17582,MergedCutProfiles.Batch439.profile17583,MergedCutProfiles.Batch439.profile17584,MergedCutProfiles.Batch306.profile12247,MergedCutProfiles.Batch439.profile17585,MergedCutProfiles.Batch439.profile17573,MergedCutProfiles.Batch439.profile17586,MergedCutProfiles.Batch439.profile17587,MergedCutProfiles.Batch439.profile17588,MergedCutProfiles.Batch439.profile17589]⟩
theorem profilesValid2766 : retention2766.ProfilesValid := by
  change ∀ j : Fin 16, (retention2766.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch439.valid17577
  · exact MergedCutProfiles.Batch439.valid17578
  · exact MergedCutProfiles.Batch439.valid17579
  · exact MergedCutProfiles.Batch439.valid17580
  · exact MergedCutProfiles.Batch306.valid12246
  · exact MergedCutProfiles.Batch439.valid17581
  · exact MergedCutProfiles.Batch439.valid17582
  · exact MergedCutProfiles.Batch439.valid17583
  · exact MergedCutProfiles.Batch439.valid17584
  · exact MergedCutProfiles.Batch306.valid12247
  · exact MergedCutProfiles.Batch439.valid17585
  · exact MergedCutProfiles.Batch439.valid17573
  · exact MergedCutProfiles.Batch439.valid17586
  · exact MergedCutProfiles.Batch439.valid17587
  · exact MergedCutProfiles.Batch439.valid17588
  · exact MergedCutProfiles.Batch439.valid17589
theorem numericValid2766 : retention2766.NumericValid := by decide +kernel
def certificate2766 : RatCutBinCertificate := ⟨⟨retention2766,(2375668480937083231/1000000000000000000),(123364672097640231/500000000000000000),(4573138638309731967/250000000000000000),(13572511252097274473/40000000000000000),(1943287445062829037/1000000000000000000)⟩,(994685652049364679/1000000000000000000),(259876288545888293/1000000000000000000),(15594464869704987/40000000000000000),(231235489132421923/1000000000000000000)⟩
theorem valid2766 : certificate2766.Valid := by decide +kernel
theorem sound2766 : certificate2766.Sound := rat_cut_bin_certificate_sound certificate2766 profilesValid2766 numericValid2766 valid2766

def retention2767 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(153257485466213963/1680861425685107738),(266668179167059731/250000000000000000),(23/10),(617257535886080582807/320000000000000000000),true,MergedCutProfiles.Batch439.profile17590,![MergedCutProfiles.Batch439.profile17590,MergedCutProfiles.Batch439.profile17591,MergedCutProfiles.Batch439.profile17592,MergedCutProfiles.Batch439.profile17593,MergedCutProfiles.Batch439.profile17594,MergedCutProfiles.Batch439.profile17595,MergedCutProfiles.Batch439.profile17572,MergedCutProfiles.Batch305.profile12234,MergedCutProfiles.Batch439.profile17596,MergedCutProfiles.Batch439.profile17597,MergedCutProfiles.Batch439.profile17598,MergedCutProfiles.Batch439.profile17599,MergedCutProfiles.Batch440.profile17600,MergedCutProfiles.Batch440.profile17601,MergedCutProfiles.Batch440.profile17602,MergedCutProfiles.Batch305.profile12239]⟩
theorem profilesValid2767 : retention2767.ProfilesValid := by
  change ∀ j : Fin 16, (retention2767.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch439.valid17590
  · exact MergedCutProfiles.Batch439.valid17591
  · exact MergedCutProfiles.Batch439.valid17592
  · exact MergedCutProfiles.Batch439.valid17593
  · exact MergedCutProfiles.Batch439.valid17594
  · exact MergedCutProfiles.Batch439.valid17595
  · exact MergedCutProfiles.Batch439.valid17572
  · exact MergedCutProfiles.Batch305.valid12234
  · exact MergedCutProfiles.Batch439.valid17596
  · exact MergedCutProfiles.Batch439.valid17597
  · exact MergedCutProfiles.Batch439.valid17598
  · exact MergedCutProfiles.Batch439.valid17599
  · exact MergedCutProfiles.Batch440.valid17600
  · exact MergedCutProfiles.Batch440.valid17601
  · exact MergedCutProfiles.Batch440.valid17602
  · exact MergedCutProfiles.Batch305.valid12239
theorem numericValid2767 : retention2767.NumericValid := by decide +kernel
def certificate2767 : RatCutBinCertificate := ⟨⟨retention2767,(2375668480937083231/1000000000000000000),(123364672097640231/500000000000000000),(4573138638309731967/250000000000000000),(13572511252097274473/40000000000000000),(371041841390963131/200000000000000000)⟩,(994685652049364679/1000000000000000000),(52917179507739403/200000000000000000),(76713029521067761/200000000000000000),(231337211085768281/1000000000000000000)⟩
theorem valid2767 : certificate2767.Valid := by decide +kernel
theorem sound2767 : certificate2767.Sound := rat_cut_bin_certificate_sound certificate2767 profilesValid2767 numericValid2767 valid2767

def retention2768 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(4698031025146108817/18489475682536185118),(1685832340128353593/1000000000000000000),(8/5),(1919953466983275879629/1280000000000000000000),true,MergedCutProfiles.Batch440.profile17603,![MergedCutProfiles.Batch440.profile17603,MergedCutProfiles.Batch440.profile17604,MergedCutProfiles.Batch440.profile17605,MergedCutProfiles.Batch440.profile17606,MergedCutProfiles.Batch440.profile17607,MergedCutProfiles.Batch440.profile17608,MergedCutProfiles.Batch440.profile17609,MergedCutProfiles.Batch440.profile17610,MergedCutProfiles.Batch440.profile17611,MergedCutProfiles.Batch440.profile17612,MergedCutProfiles.Batch440.profile17613,MergedCutProfiles.Batch440.profile17614,MergedCutProfiles.Batch440.profile17615,MergedCutProfiles.Batch440.profile17616,MergedCutProfiles.Batch440.profile17617,MergedCutProfiles.Batch440.profile17618]⟩
theorem profilesValid2768 : retention2768.ProfilesValid := by
  change ∀ j : Fin 16, (retention2768.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch440.valid17603
  · exact MergedCutProfiles.Batch440.valid17604
  · exact MergedCutProfiles.Batch440.valid17605
  · exact MergedCutProfiles.Batch440.valid17606
  · exact MergedCutProfiles.Batch440.valid17607
  · exact MergedCutProfiles.Batch440.valid17608
  · exact MergedCutProfiles.Batch440.valid17609
  · exact MergedCutProfiles.Batch440.valid17610
  · exact MergedCutProfiles.Batch440.valid17611
  · exact MergedCutProfiles.Batch440.valid17612
  · exact MergedCutProfiles.Batch440.valid17613
  · exact MergedCutProfiles.Batch440.valid17614
  · exact MergedCutProfiles.Batch440.valid17615
  · exact MergedCutProfiles.Batch440.valid17616
  · exact MergedCutProfiles.Batch440.valid17617
  · exact MergedCutProfiles.Batch440.valid17618
theorem numericValid2768 : retention2768.NumericValid := by decide +kernel
def certificate2768 : RatCutBinCertificate := ⟨⟨retention2768,(2375668480937083231/1000000000000000000),(123364672097640231/500000000000000000),(4573138638309731967/250000000000000000),(13572511252097274473/40000000000000000),(72434056500231797/50000000000000000)⟩,(994685652049364679/1000000000000000000),(295531661672735359/1000000000000000000),(68839087208596543/200000000000000000),(115922713359036207/500000000000000000)⟩
theorem valid2768 : certificate2768.Valid := by decide +kernel
theorem sound2768 : certificate2768.Sound := rat_cut_bin_certificate_sound certificate2768 profilesValid2768 numericValid2768 valid2768

def retention2769 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(8366726255401043483/18489475682536185118),(4698031025146108817/1000000000000000000),1,(268005828330376234577/256000000000000000000),true,MergedCutProfiles.Batch440.profile17619,![MergedCutProfiles.Batch440.profile17619,MergedCutProfiles.Batch440.profile17620,MergedCutProfiles.Batch440.profile17621,MergedCutProfiles.Batch440.profile17622,MergedCutProfiles.Batch440.profile17623,MergedCutProfiles.Batch440.profile17624,MergedCutProfiles.Batch440.profile17625,MergedCutProfiles.Batch440.profile17626,MergedCutProfiles.Batch440.profile17627,MergedCutProfiles.Batch440.profile17628,MergedCutProfiles.Batch440.profile17629,MergedCutProfiles.Batch440.profile17630,MergedCutProfiles.Batch440.profile17631,MergedCutProfiles.Batch307.profile12289,MergedCutProfiles.Batch440.profile17632,MergedCutProfiles.Batch440.profile17633]⟩
theorem profilesValid2769 : retention2769.ProfilesValid := by
  change ∀ j : Fin 16, (retention2769.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch440.valid17619
  · exact MergedCutProfiles.Batch440.valid17620
  · exact MergedCutProfiles.Batch440.valid17621
  · exact MergedCutProfiles.Batch440.valid17622
  · exact MergedCutProfiles.Batch440.valid17623
  · exact MergedCutProfiles.Batch440.valid17624
  · exact MergedCutProfiles.Batch440.valid17625
  · exact MergedCutProfiles.Batch440.valid17626
  · exact MergedCutProfiles.Batch440.valid17627
  · exact MergedCutProfiles.Batch440.valid17628
  · exact MergedCutProfiles.Batch440.valid17629
  · exact MergedCutProfiles.Batch440.valid17630
  · exact MergedCutProfiles.Batch440.valid17631
  · exact MergedCutProfiles.Batch307.valid12289
  · exact MergedCutProfiles.Batch440.valid17632
  · exact MergedCutProfiles.Batch440.valid17633
theorem numericValid2769 : retention2769.NumericValid := by decide +kernel
def certificate2769 : RatCutBinCertificate := ⟨⟨retention2769,(2375668480937083231/1000000000000000000),(123364672097640231/500000000000000000),(4573138638309731967/250000000000000000),(13572511252097274473/40000000000000000),(253712468245964899/250000000000000000)⟩,(994685652049364679/1000000000000000000),(353589064661664447/1000000000000000000),(278807467622502383/1000000000000000000),(2891228089453349/12500000000000000)⟩
theorem valid2769 : certificate2769.Valid := by decide +kernel
theorem sound2769 : certificate2769.Sound := rat_cut_bin_certificate_sound certificate2769 profilesValid2769 numericValid2769 valid2769

def retention2770 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(9150565286113692035/18489475682536185118),(8366726255401043483/1000000000000000000),(21/20),(13404727029281061130630277470245343400471/13386762008641669572800000000000000000000),false,MergedCutProfiles.Batch440.profile17634,(fun _ => MergedCutProfiles.Batch440.profile17634)⟩
theorem profilesValid2770 : retention2770.ProfilesValid := by
  exact MergedCutProfiles.Batch440.valid17634
theorem numericValid2770 : retention2770.NumericValid := by decide +kernel
def certificate2770 : RatCutBinCertificate := ⟨⟨retention2770,(2375668480937083231/1000000000000000000),(123364672097640231/500000000000000000),(4573138638309731967/250000000000000000),(13572511252097274473/40000000000000000),(483847066485340519/500000000000000000)⟩,(994685652049364679/1000000000000000000),(44155900327625973/125000000000000000),(27916298819312601/100000000000000000),(57881765120733057/250000000000000000)⟩
theorem valid2770 : certificate2770.Valid := by decide +kernel
theorem sound2770 : certificate2770.Sound := rat_cut_bin_certificate_sound certificate2770 profilesValid2770 numericValid2770 valid2770

def retention2771 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(4621035469487414478/9244737841268092559),(1830113057222738407/200000000000000000),(21/20),(83147619150228445549735676280431719793/83662311187325184320000000000000000000),false,MergedCutProfiles.Batch440.profile17635,(fun _ => MergedCutProfiles.Batch440.profile17635)⟩
theorem profilesValid2771 : retention2771.ProfilesValid := by
  exact MergedCutProfiles.Batch440.valid17635
theorem numericValid2771 : retention2771.NumericValid := by decide +kernel
def certificate2771 : RatCutBinCertificate := ⟨⟨retention2771,(2375668480937083231/1000000000000000000),(123364672097640231/500000000000000000),(4573138638309731967/250000000000000000),(13572511252097274473/40000000000000000),(192040070929926071/200000000000000000)⟩,(994685652049364679/1000000000000000000),(354061465274187313/1000000000000000000),(34789592014282799/125000000000000000),(231079205115118977/1000000000000000000)⟩
theorem valid2771 : certificate2771.Valid := by decide +kernel
theorem sound2771 : certificate2771.Sound := rat_cut_bin_certificate_sound certificate2771 profilesValid2771 numericValid2771 valid2771

def certificates : List RatCutBinCertificate := [certificate2760,certificate2761,certificate2762,certificate2763,certificate2764,certificate2765,certificate2766,certificate2767,certificate2768,certificate2769,certificate2770,certificate2771]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2760,List.forall_mem_cons.mpr ⟨sound2761,List.forall_mem_cons.mpr ⟨sound2762,List.forall_mem_cons.mpr ⟨sound2763,List.forall_mem_cons.mpr ⟨sound2764,List.forall_mem_cons.mpr ⟨sound2765,List.forall_mem_cons.mpr ⟨sound2766,List.forall_mem_cons.mpr ⟨sound2767,List.forall_mem_cons.mpr ⟨sound2768,List.forall_mem_cons.mpr ⟨sound2769,List.forall_mem_cons.mpr ⟨sound2770,List.forall_mem_cons.mpr ⟨sound2771,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch230
