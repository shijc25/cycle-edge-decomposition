import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch072
import Cycle12.MergedCutProfiles.Batch073
import Cycle12.MergedCutProfiles.Batch074
import Cycle12.MergedCutProfiles.Batch663
import Cycle12.MergedCutProfiles.Batch664

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch391

def retention4692 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(344697745461370009/1816613489158294724032),(682569792992811899/1000000000000000000),4,(50878679705868062397009301934673497/21330306031025371843750000000000000),false,MergedCutProfiles.Batch663.profile26538,(fun _ => MergedCutProfiles.Batch663.profile26538)⟩
theorem profilesValid4692 : retention4692.ProfilesValid := by
  exact MergedCutProfiles.Batch663.valid26538
theorem numericValid4692 : retention4692.NumericValid := by decide +kernel
def certificate4692 : RatCutBinCertificate := ⟨⟨retention4692,(1825428662414554083/1000000000000000000),(247684185361181/3906250000000000),(5424102969128447237/500000000000000000),(39518323636388087884083/1000000000000000000),(234259845829029981/100000000000000000)⟩,(249989163234205503/250000000000000000),(431272187161540077/500000000000000000),(9912325094747633/1000000000000000000),(597451867214757/125000000000000000)⟩
theorem valid4692 : certificate4692.Valid := by decide +kernel
theorem sound4692 : certificate4692.Sound := rat_cut_bin_certificate_sound certificate4692 profilesValid4692 numericValid4692 valid4692

def retention4693 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(40804042361842055/157966390361590845568),(344697745461370009/500000000000000000),4,(329363392456929140171275587543257667/137879098184548003600000000000000000),false,MergedCutProfiles.Batch663.profile26539,(fun _ => MergedCutProfiles.Batch663.profile26539)⟩
theorem profilesValid4693 : retention4693.ProfilesValid := by
  exact MergedCutProfiles.Batch663.valid26539
theorem numericValid4693 : retention4693.NumericValid := by decide +kernel
def certificate4693 : RatCutBinCertificate := ⟨⟨retention4693,(1825428662414554083/1000000000000000000),(247684185361181/3906250000000000),(5424102969128447237/500000000000000000),(39518323636388087884083/1000000000000000000),(1173052964405984011/500000000000000000)⟩,(249989163234205503/250000000000000000),(171798004852366909/200000000000000000),(2089047114569419/200000000000000000),(2525815509788753/500000000000000000)⟩
theorem valid4693 : certificate4693.Valid := by decide +kernel
theorem sound4693 : certificate4693.Sound := rat_cut_bin_certificate_sound certificate4693 profilesValid4693 numericValid4693 valid4693

def retention4694 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(3875536217917717/1599131592568921412),(187698594864473453/200000000000000000),(69/20),(6219661972514805530328516044270196193/2611458711157891520000000000000000000),false,MergedCutProfiles.Batch663.profile26540,(fun _ => MergedCutProfiles.Batch663.profile26540)⟩
theorem profilesValid4694 : retention4694.ProfilesValid := by
  exact MergedCutProfiles.Batch663.valid26540
theorem numericValid4694 : retention4694.NumericValid := by decide +kernel
def certificate4694 : RatCutBinCertificate := ⟨⟨retention4694,(1825428662414554083/1000000000000000000),(247684185361181/3906250000000000),(5424102969128447237/500000000000000000),(39518323636388087884083/1000000000000000000),(2344871256553709999/1000000000000000000)⟩,(249989163234205503/250000000000000000),(799296882495329473/1000000000000000000),(21642364160061653/1000000000000000000),(12157011929041987/1000000000000000000)⟩
theorem valid4694 : certificate4694.Valid := by decide +kernel
theorem sound4694 : certificate4694.Sound := rat_cut_bin_certificate_sound certificate4694 profilesValid4694 numericValid4694 valid4694

def retention4695 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(1/40),(275163071472157907/31250000000000000),(6/5),(1930962996078667698469043840552274474039/880521828710905302400000000000000000000),false,MergedCutProfiles.Batch663.profile26541,(fun _ => MergedCutProfiles.Batch663.profile26541)⟩
theorem profilesValid4695 : retention4695.ProfilesValid := by
  exact MergedCutProfiles.Batch663.valid26541
theorem numericValid4695 : retention4695.NumericValid := by decide +kernel
def certificate4695 : RatCutBinCertificate := ⟨⟨retention4695,(1825428662414554083/1000000000000000000),(247684185361181/3906250000000000),(5424102969128447237/500000000000000000),(39518323636388087884083/1000000000000000000),(2180172290482009453/1000000000000000000)⟩,(249989163234205503/250000000000000000),(43733070838259579/62500000000000000),(10084840594864303/200000000000000000),(39083352968488089/500000000000000000)⟩
theorem valid4695 : certificate4695.Valid := by decide +kernel
theorem sound4695 : certificate4695.Sound := rat_cut_bin_certificate_sound certificate4695 profilesValid4695 numericValid4695 valid4695

def retention4696 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(618631253773969523/3528875145859914008935),(577008539601093049/1000000000000000000),4,(256943425202135255878239318113349519/115401707920218609800000000000000000),true,MergedCutProfiles.Batch663.profile26542,![MergedCutProfiles.Batch663.profile26542,MergedCutProfiles.Batch663.profile26543,MergedCutProfiles.Batch663.profile26544,MergedCutProfiles.Batch663.profile26545,MergedCutProfiles.Batch663.profile26546,MergedCutProfiles.Batch663.profile26547,MergedCutProfiles.Batch663.profile26548,MergedCutProfiles.Batch663.profile26549,MergedCutProfiles.Batch663.profile26550,MergedCutProfiles.Batch663.profile26551,MergedCutProfiles.Batch663.profile26552,MergedCutProfiles.Batch663.profile26553,MergedCutProfiles.Batch663.profile26554,MergedCutProfiles.Batch663.profile26555,MergedCutProfiles.Batch663.profile26556,MergedCutProfiles.Batch663.profile26557]⟩
theorem profilesValid4696 : retention4696.ProfilesValid := by
  change ∀ j : Fin 16, (retention4696.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch663.valid26542
  · exact MergedCutProfiles.Batch663.valid26543
  · exact MergedCutProfiles.Batch663.valid26544
  · exact MergedCutProfiles.Batch663.valid26545
  · exact MergedCutProfiles.Batch663.valid26546
  · exact MergedCutProfiles.Batch663.valid26547
  · exact MergedCutProfiles.Batch663.valid26548
  · exact MergedCutProfiles.Batch663.valid26549
  · exact MergedCutProfiles.Batch663.valid26550
  · exact MergedCutProfiles.Batch663.valid26551
  · exact MergedCutProfiles.Batch663.valid26552
  · exact MergedCutProfiles.Batch663.valid26553
  · exact MergedCutProfiles.Batch663.valid26554
  · exact MergedCutProfiles.Batch663.valid26555
  · exact MergedCutProfiles.Batch663.valid26556
  · exact MergedCutProfiles.Batch663.valid26557
theorem numericValid4696 : retention4696.NumericValid := by decide +kernel
def certificate4696 : RatCutBinCertificate := ⟨⟨retention4696,(37576464488369051/20000000000000000),(65254397982896969/1000000000000000000),(683116614197489133/62500000000000000),(19336270263458644086213/500000000000000000),(2181644730952792379/1000000000000000000)⟩,(999954497485985609/1000000000000000000),(707335149026722231/1000000000000000000),(4774957355279751/100000000000000000),(1053203416834051/50000000000000000)⟩
theorem valid4696 : certificate4696.Valid := by decide +kernel
theorem sound4696 : certificate4696.Sound := rat_cut_bin_certificate_sound certificate4696 profilesValid4696 numericValid4696 valid4696

def retention4697 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(230145495800000000/705775029171982801787),(618631253773969523/1000000000000000000),4,(589766009988745341683/256000000000000000000),true,MergedCutProfiles.Batch663.profile26543,![MergedCutProfiles.Batch663.profile26543,MergedCutProfiles.Batch663.profile26545,MergedCutProfiles.Batch663.profile26547,MergedCutProfiles.Batch663.profile26558,MergedCutProfiles.Batch663.profile26550,MergedCutProfiles.Batch663.profile26552,MergedCutProfiles.Batch663.profile26554,MergedCutProfiles.Batch663.profile26556,MergedCutProfiles.Batch663.profile26557,MergedCutProfiles.Batch663.profile26559,MergedCutProfiles.Batch664.profile26560,MergedCutProfiles.Batch664.profile26561,MergedCutProfiles.Batch664.profile26562,MergedCutProfiles.Batch664.profile26563,MergedCutProfiles.Batch664.profile26564,MergedCutProfiles.Batch664.profile26565]⟩
theorem profilesValid4697 : retention4697.ProfilesValid := by
  change ∀ j : Fin 16, (retention4697.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch663.valid26543
  · exact MergedCutProfiles.Batch663.valid26545
  · exact MergedCutProfiles.Batch663.valid26547
  · exact MergedCutProfiles.Batch663.valid26558
  · exact MergedCutProfiles.Batch663.valid26550
  · exact MergedCutProfiles.Batch663.valid26552
  · exact MergedCutProfiles.Batch663.valid26554
  · exact MergedCutProfiles.Batch663.valid26556
  · exact MergedCutProfiles.Batch663.valid26557
  · exact MergedCutProfiles.Batch663.valid26559
  · exact MergedCutProfiles.Batch664.valid26560
  · exact MergedCutProfiles.Batch664.valid26561
  · exact MergedCutProfiles.Batch664.valid26562
  · exact MergedCutProfiles.Batch664.valid26563
  · exact MergedCutProfiles.Batch664.valid26564
  · exact MergedCutProfiles.Batch664.valid26565
theorem numericValid4697 : retention4697.NumericValid := by decide +kernel
def certificate4697 : RatCutBinCertificate := ⟨⟨retention4697,(37576464488369051/20000000000000000),(65254397982896969/1000000000000000000),(683116614197489133/62500000000000000),(19336270263458644086213/500000000000000000),(451781003295744701/200000000000000000)⟩,(999954497485985609/1000000000000000000),(326058629920021001/500000000000000000),(69082469647993273/1000000000000000000),(31761966032887221/1000000000000000000)⟩
theorem valid4697 : certificate4697.Valid := by decide +kernel
theorem sound4697 : certificate4697.Sound := rat_cut_bin_certificate_sound certificate4697 profilesValid4697 numericValid4697 valid4697

def retention4698 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(2394080181874437914/3528875145859914008935),(1150727479/1000000000),(11/4),(10994793705880876623730355335477342951/4602909916000000000000000000000000000),true,MergedCutProfiles.Batch663.profile26545,![MergedCutProfiles.Batch663.profile26545,MergedCutProfiles.Batch663.profile26558,MergedCutProfiles.Batch663.profile26553,MergedCutProfiles.Batch663.profile26556,MergedCutProfiles.Batch663.profile26559,MergedCutProfiles.Batch664.profile26561,MergedCutProfiles.Batch664.profile26564,MergedCutProfiles.Batch664.profile26566,MergedCutProfiles.Batch664.profile26567,MergedCutProfiles.Batch664.profile26568,MergedCutProfiles.Batch664.profile26569,MergedCutProfiles.Batch664.profile26570,MergedCutProfiles.Batch664.profile26571,MergedCutProfiles.Batch664.profile26572,MergedCutProfiles.Batch664.profile26573,MergedCutProfiles.Batch664.profile26574]⟩
theorem profilesValid4698 : retention4698.ProfilesValid := by
  change ∀ j : Fin 16, (retention4698.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch663.valid26545
  · exact MergedCutProfiles.Batch663.valid26558
  · exact MergedCutProfiles.Batch663.valid26553
  · exact MergedCutProfiles.Batch663.valid26556
  · exact MergedCutProfiles.Batch663.valid26559
  · exact MergedCutProfiles.Batch664.valid26561
  · exact MergedCutProfiles.Batch664.valid26564
  · exact MergedCutProfiles.Batch664.valid26566
  · exact MergedCutProfiles.Batch664.valid26567
  · exact MergedCutProfiles.Batch664.valid26568
  · exact MergedCutProfiles.Batch664.valid26569
  · exact MergedCutProfiles.Batch664.valid26570
  · exact MergedCutProfiles.Batch664.valid26571
  · exact MergedCutProfiles.Batch664.valid26572
  · exact MergedCutProfiles.Batch664.valid26573
  · exact MergedCutProfiles.Batch664.valid26574
theorem numericValid4698 : retention4698.NumericValid := by decide +kernel
def certificate4698 : RatCutBinCertificate := ⟨⟨retention4698,(37576464488369051/20000000000000000),(65254397982896969/1000000000000000000),(683116614197489133/62500000000000000),(19336270263458644086213/500000000000000000),(294726804831067297/125000000000000000)⟩,(999954497485985609/1000000000000000000),(217113499159609243/500000000000000000),(203545654007457467/1000000000000000000),(137306555148988483/1000000000000000000)⟩
theorem valid4698 : certificate4698.Valid := by decide +kernel
theorem sound4698 : certificate4698.Sound := rat_cut_bin_certificate_sound certificate4698 profilesValid4698 numericValid4698 valid4698

def retention4699 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(12800000000000000000/705775029171982801787),(1197040090937218957/500000000000000000),(17/10),(132407386603552847728215368233556109601/59852004546860947850000000000000000000),true,MergedCutProfiles.Batch664.profile26575,![MergedCutProfiles.Batch664.profile26575,MergedCutProfiles.Batch664.profile26576,MergedCutProfiles.Batch073.profile2937,MergedCutProfiles.Batch664.profile26577,MergedCutProfiles.Batch664.profile26578,MergedCutProfiles.Batch073.profile2939,MergedCutProfiles.Batch664.profile26579,MergedCutProfiles.Batch664.profile26580,MergedCutProfiles.Batch073.profile2941,MergedCutProfiles.Batch664.profile26581,MergedCutProfiles.Batch072.profile2912,MergedCutProfiles.Batch073.profile2943,MergedCutProfiles.Batch664.profile26582,MergedCutProfiles.Batch664.profile26583,MergedCutProfiles.Batch073.profile2945,MergedCutProfiles.Batch664.profile26584]⟩
theorem profilesValid4699 : retention4699.ProfilesValid := by
  change ∀ j : Fin 16, (retention4699.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch664.valid26575
  · exact MergedCutProfiles.Batch664.valid26576
  · exact MergedCutProfiles.Batch073.valid2937
  · exact MergedCutProfiles.Batch664.valid26577
  · exact MergedCutProfiles.Batch664.valid26578
  · exact MergedCutProfiles.Batch073.valid2939
  · exact MergedCutProfiles.Batch664.valid26579
  · exact MergedCutProfiles.Batch664.valid26580
  · exact MergedCutProfiles.Batch073.valid2941
  · exact MergedCutProfiles.Batch664.valid26581
  · exact MergedCutProfiles.Batch072.valid2912
  · exact MergedCutProfiles.Batch073.valid2943
  · exact MergedCutProfiles.Batch664.valid26582
  · exact MergedCutProfiles.Batch664.valid26583
  · exact MergedCutProfiles.Batch073.valid2945
  · exact MergedCutProfiles.Batch664.valid26584
theorem numericValid4699 : retention4699.NumericValid := by decide +kernel
def certificate4699 : RatCutBinCertificate := ⟨⟨retention4699,(37576464488369051/20000000000000000),(65254397982896969/1000000000000000000),(683116614197489133/62500000000000000),(19336270263458644086213/500000000000000000),(438635478663949319/200000000000000000)⟩,(999954497485985609/1000000000000000000),(68628316669015139/200000000000000000),(289822961142149843/1000000000000000000),(17743332090190661/62500000000000000)⟩
theorem valid4699 : certificate4699.Valid := by decide +kernel
theorem sound4699 : certificate4699.Sound := rat_cut_bin_certificate_sound certificate4699 profilesValid4699 numericValid4699 valid4699

def retention4700 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(1/2),64,1,(255381992356603435538601844252787218879/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch074.profile2982,(fun _ => MergedCutProfiles.Batch074.profile2982)⟩
theorem profilesValid4700 : retention4700.ProfilesValid := by
  exact MergedCutProfiles.Batch074.valid2982
theorem numericValid4700 : retention4700.NumericValid := by decide +kernel
def certificate4700 : RatCutBinCertificate := ⟨⟨retention4700,(37576464488369051/20000000000000000),(65254397982896969/1000000000000000000),(683116614197489133/62500000000000000),(19336270263458644086213/500000000000000000),(986368799986139779/1000000000000000000)⟩,(999954497485985609/1000000000000000000),(258986673594499761/500000000000000000),(141287446919050351/1000000000000000000),(137239984740023499/1000000000000000000)⟩
theorem valid4700 : certificate4700.Valid := by decide +kernel
theorem sound4700 : certificate4700.Sound := rat_cut_bin_certificate_sound certificate4700 profilesValid4700 numericValid4700 valid4700

def retention4701 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(12800000000000000000/705775029171982801787),(29072842144476235131/1000000000000000000),1,(63859086659083311735728121797994839561/29072842144476235131000000000000000000),false,MergedCutProfiles.Batch664.profile26585,(fun _ => MergedCutProfiles.Batch664.profile26585)⟩
theorem profilesValid4701 : retention4701.ProfilesValid := by
  exact MergedCutProfiles.Batch664.valid26585
theorem numericValid4701 : retention4701.NumericValid := by decide +kernel
def certificate4701 : RatCutBinCertificate := ⟨⟨retention4701,(35103164328369051/20000000000000000),(65254397982896969/1000000000000000000),(683116614197489133/62500000000000000),(19336270263458644086213/500000000000000000),(2186041462822048311/1000000000000000000)⟩,(999957492490986491/1000000000000000000),(21579372823169491/1000000000000000000),(108652409643566959/125000000000000000),(110449294115109061/62500000000000000)⟩
theorem valid4701 : certificate4701.Valid := by decide +kernel
theorem sound4701 : certificate4701.Sound := rat_cut_bin_certificate_sound certificate4701 profilesValid4701 numericValid4701 valid4701

def retention4702 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(1/2),64,1,(255381992356603435538601844252787218879/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch074.profile2982,(fun _ => MergedCutProfiles.Batch074.profile2982)⟩
theorem profilesValid4702 : retention4702.ProfilesValid := by
  exact MergedCutProfiles.Batch074.valid2982
theorem numericValid4702 : retention4702.NumericValid := by decide +kernel
def certificate4702 : RatCutBinCertificate := ⟨⟨retention4702,(35103164328369051/20000000000000000),(65254397982896969/1000000000000000000),(683116614197489133/62500000000000000),(19336270263458644086213/500000000000000000),(987107115166669677/1000000000000000000)⟩,(999957492490986491/1000000000000000000),(23894774441565401/500000000000000000),(794324011209107021/1000000000000000000),(386070040666466723/500000000000000000)⟩
theorem valid4702 : certificate4702.Valid := by decide +kernel
theorem sound4702 : certificate4702.Sound := rat_cut_bin_certificate_sound certificate4702 profilesValid4702 numericValid4702 valid4702

def retention4703 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(19750433001800019/100825004167426114541),(684420945606931351/1000000000000000000),4,(10211980041454492617909626603289381/4277630910043320943750000000000000),false,MergedCutProfiles.Batch664.profile26586,(fun _ => MergedCutProfiles.Batch664.profile26586)⟩
theorem profilesValid4703 : retention4703.ProfilesValid := by
  exact MergedCutProfiles.Batch664.valid26586
theorem numericValid4703 : retention4703.NumericValid := by decide +kernel
def certificate4703 : RatCutBinCertificate := ⟨⟨retention4703,(36590640528369051/20000000000000000),(65254397982896969/1000000000000000000),(683116614197489133/62500000000000000),(19336270263458644086213/500000000000000000),(58590168733857497/25000000000000000)⟩,(499977845627288933/500000000000000000),(429662090036706533/500000000000000000),(10394509554304801/1000000000000000000),(5016286585067977/1000000000000000000)⟩
theorem valid4703 : certificate4703.Valid := by decide +kernel
theorem sound4703 : certificate4703.Sound := rat_cut_bin_certificate_sound certificate4703 profilesValid4703 numericValid4703 valid4703

def certificates : List RatCutBinCertificate := [certificate4692,certificate4693,certificate4694,certificate4695,certificate4696,certificate4697,certificate4698,certificate4699,certificate4700,certificate4701,certificate4702,certificate4703]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4692,List.forall_mem_cons.mpr ⟨sound4693,List.forall_mem_cons.mpr ⟨sound4694,List.forall_mem_cons.mpr ⟨sound4695,List.forall_mem_cons.mpr ⟨sound4696,List.forall_mem_cons.mpr ⟨sound4697,List.forall_mem_cons.mpr ⟨sound4698,List.forall_mem_cons.mpr ⟨sound4699,List.forall_mem_cons.mpr ⟨sound4700,List.forall_mem_cons.mpr ⟨sound4701,List.forall_mem_cons.mpr ⟨sound4702,List.forall_mem_cons.mpr ⟨sound4703,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch391
