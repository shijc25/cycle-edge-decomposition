import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch253
import Cycle12.MergedCutProfiles.Batch255
import Cycle12.MergedCutProfiles.Batch542
import Cycle12.MergedCutProfiles.Batch543
import Cycle12.MergedCutProfiles.Batch544

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch294

def retention3528 : RatCutRetentionCertificate := ⟨(63/1000),(253/4000),(27441126006110706159/55065286028488616857),(1583838717041643617/62500000000000000),1,(201716247441821989394315301079251051/202731355781330382976000000000000000),false,MergedCutProfiles.Batch542.profile21703,(fun _ => MergedCutProfiles.Batch542.profile21703)⟩
theorem profilesValid3528 : retention3528.ProfilesValid := by
  exact MergedCutProfiles.Batch542.valid21703
theorem numericValid3528 : retention3528.NumericValid := by decide +kernel
def certificate3528 : RatCutBinCertificate := ⟨⟨retention3528,(231018176461169197/100000000000000000),(206867685175350651/1000000000000000000),(838835508587079997/50000000000000000),(462629335143013743249/500000000000000000),(966506553607559823/1000000000000000000)⟩,(99801379524132609/100000000000000000),(6216561126590823/50000000000000000),(122919438798308583/200000000000000000),(571024416972910581/1000000000000000000)⟩
theorem valid3528 : certificate3528.Valid := by decide +kernel
theorem sound3528 : certificate3528.Sound := rat_cut_bin_certificate_sound certificate3528 profilesValid3528 numericValid3528 valid3528

def retention3529 : RatCutRetentionCertificate := ⟨(63/1000),(253/4000),(1/2),(27441126006110706159/1000000000000000000),1,(108939724495742659417160675583213543683/109764504024442824636000000000000000000),false,MergedCutProfiles.Batch542.profile21701,(fun _ => MergedCutProfiles.Batch542.profile21701)⟩
theorem profilesValid3529 : retention3529.ProfilesValid := by
  exact MergedCutProfiles.Batch542.valid21701
theorem numericValid3529 : retention3529.NumericValid := by decide +kernel
def certificate3529 : RatCutBinCertificate := ⟨⟨retention3529,(231018176461169197/100000000000000000),(206867685175350651/1000000000000000000),(838835508587079997/50000000000000000),(462629335143013743249/500000000000000000),(240999912612555919/250000000000000000)⟩,(99801379524132609/100000000000000000),(62327274361001109/500000000000000000),(613938059964636937/1000000000000000000),(5705887655225141/10000000000000000)⟩
theorem valid3529 : certificate3529.Valid := by decide +kernel
theorem sound3529 : certificate3529.Sound := rat_cut_bin_certificate_sound certificate3529 profilesValid3529 numericValid3529 valid3529

def retention3530 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(923220386101259007/54547126863153105821),(914079590199266343/1000000000000000000),(57/20),(566747316098537931163/256000000000000000000),true,MergedCutProfiles.Batch542.profile21704,![MergedCutProfiles.Batch542.profile21704,MergedCutProfiles.Batch542.profile21705,MergedCutProfiles.Batch542.profile21706,MergedCutProfiles.Batch542.profile21707,MergedCutProfiles.Batch253.profile10134,MergedCutProfiles.Batch542.profile21708,MergedCutProfiles.Batch542.profile21709,MergedCutProfiles.Batch542.profile21710,MergedCutProfiles.Batch542.profile21711,MergedCutProfiles.Batch542.profile21712,MergedCutProfiles.Batch542.profile21713,MergedCutProfiles.Batch542.profile21714,MergedCutProfiles.Batch542.profile21715,MergedCutProfiles.Batch542.profile21716,MergedCutProfiles.Batch253.profile10136,MergedCutProfiles.Batch542.profile21717]⟩
theorem profilesValid3530 : retention3530.ProfilesValid := by
  change ∀ j : Fin 16, (retention3530.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch542.valid21704
  · exact MergedCutProfiles.Batch542.valid21705
  · exact MergedCutProfiles.Batch542.valid21706
  · exact MergedCutProfiles.Batch542.valid21707
  · exact MergedCutProfiles.Batch253.valid10134
  · exact MergedCutProfiles.Batch542.valid21708
  · exact MergedCutProfiles.Batch542.valid21709
  · exact MergedCutProfiles.Batch542.valid21710
  · exact MergedCutProfiles.Batch542.valid21711
  · exact MergedCutProfiles.Batch542.valid21712
  · exact MergedCutProfiles.Batch542.valid21713
  · exact MergedCutProfiles.Batch542.valid21714
  · exact MergedCutProfiles.Batch542.valid21715
  · exact MergedCutProfiles.Batch542.valid21716
  · exact MergedCutProfiles.Batch253.valid10136
  · exact MergedCutProfiles.Batch542.valid21717
theorem numericValid3530 : retention3530.NumericValid := by decide +kernel
def certificate3530 : RatCutBinCertificate := ⟨⟨retention3530,(2255155270266006051/1000000000000000000),(2610492019033761/12500000000000000),(16855991791084864887/1000000000000000000),(920885892078861988323/1000000000000000000),(533554821917860539/250000000000000000)⟩,(998056705642839609/1000000000000000000),(306485884750931169/1000000000000000000),(33104960976767709/100000000000000000),(48026532257948451/250000000000000000)⟩
theorem valid3530 : certificate3530.Valid := by decide +kernel
theorem sound3530 : certificate3530.Sound := rat_cut_bin_certificate_sound certificate3530 profilesValid3530 numericValid3530 valid3530

def retention3531 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(1082548509300548047/54547126863153105821),(923220386101259007/1000000000000000000),(57/20),(88249063720982386137/40000000000000000000),true,MergedCutProfiles.Batch542.profile21718,![MergedCutProfiles.Batch542.profile21718,MergedCutProfiles.Batch542.profile21719,MergedCutProfiles.Batch543.profile21720,MergedCutProfiles.Batch543.profile21721,MergedCutProfiles.Batch543.profile21722,MergedCutProfiles.Batch542.profile21709,MergedCutProfiles.Batch543.profile21723,MergedCutProfiles.Batch543.profile21724,MergedCutProfiles.Batch543.profile21725,MergedCutProfiles.Batch543.profile21726,MergedCutProfiles.Batch543.profile21727,MergedCutProfiles.Batch542.profile21716,MergedCutProfiles.Batch543.profile21728,MergedCutProfiles.Batch543.profile21729,MergedCutProfiles.Batch543.profile21730,MergedCutProfiles.Batch543.profile21731]⟩
theorem profilesValid3531 : retention3531.ProfilesValid := by
  change ∀ j : Fin 16, (retention3531.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch542.valid21718
  · exact MergedCutProfiles.Batch542.valid21719
  · exact MergedCutProfiles.Batch543.valid21720
  · exact MergedCutProfiles.Batch543.valid21721
  · exact MergedCutProfiles.Batch543.valid21722
  · exact MergedCutProfiles.Batch542.valid21709
  · exact MergedCutProfiles.Batch543.valid21723
  · exact MergedCutProfiles.Batch543.valid21724
  · exact MergedCutProfiles.Batch543.valid21725
  · exact MergedCutProfiles.Batch543.valid21726
  · exact MergedCutProfiles.Batch543.valid21727
  · exact MergedCutProfiles.Batch542.valid21716
  · exact MergedCutProfiles.Batch543.valid21728
  · exact MergedCutProfiles.Batch543.valid21729
  · exact MergedCutProfiles.Batch543.valid21730
  · exact MergedCutProfiles.Batch543.valid21731
theorem numericValid3531 : retention3531.NumericValid := by decide +kernel
def certificate3531 : RatCutBinCertificate := ⟨⟨retention3531,(2255155270266006051/1000000000000000000),(2610492019033761/12500000000000000),(16855991791084864887/1000000000000000000),(920885892078861988323/1000000000000000000),(1063294622909754457/500000000000000000)⟩,(998056705642839609/1000000000000000000),(306213941547092421/1000000000000000000),(82842795969260083/250000000000000000),(9609125860697181/50000000000000000)⟩
theorem valid3531 : certificate3531.Valid := by decide +kernel
theorem sound3531 : certificate3531.Sound := rat_cut_bin_certificate_sound certificate3531 profilesValid3531 numericValid3531 valid3531

def retention3532 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(1112528109000000000/54547126863153105821),(1082548509300548047/1000000000000000000),(5/2),(35090733789190946521/16000000000000000000),true,MergedCutProfiles.Batch543.profile21732,![MergedCutProfiles.Batch543.profile21732,MergedCutProfiles.Batch543.profile21733,MergedCutProfiles.Batch543.profile21734,MergedCutProfiles.Batch543.profile21735,MergedCutProfiles.Batch542.profile21708,MergedCutProfiles.Batch543.profile21736,MergedCutProfiles.Batch543.profile21737,MergedCutProfiles.Batch543.profile21738,MergedCutProfiles.Batch543.profile21739,MergedCutProfiles.Batch543.profile21740,MergedCutProfiles.Batch543.profile21741,MergedCutProfiles.Batch543.profile21742,MergedCutProfiles.Batch543.profile21743,MergedCutProfiles.Batch543.profile21744,MergedCutProfiles.Batch543.profile21745,MergedCutProfiles.Batch543.profile21746]⟩
theorem profilesValid3532 : retention3532.ProfilesValid := by
  change ∀ j : Fin 16, (retention3532.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch543.valid21732
  · exact MergedCutProfiles.Batch543.valid21733
  · exact MergedCutProfiles.Batch543.valid21734
  · exact MergedCutProfiles.Batch543.valid21735
  · exact MergedCutProfiles.Batch542.valid21708
  · exact MergedCutProfiles.Batch543.valid21736
  · exact MergedCutProfiles.Batch543.valid21737
  · exact MergedCutProfiles.Batch543.valid21738
  · exact MergedCutProfiles.Batch543.valid21739
  · exact MergedCutProfiles.Batch543.valid21740
  · exact MergedCutProfiles.Batch543.valid21741
  · exact MergedCutProfiles.Batch543.valid21742
  · exact MergedCutProfiles.Batch543.valid21743
  · exact MergedCutProfiles.Batch543.valid21744
  · exact MergedCutProfiles.Batch543.valid21745
  · exact MergedCutProfiles.Batch543.valid21746
theorem numericValid3532 : retention3532.NumericValid := by decide +kernel
def certificate3532 : RatCutBinCertificate := ⟨⟨retention3532,(2255155270266006051/1000000000000000000),(2610492019033761/12500000000000000),(16855991791084864887/1000000000000000000),(920885892078861988323/1000000000000000000),(414709708395741/195312500000000)⟩,(998056705642839609/1000000000000000000),(143234136280708577/500000000000000000),(355376900428851749/1000000000000000000),(14325199608059329/62500000000000000)⟩
theorem valid3532 : certificate3532.Valid := by decide +kernel
theorem sound3532 : certificate3532.Sound := rat_cut_bin_certificate_sound certificate3532 profilesValid3532 numericValid3532 valid3532

def retention3533 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(1388294844485234123/54547126863153105821),(1112528109/1000000000),(49/20),(8687277103000455867/4000000000000000000),true,MergedCutProfiles.Batch543.profile21747,![MergedCutProfiles.Batch543.profile21747,MergedCutProfiles.Batch542.profile21706,MergedCutProfiles.Batch543.profile21748,MergedCutProfiles.Batch542.profile21708,MergedCutProfiles.Batch543.profile21749,MergedCutProfiles.Batch543.profile21750,MergedCutProfiles.Batch543.profile21725,MergedCutProfiles.Batch543.profile21740,MergedCutProfiles.Batch543.profile21751,MergedCutProfiles.Batch543.profile21752,MergedCutProfiles.Batch543.profile21753,MergedCutProfiles.Batch543.profile21754,MergedCutProfiles.Batch543.profile21755,MergedCutProfiles.Batch543.profile21756,MergedCutProfiles.Batch543.profile21757,MergedCutProfiles.Batch543.profile21758]⟩
theorem profilesValid3533 : retention3533.ProfilesValid := by
  change ∀ j : Fin 16, (retention3533.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch543.valid21747
  · exact MergedCutProfiles.Batch542.valid21706
  · exact MergedCutProfiles.Batch543.valid21748
  · exact MergedCutProfiles.Batch542.valid21708
  · exact MergedCutProfiles.Batch543.valid21749
  · exact MergedCutProfiles.Batch543.valid21750
  · exact MergedCutProfiles.Batch543.valid21725
  · exact MergedCutProfiles.Batch543.valid21740
  · exact MergedCutProfiles.Batch543.valid21751
  · exact MergedCutProfiles.Batch543.valid21752
  · exact MergedCutProfiles.Batch543.valid21753
  · exact MergedCutProfiles.Batch543.valid21754
  · exact MergedCutProfiles.Batch543.valid21755
  · exact MergedCutProfiles.Batch543.valid21756
  · exact MergedCutProfiles.Batch543.valid21757
  · exact MergedCutProfiles.Batch543.valid21758
theorem numericValid3533 : retention3533.NumericValid := by decide +kernel
def certificate3533 : RatCutBinCertificate := ⟨⟨retention3533,(2255155270266006051/1000000000000000000),(2610492019033761/12500000000000000),(16855991791084864887/1000000000000000000),(920885892078861988323/1000000000000000000),(210335930467245049/100000000000000000)⟩,(998056705642839609/1000000000000000000),(285999079143967337/1000000000000000000),(177981712939950633/500000000000000000),(231863603450195783/1000000000000000000)⟩
theorem valid3533 : certificate3533.Valid := by decide +kernel
theorem sound3533 : certificate3533.Sound := rat_cut_bin_certificate_sound certificate3533 profilesValid3533 numericValid3533 valid3533

def retention3534 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(5319455394636632899/54547126863153105821),(1388294844485234123/1000000000000000000),(21/10),(2459575174570088275839/1280000000000000000000),true,MergedCutProfiles.Batch543.profile21759,![MergedCutProfiles.Batch543.profile21759,MergedCutProfiles.Batch544.profile21760,MergedCutProfiles.Batch544.profile21761,MergedCutProfiles.Batch544.profile21762,MergedCutProfiles.Batch544.profile21763,MergedCutProfiles.Batch544.profile21764,MergedCutProfiles.Batch544.profile21765,MergedCutProfiles.Batch544.profile21766,MergedCutProfiles.Batch544.profile21767,MergedCutProfiles.Batch544.profile21768,MergedCutProfiles.Batch544.profile21769,MergedCutProfiles.Batch544.profile21770,MergedCutProfiles.Batch544.profile21771,MergedCutProfiles.Batch544.profile21772,MergedCutProfiles.Batch544.profile21773,MergedCutProfiles.Batch544.profile21774]⟩
theorem profilesValid3534 : retention3534.ProfilesValid := by
  change ∀ j : Fin 16, (retention3534.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch543.valid21759
  · exact MergedCutProfiles.Batch544.valid21760
  · exact MergedCutProfiles.Batch544.valid21761
  · exact MergedCutProfiles.Batch544.valid21762
  · exact MergedCutProfiles.Batch544.valid21763
  · exact MergedCutProfiles.Batch544.valid21764
  · exact MergedCutProfiles.Batch544.valid21765
  · exact MergedCutProfiles.Batch544.valid21766
  · exact MergedCutProfiles.Batch544.valid21767
  · exact MergedCutProfiles.Batch544.valid21768
  · exact MergedCutProfiles.Batch544.valid21769
  · exact MergedCutProfiles.Batch544.valid21770
  · exact MergedCutProfiles.Batch544.valid21771
  · exact MergedCutProfiles.Batch544.valid21772
  · exact MergedCutProfiles.Batch544.valid21773
  · exact MergedCutProfiles.Batch544.valid21774
theorem numericValid3534 : retention3534.NumericValid := by decide +kernel
def certificate3534 : RatCutBinCertificate := ⟨⟨retention3534,(2255155270266006051/1000000000000000000),(2610492019033761/12500000000000000),(16855991791084864887/1000000000000000000),(920885892078861988323/1000000000000000000),(1862863447616353919/1000000000000000000)⟩,(998056705642839609/1000000000000000000),(37138993797383481/125000000000000000),(68454876742589743/200000000000000000),(23225941266631159/100000000000000000)⟩
theorem valid3534 : certificate3534.Valid := by decide +kernel
theorem sound3534 : certificate3534.Sound := rat_cut_bin_certificate_sound certificate3534 profilesValid3534 numericValid3534 valid3534

def retention3535 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(22514710653490610171/54547126863153105821),(5319455394636632899/1000000000000000000),(11/10),(2466909072621108588706835025822069930319/2127782157854653159600000000000000000000),false,MergedCutProfiles.Batch544.profile21775,(fun _ => MergedCutProfiles.Batch544.profile21775)⟩
theorem profilesValid3535 : retention3535.ProfilesValid := by
  exact MergedCutProfiles.Batch544.valid21775
theorem numericValid3535 : retention3535.NumericValid := by decide +kernel
def certificate3535 : RatCutBinCertificate := ⟨⟨retention3535,(2255155270266006051/1000000000000000000),(2610492019033761/12500000000000000),(16855991791084864887/1000000000000000000),(920885892078861988323/1000000000000000000),(1128644703474088181/1000000000000000000)⟩,(998056705642839609/1000000000000000000),(72677072276367251/200000000000000000),(134379397822035943/500000000000000000),(46823340007624869/200000000000000000)⟩
theorem valid3535 : certificate3535.Valid := by decide +kernel
theorem sound3535 : certificate3535.Sound := rat_cut_bin_certificate_sound certificate3535 profilesValid3535 numericValid3535 valid3535

def retention3536 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(26930914313988453959/54547126863153105821),(22514710653490610171/1000000000000000000),1,(90311117491324759168234868830012760283/90058842613962440684000000000000000000),false,MergedCutProfiles.Batch544.profile21776,(fun _ => MergedCutProfiles.Batch544.profile21776)⟩
theorem profilesValid3536 : retention3536.ProfilesValid := by
  exact MergedCutProfiles.Batch544.valid21776
theorem numericValid3536 : retention3536.NumericValid := by decide +kernel
def certificate3536 : RatCutBinCertificate := ⟨⟨retention3536,(2255155270266006051/1000000000000000000),(2610492019033761/12500000000000000),(16855991791084864887/1000000000000000000),(920885892078861988323/1000000000000000000),(974860420647943297/1000000000000000000)⟩,(998056705642839609/1000000000000000000),(381049996212203639/1000000000000000000),(125650595615888677/500000000000000000),(234346880881690741/1000000000000000000)⟩
theorem valid3536 : certificate3536.Valid := by decide +kernel
theorem sound3536 : certificate3536.Sound := rat_cut_bin_certificate_sound certificate3536 profilesValid3536 numericValid3536 valid3536

def retention3537 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(27200223457128338499/54547126863153105821),(26930914313988453959/1000000000000000000),1,(334939156847654341200431333498475179/336636428924855674487500000000000000),false,MergedCutProfiles.Batch544.profile21777,(fun _ => MergedCutProfiles.Batch544.profile21777)⟩
theorem profilesValid3537 : retention3537.ProfilesValid := by
  exact MergedCutProfiles.Batch544.valid21777
theorem numericValid3537 : retention3537.NumericValid := by decide +kernel
def certificate3537 : RatCutBinCertificate := ⟨⟨retention3537,(2255155270266006051/1000000000000000000),(2610492019033761/12500000000000000),(16855991791084864887/1000000000000000000),(920885892078861988323/1000000000000000000),(967017389019566657/1000000000000000000)⟩,(998056705642839609/1000000000000000000),(95528078820014827/250000000000000000),(250277792139181459/1000000000000000000),(233168801075909397/1000000000000000000)⟩
theorem valid3537 : certificate3537.Valid := by decide +kernel
theorem sound3537 : certificate3537.Sound := rat_cut_bin_certificate_sound certificate3537 profilesValid3537 numericValid3537 valid3537

def retention3538 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(1/2),(27200223457128338499/1000000000000000000),1,(107974721011807929285315329208886014779/108800893828513353996000000000000000000),false,MergedCutProfiles.Batch255.profile10215,(fun _ => MergedCutProfiles.Batch255.profile10215)⟩
theorem profilesValid3538 : retention3538.ProfilesValid := by
  exact MergedCutProfiles.Batch255.valid10215
theorem numericValid3538 : retention3538.NumericValid := by decide +kernel
def certificate3538 : RatCutBinCertificate := ⟨⟨retention3538,(2255155270266006051/1000000000000000000),(2610492019033761/12500000000000000),(16855991791084864887/1000000000000000000),(920885892078861988323/1000000000000000000),(964465808622291407/1000000000000000000)⟩,(998056705642839609/1000000000000000000),(95755144646160639/250000000000000000),(249405145294683069/1000000000000000000),(231843378002389939/1000000000000000000)⟩
theorem valid3538 : certificate3538.Valid := by decide +kernel
theorem sound3538 : certificate3538.Sound := rat_cut_bin_certificate_sound certificate3538 profilesValid3538 numericValid3538 valid3538

def retention3539 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(25079180970385413099/54547126863153105821),(1782052406425489109/200000000000000000),1,(37417361734680559906867898380989838659/35641048128509782180000000000000000000),false,MergedCutProfiles.Batch544.profile21778,(fun _ => MergedCutProfiles.Batch544.profile21778)⟩
theorem profilesValid3539 : retention3539.ProfilesValid := by
  exact MergedCutProfiles.Batch544.valid21778
theorem numericValid3539 : retention3539.NumericValid := by decide +kernel
def certificate3539 : RatCutBinCertificate := ⟨⟨retention3539,(2311929792266006051/1000000000000000000),(2610492019033761/12500000000000000),(16855991791084864887/1000000000000000000),(920885892078861988323/1000000000000000000),(510597159432612319/500000000000000000)⟩,(499003878467440373/500000000000000000),(117201441178274157/1000000000000000000),(629318791763540719/1000000000000000000),(575351236583350249/1000000000000000000)⟩
theorem valid3539 : certificate3539.Valid := by decide +kernel
theorem sound3539 : certificate3539.Sound := rat_cut_bin_certificate_sound certificate3539 profilesValid3539 numericValid3539 valid3539

def certificates : List RatCutBinCertificate := [certificate3528,certificate3529,certificate3530,certificate3531,certificate3532,certificate3533,certificate3534,certificate3535,certificate3536,certificate3537,certificate3538,certificate3539]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3528,List.forall_mem_cons.mpr ⟨sound3529,List.forall_mem_cons.mpr ⟨sound3530,List.forall_mem_cons.mpr ⟨sound3531,List.forall_mem_cons.mpr ⟨sound3532,List.forall_mem_cons.mpr ⟨sound3533,List.forall_mem_cons.mpr ⟨sound3534,List.forall_mem_cons.mpr ⟨sound3535,List.forall_mem_cons.mpr ⟨sound3536,List.forall_mem_cons.mpr ⟨sound3537,List.forall_mem_cons.mpr ⟨sound3538,List.forall_mem_cons.mpr ⟨sound3539,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch294
