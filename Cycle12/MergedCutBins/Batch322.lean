import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch032
import Cycle12.MergedCutProfiles.Batch034
import Cycle12.MergedCutProfiles.Batch325
import Cycle12.MergedCutProfiles.Batch326
import Cycle12.MergedCutProfiles.Batch459
import Cycle12.MergedCutProfiles.Batch588
import Cycle12.MergedCutProfiles.Batch589
import Cycle12.MergedCutProfiles.Batch590

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch322

def retention3864 : RatCutRetentionCertificate := ⟨(47/2000),(3/125),(4794771105836136551/1900110362806017032742),(615827793/500000000),(13/5),(18695106537118842383/8000000000000000000),true,MergedCutProfiles.Batch588.profile23545,![MergedCutProfiles.Batch588.profile23545,MergedCutProfiles.Batch588.profile23557,MergedCutProfiles.Batch589.profile23566,MergedCutProfiles.Batch589.profile23567,MergedCutProfiles.Batch589.profile23568,MergedCutProfiles.Batch589.profile23569,MergedCutProfiles.Batch589.profile23570,MergedCutProfiles.Batch589.profile23571,MergedCutProfiles.Batch589.profile23572,MergedCutProfiles.Batch589.profile23573,MergedCutProfiles.Batch589.profile23574,MergedCutProfiles.Batch589.profile23575,MergedCutProfiles.Batch589.profile23576,MergedCutProfiles.Batch589.profile23577,MergedCutProfiles.Batch589.profile23578,MergedCutProfiles.Batch589.profile23579]⟩
theorem profilesValid3864 : retention3864.ProfilesValid := by
  change ∀ j : Fin 16, (retention3864.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch588.valid23545
  · exact MergedCutProfiles.Batch588.valid23557
  · exact MergedCutProfiles.Batch589.valid23566
  · exact MergedCutProfiles.Batch589.valid23567
  · exact MergedCutProfiles.Batch589.valid23568
  · exact MergedCutProfiles.Batch589.valid23569
  · exact MergedCutProfiles.Batch589.valid23570
  · exact MergedCutProfiles.Batch589.valid23571
  · exact MergedCutProfiles.Batch589.valid23572
  · exact MergedCutProfiles.Batch589.valid23573
  · exact MergedCutProfiles.Batch589.valid23574
  · exact MergedCutProfiles.Batch589.valid23575
  · exact MergedCutProfiles.Batch589.valid23576
  · exact MergedCutProfiles.Batch589.valid23577
  · exact MergedCutProfiles.Batch589.valid23578
  · exact MergedCutProfiles.Batch589.valid23579
theorem numericValid3864 : retention3864.NumericValid := by decide +kernel
def certificate3864 : RatCutBinCertificate := ⟨⟨retention3864,(911448032109917467/500000000000000000),(12287303118992409/500000000000000000),(8954321247761919431/1000000000000000000),(2131967635031285304207/125000000000000000),(1161940475769238511/500000000000000000)⟩,(999895634456660183/1000000000000000000),(82676968012187681/200000000000000000),(110719947655911177/500000000000000000),(77358183292590401/500000000000000000)⟩
theorem valid3864 : certificate3864.Valid := by decide +kernel
theorem sound3864 : certificate3864.Sound := rat_cut_bin_certificate_sound certificate3864 profilesValid3864 numericValid3864 valid3864

def retention3865 : RatCutRetentionCertificate := ⟨(47/2000),(3/125),(32000000000000000000/950055181403008516371),(4794771105836136551/1000000000000000000),(5/4),(107531498166247295207/51200000000000000000),true,MergedCutProfiles.Batch589.profile23580,![MergedCutProfiles.Batch589.profile23580,MergedCutProfiles.Batch589.profile23581,MergedCutProfiles.Batch589.profile23582,MergedCutProfiles.Batch589.profile23583,MergedCutProfiles.Batch589.profile23584,MergedCutProfiles.Batch589.profile23585,MergedCutProfiles.Batch589.profile23586,MergedCutProfiles.Batch589.profile23587,MergedCutProfiles.Batch589.profile23588,MergedCutProfiles.Batch589.profile23589,MergedCutProfiles.Batch589.profile23590,MergedCutProfiles.Batch589.profile23591,MergedCutProfiles.Batch589.profile23592,MergedCutProfiles.Batch589.profile23593,MergedCutProfiles.Batch589.profile23594,MergedCutProfiles.Batch589.profile23595]⟩
theorem profilesValid3865 : retention3865.ProfilesValid := by
  change ∀ j : Fin 16, (retention3865.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch589.valid23580
  · exact MergedCutProfiles.Batch589.valid23581
  · exact MergedCutProfiles.Batch589.valid23582
  · exact MergedCutProfiles.Batch589.valid23583
  · exact MergedCutProfiles.Batch589.valid23584
  · exact MergedCutProfiles.Batch589.valid23585
  · exact MergedCutProfiles.Batch589.valid23586
  · exact MergedCutProfiles.Batch589.valid23587
  · exact MergedCutProfiles.Batch589.valid23588
  · exact MergedCutProfiles.Batch589.valid23589
  · exact MergedCutProfiles.Batch589.valid23590
  · exact MergedCutProfiles.Batch589.valid23591
  · exact MergedCutProfiles.Batch589.valid23592
  · exact MergedCutProfiles.Batch589.valid23593
  · exact MergedCutProfiles.Batch589.valid23594
  · exact MergedCutProfiles.Batch589.valid23595
theorem numericValid3865 : retention3865.NumericValid := by decide +kernel
def certificate3865 : RatCutBinCertificate := ⟨⟨retention3865,(911448032109917467/500000000000000000),(12287303118992409/500000000000000000),(8954321247761919431/1000000000000000000),(2131967635031285304207/125000000000000000),(2093971033715354439/1000000000000000000)⟩,(999895634456660183/1000000000000000000),(288242201944274979/1000000000000000000),(353166252547577641/1000000000000000000),(231164228375699897/500000000000000000)⟩
theorem valid3865 : certificate3865.Valid := by decide +kernel
theorem sound3865 : certificate3865.Sound := rat_cut_bin_certificate_sound certificate3865 profilesValid3865 numericValid3865 valid3865

def retention3866 : RatCutRetentionCertificate := ⟨(47/2000),(3/125),(1/2),64,1,(255373079704971790259568791427139125951/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch589.profile23596,(fun _ => MergedCutProfiles.Batch589.profile23596)⟩
theorem profilesValid3866 : retention3866.ProfilesValid := by
  exact MergedCutProfiles.Batch589.valid23596
theorem numericValid3866 : retention3866.NumericValid := by decide +kernel
def certificate3866 : RatCutBinCertificate := ⟨⟨retention3866,(911448032109917467/500000000000000000),(12287303118992409/500000000000000000),(8954321247761919431/1000000000000000000),(2131967635031285304207/125000000000000000),(992548261812276723/1000000000000000000)⟩,(999895634456660183/1000000000000000000),(49305901069730827/100000000000000000),(39571468475159901/250000000000000000),(154690794813855669/1000000000000000000)⟩
theorem valid3866 : certificate3866.Valid := by decide +kernel
theorem sound3866 : certificate3866.Sound := rat_cut_bin_certificate_sound certificate3866 profilesValid3866 numericValid3866 valid3866

def retention3867 : RatCutRetentionCertificate := ⟨(47/2000),(3/125),(32000000000000000000/950055181403008516371),(1235578016881867639/62500000000000000),1,(32935969882341511275950284624316560131/15815398616087905779200000000000000000),false,MergedCutProfiles.Batch589.profile23597,(fun _ => MergedCutProfiles.Batch589.profile23597)⟩
theorem profilesValid3867 : retention3867.ProfilesValid := by
  exact MergedCutProfiles.Batch589.valid23597
theorem numericValid3867 : retention3867.NumericValid := by decide +kernel
def certificate3867 : RatCutBinCertificate := ⟨⟨retention3867,(896969929609917467/500000000000000000),(12287303118992409/500000000000000000),(8954321247761919431/1000000000000000000),(2131967635031285304207/125000000000000000),(519400518135943123/250000000000000000)⟩,(499948646139424449/500000000000000000),(7994584333091367/250000000000000000),(419261677422530003/500000000000000000),(1576278866620640483/1000000000000000000)⟩
theorem valid3867 : certificate3867.Valid := by decide +kernel
theorem sound3867 : certificate3867.Sound := rat_cut_bin_certificate_sound certificate3867 profilesValid3867 numericValid3867 valid3867

def retention3868 : RatCutRetentionCertificate := ⟨(47/2000),(3/125),(1/2),64,1,(255373079704971790259568791427139125951/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch589.profile23596,(fun _ => MergedCutProfiles.Batch589.profile23596)⟩
theorem profilesValid3868 : retention3868.ProfilesValid := by
  exact MergedCutProfiles.Batch589.valid23596
theorem numericValid3868 : retention3868.NumericValid := by decide +kernel
def certificate3868 : RatCutBinCertificate := ⟨⟨retention3868,(896969929609917467/500000000000000000),(12287303118992409/500000000000000000),(8954321247761919431/1000000000000000000),(2131967635031285304207/125000000000000000),(992627730409879169/1000000000000000000)⟩,(499948646139424449/500000000000000000),(66931698443274881/1000000000000000000),(744434519151004629/1000000000000000000),(727585063835789491/1000000000000000000)⟩
theorem valid3868 : certificate3868.Valid := by decide +kernel
theorem sound3868 : certificate3868.Sound := rat_cut_bin_certificate_sound certificate3868 profilesValid3868 numericValid3868 valid3868

def retention3869 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(584971757597864939/1742584194153228249068),(556580555573380941/1000000000000000000),4,(1610518158249074547127208549538926157/742107407431174588000000000000000000),true,MergedCutProfiles.Batch589.profile23598,![MergedCutProfiles.Batch589.profile23598,MergedCutProfiles.Batch589.profile23599,MergedCutProfiles.Batch590.profile23600,MergedCutProfiles.Batch590.profile23601,MergedCutProfiles.Batch590.profile23602,MergedCutProfiles.Batch590.profile23603,MergedCutProfiles.Batch590.profile23604,MergedCutProfiles.Batch590.profile23605,MergedCutProfiles.Batch590.profile23606,MergedCutProfiles.Batch590.profile23607,MergedCutProfiles.Batch325.profile13022,MergedCutProfiles.Batch590.profile23608,MergedCutProfiles.Batch459.profile18370,MergedCutProfiles.Batch590.profile23609,MergedCutProfiles.Batch459.profile18386,MergedCutProfiles.Batch590.profile23610]⟩
theorem profilesValid3869 : retention3869.ProfilesValid := by
  change ∀ j : Fin 16, (retention3869.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch589.valid23598
  · exact MergedCutProfiles.Batch589.valid23599
  · exact MergedCutProfiles.Batch590.valid23600
  · exact MergedCutProfiles.Batch590.valid23601
  · exact MergedCutProfiles.Batch590.valid23602
  · exact MergedCutProfiles.Batch590.valid23603
  · exact MergedCutProfiles.Batch590.valid23604
  · exact MergedCutProfiles.Batch590.valid23605
  · exact MergedCutProfiles.Batch590.valid23606
  · exact MergedCutProfiles.Batch590.valid23607
  · exact MergedCutProfiles.Batch325.valid13022
  · exact MergedCutProfiles.Batch590.valid23608
  · exact MergedCutProfiles.Batch459.valid18370
  · exact MergedCutProfiles.Batch590.valid23609
  · exact MergedCutProfiles.Batch459.valid18386
  · exact MergedCutProfiles.Batch590.valid23610
theorem numericValid3869 : retention3869.NumericValid := by decide +kernel
def certificate3869 : RatCutBinCertificate := ⟨⟨retention3869,(455600224091006109/250000000000000000),(5353370290855499/200000000000000000),(4507551551448999817/500000000000000000),(15786723066698804416633/1000000000000000000),(429710367274760939/200000000000000000)⟩,(999887397710791101/1000000000000000000),(723257638924309281/1000000000000000000),(8482856528980911/200000000000000000),(458789702740133/25000000000000000)⟩
theorem valid3869 : certificate3869.Valid := by decide +kernel
theorem sound3869 : certificate3869.Sound := rat_cut_bin_certificate_sound certificate3869 profilesValid3869 numericValid3869 valid3869

def retention3870 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(305583948000000000/435646048538307062267),(584971757597864939/1000000000000000000),4,(114150745667830252527/51200000000000000000),true,MergedCutProfiles.Batch589.profile23599,![MergedCutProfiles.Batch589.profile23599,MergedCutProfiles.Batch459.profile18368,MergedCutProfiles.Batch590.profile23611,MergedCutProfiles.Batch459.profile18369,MergedCutProfiles.Batch590.profile23612,MergedCutProfiles.Batch459.profile18370,MergedCutProfiles.Batch590.profile23609,MergedCutProfiles.Batch459.profile18371,MergedCutProfiles.Batch590.profile23613,MergedCutProfiles.Batch326.profile13047,MergedCutProfiles.Batch325.profile13023,MergedCutProfiles.Batch459.profile18379,MergedCutProfiles.Batch326.profile13055,MergedCutProfiles.Batch459.profile18374,MergedCutProfiles.Batch590.profile23614,MergedCutProfiles.Batch325.profile13024]⟩
theorem profilesValid3870 : retention3870.ProfilesValid := by
  change ∀ j : Fin 16, (retention3870.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch589.valid23599
  · exact MergedCutProfiles.Batch459.valid18368
  · exact MergedCutProfiles.Batch590.valid23611
  · exact MergedCutProfiles.Batch459.valid18369
  · exact MergedCutProfiles.Batch590.valid23612
  · exact MergedCutProfiles.Batch459.valid18370
  · exact MergedCutProfiles.Batch590.valid23609
  · exact MergedCutProfiles.Batch459.valid18371
  · exact MergedCutProfiles.Batch590.valid23613
  · exact MergedCutProfiles.Batch326.valid13047
  · exact MergedCutProfiles.Batch325.valid13023
  · exact MergedCutProfiles.Batch459.valid18379
  · exact MergedCutProfiles.Batch326.valid13055
  · exact MergedCutProfiles.Batch459.valid18374
  · exact MergedCutProfiles.Batch590.valid23614
  · exact MergedCutProfiles.Batch325.valid13024
theorem numericValid3870 : retention3870.NumericValid := by decide +kernel
def certificate3870 : RatCutBinCertificate := ⟨⟨retention3870,(455600224091006109/250000000000000000),(5353370290855499/200000000000000000),(4507551551448999817/500000000000000000),(15786723066698804416633/1000000000000000000),(2207863085634791973/1000000000000000000)⟩,(999887397710791101/1000000000000000000),(34015254595778067/50000000000000000),(230527675819941/4000000000000000),(5147131410327897/200000000000000000)⟩
theorem valid3870 : certificate3870.Valid := by decide +kernel
theorem sound3870 : certificate3870.Sound := rat_cut_bin_certificate_sound certificate3870 profilesValid3870 numericValid3870 valid3870

def retention3871 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(3913067066266909281/1742584194153228249068),(76395987/62500000),(13/5),(28590926809554450518265034647129191/12223357920000000000000000000000000),true,MergedCutProfiles.Batch590.profile23604,![MergedCutProfiles.Batch590.profile23604,MergedCutProfiles.Batch590.profile23615,MergedCutProfiles.Batch326.profile13047,MergedCutProfiles.Batch326.profile13055,MergedCutProfiles.Batch325.profile13024,MergedCutProfiles.Batch326.profile13048,MergedCutProfiles.Batch032.profile1301,MergedCutProfiles.Batch326.profile13056,MergedCutProfiles.Batch032.profile1317,MergedCutProfiles.Batch459.profile18381,MergedCutProfiles.Batch590.profile23616,MergedCutProfiles.Batch326.profile13050,MergedCutProfiles.Batch325.profile13039,MergedCutProfiles.Batch590.profile23617,MergedCutProfiles.Batch459.profile18383,MergedCutProfiles.Batch459.profile18384]⟩
theorem profilesValid3871 : retention3871.ProfilesValid := by
  change ∀ j : Fin 16, (retention3871.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch590.valid23604
  · exact MergedCutProfiles.Batch590.valid23615
  · exact MergedCutProfiles.Batch326.valid13047
  · exact MergedCutProfiles.Batch326.valid13055
  · exact MergedCutProfiles.Batch325.valid13024
  · exact MergedCutProfiles.Batch326.valid13048
  · exact MergedCutProfiles.Batch032.valid1301
  · exact MergedCutProfiles.Batch326.valid13056
  · exact MergedCutProfiles.Batch032.valid1317
  · exact MergedCutProfiles.Batch459.valid18381
  · exact MergedCutProfiles.Batch590.valid23616
  · exact MergedCutProfiles.Batch326.valid13050
  · exact MergedCutProfiles.Batch325.valid13039
  · exact MergedCutProfiles.Batch590.valid23617
  · exact MergedCutProfiles.Batch459.valid18383
  · exact MergedCutProfiles.Batch459.valid18384
theorem numericValid3871 : retention3871.NumericValid := by decide +kernel
def certificate3871 : RatCutBinCertificate := ⟨⟨retention3871,(455600224091006109/250000000000000000),(5353370290855499/200000000000000000),(4507551551448999817/500000000000000000),(15786723066698804416633/1000000000000000000),(232497192271852239/100000000000000000)⟩,(999887397710791101/1000000000000000000),(52211588262806657/125000000000000000),(108828454273389369/500000000000000000),(75937420208413071/500000000000000000)⟩
theorem valid3871 : certificate3871.Valid := by decide +kernel
theorem sound3871 : certificate3871.Sound := rat_cut_bin_certificate_sound certificate3871 profilesValid3871 numericValid3871 valid3871

def retention3872 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(16000000000000000000/435646048538307062267),(3913067066266909281/1000000000000000000),(27/20),(2680752277020488653473/1280000000000000000000),true,MergedCutProfiles.Batch590.profile23618,![MergedCutProfiles.Batch590.profile23618,MergedCutProfiles.Batch590.profile23619,MergedCutProfiles.Batch590.profile23620,MergedCutProfiles.Batch590.profile23621,MergedCutProfiles.Batch590.profile23622,MergedCutProfiles.Batch590.profile23623,MergedCutProfiles.Batch590.profile23624,MergedCutProfiles.Batch590.profile23625,MergedCutProfiles.Batch590.profile23626,MergedCutProfiles.Batch590.profile23627,MergedCutProfiles.Batch590.profile23628,MergedCutProfiles.Batch590.profile23629,MergedCutProfiles.Batch590.profile23630,MergedCutProfiles.Batch590.profile23631,MergedCutProfiles.Batch590.profile23632,MergedCutProfiles.Batch590.profile23633]⟩
theorem profilesValid3872 : retention3872.ProfilesValid := by
  change ∀ j : Fin 16, (retention3872.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch590.valid23618
  · exact MergedCutProfiles.Batch590.valid23619
  · exact MergedCutProfiles.Batch590.valid23620
  · exact MergedCutProfiles.Batch590.valid23621
  · exact MergedCutProfiles.Batch590.valid23622
  · exact MergedCutProfiles.Batch590.valid23623
  · exact MergedCutProfiles.Batch590.valid23624
  · exact MergedCutProfiles.Batch590.valid23625
  · exact MergedCutProfiles.Batch590.valid23626
  · exact MergedCutProfiles.Batch590.valid23627
  · exact MergedCutProfiles.Batch590.valid23628
  · exact MergedCutProfiles.Batch590.valid23629
  · exact MergedCutProfiles.Batch590.valid23630
  · exact MergedCutProfiles.Batch590.valid23631
  · exact MergedCutProfiles.Batch590.valid23632
  · exact MergedCutProfiles.Batch590.valid23633
theorem numericValid3872 : retention3872.NumericValid := by decide +kernel
def certificate3872 : RatCutBinCertificate := ⟨⟨retention3872,(455600224091006109/250000000000000000),(5353370290855499/200000000000000000),(4507551551448999817/500000000000000000),(15786723066698804416633/1000000000000000000),(1043516491100243513/500000000000000000)⟩,(999887397710791101/1000000000000000000),(38096739694068203/125000000000000000),(41634754080005633/125000000000000000),(1593193217683553/4000000000000000)⟩
theorem valid3872 : certificate3872.Valid := by decide +kernel
theorem sound3872 : certificate3872.Sound := rat_cut_bin_certificate_sound certificate3872 profilesValid3872 numericValid3872 valid3872

def retention3873 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(1/2),64,1,(255373261473046173696668873617783571559/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch034.profile1386,(fun _ => MergedCutProfiles.Batch034.profile1386)⟩
theorem profilesValid3873 : retention3873.ProfilesValid := by
  exact MergedCutProfiles.Batch034.valid1386
theorem numericValid3873 : retention3873.NumericValid := by decide +kernel
def certificate3873 : RatCutBinCertificate := ⟨⟨retention3873,(455600224091006109/250000000000000000),(5353370290855499/200000000000000000),(4507551551448999817/500000000000000000),(15786723066698804416633/1000000000000000000),(49607044499204453/50000000000000000)⟩,(999887397710791101/1000000000000000000),(497080343488693613/1000000000000000000),(31091729240615613/200000000000000000),(15186511423686839/100000000000000000)⟩
theorem valid3873 : certificate3873.Valid := by decide +kernel
theorem sound3873 : certificate3873.Sound := rat_cut_bin_certificate_sound certificate3873 profilesValid3873 numericValid3873 valid3873

def retention3874 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(16000000000000000000/435646048538307062267),(20022682314540942933/1000000000000000000),1,(11054189407864831041396531738314370813/5339381950544251448800000000000000000),false,MergedCutProfiles.Batch590.profile23634,(fun _ => MergedCutProfiles.Batch590.profile23634)⟩
theorem profilesValid3874 : retention3874.ProfilesValid := by
  exact MergedCutProfiles.Batch590.valid23634
theorem numericValid3874 : retention3874.NumericValid := by decide +kernel
def certificate3874 : RatCutBinCertificate := ⟨⟨retention3874,(448506245341006109/250000000000000000),(5353370290855499/200000000000000000),(4507551551448999817/500000000000000000),(15786723066698804416633/1000000000000000000),(2064985878282252661/1000000000000000000)⟩,(499944575501669427/500000000000000000),(3198333813492231/100000000000000000),(167701782916610797/200000000000000000),(313890180863541107/200000000000000000)⟩
theorem valid3874 : certificate3874.Valid := by decide +kernel
theorem sound3874 : certificate3874.Sound := rat_cut_bin_certificate_sound certificate3874 profilesValid3874 numericValid3874 valid3874

def retention3875 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(1/2),64,1,(255373261473046173696668873617783571559/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch034.profile1386,(fun _ => MergedCutProfiles.Batch034.profile1386)⟩
theorem profilesValid3875 : retention3875.ProfilesValid := by
  exact MergedCutProfiles.Batch034.valid1386
theorem numericValid3875 : retention3875.NumericValid := by decide +kernel
def certificate3875 : RatCutBinCertificate := ⟨⟨retention3875,(448506245341006109/250000000000000000),(5353370290855499/200000000000000000),(4507551551448999817/500000000000000000),(15786723066698804416633/1000000000000000000),(248056285314526307/250000000000000000)⟩,(499944575501669427/500000000000000000),(16640664210845833/250000000000000000),(745361501437934859/1000000000000000000),(728194130070035923/1000000000000000000)⟩
theorem valid3875 : certificate3875.Valid := by decide +kernel
theorem sound3875 : certificate3875.Sound := rat_cut_bin_certificate_sound certificate3875 profilesValid3875 numericValid3875 valid3875

def certificates : List RatCutBinCertificate := [certificate3864,certificate3865,certificate3866,certificate3867,certificate3868,certificate3869,certificate3870,certificate3871,certificate3872,certificate3873,certificate3874,certificate3875]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3864,List.forall_mem_cons.mpr ⟨sound3865,List.forall_mem_cons.mpr ⟨sound3866,List.forall_mem_cons.mpr ⟨sound3867,List.forall_mem_cons.mpr ⟨sound3868,List.forall_mem_cons.mpr ⟨sound3869,List.forall_mem_cons.mpr ⟨sound3870,List.forall_mem_cons.mpr ⟨sound3871,List.forall_mem_cons.mpr ⟨sound3872,List.forall_mem_cons.mpr ⟨sound3873,List.forall_mem_cons.mpr ⟨sound3874,List.forall_mem_cons.mpr ⟨sound3875,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch322
