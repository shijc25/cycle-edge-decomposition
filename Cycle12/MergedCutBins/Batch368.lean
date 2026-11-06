import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch016
import Cycle12.MergedCutProfiles.Batch017
import Cycle12.MergedCutProfiles.Batch316
import Cycle12.MergedCutProfiles.Batch451
import Cycle12.MergedCutProfiles.Batch646
import Cycle12.MergedCutProfiles.Batch647

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch368

def retention4416 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(32000000000000000000/14638423109307511934043),(2297466528986703401/1000000000000000000),(19/10),(2160715703511727376815661676394814419599/918986611594681360400000000000000000000),false,MergedCutProfiles.Batch646.profile25876,(fun _ => MergedCutProfiles.Batch646.profile25876)⟩
theorem profilesValid4416 : retention4416.ProfilesValid := by
  exact MergedCutProfiles.Batch646.valid25876
theorem numericValid4416 : retention4416.NumericValid := by decide +kernel
def certificate4416 : RatCutBinCertificate := ⟨⟨retention4416,(1739045616684518983/1000000000000000000),(1008381335301397/125000000000000000),(390525103957195497/50000000000000000),(229720465311909498745229/1000000000000000000),(2347781169036712031/1000000000000000000)⟩,(62499530138095579/62500000000000000),(631824113551997761/1000000000000000000),(78077493321974029/1000000000000000000),(37596229947092569/500000000000000000)⟩
theorem valid4416 : certificate4416.Valid := by decide +kernel
theorem sound4416 : certificate4416.Sound := rat_cut_bin_certificate_sound certificate4416 profilesValid4416 numericValid4416 valid4416

def retention4417 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(1/40),64,1,(552274326792812916285375361392011809399/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch646.profile25879,(fun _ => MergedCutProfiles.Batch646.profile25879)⟩
theorem profilesValid4417 : retention4417.ProfilesValid := by
  exact MergedCutProfiles.Batch646.valid25879
theorem numericValid4417 : retention4417.NumericValid := by decide +kernel
def certificate4417 : RatCutBinCertificate := ⟨⟨retention4417,(1739045616684518983/1000000000000000000),(1008381335301397/125000000000000000),(390525103957195497/50000000000000000),(229720465311909498745229/1000000000000000000),(1077762710822057089/500000000000000000)⟩,(62499530138095579/62500000000000000),(38117974387796373/62500000000000000),(17706963433271933/200000000000000000),(184619598053800931/1000000000000000000)⟩
theorem valid4417 : certificate4417.Valid := by decide +kernel
theorem sound4417 : certificate4417.Sound := rat_cut_bin_certificate_sound certificate4417 profilesValid4417 numericValid4417 valid4417

def retention4418 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(771948279720804844/25385747812366614322327),(595981097177843343/1000000000000000000),4,(1076400513461024764190330864175613939/476784877742274674400000000000000000),true,MergedCutProfiles.Batch647.profile25880,![MergedCutProfiles.Batch647.profile25880,MergedCutProfiles.Batch647.profile25881,MergedCutProfiles.Batch647.profile25882,MergedCutProfiles.Batch647.profile25883,MergedCutProfiles.Batch647.profile25884,MergedCutProfiles.Batch647.profile25884,MergedCutProfiles.Batch647.profile25885,MergedCutProfiles.Batch647.profile25885,MergedCutProfiles.Batch647.profile25886,MergedCutProfiles.Batch647.profile25886,MergedCutProfiles.Batch647.profile25887,MergedCutProfiles.Batch647.profile25887,MergedCutProfiles.Batch647.profile25888,MergedCutProfiles.Batch647.profile25888,MergedCutProfiles.Batch647.profile25888,MergedCutProfiles.Batch451.profile18052]⟩
theorem profilesValid4418 : retention4418.ProfilesValid := by
  change ∀ j : Fin 16, (retention4418.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch647.valid25880
  · exact MergedCutProfiles.Batch647.valid25881
  · exact MergedCutProfiles.Batch647.valid25882
  · exact MergedCutProfiles.Batch647.valid25883
  · exact MergedCutProfiles.Batch647.valid25884
  · exact MergedCutProfiles.Batch647.valid25884
  · exact MergedCutProfiles.Batch647.valid25885
  · exact MergedCutProfiles.Batch647.valid25885
  · exact MergedCutProfiles.Batch647.valid25886
  · exact MergedCutProfiles.Batch647.valid25886
  · exact MergedCutProfiles.Batch647.valid25887
  · exact MergedCutProfiles.Batch647.valid25887
  · exact MergedCutProfiles.Batch647.valid25888
  · exact MergedCutProfiles.Batch647.valid25888
  · exact MergedCutProfiles.Batch647.valid25888
  · exact MergedCutProfiles.Batch451.valid18052
theorem numericValid4418 : retention4418.NumericValid := by decide +kernel
def certificate4418 : RatCutBinCertificate := ⟨⟨retention4418,(186120650418207757/100000000000000000),(9292470143341151/1000000000000000000),(790946750439235613/100000000000000000),(40343640626005903294591/200000000000000000),(2248876431191824607/1000000000000000000)⟩,(999990847666865183/1000000000000000000),(54158939776189399/100000000000000000),(25256489152283923/200000000000000000),(57448997477440703/1000000000000000000)⟩
theorem valid4418 : certificate4418.Valid := by decide +kernel
theorem sound4418 : certificate4418.Sound := rat_cut_bin_certificate_sound certificate4418 profilesValid4418 numericValid4418 valid4418

def retention4419 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(1278196435000000000/25385747812366614322327),(192987069930201211/250000000000000000),(15/4),(52858156233121273151013938498685921/22055665134880138400000000000000000),true,MergedCutProfiles.Batch647.profile25881,![MergedCutProfiles.Batch647.profile25881,MergedCutProfiles.Batch647.profile25883,MergedCutProfiles.Batch647.profile25884,MergedCutProfiles.Batch647.profile25885,MergedCutProfiles.Batch647.profile25886,MergedCutProfiles.Batch647.profile25886,MergedCutProfiles.Batch647.profile25887,MergedCutProfiles.Batch647.profile25888,MergedCutProfiles.Batch647.profile25888,MergedCutProfiles.Batch451.profile18052,MergedCutProfiles.Batch647.profile25889,MergedCutProfiles.Batch647.profile25889,MergedCutProfiles.Batch647.profile25890,MergedCutProfiles.Batch647.profile25890,MergedCutProfiles.Batch647.profile25891,MergedCutProfiles.Batch647.profile25891]⟩
theorem profilesValid4419 : retention4419.ProfilesValid := by
  change ∀ j : Fin 16, (retention4419.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch647.valid25881
  · exact MergedCutProfiles.Batch647.valid25883
  · exact MergedCutProfiles.Batch647.valid25884
  · exact MergedCutProfiles.Batch647.valid25885
  · exact MergedCutProfiles.Batch647.valid25886
  · exact MergedCutProfiles.Batch647.valid25886
  · exact MergedCutProfiles.Batch647.valid25887
  · exact MergedCutProfiles.Batch647.valid25888
  · exact MergedCutProfiles.Batch647.valid25888
  · exact MergedCutProfiles.Batch451.valid18052
  · exact MergedCutProfiles.Batch647.valid25889
  · exact MergedCutProfiles.Batch647.valid25889
  · exact MergedCutProfiles.Batch647.valid25890
  · exact MergedCutProfiles.Batch647.valid25890
  · exact MergedCutProfiles.Batch647.valid25891
  · exact MergedCutProfiles.Batch647.valid25891
theorem numericValid4419 : retention4419.NumericValid := by decide +kernel
def certificate4419 : RatCutBinCertificate := ⟨⟨retention4419,(186120650418207757/100000000000000000),(9292470143341151/1000000000000000000),(790946750439235613/100000000000000000),(40343640626005903294591/200000000000000000),(477675927334107553/200000000000000000)⟩,(999990847666865183/1000000000000000000),(215984142493194439/500000000000000000),(25679461924550141/125000000000000000),(107245277814308891/1000000000000000000)⟩
theorem valid4419 : certificate4419.Valid := by decide +kernel
theorem sound4419 : certificate4419.Sound := rat_cut_bin_certificate_sound certificate4419 profilesValid4419 numericValid4419 valid4419

def retention4420 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(9381083966136666552/25385747812366614322327),(255639287/200000000),(5/2),(37776897724703199781/16000000000000000000),true,MergedCutProfiles.Batch647.profile25887,![MergedCutProfiles.Batch647.profile25887,MergedCutProfiles.Batch647.profile25890,MergedCutProfiles.Batch316.profile12642,MergedCutProfiles.Batch451.profile18054,MergedCutProfiles.Batch451.profile18055,MergedCutProfiles.Batch647.profile25892,MergedCutProfiles.Batch647.profile25893,MergedCutProfiles.Batch451.profile18056,MergedCutProfiles.Batch451.profile18057,MergedCutProfiles.Batch316.profile12643,MergedCutProfiles.Batch316.profile12654,MergedCutProfiles.Batch647.profile25894,MergedCutProfiles.Batch016.profile672,MergedCutProfiles.Batch016.profile657,MergedCutProfiles.Batch647.profile25895,MergedCutProfiles.Batch451.profile18060]⟩
theorem profilesValid4420 : retention4420.ProfilesValid := by
  change ∀ j : Fin 16, (retention4420.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch647.valid25887
  · exact MergedCutProfiles.Batch647.valid25890
  · exact MergedCutProfiles.Batch316.valid12642
  · exact MergedCutProfiles.Batch451.valid18054
  · exact MergedCutProfiles.Batch451.valid18055
  · exact MergedCutProfiles.Batch647.valid25892
  · exact MergedCutProfiles.Batch647.valid25893
  · exact MergedCutProfiles.Batch451.valid18056
  · exact MergedCutProfiles.Batch451.valid18057
  · exact MergedCutProfiles.Batch316.valid12643
  · exact MergedCutProfiles.Batch316.valid12654
  · exact MergedCutProfiles.Batch647.valid25894
  · exact MergedCutProfiles.Batch016.valid672
  · exact MergedCutProfiles.Batch016.valid657
  · exact MergedCutProfiles.Batch647.valid25895
  · exact MergedCutProfiles.Batch451.valid18060
theorem numericValid4420 : retention4420.NumericValid := by decide +kernel
def certificate4420 : RatCutBinCertificate := ⟨⟨retention4420,(186120650418207757/100000000000000000),(9292470143341151/1000000000000000000),(790946750439235613/100000000000000000),(40343640626005903294591/200000000000000000),(2355589492591842639/1000000000000000000)⟩,(999990847666865183/1000000000000000000),(331910869133924973/1000000000000000000),(302018696736108901/1000000000000000000),(8790725312841751/40000000000000000)⟩
theorem valid4420 : certificate4420.Valid := by decide +kernel
theorem sound4420 : certificate4420.Sound := rat_cut_bin_certificate_sound certificate4420 profilesValid4420 numericValid4420 valid4420

def retention4421 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(64000000000000000000/25385747812366614322327),(1172635495767083319/125000000000000000),(21/20),(33139644154477317448968296972419382069/14657943697088541487500000000000000000),false,MergedCutProfiles.Batch647.profile25896,(fun _ => MergedCutProfiles.Batch647.profile25896)⟩
theorem profilesValid4421 : retention4421.ProfilesValid := by
  exact MergedCutProfiles.Batch647.valid25896
theorem numericValid4421 : retention4421.NumericValid := by decide +kernel
def certificate4421 : RatCutBinCertificate := ⟨⟨retention4421,(186120650418207757/100000000000000000),(9292470143341151/1000000000000000000),(790946750439235613/100000000000000000),(40343640626005903294591/200000000000000000),(451713971851119119/200000000000000000)⟩,(999990847666865183/1000000000000000000),(200464284432726143/1000000000000000000),(477072198941565059/1000000000000000000),(42112729307893421/50000000000000000)⟩
theorem valid4421 : certificate4421.Valid := by decide +kernel
theorem sound4421 : certificate4421.Sound := rat_cut_bin_certificate_sound certificate4421 profilesValid4421 numericValid4421 valid4421

def retention4422 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(1/2),64,1,(255369839288059878534814821034680834799/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch017.profile702,(fun _ => MergedCutProfiles.Batch017.profile702)⟩
theorem profilesValid4422 : retention4422.ProfilesValid := by
  exact MergedCutProfiles.Batch017.valid702
theorem numericValid4422 : retention4422.NumericValid := by decide +kernel
def certificate4422 : RatCutBinCertificate := ⟨⟨retention4422,(186120650418207757/100000000000000000),(9292470143341151/1000000000000000000),(790946750439235613/100000000000000000),(40343640626005903294591/200000000000000000),(124418973583511249/125000000000000000)⟩,(999990847666865183/1000000000000000000),(102591934367753813/250000000000000000),(112058041181682317/500000000000000000),(109828055570028333/500000000000000000)⟩
theorem valid4422 : certificate4422.Valid := by decide +kernel
theorem sound4422 : certificate4422.Sound := rat_cut_bin_certificate_sound certificate4422 profilesValid4422 numericValid4422 valid4422

def retention4423 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(64000000000000000000/25385747812366614322327),(16803934404520606377/1000000000000000000),1,(38198088141785081035532989635868035533/16803934404520606377000000000000000000),false,MergedCutProfiles.Batch647.profile25896,(fun _ => MergedCutProfiles.Batch647.profile25896)⟩
theorem profilesValid4423 : retention4423.ProfilesValid := by
  exact MergedCutProfiles.Batch647.valid25896
theorem numericValid4423 : retention4423.NumericValid := by decide +kernel
def certificate4423 : RatCutBinCertificate := ⟨⟨retention4423,(178508995818207757/100000000000000000),(9292470143341151/1000000000000000000),(790946750439235613/100000000000000000),(40343640626005903294591/200000000000000000),(1135533074340562371/500000000000000000)⟩,(499995610981939281/500000000000000000),(14474055295767459/500000000000000000),(847329263725145197/1000000000000000000),(1695213810361173563/1000000000000000000)⟩
theorem valid4423 : certificate4423.Valid := by decide +kernel
theorem sound4423 : certificate4423.Sound := rat_cut_bin_certificate_sound certificate4423 profilesValid4423 numericValid4423 valid4423

def retention4424 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(1/2),64,1,(255369839288059878534814821034680834799/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch017.profile702,(fun _ => MergedCutProfiles.Batch017.profile702)⟩
theorem profilesValid4424 : retention4424.ProfilesValid := by
  exact MergedCutProfiles.Batch017.valid702
theorem numericValid4424 : retention4424.NumericValid := by decide +kernel
def certificate4424 : RatCutBinCertificate := ⟨⟨retention4424,(178508995818207757/100000000000000000),(9292470143341151/1000000000000000000),(790946750439235613/100000000000000000),(40343640626005903294591/200000000000000000),(497720607251269549/500000000000000000)⟩,(499995610981939281/500000000000000000),(33022077584745607/500000000000000000),(746666134471266259/1000000000000000000),(146374457922475297/200000000000000000)⟩
theorem valid4424 : certificate4424.Valid := by decide +kernel
theorem sound4424 : certificate4424.Sound := rat_cut_bin_certificate_sound certificate4424 profilesValid4424 numericValid4424 valid4424

def retention4425 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(671914768676544956/25385747812366614322327),(166315536801124989/250000000000000000),4,(523026953670678097998948511385950173/221754049068166652000000000000000000),false,MergedCutProfiles.Batch647.profile25897,(fun _ => MergedCutProfiles.Batch647.profile25897)⟩
theorem profilesValid4425 : retention4425.ProfilesValid := by
  exact MergedCutProfiles.Batch647.valid25897
theorem numericValid4425 : retention4425.NumericValid := by decide +kernel
def certificate4425 : RatCutBinCertificate := ⟨⟨retention4425,(174545750218207757/100000000000000000),(9292470143341151/1000000000000000000),(790946750439235613/100000000000000000),(40343640626005903294591/200000000000000000),(2350387688939036839/1000000000000000000)⟩,(999991416853303063/1000000000000000000),(810392380122193941/1000000000000000000),(1923337691333069/100000000000000000),(462861590135831/50000000000000000)⟩
theorem valid4425 : certificate4425.Valid := by decide +kernel
theorem sound4425 : certificate4425.Sound := rat_cut_bin_certificate_sound certificate4425 profilesValid4425 numericValid4425 valid4425

def retention4426 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(2131049539978771400/25385747812366614322327),(167978692169136239/250000000000000000),4,(6345668418226218086231539841167881951/2687659074706179824000000000000000000),false,MergedCutProfiles.Batch647.profile25898,(fun _ => MergedCutProfiles.Batch647.profile25898)⟩
theorem profilesValid4426 : retention4426.ProfilesValid := by
  exact MergedCutProfiles.Batch647.valid25898
theorem numericValid4426 : retention4426.NumericValid := by decide +kernel
def certificate4426 : RatCutBinCertificate := ⟨⟨retention4426,(174545750218207757/100000000000000000),(9292470143341151/1000000000000000000),(790946750439235613/100000000000000000),(40343640626005903294591/200000000000000000),(1176418281713683723/500000000000000000)⟩,(999991416853303063/1000000000000000000),(403511278253582993/500000000000000000),(2493606705291687/125000000000000000),(481352334811417/50000000000000000)⟩
theorem valid4426 : certificate4426.Valid := by decide +kernel
theorem sound4426 : certificate4426.Sound := rat_cut_bin_certificate_sound certificate4426 profilesValid4426 numericValid4426 valid4426

def retention4427 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(64000000000000000000/25385747812366614322327),(10655247699893857/5000000000000000),2,(5007546890744194070995504032016394719/2131049539978771400000000000000000000),false,MergedCutProfiles.Batch647.profile25896,(fun _ => MergedCutProfiles.Batch647.profile25896)⟩
theorem profilesValid4427 : retention4427.ProfilesValid := by
  exact MergedCutProfiles.Batch647.valid25896
theorem numericValid4427 : retention4427.NumericValid := by decide +kernel
def certificate4427 : RatCutBinCertificate := ⟨⟨retention4427,(174545750218207757/100000000000000000),(9292470143341151/1000000000000000000),(790946750439235613/100000000000000000),(40343640626005903294591/200000000000000000),(146606363727200203/62500000000000000)⟩,(999991416853303063/1000000000000000000),(317985548135988071/500000000000000000),(76187009896261599/1000000000000000000),(17518124507239191/250000000000000000)⟩
theorem valid4427 : certificate4427.Valid := by decide +kernel
theorem sound4427 : certificate4427.Sound := rat_cut_bin_certificate_sound certificate4427 profilesValid4427 numericValid4427 valid4427

def certificates : List RatCutBinCertificate := [certificate4416,certificate4417,certificate4418,certificate4419,certificate4420,certificate4421,certificate4422,certificate4423,certificate4424,certificate4425,certificate4426,certificate4427]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4416,List.forall_mem_cons.mpr ⟨sound4417,List.forall_mem_cons.mpr ⟨sound4418,List.forall_mem_cons.mpr ⟨sound4419,List.forall_mem_cons.mpr ⟨sound4420,List.forall_mem_cons.mpr ⟨sound4421,List.forall_mem_cons.mpr ⟨sound4422,List.forall_mem_cons.mpr ⟨sound4423,List.forall_mem_cons.mpr ⟨sound4424,List.forall_mem_cons.mpr ⟨sound4425,List.forall_mem_cons.mpr ⟨sound4426,List.forall_mem_cons.mpr ⟨sound4427,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch368
