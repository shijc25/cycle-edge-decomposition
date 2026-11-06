import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch424
import Cycle12.MergedCutProfiles.Batch425
import Cycle12.MergedCutProfiles.Batch426
import Cycle12.MergedCutProfiles.Batch427

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch224

def retention2688 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(1/2),(1304462746037220447/125000000000000000),1,(3400640329901525516632305031634701269/3478567322765921192000000000000000000),false,MergedCutProfiles.Batch424.profile16984,(fun _ => MergedCutProfiles.Batch424.profile16984)⟩
theorem profilesValid2688 : retention2688.ProfilesValid := by
  exact MergedCutProfiles.Batch424.valid16984
theorem numericValid2688 : retention2688.NumericValid := by decide +kernel
def certificate2688 : RatCutBinCertificate := ⟨⟨retention2688,(321775190989755079/125000000000000000),(216862197802423917/1000000000000000000),(534230152214430151/31250000000000000),(11262259210868497377/31250000000000000),(944941205474589589/1000000000000000000)⟩,(49718430702073567/50000000000000000),(122532814752354321/500000000000000000),(410219665584571089/1000000000000000000),(353341055769800939/1000000000000000000)⟩
theorem valid2688 : certificate2688.Valid := by decide +kernel
theorem sound2688 : certificate2688.Sound := rat_cut_bin_certificate_sound certificate2688 profilesValid2688 numericValid2688 valid2688

def retention2689 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(473903995107619180/10313834274951837531),(938423752688354811/1000000000000000000),(13/5),(165315343127942325267/80000000000000000000),true,MergedCutProfiles.Batch424.profile16987,![MergedCutProfiles.Batch424.profile16987,MergedCutProfiles.Batch424.profile16988,MergedCutProfiles.Batch424.profile16989,MergedCutProfiles.Batch424.profile16990,MergedCutProfiles.Batch424.profile16991,MergedCutProfiles.Batch424.profile16992,MergedCutProfiles.Batch424.profile16993,MergedCutProfiles.Batch424.profile16994,MergedCutProfiles.Batch424.profile16995,MergedCutProfiles.Batch424.profile16996,MergedCutProfiles.Batch424.profile16997,MergedCutProfiles.Batch424.profile16998,MergedCutProfiles.Batch424.profile16999,MergedCutProfiles.Batch425.profile17000,MergedCutProfiles.Batch425.profile17001,MergedCutProfiles.Batch425.profile17002]⟩
theorem profilesValid2689 : retention2689.ProfilesValid := by
  change ∀ j : Fin 16, (retention2689.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch424.valid16987
  · exact MergedCutProfiles.Batch424.valid16988
  · exact MergedCutProfiles.Batch424.valid16989
  · exact MergedCutProfiles.Batch424.valid16990
  · exact MergedCutProfiles.Batch424.valid16991
  · exact MergedCutProfiles.Batch424.valid16992
  · exact MergedCutProfiles.Batch424.valid16993
  · exact MergedCutProfiles.Batch424.valid16994
  · exact MergedCutProfiles.Batch424.valid16995
  · exact MergedCutProfiles.Batch424.valid16996
  · exact MergedCutProfiles.Batch424.valid16997
  · exact MergedCutProfiles.Batch424.valid16998
  · exact MergedCutProfiles.Batch424.valid16999
  · exact MergedCutProfiles.Batch425.valid17000
  · exact MergedCutProfiles.Batch425.valid17001
  · exact MergedCutProfiles.Batch425.valid17002
theorem numericValid2689 : retention2689.NumericValid := by decide +kernel
def certificate2689 : RatCutBinCertificate := ⟨⟨retention2689,(576965550530307411/250000000000000000),(55239130418189853/250000000000000000),(17259045206314115447/1000000000000000000),(357140519850849198987/1000000000000000000),(994801245409368559/500000000000000000)⟩,(497466014269669589/500000000000000000),(282913662934941299/1000000000000000000),(359839525148897703/1000000000000000000),(208332270390296977/1000000000000000000)⟩
theorem valid2689 : certificate2689.Valid := by decide +kernel
theorem sound2689 : certificate2689.Sound := rat_cut_bin_certificate_sound certificate2689 profilesValid2689 numericValid2689 valid2689

def retention2690 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(492965728000000000/10313834274951837531),(23695199755380959/25000000000000000),(13/5),(4130528549210338877/2000000000000000000),true,MergedCutProfiles.Batch425.profile17003,![MergedCutProfiles.Batch425.profile17003,MergedCutProfiles.Batch425.profile17004,MergedCutProfiles.Batch425.profile17005,MergedCutProfiles.Batch425.profile17006,MergedCutProfiles.Batch425.profile17007,MergedCutProfiles.Batch425.profile17008,MergedCutProfiles.Batch425.profile17009,MergedCutProfiles.Batch425.profile17010,MergedCutProfiles.Batch425.profile17011,MergedCutProfiles.Batch425.profile17012,MergedCutProfiles.Batch425.profile17013,MergedCutProfiles.Batch425.profile17014,MergedCutProfiles.Batch425.profile17015,MergedCutProfiles.Batch425.profile17016,MergedCutProfiles.Batch425.profile17017,MergedCutProfiles.Batch425.profile17018]⟩
theorem profilesValid2690 : retention2690.ProfilesValid := by
  change ∀ j : Fin 16, (retention2690.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch425.valid17003
  · exact MergedCutProfiles.Batch425.valid17004
  · exact MergedCutProfiles.Batch425.valid17005
  · exact MergedCutProfiles.Batch425.valid17006
  · exact MergedCutProfiles.Batch425.valid17007
  · exact MergedCutProfiles.Batch425.valid17008
  · exact MergedCutProfiles.Batch425.valid17009
  · exact MergedCutProfiles.Batch425.valid17010
  · exact MergedCutProfiles.Batch425.valid17011
  · exact MergedCutProfiles.Batch425.valid17012
  · exact MergedCutProfiles.Batch425.valid17013
  · exact MergedCutProfiles.Batch425.valid17014
  · exact MergedCutProfiles.Batch425.valid17015
  · exact MergedCutProfiles.Batch425.valid17016
  · exact MergedCutProfiles.Batch425.valid17017
  · exact MergedCutProfiles.Batch425.valid17018
theorem numericValid2690 : retention2690.NumericValid := by decide +kernel
def certificate2690 : RatCutBinCertificate := ⟨⟨retention2690,(576965550530307411/250000000000000000),(55239130418189853/250000000000000000),(17259045206314115447/1000000000000000000),(357140519850849198987/1000000000000000000),(1988425169186893539/1000000000000000000)⟩,(497466014269669589/500000000000000000),(281978878956044469/1000000000000000000),(22563777601009137/62500000000000000),(41883656086043857/200000000000000000)⟩
theorem valid2690 : certificate2690.Valid := by decide +kernel
theorem sound2690 : certificate2690.Sound := rat_cut_bin_certificate_sound certificate2690 profilesValid2690 numericValid2690 valid2690

def retention2691 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(1046969676633278729/20627668549903675062),(15405179/15625000),(5/2),(8199784255969347653/4000000000000000000),true,MergedCutProfiles.Batch425.profile17019,![MergedCutProfiles.Batch425.profile17019,MergedCutProfiles.Batch425.profile17020,MergedCutProfiles.Batch425.profile17021,MergedCutProfiles.Batch425.profile17022,MergedCutProfiles.Batch425.profile17023,MergedCutProfiles.Batch425.profile17024,MergedCutProfiles.Batch425.profile17025,MergedCutProfiles.Batch425.profile17026,MergedCutProfiles.Batch425.profile17027,MergedCutProfiles.Batch424.profile16997,MergedCutProfiles.Batch425.profile17028,MergedCutProfiles.Batch425.profile17029,MergedCutProfiles.Batch425.profile17030,MergedCutProfiles.Batch425.profile17031,MergedCutProfiles.Batch425.profile17032,MergedCutProfiles.Batch425.profile17033]⟩
theorem profilesValid2691 : retention2691.ProfilesValid := by
  change ∀ j : Fin 16, (retention2691.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch425.valid17019
  · exact MergedCutProfiles.Batch425.valid17020
  · exact MergedCutProfiles.Batch425.valid17021
  · exact MergedCutProfiles.Batch425.valid17022
  · exact MergedCutProfiles.Batch425.valid17023
  · exact MergedCutProfiles.Batch425.valid17024
  · exact MergedCutProfiles.Batch425.valid17025
  · exact MergedCutProfiles.Batch425.valid17026
  · exact MergedCutProfiles.Batch425.valid17027
  · exact MergedCutProfiles.Batch424.valid16997
  · exact MergedCutProfiles.Batch425.valid17028
  · exact MergedCutProfiles.Batch425.valid17029
  · exact MergedCutProfiles.Batch425.valid17030
  · exact MergedCutProfiles.Batch425.valid17031
  · exact MergedCutProfiles.Batch425.valid17032
  · exact MergedCutProfiles.Batch425.valid17033
theorem numericValid2691 : retention2691.NumericValid := by decide +kernel
def certificate2691 : RatCutBinCertificate := ⟨⟨retention2691,(576965550530307411/250000000000000000),(55239130418189853/250000000000000000),(17259045206314115447/1000000000000000000),(357140519850849198987/1000000000000000000),(1976062312753918353/1000000000000000000)⟩,(497466014269669589/500000000000000000),(139727035128813043/500000000000000000),(18211272574430943/50000000000000000),(216654879780334069/1000000000000000000)⟩
theorem valid2691 : certificate2691.Valid := by decide +kernel
theorem sound2691 : certificate2691.Sound := rat_cut_bin_certificate_sound certificate2691 profilesValid2691 numericValid2691 valid2691

def retention2692 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(259799196950979281/3437944758317279177),(1046969676633278729/1000000000000000000),(47/20),(2522236986121048436361/1280000000000000000000),true,MergedCutProfiles.Batch425.profile17034,![MergedCutProfiles.Batch425.profile17034,MergedCutProfiles.Batch425.profile17021,MergedCutProfiles.Batch425.profile17035,MergedCutProfiles.Batch425.profile17036,MergedCutProfiles.Batch425.profile17037,MergedCutProfiles.Batch425.profile17038,MergedCutProfiles.Batch425.profile17039,MergedCutProfiles.Batch426.profile17040,MergedCutProfiles.Batch426.profile17041,MergedCutProfiles.Batch426.profile17042,MergedCutProfiles.Batch426.profile17043,MergedCutProfiles.Batch426.profile17044,MergedCutProfiles.Batch426.profile17045,MergedCutProfiles.Batch426.profile17046,MergedCutProfiles.Batch426.profile17047,MergedCutProfiles.Batch426.profile17048]⟩
theorem profilesValid2692 : retention2692.ProfilesValid := by
  change ∀ j : Fin 16, (retention2692.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch425.valid17034
  · exact MergedCutProfiles.Batch425.valid17021
  · exact MergedCutProfiles.Batch425.valid17035
  · exact MergedCutProfiles.Batch425.valid17036
  · exact MergedCutProfiles.Batch425.valid17037
  · exact MergedCutProfiles.Batch425.valid17038
  · exact MergedCutProfiles.Batch425.valid17039
  · exact MergedCutProfiles.Batch426.valid17040
  · exact MergedCutProfiles.Batch426.valid17041
  · exact MergedCutProfiles.Batch426.valid17042
  · exact MergedCutProfiles.Batch426.valid17043
  · exact MergedCutProfiles.Batch426.valid17044
  · exact MergedCutProfiles.Batch426.valid17045
  · exact MergedCutProfiles.Batch426.valid17046
  · exact MergedCutProfiles.Batch426.valid17047
  · exact MergedCutProfiles.Batch426.valid17048
theorem numericValid2692 : retention2692.NumericValid := by decide +kernel
def certificate2692 : RatCutBinCertificate := ⟨⟨retention2692,(576965550530307411/250000000000000000),(55239130418189853/250000000000000000),(17259045206314115447/1000000000000000000),(357140519850849198987/1000000000000000000),(950523443861084817/500000000000000000)⟩,(497466014269669589/500000000000000000),(17751220052827201/62500000000000000),(700090723788813/1953125000000000),(216884957113762399/1000000000000000000)⟩
theorem valid2692 : certificate2692.Valid := by decide +kernel
theorem sound2692 : certificate2692.Sound := rat_cut_bin_certificate_sound certificate2692 profilesValid2692 numericValid2692 valid2692

def retention2693 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(1491878382243487041/6875889516634558354),(779397590852937843/500000000000000000),(7/4),(203778079233176923239/128000000000000000000),true,MergedCutProfiles.Batch426.profile17049,![MergedCutProfiles.Batch426.profile17049,MergedCutProfiles.Batch426.profile17050,MergedCutProfiles.Batch426.profile17051,MergedCutProfiles.Batch426.profile17052,MergedCutProfiles.Batch426.profile17053,MergedCutProfiles.Batch426.profile17054,MergedCutProfiles.Batch426.profile17055,MergedCutProfiles.Batch426.profile17056,MergedCutProfiles.Batch426.profile17057,MergedCutProfiles.Batch426.profile17058,MergedCutProfiles.Batch426.profile17059,MergedCutProfiles.Batch426.profile17060,MergedCutProfiles.Batch426.profile17061,MergedCutProfiles.Batch426.profile17062,MergedCutProfiles.Batch426.profile17063,MergedCutProfiles.Batch426.profile17064]⟩
theorem profilesValid2693 : retention2693.ProfilesValid := by
  change ∀ j : Fin 16, (retention2693.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch426.valid17049
  · exact MergedCutProfiles.Batch426.valid17050
  · exact MergedCutProfiles.Batch426.valid17051
  · exact MergedCutProfiles.Batch426.valid17052
  · exact MergedCutProfiles.Batch426.valid17053
  · exact MergedCutProfiles.Batch426.valid17054
  · exact MergedCutProfiles.Batch426.valid17055
  · exact MergedCutProfiles.Batch426.valid17056
  · exact MergedCutProfiles.Batch426.valid17057
  · exact MergedCutProfiles.Batch426.valid17058
  · exact MergedCutProfiles.Batch426.valid17059
  · exact MergedCutProfiles.Batch426.valid17060
  · exact MergedCutProfiles.Batch426.valid17061
  · exact MergedCutProfiles.Batch426.valid17062
  · exact MergedCutProfiles.Batch426.valid17063
  · exact MergedCutProfiles.Batch426.valid17064
theorem numericValid2693 : retention2693.NumericValid := by decide +kernel
def certificate2693 : RatCutBinCertificate := ⟨⟨retention2693,(576965550530307411/250000000000000000),(55239130418189853/250000000000000000),(17259045206314115447/1000000000000000000),(357140519850849198987/1000000000000000000),(24067169839090339/15625000000000000)⟩,(497466014269669589/500000000000000000),(77060164615602899/250000000000000000),(328980350607011663/1000000000000000000),(108802874916167211/500000000000000000)⟩
theorem valid2693 : certificate2693.Valid := by decide +kernel
theorem sound2693 : certificate2693.Sound := rat_cut_bin_certificate_sound certificate2693 profilesValid2693 numericValid2693 valid2693

def retention2694 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(1511892678231533920/3437944758317279177),(4475635146730461123/1000000000000000000),(21/20),(1387119384415786765707/1280000000000000000000),true,MergedCutProfiles.Batch426.profile17065,![MergedCutProfiles.Batch426.profile17065,MergedCutProfiles.Batch426.profile17066,MergedCutProfiles.Batch426.profile17067,MergedCutProfiles.Batch426.profile17068,MergedCutProfiles.Batch426.profile17069,MergedCutProfiles.Batch426.profile17070,MergedCutProfiles.Batch426.profile17071,MergedCutProfiles.Batch426.profile17072,MergedCutProfiles.Batch426.profile17073,MergedCutProfiles.Batch426.profile17074,MergedCutProfiles.Batch426.profile17075,MergedCutProfiles.Batch426.profile17076,MergedCutProfiles.Batch426.profile17077,MergedCutProfiles.Batch426.profile17078,MergedCutProfiles.Batch426.profile17079,MergedCutProfiles.Batch427.profile17080]⟩
theorem profilesValid2694 : retention2694.ProfilesValid := by
  change ∀ j : Fin 16, (retention2694.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch426.valid17065
  · exact MergedCutProfiles.Batch426.valid17066
  · exact MergedCutProfiles.Batch426.valid17067
  · exact MergedCutProfiles.Batch426.valid17068
  · exact MergedCutProfiles.Batch426.valid17069
  · exact MergedCutProfiles.Batch426.valid17070
  · exact MergedCutProfiles.Batch426.valid17071
  · exact MergedCutProfiles.Batch426.valid17072
  · exact MergedCutProfiles.Batch426.valid17073
  · exact MergedCutProfiles.Batch426.valid17074
  · exact MergedCutProfiles.Batch426.valid17075
  · exact MergedCutProfiles.Batch426.valid17076
  · exact MergedCutProfiles.Batch426.valid17077
  · exact MergedCutProfiles.Batch426.valid17078
  · exact MergedCutProfiles.Batch426.valid17079
  · exact MergedCutProfiles.Batch427.valid17080
theorem numericValid2694 : retention2694.NumericValid := by decide +kernel
def certificate2694 : RatCutBinCertificate := ⟨⟨retention2694,(576965550530307411/250000000000000000),(55239130418189853/250000000000000000),(17259045206314115447/1000000000000000000),(357140519850849198987/1000000000000000000),(1315824432873907/1250000000000000)⟩,(497466014269669589/500000000000000000),(368521378121880483/1000000000000000000),(263596323170051233/1000000000000000000),(216566153385369793/1000000000000000000)⟩
theorem valid2694 : certificate2694.Valid := by decide +kernel
theorem sound2694 : certificate2694.Sound := rat_cut_bin_certificate_sound certificate2694 profilesValid2694 numericValid2694 valid2694

def retention2695 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(1686770804657972883/3437944758317279177),(28347987716841261/3125000000000000),(21/20),(36705266560895003683746954279071898599/36285424277556814080000000000000000000),false,MergedCutProfiles.Batch427.profile17081,(fun _ => MergedCutProfiles.Batch427.profile17081)⟩
theorem profilesValid2695 : retention2695.ProfilesValid := by
  exact MergedCutProfiles.Batch427.valid17081
theorem numericValid2695 : retention2695.NumericValid := by decide +kernel
def certificate2695 : RatCutBinCertificate := ⟨⟨retention2695,(576965550530307411/250000000000000000),(55239130418189853/250000000000000000),(17259045206314115447/1000000000000000000),(357140519850849198987/1000000000000000000),(980545145489109481/1000000000000000000)⟩,(497466014269669589/500000000000000000),(371642323835527517/1000000000000000000),(260494293336586229/1000000000000000000),(220347449130091921/1000000000000000000)⟩
theorem valid2695 : certificate2695.Valid := by decide +kernel
theorem sound2695 : certificate2695.Sound := rat_cut_bin_certificate_sound certificate2695 profilesValid2695 numericValid2695 valid2695

def retention2696 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(10221831076227315671/20627668549903675062),(5060312413973918649/500000000000000000),(21/20),(109881367866857486751002983597458487667/109412160302138781600000000000000000000),false,MergedCutProfiles.Batch427.profile17082,(fun _ => MergedCutProfiles.Batch427.profile17082)⟩
theorem profilesValid2696 : retention2696.ProfilesValid := by
  exact MergedCutProfiles.Batch427.valid17082
theorem numericValid2696 : retention2696.NumericValid := by decide +kernel
def certificate2696 : RatCutBinCertificate := ⟨⟨retention2696,(576965550530307411/250000000000000000),(55239130418189853/250000000000000000),(17259045206314115447/1000000000000000000),(357140519850849198987/1000000000000000000),(243315811508602583/250000000000000000)⟩,(497466014269669589/500000000000000000),(185991706801884397/500000000000000000),(130078431026724161/500000000000000000),(110303932642923941/500000000000000000)⟩
theorem valid2696 : certificate2696.Valid := by decide +kernel
theorem sound2696 : certificate2696.Sound := rat_cut_bin_certificate_sound certificate2696 profilesValid2696 numericValid2696 valid2696

def retention2697 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(1/2),(10221831076227315671/1000000000000000000),(21/20),(16285429644291800717914275542154811298679/16354929721963705073600000000000000000000),false,MergedCutProfiles.Batch427.profile17083,(fun _ => MergedCutProfiles.Batch427.profile17083)⟩
theorem profilesValid2697 : retention2697.ProfilesValid := by
  exact MergedCutProfiles.Batch427.valid17083
theorem numericValid2697 : retention2697.NumericValid := by decide +kernel
def certificate2697 : RatCutBinCertificate := ⟨⟨retention2697,(576965550530307411/250000000000000000),(55239130418189853/250000000000000000),(17259045206314115447/1000000000000000000),(357140519850849198987/1000000000000000000),(964725335181494993/1000000000000000000)⟩,(497466014269669589/500000000000000000),(93766209027727527/250000000000000000),(128561309281689311/500000000000000000),(216445480754862743/1000000000000000000)⟩
theorem valid2697 : certificate2697.Valid := by decide +kernel
theorem sound2697 : certificate2697.Sound := rat_cut_bin_certificate_sound certificate2697 profilesValid2697 numericValid2697 valid2697

def retention2698 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(9387482985165538735/20627668549903675062),(1216966159540410207/250000000000000000),(21/20),(1337712223804222395377625577752621189/1267673082854593965625000000000000000),false,MergedCutProfiles.Batch427.profile17084,(fun _ => MergedCutProfiles.Batch427.profile17084)⟩
theorem profilesValid2698 : retention2698.ProfilesValid := by
  exact MergedCutProfiles.Batch427.valid17084
theorem numericValid2698 : retention2698.NumericValid := by decide +kernel
def certificate2698 : RatCutBinCertificate := ⟨⟨retention2698,(644396879280307411/250000000000000000),(55239130418189853/250000000000000000),(17259045206314115447/1000000000000000000),(357140519850849198987/1000000000000000000),(102059680086659153/100000000000000000)⟩,(994338794346485983/1000000000000000000),(14064055867949347/62500000000000000),(439180978848239673/1000000000000000000),(44555310015243001/125000000000000000)⟩
theorem valid2698 : certificate2698.Valid := by decide +kernel
theorem sound2698 : certificate2698.Sound := rat_cut_bin_certificate_sound certificate2698 profilesValid2698 numericValid2698 valid2698

def retention2699 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(1694216483242668402/3437944758317279177),(1877496597033107747/200000000000000000),1,(1160037364632254977885493581939394193/1173435373145692341875000000000000000),false,MergedCutProfiles.Batch427.profile17085,(fun _ => MergedCutProfiles.Batch427.profile17085)⟩
theorem profilesValid2699 : retention2699.ProfilesValid := by
  exact MergedCutProfiles.Batch427.valid17085
theorem numericValid2699 : retention2699.NumericValid := by decide +kernel
def certificate2699 : RatCutBinCertificate := ⟨⟨retention2699,(644396879280307411/250000000000000000),(55239130418189853/250000000000000000),(17259045206314115447/1000000000000000000),(357140519850849198987/1000000000000000000),(119447606976792469/125000000000000000)⟩,(994338794346485983/1000000000000000000),(30041896169646393/125000000000000000),(83381091734980701/200000000000000000),(179707074643927429/500000000000000000)⟩
theorem valid2699 : certificate2699.Valid := by decide +kernel
theorem sound2699 : certificate2699.Sound := rat_cut_bin_certificate_sound certificate2699 profilesValid2699 numericValid2699 valid2699

def certificates : List RatCutBinCertificate := [certificate2688,certificate2689,certificate2690,certificate2691,certificate2692,certificate2693,certificate2694,certificate2695,certificate2696,certificate2697,certificate2698,certificate2699]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2688,List.forall_mem_cons.mpr ⟨sound2689,List.forall_mem_cons.mpr ⟨sound2690,List.forall_mem_cons.mpr ⟨sound2691,List.forall_mem_cons.mpr ⟨sound2692,List.forall_mem_cons.mpr ⟨sound2693,List.forall_mem_cons.mpr ⟨sound2694,List.forall_mem_cons.mpr ⟨sound2695,List.forall_mem_cons.mpr ⟨sound2696,List.forall_mem_cons.mpr ⟨sound2697,List.forall_mem_cons.mpr ⟨sound2698,List.forall_mem_cons.mpr ⟨sound2699,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch224
