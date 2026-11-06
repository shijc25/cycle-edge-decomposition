import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch003
import Cycle12.MergedCutProfiles.Batch004
import Cycle12.MergedCutProfiles.Batch005
import Cycle12.MergedCutProfiles.Batch307
import Cycle12.MergedCutProfiles.Batch308
import Cycle12.MergedCutProfiles.Batch441

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch232

def retention2784 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(1/2),64,1,(15960555614684130987744105293091422311/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch003.profile124,(fun _ => MergedCutProfiles.Batch003.profile124)⟩
theorem profilesValid2784 : retention2784.ProfilesValid := by
  exact MergedCutProfiles.Batch003.valid124
theorem numericValid2784 : retention2784.NumericValid := by decide +kernel
def certificate2784 : RatCutBinCertificate := ⟨⟨retention2784,(77319636757781447/40000000000000000),(637434242080419/1000000000000000000),(6917663836391420737/1000000000000000000),(130298704196336693278041/1000000000000000000),(199471321752561019/200000000000000000)⟩,(249996292557175341/250000000000000000),(76709310864653111/500000000000000000),(279030675683078221/500000000000000000),(548037408152832859/1000000000000000000)⟩
theorem valid2784 : certificate2784.Valid := by decide +kernel
theorem sound2784 : certificate2784.Sound := rat_cut_bin_certificate_sound certificate2784 profilesValid2784 numericValid2784 valid2784

def retention2785 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(162015240366530816/2987560786308013962495),(143780299544425427/250000000000000000),4,(5086275108803395114725763546813600263/2300484792710806832000000000000000000),true,MergedCutProfiles.Batch441.profile17645,![MergedCutProfiles.Batch441.profile17645,MergedCutProfiles.Batch307.profile12314,MergedCutProfiles.Batch441.profile17646,MergedCutProfiles.Batch441.profile17647,MergedCutProfiles.Batch003.profile126,MergedCutProfiles.Batch307.profile12315,MergedCutProfiles.Batch307.profile12315,MergedCutProfiles.Batch441.profile17648,MergedCutProfiles.Batch003.profile127,MergedCutProfiles.Batch003.profile127,MergedCutProfiles.Batch003.profile142,MergedCutProfiles.Batch307.profile12316,MergedCutProfiles.Batch307.profile12316,MergedCutProfiles.Batch003.profile128,MergedCutProfiles.Batch003.profile128,MergedCutProfiles.Batch441.profile17649]⟩
theorem profilesValid2785 : retention2785.ProfilesValid := by
  change ∀ j : Fin 16, (retention2785.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch441.valid17645
  · exact MergedCutProfiles.Batch307.valid12314
  · exact MergedCutProfiles.Batch441.valid17646
  · exact MergedCutProfiles.Batch441.valid17647
  · exact MergedCutProfiles.Batch003.valid126
  · exact MergedCutProfiles.Batch307.valid12315
  · exact MergedCutProfiles.Batch307.valid12315
  · exact MergedCutProfiles.Batch441.valid17648
  · exact MergedCutProfiles.Batch003.valid127
  · exact MergedCutProfiles.Batch003.valid127
  · exact MergedCutProfiles.Batch003.valid142
  · exact MergedCutProfiles.Batch307.valid12316
  · exact MergedCutProfiles.Batch307.valid12316
  · exact MergedCutProfiles.Batch003.valid128
  · exact MergedCutProfiles.Batch003.valid128
  · exact MergedCutProfiles.Batch441.valid17649
theorem numericValid2785 : retention2785.NumericValid := by decide +kernel
def certificate2785 : RatCutBinCertificate := ⟨⟨retention2785,(35569977826114699/20000000000000000),(249776479000013/250000000000000000),(6999655487317294221/1000000000000000000),(84013806151498242387647/1000000000000000000),(1104971254728885703/500000000000000000)⟩,(999978844367127081/1000000000000000000),(1141464035018679/1953125000000000),(101662192448475847/1000000000000000000),(45288877037721093/1000000000000000000)⟩
theorem valid2785 : certificate2785.Valid := by decide +kernel
theorem sound2785 : certificate2785.Sound := rat_cut_bin_certificate_sound certificate2785 profilesValid2785 numericValid2785 valid2785

def retention2786 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(22176470150000000/199170719087200930833),(632872032681761/976562500000000),4,(6039350538285000018969473897498718511/2592243845864493056000000000000000000),true,MergedCutProfiles.Batch307.profile12314,![MergedCutProfiles.Batch307.profile12314,MergedCutProfiles.Batch441.profile17647,MergedCutProfiles.Batch307.profile12315,MergedCutProfiles.Batch441.profile17648,MergedCutProfiles.Batch003.profile142,MergedCutProfiles.Batch307.profile12316,MergedCutProfiles.Batch003.profile128,MergedCutProfiles.Batch441.profile17649,MergedCutProfiles.Batch003.profile129,MergedCutProfiles.Batch307.profile12317,MergedCutProfiles.Batch307.profile12317,MergedCutProfiles.Batch003.profile130,MergedCutProfiles.Batch307.profile12318,MergedCutProfiles.Batch003.profile131,MergedCutProfiles.Batch003.profile131,MergedCutProfiles.Batch003.profile132]⟩
theorem profilesValid2786 : retention2786.ProfilesValid := by
  change ∀ j : Fin 16, (retention2786.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch307.valid12314
  · exact MergedCutProfiles.Batch441.valid17647
  · exact MergedCutProfiles.Batch307.valid12315
  · exact MergedCutProfiles.Batch441.valid17648
  · exact MergedCutProfiles.Batch003.valid142
  · exact MergedCutProfiles.Batch307.valid12316
  · exact MergedCutProfiles.Batch003.valid128
  · exact MergedCutProfiles.Batch441.valid17649
  · exact MergedCutProfiles.Batch003.valid129
  · exact MergedCutProfiles.Batch307.valid12317
  · exact MergedCutProfiles.Batch307.valid12317
  · exact MergedCutProfiles.Batch003.valid130
  · exact MergedCutProfiles.Batch307.valid12318
  · exact MergedCutProfiles.Batch003.valid131
  · exact MergedCutProfiles.Batch003.valid131
  · exact MergedCutProfiles.Batch003.valid132
theorem numericValid2786 : retention2786.NumericValid := by decide +kernel
def certificate2786 : RatCutBinCertificate := ⟨⟨retention2786,(35569977826114699/20000000000000000),(249776479000013/250000000000000000),(6999655487317294221/1000000000000000000),(84013806151498242387647/1000000000000000000),(582190436582240393/250000000000000000)⟩,(999978844367127081/1000000000000000000),(511597041439188837/1000000000000000000),(145521383221641081/1000000000000000000),(69181595676433991/1000000000000000000)⟩
theorem valid2786 : certificate2786.Valid := by decide +kernel
theorem sound2786 : certificate2786.Sound := rat_cut_bin_certificate_sound certificate2786 profilesValid2786 numericValid2786 valid2786

def retention2787 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(3437301445737886532/2987560786308013962495),(1330588209/1000000000),(12/5),(18627063236720712603/8000000000000000000),true,MergedCutProfiles.Batch307.profile12317,![MergedCutProfiles.Batch307.profile12317,MergedCutProfiles.Batch003.profile134,MergedCutProfiles.Batch003.profile151,MergedCutProfiles.Batch308.profile12321,MergedCutProfiles.Batch441.profile17650,MergedCutProfiles.Batch003.profile152,MergedCutProfiles.Batch441.profile17651,MergedCutProfiles.Batch441.profile17652,MergedCutProfiles.Batch003.profile154,MergedCutProfiles.Batch441.profile17653,MergedCutProfiles.Batch441.profile17654,MergedCutProfiles.Batch003.profile156,MergedCutProfiles.Batch308.profile12324,MergedCutProfiles.Batch441.profile17655,MergedCutProfiles.Batch003.profile158,MergedCutProfiles.Batch441.profile17656]⟩
theorem profilesValid2787 : retention2787.ProfilesValid := by
  change ∀ j : Fin 16, (retention2787.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch307.valid12317
  · exact MergedCutProfiles.Batch003.valid134
  · exact MergedCutProfiles.Batch003.valid151
  · exact MergedCutProfiles.Batch308.valid12321
  · exact MergedCutProfiles.Batch441.valid17650
  · exact MergedCutProfiles.Batch003.valid152
  · exact MergedCutProfiles.Batch441.valid17651
  · exact MergedCutProfiles.Batch441.valid17652
  · exact MergedCutProfiles.Batch003.valid154
  · exact MergedCutProfiles.Batch441.valid17653
  · exact MergedCutProfiles.Batch441.valid17654
  · exact MergedCutProfiles.Batch003.valid156
  · exact MergedCutProfiles.Batch308.valid12324
  · exact MergedCutProfiles.Batch441.valid17655
  · exact MergedCutProfiles.Batch003.valid158
  · exact MergedCutProfiles.Batch441.valid17656
theorem numericValid2787 : retention2787.NumericValid := by decide +kernel
def certificate2787 : RatCutBinCertificate := ⟨⟨retention2787,(35569977826114699/20000000000000000),(249776479000013/250000000000000000),(6999655487317294221/1000000000000000000),(84013806151498242387647/1000000000000000000),(1163886824370357701/500000000000000000)⟩,(999978844367127081/1000000000000000000),(337769696881008851/1000000000000000000),(295609920491791987/1000000000000000000),(109957150299704413/500000000000000000)⟩
theorem valid2787 : certificate2787.Valid := by decide +kernel
theorem sound2787 : certificate2787.Sound := rat_cut_bin_certificate_sound certificate2787 profilesValid2787 numericValid2787 valid2787

def retention2788 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(3200000000000000000/597512157261602792499),(859325361434471633/62500000000000000),1,(121746137476174900457999313982984180767/54996823131806184512000000000000000000),false,MergedCutProfiles.Batch441.profile17657,(fun _ => MergedCutProfiles.Batch441.profile17657)⟩
theorem profilesValid2788 : retention2788.ProfilesValid := by
  exact MergedCutProfiles.Batch441.valid17657
theorem numericValid2788 : retention2788.NumericValid := by decide +kernel
def certificate2788 : RatCutBinCertificate := ⟨⟨retention2788,(35569977826114699/20000000000000000),(249776479000013/250000000000000000),(6999655487317294221/1000000000000000000),(84013806151498242387647/1000000000000000000),(69170004532423101/31250000000000000)⟩,(999978844367127081/1000000000000000000),(99121991069600269/500000000000000000),(48063634065658861/100000000000000000),(183264185942467183/200000000000000000)⟩
theorem valid2788 : certificate2788.Valid := by decide +kernel
theorem sound2788 : certificate2788.Sound := rat_cut_bin_certificate_sound certificate2788 profilesValid2788 numericValid2788 valid2788

def retention2789 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(1/2),64,1,(63842214036820242051452344238848143879/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch004.profile181,(fun _ => MergedCutProfiles.Batch004.profile181)⟩
theorem profilesValid2789 : retention2789.ProfilesValid := by
  exact MergedCutProfiles.Batch004.valid181
theorem numericValid2789 : retention2789.NumericValid := by decide +kernel
def certificate2789 : RatCutBinCertificate := ⟨⟨retention2789,(35569977826114699/20000000000000000),(249776479000013/250000000000000000),(6999655487317294221/1000000000000000000),(84013806151498242387647/1000000000000000000),(31165023053822149/31250000000000000)⟩,(999978844367127081/1000000000000000000),(410688149993449431/1000000000000000000),(13989426567415247/62500000000000000),(219792488055478549/1000000000000000000)⟩
theorem valid2789 : certificate2789.Valid := by decide +kernel
theorem sound2789 : certificate2789.Sound := rat_cut_bin_certificate_sound certificate2789 profilesValid2789 numericValid2789 valid2789

def retention2790 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(3200000000000000000/597512157261602792499),(7340418926741313407/1000000000000000000),1,(12501761526819972618777968175442999071/5872335141393050725600000000000000000),false,MergedCutProfiles.Batch441.profile17657,(fun _ => MergedCutProfiles.Batch441.profile17657)⟩
theorem profilesValid2790 : retention2790.ProfilesValid := by
  exact MergedCutProfiles.Batch441.valid17657
theorem numericValid2790 : retention2790.NumericValid := by decide +kernel
def certificate2790 : RatCutBinCertificate := ⟨⟨retention2790,(38818869186114699/20000000000000000),(249776479000013/250000000000000000),(6999655487317294221/1000000000000000000),(84013806151498242387647/1000000000000000000),(2128648030871497673/1000000000000000000)⟩,(999976912053471887/1000000000000000000),(70988906395261837/1000000000000000000),(73432941189321999/100000000000000000),(1211707694804512237/1000000000000000000)⟩
theorem valid2790 : certificate2790.Valid := by decide +kernel
theorem sound2790 : certificate2790.Sound := rat_cut_bin_certificate_sound certificate2790 profilesValid2790 numericValid2790 valid2790

def retention2791 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(1/2),64,1,(63842214036820242051452344238848143879/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch004.profile181,(fun _ => MergedCutProfiles.Batch004.profile181)⟩
theorem profilesValid2791 : retention2791.ProfilesValid := by
  exact MergedCutProfiles.Batch004.valid181
theorem numericValid2791 : retention2791.NumericValid := by decide +kernel
def certificate2791 : RatCutBinCertificate := ⟨⟨retention2791,(38818869186114699/20000000000000000),(249776479000013/250000000000000000),(6999655487317294221/1000000000000000000),(84013806151498242387647/1000000000000000000),(2493143877406817/2500000000000000)⟩,(999976912053471887/1000000000000000000),(151525948002215761/1000000000000000000),(35098612373021059/62500000000000000),(8616127630561333/15625000000000000)⟩
theorem valid2791 : certificate2791.Valid := by decide +kernel
theorem sound2791 : certificate2791.Sound := rat_cut_bin_certificate_sound certificate2791 profilesValid2791 numericValid2791 valid2791

def retention2792 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(646488179487749251/8262401419614876623282),(573725434029482697/1000000000000000000),4,(1013219396304224610817497442163686243/458980347223586157600000000000000000),true,MergedCutProfiles.Batch441.profile17658,![MergedCutProfiles.Batch441.profile17658,MergedCutProfiles.Batch308.profile12337,MergedCutProfiles.Batch441.profile17659,MergedCutProfiles.Batch004.profile183,MergedCutProfiles.Batch308.profile12344,MergedCutProfiles.Batch308.profile12338,MergedCutProfiles.Batch308.profile12338,MergedCutProfiles.Batch441.profile17660,MergedCutProfiles.Batch004.profile184,MergedCutProfiles.Batch004.profile199,MergedCutProfiles.Batch308.profile12339,MergedCutProfiles.Batch308.profile12339,MergedCutProfiles.Batch308.profile12340,MergedCutProfiles.Batch308.profile12340,MergedCutProfiles.Batch004.profile185,MergedCutProfiles.Batch308.profile12346]⟩
theorem profilesValid2792 : retention2792.ProfilesValid := by
  change ∀ j : Fin 16, (retention2792.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch441.valid17658
  · exact MergedCutProfiles.Batch308.valid12337
  · exact MergedCutProfiles.Batch441.valid17659
  · exact MergedCutProfiles.Batch004.valid183
  · exact MergedCutProfiles.Batch308.valid12344
  · exact MergedCutProfiles.Batch308.valid12338
  · exact MergedCutProfiles.Batch308.valid12338
  · exact MergedCutProfiles.Batch441.valid17660
  · exact MergedCutProfiles.Batch004.valid184
  · exact MergedCutProfiles.Batch004.valid199
  · exact MergedCutProfiles.Batch308.valid12339
  · exact MergedCutProfiles.Batch308.valid12339
  · exact MergedCutProfiles.Batch308.valid12340
  · exact MergedCutProfiles.Batch308.valid12340
  · exact MergedCutProfiles.Batch004.valid185
  · exact MergedCutProfiles.Batch308.valid12346
theorem numericValid2792 : retention2792.NumericValid := by decide +kernel
def certificate2792 : RatCutBinCertificate := ⟨⟨retention2792,(358699172037669049/200000000000000000),(721626522366223/500000000000000000),(1770790956639435221/250000000000000000),(7347702253895599093683/125000000000000000),(2206082426174648871/1000000000000000000)⟩,(999969519314328231/1000000000000000000),(294000260579661711/500000000000000000),(99755062922129987/1000000000000000000),(44355308903101439/1000000000000000000)⟩
theorem valid2792 : certificate2792.Valid := by decide +kernel
theorem sound2792 : certificate2792.Sound := rat_cut_bin_certificate_sound certificate2792 profilesValid2792 numericValid2792 valid2792

def retention2793 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(663966629000000000/4131200709807438311641),(646488179487749251/1000000000000000000),4,(1503903573503820041106672485691618379/646488179487749251000000000000000000),true,MergedCutProfiles.Batch308.profile12337,![MergedCutProfiles.Batch308.profile12337,MergedCutProfiles.Batch004.profile183,MergedCutProfiles.Batch308.profile12338,MergedCutProfiles.Batch441.profile17660,MergedCutProfiles.Batch004.profile199,MergedCutProfiles.Batch308.profile12339,MergedCutProfiles.Batch004.profile185,MergedCutProfiles.Batch308.profile12346,MergedCutProfiles.Batch004.profile186,MergedCutProfiles.Batch005.profile200,MergedCutProfiles.Batch004.profile187,MergedCutProfiles.Batch308.profile12341,MergedCutProfiles.Batch308.profile12342,MergedCutProfiles.Batch004.profile188,MergedCutProfiles.Batch004.profile189,MergedCutProfiles.Batch004.profile189]⟩
theorem profilesValid2793 : retention2793.ProfilesValid := by
  change ∀ j : Fin 16, (retention2793.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch308.valid12337
  · exact MergedCutProfiles.Batch004.valid183
  · exact MergedCutProfiles.Batch308.valid12338
  · exact MergedCutProfiles.Batch441.valid17660
  · exact MergedCutProfiles.Batch004.valid199
  · exact MergedCutProfiles.Batch308.valid12339
  · exact MergedCutProfiles.Batch004.valid185
  · exact MergedCutProfiles.Batch308.valid12346
  · exact MergedCutProfiles.Batch004.valid186
  · exact MergedCutProfiles.Batch005.valid200
  · exact MergedCutProfiles.Batch004.valid187
  · exact MergedCutProfiles.Batch308.valid12341
  · exact MergedCutProfiles.Batch308.valid12342
  · exact MergedCutProfiles.Batch004.valid188
  · exact MergedCutProfiles.Batch004.valid189
  · exact MergedCutProfiles.Batch004.valid189
theorem numericValid2793 : retention2793.NumericValid := by decide +kernel
def certificate2793 : RatCutBinCertificate := ⟨⟨retention2793,(358699172037669049/200000000000000000),(721626522366223/500000000000000000),(1770790956639435221/250000000000000000),(7347702253895599093683/125000000000000000),(581201099929584723/250000000000000000)⟩,(999969519314328231/1000000000000000000),(514726646477510881/1000000000000000000),(71716711083022013/500000000000000000),(34031621472255397/500000000000000000)⟩
theorem valid2793 : certificate2793.Valid := by decide +kernel
theorem sound2793 : certificate2793.Sound := rat_cut_bin_certificate_sound certificate2793 profilesValid2793 numericValid2793 valid2793

def retention2794 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(5620369502425913705/4131200709807438311641),(663966629/500000000),(12/5),(18594139237748011143/8000000000000000000),true,MergedCutProfiles.Batch308.profile12346,![MergedCutProfiles.Batch308.profile12346,MergedCutProfiles.Batch308.profile12343,MergedCutProfiles.Batch004.profile193,MergedCutProfiles.Batch005.profile202,MergedCutProfiles.Batch005.profile204,MergedCutProfiles.Batch441.profile17661,MergedCutProfiles.Batch005.profile207,MergedCutProfiles.Batch005.profile209,MergedCutProfiles.Batch441.profile17662,MergedCutProfiles.Batch441.profile17663,MergedCutProfiles.Batch005.profile216,MergedCutProfiles.Batch441.profile17664,MergedCutProfiles.Batch441.profile17665,MergedCutProfiles.Batch441.profile17666,MergedCutProfiles.Batch441.profile17667,MergedCutProfiles.Batch441.profile17668]⟩
theorem profilesValid2794 : retention2794.ProfilesValid := by
  change ∀ j : Fin 16, (retention2794.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch308.valid12346
  · exact MergedCutProfiles.Batch308.valid12343
  · exact MergedCutProfiles.Batch004.valid193
  · exact MergedCutProfiles.Batch005.valid202
  · exact MergedCutProfiles.Batch005.valid204
  · exact MergedCutProfiles.Batch441.valid17661
  · exact MergedCutProfiles.Batch005.valid207
  · exact MergedCutProfiles.Batch005.valid209
  · exact MergedCutProfiles.Batch441.valid17662
  · exact MergedCutProfiles.Batch441.valid17663
  · exact MergedCutProfiles.Batch005.valid216
  · exact MergedCutProfiles.Batch441.valid17664
  · exact MergedCutProfiles.Batch441.valid17665
  · exact MergedCutProfiles.Batch441.valid17666
  · exact MergedCutProfiles.Batch441.valid17667
  · exact MergedCutProfiles.Batch441.valid17668
theorem numericValid2794 : retention2794.NumericValid := by decide +kernel
def certificate2794 : RatCutBinCertificate := ⟨⟨retention2794,(358699172037669049/200000000000000000),(721626522366223/500000000000000000),(1770790956639435221/250000000000000000),(7347702253895599093683/125000000000000000),(2323390349737674419/1000000000000000000)⟩,(999969519314328231/1000000000000000000),(169974958302453963/500000000000000000),(293251035722010009/1000000000000000000),(108870317530513563/500000000000000000)⟩
theorem valid2794 : certificate2794.Valid := by decide +kernel
theorem sound2794 : certificate2794.Sound := rat_cut_bin_certificate_sound certificate2794 profilesValid2794 numericValid2794 valid2794

def retention2795 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(32000000000000000000/4131200709807438311641),(1124073900485182741/100000000000000000),(21/20),(399441247398080571534719996488500820239/179851824077629238560000000000000000000),false,MergedCutProfiles.Batch441.profile17669,(fun _ => MergedCutProfiles.Batch441.profile17669)⟩
theorem profilesValid2795 : retention2795.ProfilesValid := by
  exact MergedCutProfiles.Batch441.valid17669
theorem numericValid2795 : retention2795.NumericValid := by decide +kernel
def certificate2795 : RatCutBinCertificate := ⟨⟨retention2795,(358699172037669049/200000000000000000),(721626522366223/500000000000000000),(1770790956639435221/250000000000000000),(7347702253895599093683/125000000000000000),(2220562611603880177/1000000000000000000)⟩,(999969519314328231/1000000000000000000),(101211916594892769/500000000000000000),(7405411815645039/15625000000000000),(849980641074487149/1000000000000000000)⟩
theorem valid2795 : certificate2795.Valid := by decide +kernel
theorem sound2795 : certificate2795.Sound := rat_cut_bin_certificate_sound certificate2795 profilesValid2795 numericValid2795 valid2795

def certificates : List RatCutBinCertificate := [certificate2784,certificate2785,certificate2786,certificate2787,certificate2788,certificate2789,certificate2790,certificate2791,certificate2792,certificate2793,certificate2794,certificate2795]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2784,List.forall_mem_cons.mpr ⟨sound2785,List.forall_mem_cons.mpr ⟨sound2786,List.forall_mem_cons.mpr ⟨sound2787,List.forall_mem_cons.mpr ⟨sound2788,List.forall_mem_cons.mpr ⟨sound2789,List.forall_mem_cons.mpr ⟨sound2790,List.forall_mem_cons.mpr ⟨sound2791,List.forall_mem_cons.mpr ⟨sound2792,List.forall_mem_cons.mpr ⟨sound2793,List.forall_mem_cons.mpr ⟨sound2794,List.forall_mem_cons.mpr ⟨sound2795,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch232
