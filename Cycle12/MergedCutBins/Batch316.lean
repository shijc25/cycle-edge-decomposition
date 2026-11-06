import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch020
import Cycle12.MergedCutProfiles.Batch021
import Cycle12.MergedCutProfiles.Batch022
import Cycle12.MergedCutProfiles.Batch318
import Cycle12.MergedCutProfiles.Batch453
import Cycle12.MergedCutProfiles.Batch454
import Cycle12.MergedCutProfiles.Batch577
import Cycle12.MergedCutProfiles.Batch578
import Cycle12.MergedCutProfiles.Batch579

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch316

def retention3792 : RatCutRetentionCertificate := ⟨(33/2000),(17/1000),(633941014000000000/1958051853593993522639),(158271063586121197/250000000000000000),4,(5851123488046843718370050574071049063/2532337017377939152000000000000000000),true,MergedCutProfiles.Batch577.profile23100,![MergedCutProfiles.Batch577.profile23100,MergedCutProfiles.Batch577.profile23102,MergedCutProfiles.Batch577.profile23104,MergedCutProfiles.Batch577.profile23106,MergedCutProfiles.Batch577.profile23108,MergedCutProfiles.Batch577.profile23110,MergedCutProfiles.Batch577.profile23112,MergedCutProfiles.Batch577.profile23114,MergedCutProfiles.Batch577.profile23115,MergedCutProfiles.Batch577.profile23116,MergedCutProfiles.Batch577.profile23117,MergedCutProfiles.Batch577.profile23118,MergedCutProfiles.Batch577.profile23119,MergedCutProfiles.Batch578.profile23120,MergedCutProfiles.Batch578.profile23121,MergedCutProfiles.Batch578.profile23122]⟩
theorem profilesValid3792 : retention3792.ProfilesValid := by
  change ∀ j : Fin 16, (retention3792.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch577.valid23100
  · exact MergedCutProfiles.Batch577.valid23102
  · exact MergedCutProfiles.Batch577.valid23104
  · exact MergedCutProfiles.Batch577.valid23106
  · exact MergedCutProfiles.Batch577.valid23108
  · exact MergedCutProfiles.Batch577.valid23110
  · exact MergedCutProfiles.Batch577.valid23112
  · exact MergedCutProfiles.Batch577.valid23114
  · exact MergedCutProfiles.Batch577.valid23115
  · exact MergedCutProfiles.Batch577.valid23116
  · exact MergedCutProfiles.Batch577.valid23117
  · exact MergedCutProfiles.Batch577.valid23118
  · exact MergedCutProfiles.Batch577.valid23119
  · exact MergedCutProfiles.Batch578.valid23120
  · exact MergedCutProfiles.Batch578.valid23121
  · exact MergedCutProfiles.Batch578.valid23122
theorem numericValid3792 : retention3792.NumericValid := by decide +kernel
def certificate3792 : RatCutBinCertificate := ⟨⟨retention3792,(1807303819852339791/1000000000000000000),(12019078477736559/1000000000000000000),(1020687319340430753/125000000000000000),(2003244153128702748469/62500000000000000),(287490222515069763/125000000000000000)⟩,(499972125251230043/500000000000000000),(29400362148562783/50000000000000000),(2493787337360237/25000000000000000),(11684758539138127/250000000000000000)⟩
theorem valid3792 : certificate3792.Valid := by decide +kernel
theorem sound3792 : certificate3792.Sound := rat_cut_bin_certificate_sound certificate3792 profilesValid3792 numericValid3792 valid3792

def retention3793 : RatCutRetentionCertificate := ⟨(33/2000),(17/1000),(3413813964292010902/1958051853593993522639),(316970507/250000000),(51/20),(9370120672814061503/4000000000000000000),true,MergedCutProfiles.Batch577.profile23109,![MergedCutProfiles.Batch577.profile23109,MergedCutProfiles.Batch577.profile23117,MergedCutProfiles.Batch578.profile23123,MergedCutProfiles.Batch578.profile23124,MergedCutProfiles.Batch578.profile23125,MergedCutProfiles.Batch578.profile23126,MergedCutProfiles.Batch578.profile23127,MergedCutProfiles.Batch578.profile23128,MergedCutProfiles.Batch578.profile23129,MergedCutProfiles.Batch578.profile23130,MergedCutProfiles.Batch578.profile23131,MergedCutProfiles.Batch578.profile23132,MergedCutProfiles.Batch578.profile23133,MergedCutProfiles.Batch578.profile23134,MergedCutProfiles.Batch578.profile23135,MergedCutProfiles.Batch578.profile23136]⟩
theorem profilesValid3793 : retention3793.ProfilesValid := by
  change ∀ j : Fin 16, (retention3793.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch577.valid23109
  · exact MergedCutProfiles.Batch577.valid23117
  · exact MergedCutProfiles.Batch578.valid23123
  · exact MergedCutProfiles.Batch578.valid23124
  · exact MergedCutProfiles.Batch578.valid23125
  · exact MergedCutProfiles.Batch578.valid23126
  · exact MergedCutProfiles.Batch578.valid23127
  · exact MergedCutProfiles.Batch578.valid23128
  · exact MergedCutProfiles.Batch578.valid23129
  · exact MergedCutProfiles.Batch578.valid23130
  · exact MergedCutProfiles.Batch578.valid23131
  · exact MergedCutProfiles.Batch578.valid23132
  · exact MergedCutProfiles.Batch578.valid23133
  · exact MergedCutProfiles.Batch578.valid23134
  · exact MergedCutProfiles.Batch578.valid23135
  · exact MergedCutProfiles.Batch578.valid23136
theorem numericValid3793 : retention3793.NumericValid := by decide +kernel
def certificate3793 : RatCutBinCertificate := ⟨⟨retention3793,(1807303819852339791/1000000000000000000),(12019078477736559/1000000000000000000),(1020687319340430753/125000000000000000),(2003244153128702748469/62500000000000000),(1167873286988250673/500000000000000000)⟩,(499972125251230043/500000000000000000),(48276316020900989/125000000000000000),(246357305874212393/1000000000000000000),(21978643541583881/125000000000000000)⟩
theorem valid3793 : certificate3793.Valid := by decide +kernel
theorem sound3793 : certificate3793.Sound := rat_cut_bin_certificate_sound certificate3793 profilesValid3793 numericValid3793 valid3793

def retention3794 : RatCutRetentionCertificate := ⟨(33/2000),(17/1000),(32000000000000000000/1958051853593993522639),(1706906982146005451/250000000000000000),(23/20),(697808136331202383567/320000000000000000000),true,MergedCutProfiles.Batch578.profile23137,![MergedCutProfiles.Batch578.profile23137,MergedCutProfiles.Batch578.profile23138,MergedCutProfiles.Batch578.profile23139,MergedCutProfiles.Batch578.profile23140,MergedCutProfiles.Batch578.profile23141,MergedCutProfiles.Batch578.profile23142,MergedCutProfiles.Batch578.profile23143,MergedCutProfiles.Batch578.profile23144,MergedCutProfiles.Batch578.profile23145,MergedCutProfiles.Batch578.profile23146,MergedCutProfiles.Batch578.profile23147,MergedCutProfiles.Batch578.profile23148,MergedCutProfiles.Batch578.profile23149,MergedCutProfiles.Batch578.profile23150,MergedCutProfiles.Batch578.profile23151,MergedCutProfiles.Batch578.profile23152]⟩
theorem profilesValid3794 : retention3794.ProfilesValid := by
  change ∀ j : Fin 16, (retention3794.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch578.valid23137
  · exact MergedCutProfiles.Batch578.valid23138
  · exact MergedCutProfiles.Batch578.valid23139
  · exact MergedCutProfiles.Batch578.valid23140
  · exact MergedCutProfiles.Batch578.valid23141
  · exact MergedCutProfiles.Batch578.valid23142
  · exact MergedCutProfiles.Batch578.valid23143
  · exact MergedCutProfiles.Batch578.valid23144
  · exact MergedCutProfiles.Batch578.valid23145
  · exact MergedCutProfiles.Batch578.valid23146
  · exact MergedCutProfiles.Batch578.valid23147
  · exact MergedCutProfiles.Batch578.valid23148
  · exact MergedCutProfiles.Batch578.valid23149
  · exact MergedCutProfiles.Batch578.valid23150
  · exact MergedCutProfiles.Batch578.valid23151
  · exact MergedCutProfiles.Batch578.valid23152
theorem numericValid3794 : retention3794.NumericValid := by decide +kernel
def certificate3794 : RatCutBinCertificate := ⟨⟨retention3794,(1807303819852339791/1000000000000000000),(12019078477736559/1000000000000000000),(1020687319340430753/125000000000000000),(2003244153128702748469/62500000000000000),(2177591158258996211/1000000000000000000)⟩,(499972125251230043/500000000000000000),(123167171841750057/500000000000000000),(2042209482623837/5000000000000000),(623095078564280947/1000000000000000000)⟩
theorem valid3794 : certificate3794.Valid := by decide +kernel
theorem sound3794 : certificate3794.Sound := rat_cut_bin_certificate_sound certificate3794 profilesValid3794 numericValid3794 valid3794

def retention3795 : RatCutRetentionCertificate := ⟨(33/2000),(17/1000),(1/2),64,1,(2553705145399634305364347685776054111/2560000000000000000000000000000000000),false,MergedCutProfiles.Batch578.profile23153,(fun _ => MergedCutProfiles.Batch578.profile23153)⟩
theorem profilesValid3795 : retention3795.ProfilesValid := by
  exact MergedCutProfiles.Batch578.valid23153
theorem numericValid3795 : retention3795.NumericValid := by decide +kernel
def certificate3795 : RatCutBinCertificate := ⟨⟨retention3795,(1807303819852339791/1000000000000000000),(12019078477736559/1000000000000000000),(1020687319340430753/125000000000000000),(2003244153128702748469/62500000000000000),(994880839684488341/1000000000000000000)⟩,(499972125251230043/500000000000000000),(464297713574056437/1000000000000000000),(179479298891114423/1000000000000000000),(43954347635205891/250000000000000000)⟩
theorem valid3795 : certificate3795.Valid := by decide +kernel
theorem sound3795 : certificate3795.Sound := rat_cut_bin_certificate_sound certificate3795 profilesValid3795 numericValid3795 valid3795

def retention3796 : RatCutRetentionCertificate := ⟨(33/2000),(17/1000),(32000000000000000000/1958051853593993522639),(1790801840224050961/100000000000000000),1,(38682498152266291125137906692082086939/17908018402240509610000000000000000000),false,MergedCutProfiles.Batch578.profile23154,(fun _ => MergedCutProfiles.Batch578.profile23154)⟩
theorem profilesValid3796 : retention3796.ProfilesValid := by
  exact MergedCutProfiles.Batch578.valid23154
theorem numericValid3796 : retention3796.NumericValid := by decide +kernel
def certificate3796 : RatCutBinCertificate := ⟨⟨retention3796,(1780048621852339791/1000000000000000000),(12019078477736559/1000000000000000000),(1020687319340430753/125000000000000000),(2003244153128702748469/62500000000000000),(2157445688204679607/1000000000000000000)⟩,(199989018247599431/200000000000000000),(4048825045254171/125000000000000000),(837333920690172723/1000000000000000000),(322435123762583657/200000000000000000)⟩
theorem valid3796 : certificate3796.Valid := by decide +kernel
theorem sound3796 : certificate3796.Sound := rat_cut_bin_certificate_sound certificate3796 profilesValid3796 numericValid3796 valid3796

def retention3797 : RatCutRetentionCertificate := ⟨(33/2000),(17/1000),(1/2),64,1,(2553705145399634305364347685776054111/2560000000000000000000000000000000000),false,MergedCutProfiles.Batch578.profile23153,(fun _ => MergedCutProfiles.Batch578.profile23153)⟩
theorem profilesValid3797 : retention3797.ProfilesValid := by
  exact MergedCutProfiles.Batch578.valid23153
theorem numericValid3797 : retention3797.NumericValid := by decide +kernel
def certificate3797 : RatCutBinCertificate := ⟨⟨retention3797,(1780048621852339791/1000000000000000000),(12019078477736559/1000000000000000000),(1020687319340430753/125000000000000000),(2003244153128702748469/62500000000000000),(198984191509822511/200000000000000000)⟩,(199989018247599431/200000000000000000),(70237701356271079/1000000000000000000),(92023574257750119/125000000000000000),(180299352979735169/250000000000000000)⟩
theorem valid3797 : certificate3797.Valid := by decide +kernel
theorem sound3797 : certificate3797.Sound := rat_cut_bin_certificate_sound certificate3797 profilesValid3797 numericValid3797 valid3797

def retention3798 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(13141284613047941/80852939120339639460),(559480434020852933/1000000000000000000),4,(4871560086715505896420517182242586599/2237921736083411732000000000000000000),true,MergedCutProfiles.Batch578.profile23155,![MergedCutProfiles.Batch578.profile23155,MergedCutProfiles.Batch578.profile23156,MergedCutProfiles.Batch578.profile23157,MergedCutProfiles.Batch453.profile18148,MergedCutProfiles.Batch578.profile23158,MergedCutProfiles.Batch578.profile23159,MergedCutProfiles.Batch579.profile23160,MergedCutProfiles.Batch453.profile18149,MergedCutProfiles.Batch453.profile18158,MergedCutProfiles.Batch579.profile23161,MergedCutProfiles.Batch318.profile12730,MergedCutProfiles.Batch579.profile23162,MergedCutProfiles.Batch453.profile18150,MergedCutProfiles.Batch579.profile23163,MergedCutProfiles.Batch579.profile23164,MergedCutProfiles.Batch453.profile18151]⟩
theorem profilesValid3798 : retention3798.ProfilesValid := by
  change ∀ j : Fin 16, (retention3798.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch578.valid23155
  · exact MergedCutProfiles.Batch578.valid23156
  · exact MergedCutProfiles.Batch578.valid23157
  · exact MergedCutProfiles.Batch453.valid18148
  · exact MergedCutProfiles.Batch578.valid23158
  · exact MergedCutProfiles.Batch578.valid23159
  · exact MergedCutProfiles.Batch579.valid23160
  · exact MergedCutProfiles.Batch453.valid18149
  · exact MergedCutProfiles.Batch453.valid18158
  · exact MergedCutProfiles.Batch579.valid23161
  · exact MergedCutProfiles.Batch318.valid12730
  · exact MergedCutProfiles.Batch579.valid23162
  · exact MergedCutProfiles.Batch453.valid18150
  · exact MergedCutProfiles.Batch579.valid23163
  · exact MergedCutProfiles.Batch579.valid23164
  · exact MergedCutProfiles.Batch453.valid18151
theorem numericValid3798 : retention3798.NumericValid := by decide +kernel
def certificate3798 : RatCutBinCertificate := ⟨⟨retention3798,(1807091693027474153/1000000000000000000),(13522397103991873/1000000000000000000),(8218234299472071169/1000000000000000000),(14353424855149524330681/500000000000000000),(54123240027621159/25000000000000000)⟩,(999937806708670629/1000000000000000000),(342078669300567431/500000000000000000),(56158866123334827/1000000000000000000),(12236912480843763/500000000000000000)⟩
theorem valid3798 : certificate3798.Valid := by decide +kernel
theorem sound3798 : certificate3798.Sound := rat_cut_bin_certificate_sound certificate3798 profilesValid3798 numericValid3798 valid3798

def retention3799 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(63174463150000000/173833819108730224839),(565075238361061463/1000000000000000000),4,(140008131196471921007/64000000000000000000),true,MergedCutProfiles.Batch578.profile23156,![MergedCutProfiles.Batch578.profile23156,MergedCutProfiles.Batch453.profile18148,MergedCutProfiles.Batch579.profile23165,MergedCutProfiles.Batch453.profile18158,MergedCutProfiles.Batch318.profile12730,MergedCutProfiles.Batch453.profile18150,MergedCutProfiles.Batch579.profile23164,MergedCutProfiles.Batch453.profile18159,MergedCutProfiles.Batch453.profile18152,MergedCutProfiles.Batch318.profile12731,MergedCutProfiles.Batch318.profile12754,MergedCutProfiles.Batch454.profile18160,MergedCutProfiles.Batch453.profile18153,MergedCutProfiles.Batch579.profile23166,MergedCutProfiles.Batch318.profile12732,MergedCutProfiles.Batch021.profile847]⟩
theorem profilesValid3799 : retention3799.ProfilesValid := by
  change ∀ j : Fin 16, (retention3799.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch578.valid23156
  · exact MergedCutProfiles.Batch453.valid18148
  · exact MergedCutProfiles.Batch579.valid23165
  · exact MergedCutProfiles.Batch453.valid18158
  · exact MergedCutProfiles.Batch318.valid12730
  · exact MergedCutProfiles.Batch453.valid18150
  · exact MergedCutProfiles.Batch579.valid23164
  · exact MergedCutProfiles.Batch453.valid18159
  · exact MergedCutProfiles.Batch453.valid18152
  · exact MergedCutProfiles.Batch318.valid12731
  · exact MergedCutProfiles.Batch318.valid12754
  · exact MergedCutProfiles.Batch454.valid18160
  · exact MergedCutProfiles.Batch453.valid18153
  · exact MergedCutProfiles.Batch579.valid23166
  · exact MergedCutProfiles.Batch318.valid12732
  · exact MergedCutProfiles.Batch021.valid847
theorem numericValid3799 : retention3799.NumericValid := by decide +kernel
def certificate3799 : RatCutBinCertificate := ⟨⟨retention3799,(1807091693027474153/1000000000000000000),(13522397103991873/1000000000000000000),(8218234299472071169/1000000000000000000),(14353424855149524330681/500000000000000000),(108786669608473589/50000000000000000)⟩,(999937806708670629/1000000000000000000),(169024549041855587/250000000000000000),(5926550801258649/100000000000000000),(25981677572958381/1000000000000000000)⟩
theorem valid3799 : certificate3799.Valid := by decide +kernel
theorem sound3799 : certificate3799.Sound := rat_cut_bin_certificate_sound certificate3799 profilesValid3799 numericValid3799 valid3799

def retention3800 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(528468200975918651/289723031847883708065),(1263489263/1000000000),(51/20),(18724965635255394363/8000000000000000000),true,MergedCutProfiles.Batch318.profile12730,![MergedCutProfiles.Batch318.profile12730,MergedCutProfiles.Batch318.profile12731,MergedCutProfiles.Batch318.profile12732,MergedCutProfiles.Batch318.profile12733,MergedCutProfiles.Batch318.profile12734,MergedCutProfiles.Batch020.profile833,MergedCutProfiles.Batch318.profile12735,MergedCutProfiles.Batch318.profile12736,MergedCutProfiles.Batch318.profile12737,MergedCutProfiles.Batch020.profile835,MergedCutProfiles.Batch318.profile12739,MergedCutProfiles.Batch021.profile874,MergedCutProfiles.Batch318.profile12740,MergedCutProfiles.Batch318.profile12741,MergedCutProfiles.Batch318.profile12742,MergedCutProfiles.Batch579.profile23167]⟩
theorem profilesValid3800 : retention3800.ProfilesValid := by
  change ∀ j : Fin 16, (retention3800.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch318.valid12730
  · exact MergedCutProfiles.Batch318.valid12731
  · exact MergedCutProfiles.Batch318.valid12732
  · exact MergedCutProfiles.Batch318.valid12733
  · exact MergedCutProfiles.Batch318.valid12734
  · exact MergedCutProfiles.Batch020.valid833
  · exact MergedCutProfiles.Batch318.valid12735
  · exact MergedCutProfiles.Batch318.valid12736
  · exact MergedCutProfiles.Batch318.valid12737
  · exact MergedCutProfiles.Batch020.valid835
  · exact MergedCutProfiles.Batch318.valid12739
  · exact MergedCutProfiles.Batch021.valid874
  · exact MergedCutProfiles.Batch318.valid12740
  · exact MergedCutProfiles.Batch318.valid12741
  · exact MergedCutProfiles.Batch318.valid12742
  · exact MergedCutProfiles.Batch579.valid23167
theorem numericValid3800 : retention3800.NumericValid := by decide +kernel
def certificate3800 : RatCutBinCertificate := ⟨⟨retention3800,(1807091693027474153/1000000000000000000),(13522397103991873/1000000000000000000),(8218234299472071169/1000000000000000000),(14353424855149524330681/500000000000000000),(116651924902335539/50000000000000000)⟩,(999937806708670629/1000000000000000000),(390193251839491513/1000000000000000000),(60647236075786563/250000000000000000),(86424661309833879/500000000000000000)⟩
theorem valid3800 : certificate3800.Valid := by decide +kernel
theorem sound3800 : certificate3800.Sound := rat_cut_bin_certificate_sound certificate3800 profilesValid3800 numericValid3800 valid3800

def retention3801 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(3200000000000000000/173833819108730224839),(1585404602927755953/250000000000000000),(23/20),(456465354327216173286570495272166985653/211387280390367460400000000000000000000),true,MergedCutProfiles.Batch020.profile835,![MergedCutProfiles.Batch020.profile835,MergedCutProfiles.Batch021.profile840,MergedCutProfiles.Batch021.profile845,MergedCutProfiles.Batch021.profile856,MergedCutProfiles.Batch579.profile23168,MergedCutProfiles.Batch021.profile873,MergedCutProfiles.Batch579.profile23169,MergedCutProfiles.Batch454.profile18172,MergedCutProfiles.Batch579.profile23170,MergedCutProfiles.Batch579.profile23171,MergedCutProfiles.Batch579.profile23172,MergedCutProfiles.Batch454.profile18173,MergedCutProfiles.Batch579.profile23173,MergedCutProfiles.Batch579.profile23174,MergedCutProfiles.Batch579.profile23175,MergedCutProfiles.Batch454.profile18174]⟩
theorem profilesValid3801 : retention3801.ProfilesValid := by
  change ∀ j : Fin 16, (retention3801.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch020.valid835
  · exact MergedCutProfiles.Batch021.valid840
  · exact MergedCutProfiles.Batch021.valid845
  · exact MergedCutProfiles.Batch021.valid856
  · exact MergedCutProfiles.Batch579.valid23168
  · exact MergedCutProfiles.Batch021.valid873
  · exact MergedCutProfiles.Batch579.valid23169
  · exact MergedCutProfiles.Batch454.valid18172
  · exact MergedCutProfiles.Batch579.valid23170
  · exact MergedCutProfiles.Batch579.valid23171
  · exact MergedCutProfiles.Batch579.valid23172
  · exact MergedCutProfiles.Batch454.valid18173
  · exact MergedCutProfiles.Batch579.valid23173
  · exact MergedCutProfiles.Batch579.valid23174
  · exact MergedCutProfiles.Batch579.valid23175
  · exact MergedCutProfiles.Batch454.valid18174
theorem numericValid3801 : retention3801.NumericValid := by decide +kernel
def certificate3801 : RatCutBinCertificate := ⟨⟨retention3801,(1807091693027474153/1000000000000000000),(13522397103991873/1000000000000000000),(8218234299472071169/1000000000000000000),(14353424855149524330681/500000000000000000),(2155960047822540669/1000000000000000000)⟩,(999937806708670629/1000000000000000000),(126877282935873957/500000000000000000),(398172408511149093/1000000000000000000),(593782247180848109/1000000000000000000)⟩
theorem valid3801 : certificate3801.Valid := by decide +kernel
theorem sound3801 : certificate3801.Sound := rat_cut_bin_certificate_sound certificate3801 profilesValid3801 numericValid3801 valid3801

def retention3802 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(1/2),64,1,(63842651577774958124598119296594031199/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch022.profile888,(fun _ => MergedCutProfiles.Batch022.profile888)⟩
theorem profilesValid3802 : retention3802.ProfilesValid := by
  exact MergedCutProfiles.Batch022.valid888
theorem numericValid3802 : retention3802.NumericValid := by decide +kernel
def certificate3802 : RatCutBinCertificate := ⟨⟨retention3802,(1807091693027474153/1000000000000000000),(13522397103991873/1000000000000000000),(8218234299472071169/1000000000000000000),(14353424855149524330681/500000000000000000),(994568017056663763/1000000000000000000)⟩,(999937806708670629/1000000000000000000),(234101531148364147/500000000000000000),(88249700466925453/500000000000000000),(172843634657053379/1000000000000000000)⟩
theorem valid3802 : certificate3802.Valid := by decide +kernel
theorem sound3802 : certificate3802.Sound := rat_cut_bin_certificate_sound certificate3802 profilesValid3802 numericValid3802 valid3802

def retention3803 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(3200000000000000000/173833819108730224839),(18137765199184925539/1000000000000000000),1,(7795496462044071701396837037795605537/3627553039836985107800000000000000000),false,MergedCutProfiles.Batch579.profile23176,(fun _ => MergedCutProfiles.Batch579.profile23176)⟩
theorem profilesValid3803 : retention3803.ProfilesValid := by
  exact MergedCutProfiles.Batch579.valid23176
theorem numericValid3803 : retention3803.NumericValid := by decide +kernel
def certificate3803 : RatCutBinCertificate := ⟨⟨retention3803,(1780549791027474153/1000000000000000000),(13522397103991873/1000000000000000000),(8218234299472071169/1000000000000000000),(14353424855149524330681/500000000000000000),(2146038551034667249/1000000000000000000)⟩,(19998774403633457/20000000000000000),(32371558791973803/1000000000000000000),(167477762616522879/200000000000000000),(401709116525353601/250000000000000000)⟩
theorem valid3803 : certificate3803.Valid := by decide +kernel
theorem sound3803 : certificate3803.Sound := rat_cut_bin_certificate_sound certificate3803 profilesValid3803 numericValid3803 valid3803

def certificates : List RatCutBinCertificate := [certificate3792,certificate3793,certificate3794,certificate3795,certificate3796,certificate3797,certificate3798,certificate3799,certificate3800,certificate3801,certificate3802,certificate3803]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3792,List.forall_mem_cons.mpr ⟨sound3793,List.forall_mem_cons.mpr ⟨sound3794,List.forall_mem_cons.mpr ⟨sound3795,List.forall_mem_cons.mpr ⟨sound3796,List.forall_mem_cons.mpr ⟨sound3797,List.forall_mem_cons.mpr ⟨sound3798,List.forall_mem_cons.mpr ⟨sound3799,List.forall_mem_cons.mpr ⟨sound3800,List.forall_mem_cons.mpr ⟨sound3801,List.forall_mem_cons.mpr ⟨sound3802,List.forall_mem_cons.mpr ⟨sound3803,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch316
