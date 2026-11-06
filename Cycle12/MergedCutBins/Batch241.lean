import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch020
import Cycle12.MergedCutProfiles.Batch021
import Cycle12.MergedCutProfiles.Batch022
import Cycle12.MergedCutProfiles.Batch023
import Cycle12.MergedCutProfiles.Batch318
import Cycle12.MergedCutProfiles.Batch319
import Cycle12.MergedCutProfiles.Batch453
import Cycle12.MergedCutProfiles.Batch454
import Cycle12.MergedCutProfiles.Batch455

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch241

def retention2892 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(594248898928818794/869169095543651124195),(588365246464177023/1000000000000000000),4,(5256076430892680006474826170743621439/2353460985856708092000000000000000000),true,MergedCutProfiles.Batch453.profile18148,![MergedCutProfiles.Batch453.profile18148,MergedCutProfiles.Batch453.profile18149,MergedCutProfiles.Batch453.profile18150,MergedCutProfiles.Batch453.profile18151,MergedCutProfiles.Batch453.profile18152,MergedCutProfiles.Batch318.profile12754,MergedCutProfiles.Batch453.profile18153,MergedCutProfiles.Batch318.profile12732,MergedCutProfiles.Batch453.profile18154,MergedCutProfiles.Batch021.profile861,MergedCutProfiles.Batch020.profile832,MergedCutProfiles.Batch453.profile18155,MergedCutProfiles.Batch318.profile12734,MergedCutProfiles.Batch453.profile18156,MergedCutProfiles.Batch453.profile18157,MergedCutProfiles.Batch020.profile833]⟩
theorem profilesValid2892 : retention2892.ProfilesValid := by
  change ∀ j : Fin 16, (retention2892.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch453.valid18148
  · exact MergedCutProfiles.Batch453.valid18149
  · exact MergedCutProfiles.Batch453.valid18150
  · exact MergedCutProfiles.Batch453.valid18151
  · exact MergedCutProfiles.Batch453.valid18152
  · exact MergedCutProfiles.Batch318.valid12754
  · exact MergedCutProfiles.Batch453.valid18153
  · exact MergedCutProfiles.Batch318.valid12732
  · exact MergedCutProfiles.Batch453.valid18154
  · exact MergedCutProfiles.Batch021.valid861
  · exact MergedCutProfiles.Batch020.valid832
  · exact MergedCutProfiles.Batch453.valid18155
  · exact MergedCutProfiles.Batch318.valid12734
  · exact MergedCutProfiles.Batch453.valid18156
  · exact MergedCutProfiles.Batch453.valid18157
  · exact MergedCutProfiles.Batch020.valid833
theorem numericValid2892 : retention2892.NumericValid := by decide +kernel
def certificate2892 : RatCutBinCertificate := ⟨⟨retention2892,(185006461610989661/100000000000000000),(13522397103991873/1000000000000000000),(821823307011731661/100000000000000000),(179417783850497030531/25000000000000000),(2221162596264047733/1000000000000000000)⟩,(999745310334918101/1000000000000000000),(118538393623678071/200000000000000000),(97282442247648189/1000000000000000000),(21847083947486077/500000000000000000)⟩
theorem valid2892 : certificate2892.Valid := by decide +kernel
theorem sound2892 : certificate2892.Sound := rat_cut_bin_certificate_sound certificate2892 profilesValid2892 numericValid2892 valid2892

def retention2893 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(246737320000000000/173833819108730224839),(297124449464409397/500000000000000000),4,(2237036003797144991/1000000000000000000),true,MergedCutProfiles.Batch453.profile18158,![MergedCutProfiles.Batch453.profile18158,MergedCutProfiles.Batch453.profile18159,MergedCutProfiles.Batch454.profile18160,MergedCutProfiles.Batch454.profile18161,MergedCutProfiles.Batch318.profile12733,MergedCutProfiles.Batch454.profile18162,MergedCutProfiles.Batch453.profile18157,MergedCutProfiles.Batch454.profile18163,MergedCutProfiles.Batch318.profile12735,MergedCutProfiles.Batch021.profile862,MergedCutProfiles.Batch454.profile18164,MergedCutProfiles.Batch454.profile18165,MergedCutProfiles.Batch020.profile835,MergedCutProfiles.Batch318.profile12739,MergedCutProfiles.Batch318.profile12746,MergedCutProfiles.Batch454.profile18166]⟩
theorem profilesValid2893 : retention2893.ProfilesValid := by
  change ∀ j : Fin 16, (retention2893.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch453.valid18158
  · exact MergedCutProfiles.Batch453.valid18159
  · exact MergedCutProfiles.Batch454.valid18160
  · exact MergedCutProfiles.Batch454.valid18161
  · exact MergedCutProfiles.Batch318.valid12733
  · exact MergedCutProfiles.Batch454.valid18162
  · exact MergedCutProfiles.Batch453.valid18157
  · exact MergedCutProfiles.Batch454.valid18163
  · exact MergedCutProfiles.Batch318.valid12735
  · exact MergedCutProfiles.Batch021.valid862
  · exact MergedCutProfiles.Batch454.valid18164
  · exact MergedCutProfiles.Batch454.valid18165
  · exact MergedCutProfiles.Batch020.valid835
  · exact MergedCutProfiles.Batch318.valid12739
  · exact MergedCutProfiles.Batch318.valid12746
  · exact MergedCutProfiles.Batch454.valid18166
theorem numericValid2893 : retention2893.NumericValid := by decide +kernel
def certificate2893 : RatCutBinCertificate := ⟨⟨retention2893,(185006461610989661/100000000000000000),(13522397103991873/1000000000000000000),(821823307011731661/100000000000000000),(179417783850497030531/25000000000000000),(556214876010939463/250000000000000000)⟩,(999745310334918101/1000000000000000000),(587803773135275819/1000000000000000000),(24964893607202953/250000000000000000),(899944895166429/20000000000000000)⟩
theorem valid2893 : certificate2893.Valid := by decide +kernel
theorem sound2893 : certificate2893.Sound := rat_cut_bin_certificate_sound certificate2893 profilesValid2893 numericValid2893 valid2893

def retention2894 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(1253347270020024844/869169095543651124195),(6168433/5000000),(5/2),(9303663676007589599/4000000000000000000),true,MergedCutProfiles.Batch453.profile18158,![MergedCutProfiles.Batch453.profile18158,MergedCutProfiles.Batch453.profile18159,MergedCutProfiles.Batch454.profile18160,MergedCutProfiles.Batch454.profile18161,MergedCutProfiles.Batch318.profile12733,MergedCutProfiles.Batch454.profile18162,MergedCutProfiles.Batch453.profile18157,MergedCutProfiles.Batch454.profile18163,MergedCutProfiles.Batch454.profile18167,MergedCutProfiles.Batch318.profile12736,MergedCutProfiles.Batch454.profile18168,MergedCutProfiles.Batch318.profile12745,MergedCutProfiles.Batch454.profile18169,MergedCutProfiles.Batch318.profile12739,MergedCutProfiles.Batch021.profile874,MergedCutProfiles.Batch454.profile18166]⟩
theorem profilesValid2894 : retention2894.ProfilesValid := by
  change ∀ j : Fin 16, (retention2894.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch453.valid18158
  · exact MergedCutProfiles.Batch453.valid18159
  · exact MergedCutProfiles.Batch454.valid18160
  · exact MergedCutProfiles.Batch454.valid18161
  · exact MergedCutProfiles.Batch318.valid12733
  · exact MergedCutProfiles.Batch454.valid18162
  · exact MergedCutProfiles.Batch453.valid18157
  · exact MergedCutProfiles.Batch454.valid18163
  · exact MergedCutProfiles.Batch454.valid18167
  · exact MergedCutProfiles.Batch318.valid12736
  · exact MergedCutProfiles.Batch454.valid18168
  · exact MergedCutProfiles.Batch318.valid12745
  · exact MergedCutProfiles.Batch454.valid18169
  · exact MergedCutProfiles.Batch318.valid12739
  · exact MergedCutProfiles.Batch021.valid874
  · exact MergedCutProfiles.Batch454.valid18166
theorem numericValid2894 : retention2894.NumericValid := by decide +kernel
def certificate2894 : RatCutBinCertificate := ⟨⟨retention2894,(185006461610989661/100000000000000000),(13522397103991873/1000000000000000000),(821823307011731661/100000000000000000),(179417783850497030531/25000000000000000),(579576402009829283/250000000000000000)⟩,(999745310334918101/1000000000000000000),(14797957931079403/40000000000000000),(262174142177816623/1000000000000000000),(46716305485878017/250000000000000000)⟩
theorem valid2894 : certificate2894.Valid := by decide +kernel
theorem sound2894 : certificate2894.Sound := rat_cut_bin_certificate_sound certificate2894 profilesValid2894 numericValid2894 valid2894

def retention2895 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(2643470407935605507/869169095543651124195),(313336817505006211/250000000000000000),(49/20),(735667691636828000123/320000000000000000000),true,MergedCutProfiles.Batch454.profile18170,![MergedCutProfiles.Batch454.profile18170,MergedCutProfiles.Batch021.profile847,MergedCutProfiles.Batch318.profile12734,MergedCutProfiles.Batch021.profile848,MergedCutProfiles.Batch454.profile18164,MergedCutProfiles.Batch020.profile835,MergedCutProfiles.Batch318.profile12746,MergedCutProfiles.Batch021.profile849,MergedCutProfiles.Batch318.profile12742,MergedCutProfiles.Batch021.profile850,MergedCutProfiles.Batch020.profile839,MergedCutProfiles.Batch021.profile851,MergedCutProfiles.Batch454.profile18171,MergedCutProfiles.Batch021.profile852,MergedCutProfiles.Batch318.profile12750,MergedCutProfiles.Batch021.profile843]⟩
theorem profilesValid2895 : retention2895.ProfilesValid := by
  change ∀ j : Fin 16, (retention2895.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch454.valid18170
  · exact MergedCutProfiles.Batch021.valid847
  · exact MergedCutProfiles.Batch318.valid12734
  · exact MergedCutProfiles.Batch021.valid848
  · exact MergedCutProfiles.Batch454.valid18164
  · exact MergedCutProfiles.Batch020.valid835
  · exact MergedCutProfiles.Batch318.valid12746
  · exact MergedCutProfiles.Batch021.valid849
  · exact MergedCutProfiles.Batch318.valid12742
  · exact MergedCutProfiles.Batch021.valid850
  · exact MergedCutProfiles.Batch020.valid839
  · exact MergedCutProfiles.Batch021.valid851
  · exact MergedCutProfiles.Batch454.valid18171
  · exact MergedCutProfiles.Batch021.valid852
  · exact MergedCutProfiles.Batch318.valid12750
  · exact MergedCutProfiles.Batch021.valid843
theorem numericValid2895 : retention2895.NumericValid := by decide +kernel
def certificate2895 : RatCutBinCertificate := ⟨⟨retention2895,(185006461610989661/100000000000000000),(13522397103991873/1000000000000000000),(821823307011731661/100000000000000000),(179417783850497030531/25000000000000000),(2291503431601704319/1000000000000000000)⟩,(999745310334918101/1000000000000000000),(37141240343127501/100000000000000000),(130360962045661621/500000000000000000),(46716651441781309/250000000000000000)⟩
theorem valid2895 : certificate2895.Valid := by decide +kernel
theorem sound2895 : certificate2895.Sound := rat_cut_bin_certificate_sound certificate2895 profilesValid2895 numericValid2895 valid2895

def retention2896 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(12800000000000000000/173833819108730224839),(2643470407935605507/1000000000000000000),(31/20),(2505628675875096189443/1280000000000000000000),true,MergedCutProfiles.Batch021.profile856,![MergedCutProfiles.Batch021.profile856,MergedCutProfiles.Batch454.profile18172,MergedCutProfiles.Batch454.profile18173,MergedCutProfiles.Batch454.profile18174,MergedCutProfiles.Batch454.profile18175,MergedCutProfiles.Batch454.profile18176,MergedCutProfiles.Batch454.profile18177,MergedCutProfiles.Batch454.profile18178,MergedCutProfiles.Batch454.profile18179,MergedCutProfiles.Batch454.profile18180,MergedCutProfiles.Batch454.profile18181,MergedCutProfiles.Batch454.profile18182,MergedCutProfiles.Batch454.profile18183,MergedCutProfiles.Batch454.profile18184,MergedCutProfiles.Batch454.profile18185,MergedCutProfiles.Batch454.profile18186]⟩
theorem profilesValid2896 : retention2896.ProfilesValid := by
  change ∀ j : Fin 16, (retention2896.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch021.valid856
  · exact MergedCutProfiles.Batch454.valid18172
  · exact MergedCutProfiles.Batch454.valid18173
  · exact MergedCutProfiles.Batch454.valid18174
  · exact MergedCutProfiles.Batch454.valid18175
  · exact MergedCutProfiles.Batch454.valid18176
  · exact MergedCutProfiles.Batch454.valid18177
  · exact MergedCutProfiles.Batch454.valid18178
  · exact MergedCutProfiles.Batch454.valid18179
  · exact MergedCutProfiles.Batch454.valid18180
  · exact MergedCutProfiles.Batch454.valid18181
  · exact MergedCutProfiles.Batch454.valid18182
  · exact MergedCutProfiles.Batch454.valid18183
  · exact MergedCutProfiles.Batch454.valid18184
  · exact MergedCutProfiles.Batch454.valid18185
  · exact MergedCutProfiles.Batch454.valid18186
theorem numericValid2896 : retention2896.NumericValid := by decide +kernel
def certificate2896 : RatCutBinCertificate := ⟨⟨retention2896,(185006461610989661/100000000000000000),(13522397103991873/1000000000000000000),(821823307011731661/100000000000000000),(179417783850497030531/25000000000000000),(1952804010943390407/1000000000000000000)⟩,(999745310334918101/1000000000000000000),(324949938289234593/1000000000000000000),(12390691735107231/40000000000000000),(298403879848876323/1000000000000000000)⟩
theorem valid2896 : certificate2896.Valid := by decide +kernel
theorem sound2896 : certificate2896.Sound := rat_cut_bin_certificate_sound certificate2896 profilesValid2896 numericValid2896 valid2896

def retention2897 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(1/2),64,1,(63842651577774958124598119296594031199/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch022.profile888,(fun _ => MergedCutProfiles.Batch022.profile888)⟩
theorem profilesValid2897 : retention2897.ProfilesValid := by
  exact MergedCutProfiles.Batch022.valid888
theorem numericValid2897 : retention2897.NumericValid := by decide +kernel
def certificate2897 : RatCutBinCertificate := ⟨⟨retention2897,(185006461610989661/100000000000000000),(13522397103991873/1000000000000000000),(821823307011731661/100000000000000000),(179417783850497030531/25000000000000000),(39779892331511663/40000000000000000)⟩,(999745310334918101/1000000000000000000),(56234750452635731/125000000000000000),(190768688222729527/1000000000000000000),(37353604625751427/200000000000000000)⟩
theorem valid2897 : certificate2897.Valid := by decide +kernel
theorem sound2897 : certificate2897.Sound := rat_cut_bin_certificate_sound certificate2897 profilesValid2897 numericValid2897 valid2897

def retention2898 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(12800000000000000000/173833819108730224839),(8429140451159841159/1000000000000000000),1,(38794953447048094316968879228432621/20812692471999607800000000000000000),false,MergedCutProfiles.Batch454.profile18187,(fun _ => MergedCutProfiles.Batch454.profile18187)⟩
theorem profilesValid2898 : retention2898.ProfilesValid := by
  exact MergedCutProfiles.Batch454.valid18187
theorem numericValid2898 : retention2898.NumericValid := by decide +kernel
def certificate2898 : RatCutBinCertificate := ⟨⟨retention2898,(200356997910989661/100000000000000000),(13522397103991873/1000000000000000000),(821823307011731661/100000000000000000),(179417783850497030531/25000000000000000),(232588480743715807/125000000000000000)⟩,(499862088952545259/500000000000000000),(18915195024621561/250000000000000000),(361442607470778353/500000000000000000),(550764687144157031/500000000000000000)⟩
theorem valid2898 : certificate2898.Valid := by decide +kernel
theorem sound2898 : certificate2898.Sound := rat_cut_bin_certificate_sound certificate2898 profilesValid2898 numericValid2898 valid2898

def retention2899 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(1/2),64,1,(63842651577774958124598119296594031199/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch022.profile888,(fun _ => MergedCutProfiles.Batch022.profile888)⟩
theorem profilesValid2899 : retention2899.ProfilesValid := by
  exact MergedCutProfiles.Batch022.valid888
theorem numericValid2899 : retention2899.NumericValid := by decide +kernel
def certificate2899 : RatCutBinCertificate := ⟨⟨retention2899,(200356997910989661/100000000000000000),(13522397103991873/1000000000000000000),(821823307011731661/100000000000000000),(179417783850497030531/25000000000000000),(198848945676337533/200000000000000000)⟩,(499862088952545259/500000000000000000),(8849846216250457/62500000000000000),(580383185792502349/1000000000000000000),(142014422429897237/250000000000000000)⟩
theorem valid2899 : certificate2899.Valid := by decide +kernel
theorem sound2899 : certificate2899.Sound := rat_cut_bin_certificate_sound certificate2899 profilesValid2899 numericValid2899 valid2899

def retention2900 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(603697433939943952/776403571869755913701),(2311727380970401/3906250000000000),4,(895684914842336153/400000000000000000),true,MergedCutProfiles.Batch454.profile18188,![MergedCutProfiles.Batch454.profile18188,MergedCutProfiles.Batch454.profile18189,MergedCutProfiles.Batch454.profile18190,MergedCutProfiles.Batch454.profile18191,MergedCutProfiles.Batch454.profile18192,MergedCutProfiles.Batch454.profile18193,MergedCutProfiles.Batch454.profile18194,MergedCutProfiles.Batch319.profile12774,MergedCutProfiles.Batch454.profile18195,MergedCutProfiles.Batch319.profile12786,MergedCutProfiles.Batch454.profile18196,MergedCutProfiles.Batch454.profile18197,MergedCutProfiles.Batch319.profile12775,MergedCutProfiles.Batch454.profile18198,MergedCutProfiles.Batch319.profile12787,MergedCutProfiles.Batch022.profile891]⟩
theorem profilesValid2900 : retention2900.ProfilesValid := by
  change ∀ j : Fin 16, (retention2900.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch454.valid18188
  · exact MergedCutProfiles.Batch454.valid18189
  · exact MergedCutProfiles.Batch454.valid18190
  · exact MergedCutProfiles.Batch454.valid18191
  · exact MergedCutProfiles.Batch454.valid18192
  · exact MergedCutProfiles.Batch454.valid18193
  · exact MergedCutProfiles.Batch454.valid18194
  · exact MergedCutProfiles.Batch319.valid12774
  · exact MergedCutProfiles.Batch454.valid18195
  · exact MergedCutProfiles.Batch319.valid12786
  · exact MergedCutProfiles.Batch454.valid18196
  · exact MergedCutProfiles.Batch454.valid18197
  · exact MergedCutProfiles.Batch319.valid12775
  · exact MergedCutProfiles.Batch454.valid18198
  · exact MergedCutProfiles.Batch319.valid12787
  · exact MergedCutProfiles.Batch022.valid891
theorem numericValid2900 : retention2900.NumericValid := by decide +kernel
def certificate2900 : RatCutBinCertificate := ⟨⟨retention2900,(1855866918952946473/1000000000000000000),(15120529320228081/1000000000000000000),(8325288334521964189/1000000000000000000),(259777396068867272681/40000000000000000),(2225729646440669273/1000000000000000000)⟩,(999718100457292219/1000000000000000000),(588504682599178027/1000000000000000000),(99487555472597607/1000000000000000000),(44807220342825529/1000000000000000000)⟩
theorem valid2900 : certificate2900.Valid := by decide +kernel
theorem sound2900 : certificate2900.Sound := rat_cut_bin_certificate_sound certificate2900 profilesValid2900 numericValid2900 valid2900

def retention2901 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(1239752555000000000/776403571869755913701),(37731089621246497/62500000000000000),4,(36032682535005763957/16000000000000000000),true,MergedCutProfiles.Batch454.profile18189,![MergedCutProfiles.Batch454.profile18189,MergedCutProfiles.Batch454.profile18191,MergedCutProfiles.Batch454.profile18199,MergedCutProfiles.Batch319.profile12774,MergedCutProfiles.Batch319.profile12786,MergedCutProfiles.Batch455.profile18200,MergedCutProfiles.Batch455.profile18201,MergedCutProfiles.Batch022.profile891,MergedCutProfiles.Batch319.profile12777,MergedCutProfiles.Batch319.profile12788,MergedCutProfiles.Batch455.profile18202,MergedCutProfiles.Batch455.profile18203,MergedCutProfiles.Batch319.profile12780,MergedCutProfiles.Batch319.profile12781,MergedCutProfiles.Batch319.profile12790,MergedCutProfiles.Batch022.profile894]⟩
theorem profilesValid2901 : retention2901.ProfilesValid := by
  change ∀ j : Fin 16, (retention2901.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch454.valid18189
  · exact MergedCutProfiles.Batch454.valid18191
  · exact MergedCutProfiles.Batch454.valid18199
  · exact MergedCutProfiles.Batch319.valid12774
  · exact MergedCutProfiles.Batch319.valid12786
  · exact MergedCutProfiles.Batch455.valid18200
  · exact MergedCutProfiles.Batch455.valid18201
  · exact MergedCutProfiles.Batch022.valid891
  · exact MergedCutProfiles.Batch319.valid12777
  · exact MergedCutProfiles.Batch319.valid12788
  · exact MergedCutProfiles.Batch455.valid18202
  · exact MergedCutProfiles.Batch455.valid18203
  · exact MergedCutProfiles.Batch319.valid12780
  · exact MergedCutProfiles.Batch319.valid12781
  · exact MergedCutProfiles.Batch319.valid12790
  · exact MergedCutProfiles.Batch022.valid894
theorem numericValid2901 : retention2901.NumericValid := by decide +kernel
def certificate2901 : RatCutBinCertificate := ⟨⟨retention2901,(1855866918952946473/1000000000000000000),(15120529320228081/1000000000000000000),(8325288334521964189/1000000000000000000),(259777396068867272681/40000000000000000),(2238560018033975593/1000000000000000000)⟩,(999718100457292219/1000000000000000000),(577484480427896763/1000000000000000000),(105433970480046889/1000000000000000000),(47887222343371771/1000000000000000000)⟩
theorem valid2901 : certificate2901.Valid := by decide +kernel
theorem sound2901 : certificate2901.Sound := rat_cut_bin_certificate_sound certificate2901 profilesValid2901 numericValid2901 valid2901

def retention2902 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(1933837877730043969/776403571869755913701),(247950511/200000000),(5/2),(18509409470794240153/8000000000000000000),true,MergedCutProfiles.Batch455.profile18204,![MergedCutProfiles.Batch455.profile18204,MergedCutProfiles.Batch455.profile18205,MergedCutProfiles.Batch023.profile920,MergedCutProfiles.Batch319.profile12775,MergedCutProfiles.Batch022.profile891,MergedCutProfiles.Batch455.profile18206,MergedCutProfiles.Batch455.profile18202,MergedCutProfiles.Batch319.profile12789,MergedCutProfiles.Batch319.profile12781,MergedCutProfiles.Batch319.profile12782,MergedCutProfiles.Batch455.profile18207,MergedCutProfiles.Batch455.profile18208,MergedCutProfiles.Batch319.profile12785,MergedCutProfiles.Batch455.profile18209,MergedCutProfiles.Batch455.profile18210,MergedCutProfiles.Batch319.profile12793]⟩
theorem profilesValid2902 : retention2902.ProfilesValid := by
  change ∀ j : Fin 16, (retention2902.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch455.valid18204
  · exact MergedCutProfiles.Batch455.valid18205
  · exact MergedCutProfiles.Batch023.valid920
  · exact MergedCutProfiles.Batch319.valid12775
  · exact MergedCutProfiles.Batch022.valid891
  · exact MergedCutProfiles.Batch455.valid18206
  · exact MergedCutProfiles.Batch455.valid18202
  · exact MergedCutProfiles.Batch319.valid12789
  · exact MergedCutProfiles.Batch319.valid12781
  · exact MergedCutProfiles.Batch319.valid12782
  · exact MergedCutProfiles.Batch455.valid18207
  · exact MergedCutProfiles.Batch455.valid18208
  · exact MergedCutProfiles.Batch319.valid12785
  · exact MergedCutProfiles.Batch455.valid18209
  · exact MergedCutProfiles.Batch455.valid18210
  · exact MergedCutProfiles.Batch319.valid12793
theorem numericValid2902 : retention2902.NumericValid := by decide +kernel
def certificate2902 : RatCutBinCertificate := ⟨⟨retention2902,(1855866918952946473/1000000000000000000),(15120529320228081/1000000000000000000),(8325288334521964189/1000000000000000000),(259777396068867272681/40000000000000000),(28815619192392623/12500000000000000)⟩,(999718100457292219/1000000000000000000),(371231915862092877/1000000000000000000),(32612589238151703/125000000000000000),(92677189472798457/500000000000000000)⟩
theorem valid2902 : certificate2902.Valid := by decide +kernel
theorem sound2902 : certificate2902.Sound := rat_cut_bin_certificate_sound certificate2902 profilesValid2902 numericValid2902 valid2902

def retention2903 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(64000000000000000000/776403571869755913701),(1933837877730043969/1000000000000000000),(19/10),(1505541365452405633367019710765115714519/773535151092017587600000000000000000000),false,MergedCutProfiles.Batch455.profile18211,(fun _ => MergedCutProfiles.Batch455.profile18211)⟩
theorem profilesValid2903 : retention2903.ProfilesValid := by
  exact MergedCutProfiles.Batch455.valid18211
theorem numericValid2903 : retention2903.NumericValid := by decide +kernel
def certificate2903 : RatCutBinCertificate := ⟨⟨retention2903,(1855866918952946473/1000000000000000000),(15120529320228081/1000000000000000000),(8325288334521964189/1000000000000000000),(259777396068867272681/40000000000000000),(484977136862280509/250000000000000000)⟩,(999718100457292219/1000000000000000000),(364414913724397509/1000000000000000000),(133859080876064869/500000000000000000),(213835215148433881/1000000000000000000)⟩
theorem valid2903 : certificate2903.Valid := by decide +kernel
theorem sound2903 : certificate2903.Sound := rat_cut_bin_certificate_sound certificate2903 profilesValid2903 numericValid2903 valid2903

def certificates : List RatCutBinCertificate := [certificate2892,certificate2893,certificate2894,certificate2895,certificate2896,certificate2897,certificate2898,certificate2899,certificate2900,certificate2901,certificate2902,certificate2903]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2892,List.forall_mem_cons.mpr ⟨sound2893,List.forall_mem_cons.mpr ⟨sound2894,List.forall_mem_cons.mpr ⟨sound2895,List.forall_mem_cons.mpr ⟨sound2896,List.forall_mem_cons.mpr ⟨sound2897,List.forall_mem_cons.mpr ⟨sound2898,List.forall_mem_cons.mpr ⟨sound2899,List.forall_mem_cons.mpr ⟨sound2900,List.forall_mem_cons.mpr ⟨sound2901,List.forall_mem_cons.mpr ⟨sound2902,List.forall_mem_cons.mpr ⟨sound2903,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch241
