import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch146
import Cycle12.MergedCutProfiles.Batch147
import Cycle12.MergedCutProfiles.Batch148

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch072

def retention864 : RatCutRetentionCertificate := ⟨(49/1000),(197/4000),(894699353091764873/9873727067984791355),(965565954885058859/1000000000000000000),(13/5),(2466881420469519540647/1280000000000000000000),true,MergedCutProfiles.Batch146.profile5862,![MergedCutProfiles.Batch146.profile5862,MergedCutProfiles.Batch146.profile5863,MergedCutProfiles.Batch146.profile5864,MergedCutProfiles.Batch146.profile5865,MergedCutProfiles.Batch146.profile5866,MergedCutProfiles.Batch146.profile5867,MergedCutProfiles.Batch146.profile5868,MergedCutProfiles.Batch146.profile5869,MergedCutProfiles.Batch146.profile5870,MergedCutProfiles.Batch146.profile5871,MergedCutProfiles.Batch146.profile5872,MergedCutProfiles.Batch146.profile5873,MergedCutProfiles.Batch146.profile5874,MergedCutProfiles.Batch146.profile5875,MergedCutProfiles.Batch146.profile5876,MergedCutProfiles.Batch146.profile5877]⟩
theorem profilesValid864 : retention864.ProfilesValid := by
  change ∀ j : Fin 16, (retention864.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch146.valid5862
  · exact MergedCutProfiles.Batch146.valid5863
  · exact MergedCutProfiles.Batch146.valid5864
  · exact MergedCutProfiles.Batch146.valid5865
  · exact MergedCutProfiles.Batch146.valid5866
  · exact MergedCutProfiles.Batch146.valid5867
  · exact MergedCutProfiles.Batch146.valid5868
  · exact MergedCutProfiles.Batch146.valid5869
  · exact MergedCutProfiles.Batch146.valid5870
  · exact MergedCutProfiles.Batch146.valid5871
  · exact MergedCutProfiles.Batch146.valid5872
  · exact MergedCutProfiles.Batch146.valid5873
  · exact MergedCutProfiles.Batch146.valid5874
  · exact MergedCutProfiles.Batch146.valid5875
  · exact MergedCutProfiles.Batch146.valid5876
  · exact MergedCutProfiles.Batch146.valid5877
theorem numericValid864 : retention864.NumericValid := by decide +kernel
def certificate864 : RatCutBinCertificate := ⟨⟨retention864,(2158102615044373853/1000000000000000000),(115712893678697359/1000000000000000000),(818779701756686403/62500000000000000),(259069613155146490359/1000000000000000000),(938840641372630143/500000000000000000)⟩,(992615489941763403/1000000000000000000),(38126430424338757/100000000000000000),(251094496737701147/1000000000000000000),(69799201261278107/500000000000000000)⟩
theorem valid864 : certificate864.Valid := by decide +kernel
theorem sound864 : certificate864.Sound := rat_cut_bin_certificate_sound certificate864 profilesValid864 numericValid864 valid864

def retention865 : RatCutRetentionCertificate := ⟨(49/1000),(197/4000),(5675269345786197701/19747454135969582710),(894699353091764873/500000000000000000),(33/20),(918075335524012102761/640000000000000000000),true,MergedCutProfiles.Batch146.profile5878,![MergedCutProfiles.Batch146.profile5878,MergedCutProfiles.Batch146.profile5879,MergedCutProfiles.Batch147.profile5880,MergedCutProfiles.Batch147.profile5881,MergedCutProfiles.Batch147.profile5882,MergedCutProfiles.Batch147.profile5883,MergedCutProfiles.Batch147.profile5884,MergedCutProfiles.Batch147.profile5885,MergedCutProfiles.Batch147.profile5886,MergedCutProfiles.Batch147.profile5887,MergedCutProfiles.Batch147.profile5888,MergedCutProfiles.Batch147.profile5889,MergedCutProfiles.Batch147.profile5890,MergedCutProfiles.Batch147.profile5891,MergedCutProfiles.Batch147.profile5892,MergedCutProfiles.Batch147.profile5893]⟩
theorem profilesValid865 : retention865.ProfilesValid := by
  change ∀ j : Fin 16, (retention865.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch146.valid5878
  · exact MergedCutProfiles.Batch146.valid5879
  · exact MergedCutProfiles.Batch147.valid5880
  · exact MergedCutProfiles.Batch147.valid5881
  · exact MergedCutProfiles.Batch147.valid5882
  · exact MergedCutProfiles.Batch147.valid5883
  · exact MergedCutProfiles.Batch147.valid5884
  · exact MergedCutProfiles.Batch147.valid5885
  · exact MergedCutProfiles.Batch147.valid5886
  · exact MergedCutProfiles.Batch147.valid5887
  · exact MergedCutProfiles.Batch147.valid5888
  · exact MergedCutProfiles.Batch147.valid5889
  · exact MergedCutProfiles.Batch147.valid5890
  · exact MergedCutProfiles.Batch147.valid5891
  · exact MergedCutProfiles.Batch147.valid5892
  · exact MergedCutProfiles.Batch147.valid5893
theorem numericValid865 : retention865.NumericValid := by decide +kernel
def certificate865 : RatCutBinCertificate := ⟨⟨retention865,(2158102615044373853/1000000000000000000),(115712893678697359/1000000000000000000),(818779701756686403/62500000000000000),(259069613155146490359/1000000000000000000),(70151788735353801/50000000000000000)⟩,(992615489941763403/1000000000000000000),(84247603396368067/200000000000000000),(8583076185151223/40000000000000000),(140455211216613607/1000000000000000000)⟩
theorem valid865 : certificate865.Valid := by decide +kernel
theorem sound865 : certificate865.Sound := rat_cut_bin_certificate_sound certificate865 profilesValid865 numericValid865 valid865

def retention866 : RatCutRetentionCertificate := ⟨(49/1000),(197/4000),(4529612493637825312/9873727067984791355),(5675269345786197701/1000000000000000000),1,(265707569933187492821/256000000000000000000),true,MergedCutProfiles.Batch147.profile5894,![MergedCutProfiles.Batch147.profile5894,MergedCutProfiles.Batch147.profile5895,MergedCutProfiles.Batch147.profile5896,MergedCutProfiles.Batch147.profile5897,MergedCutProfiles.Batch147.profile5898,MergedCutProfiles.Batch147.profile5899,MergedCutProfiles.Batch147.profile5900,MergedCutProfiles.Batch147.profile5901,MergedCutProfiles.Batch147.profile5902,MergedCutProfiles.Batch147.profile5903,MergedCutProfiles.Batch147.profile5904,MergedCutProfiles.Batch147.profile5905,MergedCutProfiles.Batch147.profile5906,MergedCutProfiles.Batch147.profile5907,MergedCutProfiles.Batch147.profile5908,MergedCutProfiles.Batch147.profile5909]⟩
theorem profilesValid866 : retention866.ProfilesValid := by
  change ∀ j : Fin 16, (retention866.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch147.valid5894
  · exact MergedCutProfiles.Batch147.valid5895
  · exact MergedCutProfiles.Batch147.valid5896
  · exact MergedCutProfiles.Batch147.valid5897
  · exact MergedCutProfiles.Batch147.valid5898
  · exact MergedCutProfiles.Batch147.valid5899
  · exact MergedCutProfiles.Batch147.valid5900
  · exact MergedCutProfiles.Batch147.valid5901
  · exact MergedCutProfiles.Batch147.valid5902
  · exact MergedCutProfiles.Batch147.valid5903
  · exact MergedCutProfiles.Batch147.valid5904
  · exact MergedCutProfiles.Batch147.valid5905
  · exact MergedCutProfiles.Batch147.valid5906
  · exact MergedCutProfiles.Batch147.valid5907
  · exact MergedCutProfiles.Batch147.valid5908
  · exact MergedCutProfiles.Batch147.valid5909
theorem numericValid866 : retention866.NumericValid := by decide +kernel
def certificate866 : RatCutBinCertificate := ⟨⟨retention866,(2158102615044373853/1000000000000000000),(115712893678697359/1000000000000000000),(818779701756686403/62500000000000000),(259069613155146490359/1000000000000000000),(509428384085389087/500000000000000000)⟩,(992615489941763403/1000000000000000000),(240855837183399373/500000000000000000),(83220715899980959/500000000000000000),(71307801393735263/500000000000000000)⟩
theorem valid866 : certificate866.Valid := by decide +kernel
theorem sound866 : certificate866.Sound := rat_cut_bin_certificate_sound certificate866 profilesValid866 numericValid866 valid866

def retention867 : RatCutRetentionCertificate := ⟨(49/1000),(197/4000),(4856357685774701437/9873727067984791355),(141550390426182041/15625000000000000),(21/20),(914157718986824275777197953929765153439/905922498727565062400000000000000000000),false,MergedCutProfiles.Batch147.profile5910,(fun _ => MergedCutProfiles.Batch147.profile5910)⟩
theorem profilesValid867 : retention867.ProfilesValid := by
  exact MergedCutProfiles.Batch147.valid5910
theorem numericValid867 : retention867.NumericValid := by decide +kernel
def certificate867 : RatCutBinCertificate := ⟨⟨retention867,(2158102615044373853/1000000000000000000),(115712893678697359/1000000000000000000),(818779701756686403/62500000000000000),(259069613155146490359/1000000000000000000),(197814892372160117/200000000000000000)⟩,(992615489941763403/1000000000000000000),(119696993625688053/250000000000000000),(42146452604655903/250000000000000000),(143368193771934393/1000000000000000000)⟩
theorem valid867 : certificate867.Valid := by decide +kernel
theorem sound867 : certificate867.Sound := rat_cut_bin_certificate_sound certificate867 profilesValid867 numericValid867 valid867

def retention868 : RatCutRetentionCertificate := ⟨(49/1000),(197/4000),(9809842525264896903/19747454135969582710),(4856357685774701437/500000000000000000),(21/20),(3889000138178644241109903473142369003351/3885086148619761149600000000000000000000),false,MergedCutProfiles.Batch147.profile5911,(fun _ => MergedCutProfiles.Batch147.profile5911)⟩
theorem profilesValid868 : retention868.ProfilesValid := by
  exact MergedCutProfiles.Batch147.valid5911
theorem numericValid868 : retention868.NumericValid := by decide +kernel
def certificate868 : RatCutBinCertificate := ⟨⟨retention868,(2158102615044373853/1000000000000000000),(115712893678697359/1000000000000000000),(818779701756686403/62500000000000000),(259069613155146490359/1000000000000000000),(980991539972860821/1000000000000000000)⟩,(992615489941763403/1000000000000000000),(120187531703339493/250000000000000000),(16714471237012469/100000000000000000),(70971306151076293/500000000000000000)⟩
theorem valid868 : certificate868.Valid := by decide +kernel
theorem sound868 : certificate868.Sound := rat_cut_bin_certificate_sound certificate868 profilesValid868 numericValid868 valid868

def retention869 : RatCutRetentionCertificate := ⟨(49/1000),(197/4000),(1/2),(9809842525264896903/1000000000000000000),(21/20),(15615587728831210762234280658766921916231/15695748040423835044800000000000000000000),false,MergedCutProfiles.Batch147.profile5912,(fun _ => MergedCutProfiles.Batch147.profile5912)⟩
theorem profilesValid869 : retention869.ProfilesValid := by
  exact MergedCutProfiles.Batch147.valid5912
theorem numericValid869 : retention869.NumericValid := by decide +kernel
def certificate869 : RatCutBinCertificate := ⟨⟨retention869,(2158102615044373853/1000000000000000000),(115712893678697359/1000000000000000000),(818779701756686403/62500000000000000),(259069613155146490359/1000000000000000000),(243719243399647457/250000000000000000)⟩,(992615489941763403/1000000000000000000),(483491596273276871/1000000000000000000),(82572324985719683/500000000000000000),(17444834596496049/125000000000000000)⟩
theorem valid869 : certificate869.Valid := by decide +kernel
theorem sound869 : certificate869.Sound := rat_cut_bin_certificate_sound certificate869 profilesValid869 numericValid869 valid869

def retention870 : RatCutRetentionCertificate := ⟨(49/1000),(197/4000),(4451909962778221198/9873727067984791355),(1854665013682387367/500000000000000000),(6/5),(405026691932199302463452554815289579199/370933002736477473400000000000000000000),false,MergedCutProfiles.Batch147.profile5913,(fun _ => MergedCutProfiles.Batch147.profile5913)⟩
theorem profilesValid870 : retention870.ProfilesValid := by
  exact MergedCutProfiles.Batch147.valid5913
theorem numericValid870 : retention870.NumericValid := by decide +kernel
def certificate870 : RatCutBinCertificate := ⟨⟨retention870,(2530573072044373853/1000000000000000000),(115712893678697359/1000000000000000000),(818779701756686403/62500000000000000),(259069613155146490359/1000000000000000000),(1065088416245562493/1000000000000000000)⟩,(991339559862810491/1000000000000000000),(15240093807198557/40000000000000000),(6283679144284291/25000000000000000),(36847959456665949/200000000000000000)⟩
theorem valid870 : certificate870.Valid := by decide +kernel
theorem sound870 : certificate870.Sound := rat_cut_bin_certificate_sound certificate870 profilesValid870 numericValid870 valid870

def retention871 : RatCutRetentionCertificate := ⟨(49/1000),(197/4000),(4868988361607321842/9873727067984791355),(2225954981389110599/250000000000000000),(21/20),(895905609944185766700157759134496819679/890381992555644239600000000000000000000),false,MergedCutProfiles.Batch147.profile5914,(fun _ => MergedCutProfiles.Batch147.profile5914)⟩
theorem profilesValid871 : retention871.ProfilesValid := by
  exact MergedCutProfiles.Batch147.valid5914
theorem numericValid871 : retention871.NumericValid := by decide +kernel
def certificate871 : RatCutBinCertificate := ⟨⟨retention871,(2530573072044373853/1000000000000000000),(115712893678697359/1000000000000000000),(818779701756686403/62500000000000000),(259069613155146490359/1000000000000000000),(12284163490310371/12500000000000000)⟩,(991339559862810491/1000000000000000000),(82586247067955611/200000000000000000),(22184083534423487/100000000000000000),(187021083520037379/1000000000000000000)⟩
theorem valid871 : certificate871.Valid := by decide +kernel
theorem sound871 : certificate871.Sound := rat_cut_bin_certificate_sound certificate871 profilesValid871 numericValid871 valid871

def retention872 : RatCutRetentionCertificate := ⟨(49/1000),(197/4000),(9835356490446790121/19747454135969582710),(2434494180803660921/250000000000000000),(21/20),(972374893206314117697341131351070450319/973797672321464368400000000000000000000),false,MergedCutProfiles.Batch147.profile5915,(fun _ => MergedCutProfiles.Batch147.profile5915)⟩
theorem profilesValid872 : retention872.ProfilesValid := by
  exact MergedCutProfiles.Batch147.valid5915
theorem numericValid872 : retention872.NumericValid := by decide +kernel
def certificate872 : RatCutBinCertificate := ⟨⟨retention872,(2530573072044373853/1000000000000000000),(115712893678697359/1000000000000000000),(818779701756686403/62500000000000000),(259069613155146490359/1000000000000000000),(487534231943559621/500000000000000000)⟩,(991339559862810491/1000000000000000000),(416177119292570297/1000000000000000000),(13686421575696303/62500000000000000),(46184427804156141/250000000000000000)⟩
theorem valid872 : certificate872.Valid := by decide +kernel
theorem sound872 : certificate872.Sound := rat_cut_bin_certificate_sound certificate872 profilesValid872 numericValid872 valid872

def retention873 : RatCutRetentionCertificate := ⟨(49/1000),(197/4000),(1/2),(9835356490446790121/1000000000000000000),(21/20),(15656994215701469064306350440565695444439/15736570384714864193600000000000000000000),false,MergedCutProfiles.Batch147.profile5912,(fun _ => MergedCutProfiles.Batch147.profile5912)⟩
theorem profilesValid873 : retention873.ProfilesValid := by
  exact MergedCutProfiles.Batch147.valid5912
theorem numericValid873 : retention873.NumericValid := by decide +kernel
def certificate873 : RatCutBinCertificate := ⟨⟨retention873,(2530573072044373853/1000000000000000000),(115712893678697359/1000000000000000000),(818779701756686403/62500000000000000),(259069613155146490359/1000000000000000000),(242868192359539249/250000000000000000)⟩,(991339559862810491/1000000000000000000),(417717508076180619/1000000000000000000),(27204407191512517/125000000000000000),(183131153630177223/1000000000000000000)⟩
theorem valid873 : certificate873.Valid := by decide +kernel
theorem sound873 : certificate873.Sound := rat_cut_bin_certificate_sound certificate873 profilesValid873 numericValid873 valid873

def retention874 : RatCutRetentionCertificate := ⟨(197/4000),(99/2000),(852069711175689275/19520632267002855852),(843633377401672549/1000000000000000000),(29/10),(165912175884216760927/80000000000000000000),true,MergedCutProfiles.Batch147.profile5916,![MergedCutProfiles.Batch147.profile5916,MergedCutProfiles.Batch147.profile5917,MergedCutProfiles.Batch147.profile5918,MergedCutProfiles.Batch147.profile5919,MergedCutProfiles.Batch148.profile5920,MergedCutProfiles.Batch148.profile5921,MergedCutProfiles.Batch148.profile5922,MergedCutProfiles.Batch148.profile5923,MergedCutProfiles.Batch148.profile5924,MergedCutProfiles.Batch148.profile5925,MergedCutProfiles.Batch148.profile5926,MergedCutProfiles.Batch148.profile5927,MergedCutProfiles.Batch148.profile5928,MergedCutProfiles.Batch148.profile5929,MergedCutProfiles.Batch148.profile5930,MergedCutProfiles.Batch148.profile5931]⟩
theorem profilesValid874 : retention874.ProfilesValid := by
  change ∀ j : Fin 16, (retention874.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch147.valid5916
  · exact MergedCutProfiles.Batch147.valid5917
  · exact MergedCutProfiles.Batch147.valid5918
  · exact MergedCutProfiles.Batch147.valid5919
  · exact MergedCutProfiles.Batch148.valid5920
  · exact MergedCutProfiles.Batch148.valid5921
  · exact MergedCutProfiles.Batch148.valid5922
  · exact MergedCutProfiles.Batch148.valid5923
  · exact MergedCutProfiles.Batch148.valid5924
  · exact MergedCutProfiles.Batch148.valid5925
  · exact MergedCutProfiles.Batch148.valid5926
  · exact MergedCutProfiles.Batch148.valid5927
  · exact MergedCutProfiles.Batch148.valid5928
  · exact MergedCutProfiles.Batch148.valid5929
  · exact MergedCutProfiles.Batch148.valid5930
  · exact MergedCutProfiles.Batch148.valid5931
theorem numericValid874 : retention874.NumericValid := by decide +kernel
def certificate874 : RatCutBinCertificate := ⟨⟨retention874,(134770246555588883/62500000000000000),(7315173282470881/62500000000000000),(13154822491454154077/1000000000000000000),(128578448836555681817/500000000000000000),(2018253834874430929/1000000000000000000)⟩,(496288820713863167/500000000000000000),(372741808017167517/1000000000000000000),(51881544285566919/200000000000000000),(870722206264479/6250000000000000)⟩
theorem valid874 : certificate874.Valid := by decide +kernel
theorem sound874 : certificate874.Sound := rat_cut_bin_certificate_sound certificate874 profilesValid874 numericValid874 valid874

def retention875 : RatCutRetentionCertificate := ⟨(197/4000),(99/2000),(153778233401529433/3253438711167142642),(34082788447027571/40000000000000000),(29/10),(105811232498308158863/51200000000000000000),true,MergedCutProfiles.Batch148.profile5932,![MergedCutProfiles.Batch148.profile5932,MergedCutProfiles.Batch148.profile5933,MergedCutProfiles.Batch148.profile5934,MergedCutProfiles.Batch148.profile5935,MergedCutProfiles.Batch148.profile5936,MergedCutProfiles.Batch148.profile5937,MergedCutProfiles.Batch148.profile5938,MergedCutProfiles.Batch148.profile5939,MergedCutProfiles.Batch148.profile5940,MergedCutProfiles.Batch148.profile5941,MergedCutProfiles.Batch148.profile5942,MergedCutProfiles.Batch148.profile5928,MergedCutProfiles.Batch148.profile5943,MergedCutProfiles.Batch148.profile5944,MergedCutProfiles.Batch148.profile5945,MergedCutProfiles.Batch148.profile5946]⟩
theorem profilesValid875 : retention875.ProfilesValid := by
  change ∀ j : Fin 16, (retention875.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch148.valid5932
  · exact MergedCutProfiles.Batch148.valid5933
  · exact MergedCutProfiles.Batch148.valid5934
  · exact MergedCutProfiles.Batch148.valid5935
  · exact MergedCutProfiles.Batch148.valid5936
  · exact MergedCutProfiles.Batch148.valid5937
  · exact MergedCutProfiles.Batch148.valid5938
  · exact MergedCutProfiles.Batch148.valid5939
  · exact MergedCutProfiles.Batch148.valid5940
  · exact MergedCutProfiles.Batch148.valid5941
  · exact MergedCutProfiles.Batch148.valid5942
  · exact MergedCutProfiles.Batch148.valid5928
  · exact MergedCutProfiles.Batch148.valid5943
  · exact MergedCutProfiles.Batch148.valid5944
  · exact MergedCutProfiles.Batch148.valid5945
  · exact MergedCutProfiles.Batch148.valid5946
theorem numericValid875 : retention875.NumericValid := by decide +kernel
def certificate875 : RatCutBinCertificate := ⟨⟨retention875,(134770246555588883/62500000000000000),(7315173282470881/62500000000000000),(13154822491454154077/1000000000000000000),(128578448836555681817/500000000000000000),(2010977373535669609/1000000000000000000)⟩,(496288820713863167/500000000000000000),(37257503389787261/100000000000000000),(129786164129955689/500000000000000000),(69659160871132273/500000000000000000)⟩
theorem valid875 : certificate875.Valid := by decide +kernel
theorem sound875 : certificate875.Sound := rat_cut_bin_certificate_sound certificate875 profilesValid875 numericValid875 valid875

def certificates : List RatCutBinCertificate := [certificate864,certificate865,certificate866,certificate867,certificate868,certificate869,certificate870,certificate871,certificate872,certificate873,certificate874,certificate875]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound864,List.forall_mem_cons.mpr ⟨sound865,List.forall_mem_cons.mpr ⟨sound866,List.forall_mem_cons.mpr ⟨sound867,List.forall_mem_cons.mpr ⟨sound868,List.forall_mem_cons.mpr ⟨sound869,List.forall_mem_cons.mpr ⟨sound870,List.forall_mem_cons.mpr ⟨sound871,List.forall_mem_cons.mpr ⟨sound872,List.forall_mem_cons.mpr ⟨sound873,List.forall_mem_cons.mpr ⟨sound874,List.forall_mem_cons.mpr ⟨sound875,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch072
