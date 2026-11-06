import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch072
import Cycle12.MergedCutProfiles.Batch073
import Cycle12.MergedCutProfiles.Batch074

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch036

def retention432 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(12998050598616684509/36332269783165894480),(3040588516702043483/1000000000000000000),(13/10),(1557297633537814638183566685403584698559/1216235406680817393200000000000000000000),false,MergedCutProfiles.Batch072.profile2897,(fun _ => MergedCutProfiles.Batch072.profile2897)⟩
theorem profilesValid432 : retention432.ProfilesValid := by
  exact MergedCutProfiles.Batch072.valid2897
theorem numericValid432 : retention432.NumericValid := by decide +kernel
def certificate432 : RatCutBinCertificate := ⟨⟨retention432,(102635127272770413/50000000000000000),(247684185361181/3906250000000000),(10847452451916845639/1000000000000000000),(395155788030754533383/1000000000000000000),(158103186374411541/125000000000000000)⟩,(24878092418289623/25000000000000000),(11209844663589739/25000000000000000),(191956686537593811/1000000000000000000),(29812035349585793/200000000000000000)⟩
theorem valid432 : certificate432.Valid := by decide +kernel
theorem sound432 : certificate432.Sound := rat_cut_bin_certificate_sound certificate432 profilesValid432 numericValid432 valid432

def retention433 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(3538920496959120091/7266453956633178896),(12998050598616684509/1000000000000000000),(21/20),(21312479172985672274762578544055486687239/20796880957786695214400000000000000000000),false,MergedCutProfiles.Batch072.profile2898,(fun _ => MergedCutProfiles.Batch072.profile2898)⟩
theorem profilesValid433 : retention433.ProfilesValid := by
  exact MergedCutProfiles.Batch072.valid2898
theorem numericValid433 : retention433.NumericValid := by decide +kernel
def certificate433 : RatCutBinCertificate := ⟨⟨retention433,(102635127272770413/50000000000000000),(247684185361181/3906250000000000),(10847452451916845639/1000000000000000000),(395155788030754533383/1000000000000000000),(101219324315418777/100000000000000000)⟩,(24878092418289623/25000000000000000),(479709528185100057/1000000000000000000),(167907978139542091/1000000000000000000),(75209315593757699/500000000000000000)⟩
theorem valid433 : certificate433.Valid := by decide +kernel
theorem sound433 : certificate433.Sound := rat_cut_bin_certificate_sound certificate433 profilesValid433 numericValid433 valid433

def retention434 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(3610052798947998405/7266453956633178896),(3538920496959120091/200000000000000000),1,(17580294912037785209525631238367030541/17694602484795600455000000000000000000),false,MergedCutProfiles.Batch072.profile2899,(fun _ => MergedCutProfiles.Batch072.profile2899)⟩
theorem profilesValid434 : retention434.ProfilesValid := by
  exact MergedCutProfiles.Batch072.valid2899
theorem numericValid434 : retention434.NumericValid := by decide +kernel
def certificate434 : RatCutBinCertificate := ⟨⟨retention434,(102635127272770413/50000000000000000),(247684185361181/3906250000000000),(10847452451916845639/1000000000000000000),(395155788030754533383/1000000000000000000),(981541102356952807/1000000000000000000)⟩,(24878092418289623/25000000000000000),(487953766700391541/1000000000000000000),(16192243621790063/100000000000000000),(74912335311728651/500000000000000000)⟩
theorem valid434 : certificate434.Valid := by decide +kernel
theorem sound434 : certificate434.Sound := rat_cut_bin_certificate_sound certificate434 profilesValid434 numericValid434 valid434

def retention435 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(1/2),(722010559789599681/40000000000000000),1,(45337307424792646472857029122653/45906063058850437500000000000000),false,MergedCutProfiles.Batch072.profile2900,(fun _ => MergedCutProfiles.Batch072.profile2900)⟩
theorem profilesValid435 : retention435.ProfilesValid := by
  exact MergedCutProfiles.Batch072.valid2900
theorem numericValid435 : retention435.NumericValid := by decide +kernel
def certificate435 : RatCutBinCertificate := ⟨⟨retention435,(102635127272770413/50000000000000000),(247684185361181/3906250000000000),(10847452451916845639/1000000000000000000),(395155788030754533383/1000000000000000000),(487805787846670753/500000000000000000)⟩,(24878092418289623/25000000000000000),(245274922952740877/500000000000000000),(160066560032995707/1000000000000000000),(73705827669284209/500000000000000000)⟩
theorem valid435 : certificate435.Valid := by decide +kernel
theorem sound435 : certificate435.Sound := rat_cut_bin_certificate_sound certificate435 profilesValid435 numericValid435 valid435

def retention436 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(15580623567226746553/36332269783165894480),(3717979666524110001/1000000000000000000),(5/4),(271778651167496063120122587859538698391/237950698657543040064000000000000000000),false,MergedCutProfiles.Batch072.profile2901,(fun _ => MergedCutProfiles.Batch072.profile2901)⟩
theorem profilesValid436 : retention436.ProfilesValid := by
  exact MergedCutProfiles.Batch072.valid2901
theorem numericValid436 : retention436.NumericValid := by decide +kernel
def certificate436 : RatCutBinCertificate := ⟨⟨retention436,(121861877572770413/50000000000000000),(247684185361181/3906250000000000),(10847452451916845639/1000000000000000000),(395155788030754533383/1000000000000000000),(1124354956566897301/1000000000000000000)⟩,(99420986640053163/100000000000000000),(179998023508444653/500000000000000000),(54441043811403489/200000000000000000),(101926766988113373/500000000000000000)⟩
theorem valid436 : certificate436.Valid := by decide +kernel
theorem sound436 : certificate436.Sound := rat_cut_bin_certificate_sound certificate436 profilesValid436 numericValid436 valid436

def retention437 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(17909525016689520891/36332269783165894480),(15580623567226746553/1000000000000000000),1,(12453380702691072002971640116316963127/12464498853781397242400000000000000000),false,MergedCutProfiles.Batch072.profile2902,(fun _ => MergedCutProfiles.Batch072.profile2902)⟩
theorem profilesValid437 : retention437.ProfilesValid := by
  exact MergedCutProfiles.Batch072.valid2902
theorem numericValid437 : retention437.NumericValid := by decide +kernel
def certificate437 : RatCutBinCertificate := ⟨⟨retention437,(121861877572770413/50000000000000000),(247684185361181/3906250000000000),(10847452451916845639/1000000000000000000),(395155788030754533383/1000000000000000000),(984861362414043419/1000000000000000000)⟩,(99420986640053163/100000000000000000),(102746273550571989/250000000000000000),(111783342153166163/500000000000000000),(20585906822392217/100000000000000000)⟩
theorem valid437 : certificate437.Valid := by decide +kernel
theorem sound437 : certificate437.Sound := rat_cut_bin_certificate_sound certificate437 profilesValid437 numericValid437 valid437

def retention438 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(47601632281201095/95611236271489196),(17909525016689520891/1000000000000000000),1,(947204580560356152107804815554760137/955174667556774447520000000000000000),false,MergedCutProfiles.Batch072.profile2903,(fun _ => MergedCutProfiles.Batch072.profile2903)⟩
theorem profilesValid438 : retention438.ProfilesValid := by
  exact MergedCutProfiles.Batch072.valid2903
theorem numericValid438 : retention438.NumericValid := by decide +kernel
def certificate438 : RatCutBinCertificate := ⟨⟨retention438,(121861877572770413/50000000000000000),(247684185361181/3906250000000000),(10847452451916845639/1000000000000000000),(395155788030754533383/1000000000000000000),(122176156523561137/125000000000000000)⟩,(99420986640053163/100000000000000000),(207059294201295557/500000000000000000),(55198097558580989/250000000000000000),(203422505746957041/1000000000000000000)⟩
theorem valid438 : certificate438.Valid := by decide +kernel
theorem sound438 : certificate438.Sound := rat_cut_bin_certificate_sound certificate438 profilesValid438 numericValid438 valid438

def retention439 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(1/2),(180886202668564161/10000000000000000),1,(178650431743633302142190028848848451/180886202668564161000000000000000000),false,MergedCutProfiles.Batch072.profile2900,(fun _ => MergedCutProfiles.Batch072.profile2900)⟩
theorem profilesValid439 : retention439.ProfilesValid := by
  exact MergedCutProfiles.Batch072.valid2900
theorem numericValid439 : retention439.NumericValid := by decide +kernel
def certificate439 : RatCutBinCertificate := ⟨⟨retention439,(121861877572770413/50000000000000000),(247684185361181/3906250000000000),(10847452451916845639/1000000000000000000),(395155788030754533383/1000000000000000000),(973393271640132283/1000000000000000000)⟩,(99420986640053163/100000000000000000),(415827139554722603/1000000000000000000),(13705605702032639/62500000000000000),(201353716114990303/1000000000000000000)⟩
theorem valid439 : certificate439.Valid := by decide +kernel
theorem sound439 : certificate439.Sound := rat_cut_bin_certificate_sound certificate439 profilesValid439 numericValid439 valid439

def retention440 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(777910157391661117/35288751458599140089),(385104038312703523/500000000000000000),(67/20),(1395119542890513436747/640000000000000000000),true,MergedCutProfiles.Batch072.profile2904,![MergedCutProfiles.Batch072.profile2904,MergedCutProfiles.Batch072.profile2905,MergedCutProfiles.Batch072.profile2906,MergedCutProfiles.Batch072.profile2907,MergedCutProfiles.Batch072.profile2908,MergedCutProfiles.Batch072.profile2909,MergedCutProfiles.Batch072.profile2910,MergedCutProfiles.Batch072.profile2911,MergedCutProfiles.Batch072.profile2912,MergedCutProfiles.Batch072.profile2913,MergedCutProfiles.Batch072.profile2914,MergedCutProfiles.Batch072.profile2915,MergedCutProfiles.Batch072.profile2916,MergedCutProfiles.Batch072.profile2917,MergedCutProfiles.Batch072.profile2918,MergedCutProfiles.Batch072.profile2919]⟩
theorem profilesValid440 : retention440.ProfilesValid := by
  change ∀ j : Fin 16, (retention440.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch072.valid2904
  · exact MergedCutProfiles.Batch072.valid2905
  · exact MergedCutProfiles.Batch072.valid2906
  · exact MergedCutProfiles.Batch072.valid2907
  · exact MergedCutProfiles.Batch072.valid2908
  · exact MergedCutProfiles.Batch072.valid2909
  · exact MergedCutProfiles.Batch072.valid2910
  · exact MergedCutProfiles.Batch072.valid2911
  · exact MergedCutProfiles.Batch072.valid2912
  · exact MergedCutProfiles.Batch072.valid2913
  · exact MergedCutProfiles.Batch072.valid2914
  · exact MergedCutProfiles.Batch072.valid2915
  · exact MergedCutProfiles.Batch072.valid2916
  · exact MergedCutProfiles.Batch072.valid2917
  · exact MergedCutProfiles.Batch072.valid2918
  · exact MergedCutProfiles.Batch072.valid2919
theorem numericValid440 : retention440.NumericValid := by decide +kernel
def certificate440 : RatCutBinCertificate := ⟨⟨retention440,(514170209211313733/250000000000000000),(65254397982896969/1000000000000000000),(10929067132421787051/1000000000000000000),(193348572747214585511/500000000000000000),(1069367023648719453/500000000000000000)⟩,(995016948275565787/1000000000000000000),(102821053231663573/250000000000000000),(223300826069670719/1000000000000000000),(113616647798137157/1000000000000000000)⟩
theorem valid440 : certificate440.Valid := by decide +kernel
theorem sound440 : certificate440.Sound := rat_cut_bin_certificate_sound certificate440 profilesValid440 numericValid440 valid440

def retention441 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(885334322908252094/35288751458599140089),(777910157391661117/1000000000000000000),(33/10),(2768890189303283598769/1280000000000000000000),true,MergedCutProfiles.Batch073.profile2920,![MergedCutProfiles.Batch073.profile2920,MergedCutProfiles.Batch073.profile2921,MergedCutProfiles.Batch073.profile2922,MergedCutProfiles.Batch073.profile2923,MergedCutProfiles.Batch073.profile2924,MergedCutProfiles.Batch073.profile2925,MergedCutProfiles.Batch073.profile2926,MergedCutProfiles.Batch073.profile2927,MergedCutProfiles.Batch073.profile2928,MergedCutProfiles.Batch073.profile2929,MergedCutProfiles.Batch073.profile2930,MergedCutProfiles.Batch073.profile2931,MergedCutProfiles.Batch073.profile2932,MergedCutProfiles.Batch073.profile2933,MergedCutProfiles.Batch073.profile2934,MergedCutProfiles.Batch073.profile2935]⟩
theorem profilesValid441 : retention441.ProfilesValid := by
  change ∀ j : Fin 16, (retention441.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch073.valid2920
  · exact MergedCutProfiles.Batch073.valid2921
  · exact MergedCutProfiles.Batch073.valid2922
  · exact MergedCutProfiles.Batch073.valid2923
  · exact MergedCutProfiles.Batch073.valid2924
  · exact MergedCutProfiles.Batch073.valid2925
  · exact MergedCutProfiles.Batch073.valid2926
  · exact MergedCutProfiles.Batch073.valid2927
  · exact MergedCutProfiles.Batch073.valid2928
  · exact MergedCutProfiles.Batch073.valid2929
  · exact MergedCutProfiles.Batch073.valid2930
  · exact MergedCutProfiles.Batch073.valid2931
  · exact MergedCutProfiles.Batch073.valid2932
  · exact MergedCutProfiles.Batch073.valid2933
  · exact MergedCutProfiles.Batch073.valid2934
  · exact MergedCutProfiles.Batch073.valid2935
theorem numericValid441 : retention441.NumericValid := by decide +kernel
def certificate441 : RatCutBinCertificate := ⟨⟨retention441,(514170209211313733/250000000000000000),(65254397982896969/1000000000000000000),(10929067132421787051/1000000000000000000),(193348572747214585511/500000000000000000),(2122669241816353511/1000000000000000000)⟩,(995016948275565787/1000000000000000000),(206221041194847737/500000000000000000),(111136877289804933/500000000000000000),(5682973232946481/50000000000000000)⟩
theorem valid441 : certificate441.Valid := by decide +kernel
theorem sound441 : certificate441.Sound := rat_cut_bin_certificate_sound certificate441 profilesValid441 numericValid441 valid441

def retention442 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(960697508000000000/35288751458599140089),(442667161454126047/500000000000000000),(59/20),(1373590370022548735871/640000000000000000000),true,MergedCutProfiles.Batch073.profile2936,![MergedCutProfiles.Batch073.profile2936,MergedCutProfiles.Batch073.profile2937,MergedCutProfiles.Batch073.profile2938,MergedCutProfiles.Batch073.profile2939,MergedCutProfiles.Batch073.profile2940,MergedCutProfiles.Batch073.profile2941,MergedCutProfiles.Batch073.profile2942,MergedCutProfiles.Batch073.profile2943,MergedCutProfiles.Batch073.profile2944,MergedCutProfiles.Batch073.profile2945,MergedCutProfiles.Batch073.profile2931,MergedCutProfiles.Batch073.profile2932,MergedCutProfiles.Batch072.profile2919,MergedCutProfiles.Batch073.profile2946,MergedCutProfiles.Batch073.profile2947,MergedCutProfiles.Batch073.profile2948]⟩
theorem profilesValid442 : retention442.ProfilesValid := by
  change ∀ j : Fin 16, (retention442.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch073.valid2936
  · exact MergedCutProfiles.Batch073.valid2937
  · exact MergedCutProfiles.Batch073.valid2938
  · exact MergedCutProfiles.Batch073.valid2939
  · exact MergedCutProfiles.Batch073.valid2940
  · exact MergedCutProfiles.Batch073.valid2941
  · exact MergedCutProfiles.Batch073.valid2942
  · exact MergedCutProfiles.Batch073.valid2943
  · exact MergedCutProfiles.Batch073.valid2944
  · exact MergedCutProfiles.Batch073.valid2945
  · exact MergedCutProfiles.Batch073.valid2931
  · exact MergedCutProfiles.Batch073.valid2932
  · exact MergedCutProfiles.Batch072.valid2919
  · exact MergedCutProfiles.Batch073.valid2946
  · exact MergedCutProfiles.Batch073.valid2947
  · exact MergedCutProfiles.Batch073.valid2948
theorem numericValid442 : retention442.NumericValid := by decide +kernel
def certificate442 : RatCutBinCertificate := ⟨⟨retention442,(514170209211313733/250000000000000000),(65254397982896969/1000000000000000000),(10929067132421787051/1000000000000000000),(193348572747214585511/500000000000000000),(211000701058145253/100000000000000000)⟩,(995016948275565787/1000000000000000000),(391055598261191721/1000000000000000000),(241778376913669379/1000000000000000000),(4217704522821031/31250000000000000)⟩
theorem valid442 : certificate442.Valid := by decide +kernel
theorem sound442 : certificate442.Sound := rat_cut_bin_certificate_sound certificate442 profilesValid442 numericValid442 valid442

def retention443 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(1158202221330349133/35288751458599140089),(240174377/250000000),(11/4),(4237840452578065467/2000000000000000000),true,MergedCutProfiles.Batch073.profile2949,![MergedCutProfiles.Batch073.profile2949,MergedCutProfiles.Batch072.profile2906,MergedCutProfiles.Batch073.profile2950,MergedCutProfiles.Batch073.profile2951,MergedCutProfiles.Batch073.profile2952,MergedCutProfiles.Batch073.profile2953,MergedCutProfiles.Batch073.profile2954,MergedCutProfiles.Batch073.profile2955,MergedCutProfiles.Batch073.profile2956,MergedCutProfiles.Batch073.profile2957,MergedCutProfiles.Batch073.profile2958,MergedCutProfiles.Batch073.profile2959,MergedCutProfiles.Batch074.profile2960,MergedCutProfiles.Batch074.profile2961,MergedCutProfiles.Batch074.profile2962,MergedCutProfiles.Batch074.profile2963]⟩
theorem profilesValid443 : retention443.ProfilesValid := by
  change ∀ j : Fin 16, (retention443.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch073.valid2949
  · exact MergedCutProfiles.Batch072.valid2906
  · exact MergedCutProfiles.Batch073.valid2950
  · exact MergedCutProfiles.Batch073.valid2951
  · exact MergedCutProfiles.Batch073.valid2952
  · exact MergedCutProfiles.Batch073.valid2953
  · exact MergedCutProfiles.Batch073.valid2954
  · exact MergedCutProfiles.Batch073.valid2955
  · exact MergedCutProfiles.Batch073.valid2956
  · exact MergedCutProfiles.Batch073.valid2957
  · exact MergedCutProfiles.Batch073.valid2958
  · exact MergedCutProfiles.Batch073.valid2959
  · exact MergedCutProfiles.Batch074.valid2960
  · exact MergedCutProfiles.Batch074.valid2961
  · exact MergedCutProfiles.Batch074.valid2962
  · exact MergedCutProfiles.Batch074.valid2963
theorem numericValid443 : retention443.NumericValid := by decide +kernel
def certificate443 : RatCutBinCertificate := ⟨⟨retention443,(514170209211313733/250000000000000000),(65254397982896969/1000000000000000000),(10929067132421787051/1000000000000000000),(193348572747214585511/500000000000000000),(2085148440337102573/1000000000000000000)⟩,(995016948275565787/1000000000000000000),(191000537679954777/500000000000000000),(250384818106170151/1000000000000000000),(36664871861932759/250000000000000000)⟩
theorem valid443 : certificate443.Valid := by decide +kernel
theorem sound443 : certificate443.Sound := rat_cut_bin_certificate_sound certificate443 profilesValid443 numericValid443 valid443

def certificates : List RatCutBinCertificate := [certificate432,certificate433,certificate434,certificate435,certificate436,certificate437,certificate438,certificate439,certificate440,certificate441,certificate442,certificate443]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound432,List.forall_mem_cons.mpr ⟨sound433,List.forall_mem_cons.mpr ⟨sound434,List.forall_mem_cons.mpr ⟨sound435,List.forall_mem_cons.mpr ⟨sound436,List.forall_mem_cons.mpr ⟨sound437,List.forall_mem_cons.mpr ⟨sound438,List.forall_mem_cons.mpr ⟨sound439,List.forall_mem_cons.mpr ⟨sound440,List.forall_mem_cons.mpr ⟨sound441,List.forall_mem_cons.mpr ⟨sound442,List.forall_mem_cons.mpr ⟨sound443,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch036
