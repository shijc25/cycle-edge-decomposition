import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch019
import Cycle12.MergedCutProfiles.Batch020
import Cycle12.MergedCutProfiles.Batch021
import Cycle12.MergedCutProfiles.Batch317
import Cycle12.MergedCutProfiles.Batch318

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch169

def retention2028 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(64000000000000000000/444163735094597351287),(218143309212850761/12500000000000000),1,(120739414804335848194927992948980093039/69805858948112243520000000000000000000),false,MergedCutProfiles.Batch317.profile12703,(fun _ => MergedCutProfiles.Batch317.profile12703)⟩
theorem profilesValid2028 : retention2028.ProfilesValid := by
  exact MergedCutProfiles.Batch317.valid12703
theorem numericValid2028 : retention2028.NumericValid := by decide +kernel
def certificate2028 : RatCutBinCertificate := ⟨⟨retention2028,(1872801735989206349/1000000000000000000),(1060946273715283/100000000000000000),(8010371959623307101/1000000000000000000),(714899821114160991899/200000000000000000),(17271653961069663/10000000000000000)⟩,(499740466038570041/500000000000000000),(65980251609646511/250000000000000000),(384449004479565299/1000000000000000000),(15097154014817203/25000000000000000)⟩
theorem valid2028 : certificate2028.Valid := by decide +kernel
theorem sound2028 : certificate2028.Sound := rat_cut_bin_certificate_sound certificate2028 profilesValid2028 numericValid2028 valid2028

def retention2029 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(1/2),64,1,(255370070520985369056173916463207973031/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch019.profile763,(fun _ => MergedCutProfiles.Batch019.profile763)⟩
theorem profilesValid2029 : retention2029.ProfilesValid := by
  exact MergedCutProfiles.Batch019.valid763
theorem numericValid2029 : retention2029.NumericValid := by decide +kernel
def certificate2029 : RatCutBinCertificate := ⟨⟨retention2029,(1872801735989206349/1000000000000000000),(1060946273715283/100000000000000000),(8010371959623307101/1000000000000000000),(714899821114160991899/200000000000000000),(1554779494116457/1562500000000000)⟩,(499740466038570041/500000000000000000),(54763706996968089/125000000000000000),(200324149337517401/1000000000000000000),(196179824099827621/1000000000000000000)⟩
theorem valid2029 : certificate2029.Valid := by decide +kernel
theorem sound2029 : certificate2029.Sound := rat_cut_bin_certificate_sound certificate2029 profilesValid2029 numericValid2029 valid2029

def retention2030 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(64000000000000000000/444163735094597351287),(2506602540922815353/500000000000000000),(11/10),(212296489832420165717963477051085175909/125330127046140767650000000000000000000),false,MergedCutProfiles.Batch317.profile12703,(fun _ => MergedCutProfiles.Batch317.profile12703)⟩
theorem profilesValid2030 : retention2030.ProfilesValid := by
  exact MergedCutProfiles.Batch317.valid12703
theorem numericValid2030 : retention2030.NumericValid := by decide +kernel
def certificate2030 : RatCutBinCertificate := ⟨⟨retention2030,(2153649835989206349/1000000000000000000),(1060946273715283/100000000000000000),(8010371959623307101/1000000000000000000),(714899821114160991899/200000000000000000),(338152124999262963/200000000000000000)⟩,(199880618290592343/200000000000000000),(142850837501845531/1000000000000000000),(144493863114613811/250000000000000000),(69429458063441167/100000000000000000)⟩
theorem valid2030 : certificate2030.Valid := by decide +kernel
theorem sound2030 : certificate2030.Sound := rat_cut_bin_certificate_sound certificate2030 profilesValid2030 numericValid2030 valid2030

def retention2031 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(1/2),64,1,(255370070520985369056173916463207973031/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch019.profile763,(fun _ => MergedCutProfiles.Batch019.profile763)⟩
theorem profilesValid2031 : retention2031.ProfilesValid := by
  exact MergedCutProfiles.Batch019.valid763
theorem numericValid2031 : retention2031.NumericValid := by decide +kernel
def certificate2031 : RatCutBinCertificate := ⟨⟨retention2031,(2153649835989206349/1000000000000000000),(1060946273715283/100000000000000000),(8010371959623307101/1000000000000000000),(714899821114160991899/200000000000000000),(994686902547797963/1000000000000000000)⟩,(199880618290592343/200000000000000000),(60704169994904807/250000000000000000),(51673362375251079/125000000000000000),(101163543519760799/250000000000000000)⟩
theorem valid2031 : certificate2031.Valid := by decide +kernel
theorem sound2031 : certificate2031.Sound := rat_cut_bin_certificate_sound certificate2031 profilesValid2031 numericValid2031 valid2031

def retention2032 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(627656122555121105/391610370718798704527),(609196848838466723/1000000000000000000),4,(578367556785086370851/256000000000000000000),true,MergedCutProfiles.Batch317.profile12704,![MergedCutProfiles.Batch317.profile12704,MergedCutProfiles.Batch317.profile12705,MergedCutProfiles.Batch317.profile12706,MergedCutProfiles.Batch020.profile804,MergedCutProfiles.Batch317.profile12707,MergedCutProfiles.Batch019.profile766,MergedCutProfiles.Batch019.profile781,MergedCutProfiles.Batch020.profile805,MergedCutProfiles.Batch317.profile12708,MergedCutProfiles.Batch317.profile12709,MergedCutProfiles.Batch317.profile12710,MergedCutProfiles.Batch019.profile769,MergedCutProfiles.Batch317.profile12711,MergedCutProfiles.Batch317.profile12712,MergedCutProfiles.Batch019.profile796,MergedCutProfiles.Batch317.profile12713]⟩
theorem profilesValid2032 : retention2032.ProfilesValid := by
  change ∀ j : Fin 16, (retention2032.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch317.valid12704
  · exact MergedCutProfiles.Batch317.valid12705
  · exact MergedCutProfiles.Batch317.valid12706
  · exact MergedCutProfiles.Batch020.valid804
  · exact MergedCutProfiles.Batch317.valid12707
  · exact MergedCutProfiles.Batch019.valid766
  · exact MergedCutProfiles.Batch019.valid781
  · exact MergedCutProfiles.Batch020.valid805
  · exact MergedCutProfiles.Batch317.valid12708
  · exact MergedCutProfiles.Batch317.valid12709
  · exact MergedCutProfiles.Batch317.valid12710
  · exact MergedCutProfiles.Batch019.valid769
  · exact MergedCutProfiles.Batch317.valid12711
  · exact MergedCutProfiles.Batch317.valid12712
  · exact MergedCutProfiles.Batch019.valid796
  · exact MergedCutProfiles.Batch317.valid12713
theorem numericValid2032 : retention2032.NumericValid := by decide +kernel
def certificate2032 : RatCutBinCertificate := ⟨⟨retention2032,(1879312695523397901/1000000000000000000),(12019078477736559/1000000000000000000),(4056637588455089877/500000000000000000),(3192136288045801448521/1000000000000000000),(2248112128881106797/1000000000000000000)⟩,(99941751051347537/100000000000000000),(268751422437290243/500000000000000000),(64401983594394147/500000000000000000),(58783594221625617/1000000000000000000)⟩
theorem valid2032 : certificate2032.Valid := by decide +kernel
theorem sound2032 : certificate2032.Sound := rat_cut_bin_certificate_sound certificate2032 profilesValid2032 numericValid2032 valid2032

def retention2033 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(1244293919000000000/391610370718798704527),(125531224511024221/200000000000000000),4,(29071626689074590933/12800000000000000000),true,MergedCutProfiles.Batch317.profile12705,![MergedCutProfiles.Batch317.profile12705,MergedCutProfiles.Batch020.profile804,MergedCutProfiles.Batch020.profile817,MergedCutProfiles.Batch020.profile805,MergedCutProfiles.Batch317.profile12709,MergedCutProfiles.Batch317.profile12714,MergedCutProfiles.Batch317.profile12712,MergedCutProfiles.Batch317.profile12713,MergedCutProfiles.Batch019.profile783,MergedCutProfiles.Batch317.profile12715,MergedCutProfiles.Batch317.profile12716,MergedCutProfiles.Batch317.profile12717,MergedCutProfiles.Batch317.profile12718,MergedCutProfiles.Batch317.profile12719,MergedCutProfiles.Batch318.profile12720,MergedCutProfiles.Batch019.profile785]⟩
theorem profilesValid2033 : retention2033.ProfilesValid := by
  change ∀ j : Fin 16, (retention2033.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch317.valid12705
  · exact MergedCutProfiles.Batch020.valid804
  · exact MergedCutProfiles.Batch020.valid817
  · exact MergedCutProfiles.Batch020.valid805
  · exact MergedCutProfiles.Batch317.valid12709
  · exact MergedCutProfiles.Batch317.valid12714
  · exact MergedCutProfiles.Batch317.valid12712
  · exact MergedCutProfiles.Batch317.valid12713
  · exact MergedCutProfiles.Batch019.valid783
  · exact MergedCutProfiles.Batch317.valid12715
  · exact MergedCutProfiles.Batch317.valid12716
  · exact MergedCutProfiles.Batch317.valid12717
  · exact MergedCutProfiles.Batch317.valid12718
  · exact MergedCutProfiles.Batch317.valid12719
  · exact MergedCutProfiles.Batch318.valid12720
  · exact MergedCutProfiles.Batch019.valid785
theorem numericValid2033 : retention2033.NumericValid := by decide +kernel
def certificate2033 : RatCutBinCertificate := ⟨⟨retention2033,(1879312695523397901/1000000000000000000),(12019078477736559/1000000000000000000),(4056637588455089877/500000000000000000),(3192136288045801448521/1000000000000000000),(226008469577937201/100000000000000000)⟩,(99941751051347537/100000000000000000),(524535387762397967/1000000000000000000),(137012127473671723/1000000000000000000),(31574854807094899/500000000000000000)⟩
theorem valid2033 : certificate2033.Valid := by decide +kernel
theorem sound2033 : certificate2033.Sound := rat_cut_bin_certificate_sound certificate2033 profilesValid2033 numericValid2033 valid2033

def retention2034 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(2113145352807558835/391610370718798704527),(1244293919/1000000000),(49/20),(36362412344651000663/16000000000000000000),true,MergedCutProfiles.Batch318.profile12721,![MergedCutProfiles.Batch318.profile12721,MergedCutProfiles.Batch318.profile12722,MergedCutProfiles.Batch019.profile768,MergedCutProfiles.Batch318.profile12723,MergedCutProfiles.Batch318.profile12724,MergedCutProfiles.Batch019.profile773,MergedCutProfiles.Batch317.profile12717,MergedCutProfiles.Batch020.profile809,MergedCutProfiles.Batch019.profile778,MergedCutProfiles.Batch318.profile12725,MergedCutProfiles.Batch318.profile12726,MergedCutProfiles.Batch020.profile820,MergedCutProfiles.Batch318.profile12727,MergedCutProfiles.Batch318.profile12728,MergedCutProfiles.Batch020.profile813,MergedCutProfiles.Batch020.profile814]⟩
theorem profilesValid2034 : retention2034.ProfilesValid := by
  change ∀ j : Fin 16, (retention2034.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch318.valid12721
  · exact MergedCutProfiles.Batch318.valid12722
  · exact MergedCutProfiles.Batch019.valid768
  · exact MergedCutProfiles.Batch318.valid12723
  · exact MergedCutProfiles.Batch318.valid12724
  · exact MergedCutProfiles.Batch019.valid773
  · exact MergedCutProfiles.Batch317.valid12717
  · exact MergedCutProfiles.Batch020.valid809
  · exact MergedCutProfiles.Batch019.valid778
  · exact MergedCutProfiles.Batch318.valid12725
  · exact MergedCutProfiles.Batch318.valid12726
  · exact MergedCutProfiles.Batch020.valid820
  · exact MergedCutProfiles.Batch318.valid12727
  · exact MergedCutProfiles.Batch318.valid12728
  · exact MergedCutProfiles.Batch020.valid813
  · exact MergedCutProfiles.Batch020.valid814
theorem numericValid2034 : retention2034.NumericValid := by decide +kernel
def certificate2034 : RatCutBinCertificate := ⟨⟨retention2034,(1879312695523397901/1000000000000000000),(12019078477736559/1000000000000000000),(4056637588455089877/500000000000000000),(3192136288045801448521/1000000000000000000),(141614368001346759/62500000000000000)⟩,(99941751051347537/100000000000000000),(89527776465687783/250000000000000000),(274135693024804461/1000000000000000000),(38877781233681359/200000000000000000)⟩
theorem valid2034 : certificate2034.Valid := by decide +kernel
theorem sound2034 : certificate2034.Sound := rat_cut_bin_certificate_sound certificate2034 profilesValid2034 numericValid2034 valid2034

def retention2035 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(64000000000000000000/391610370718798704527),(422629070561511767/200000000000000000),(7/4),(233076070197884292135066059245553383311/135241302579683765440000000000000000000),false,MergedCutProfiles.Batch318.profile12729,(fun _ => MergedCutProfiles.Batch318.profile12729)⟩
theorem profilesValid2035 : retention2035.ProfilesValid := by
  exact MergedCutProfiles.Batch318.valid12729
theorem numericValid2035 : retention2035.NumericValid := by decide +kernel
def certificate2035 : RatCutBinCertificate := ⟨⟨retention2035,(1879312695523397901/1000000000000000000),(12019078477736559/1000000000000000000),(4056637588455089877/500000000000000000),(3192136288045801448521/1000000000000000000),(429634220858084349/250000000000000000)⟩,(99941751051347537/100000000000000000),(190529453626556703/500000000000000000),(6282314859159123/25000000000000000),(97433258488873457/500000000000000000)⟩
theorem valid2035 : certificate2035.Valid := by decide +kernel
theorem sound2035 : certificate2035.Sound := rat_cut_bin_certificate_sound certificate2035 profilesValid2035 numericValid2035 valid2035

def retention2036 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(1/2),64,1,(408592521868712119380352324506759031/409600000000000000000000000000000000),false,MergedCutProfiles.Batch020.profile830,(fun _ => MergedCutProfiles.Batch020.profile830)⟩
theorem profilesValid2036 : retention2036.ProfilesValid := by
  exact MergedCutProfiles.Batch020.valid830
theorem numericValid2036 : retention2036.NumericValid := by decide +kernel
def certificate2036 : RatCutBinCertificate := ⟨⟨retention2036,(1879312695523397901/1000000000000000000),(12019078477736559/1000000000000000000),(4056637588455089877/500000000000000000),(3192136288045801448521/1000000000000000000),(198951261155769403/200000000000000000)⟩,(99941751051347537/100000000000000000),(110092774772561513/250000000000000000),(99231833595478601/500000000000000000),(38857441099527581/200000000000000000)⟩
theorem valid2036 : certificate2036.Valid := by decide +kernel
theorem sound2036 : certificate2036.Sound := rat_cut_bin_certificate_sound certificate2036 profilesValid2036 numericValid2036 valid2036

def retention2037 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(64000000000000000000/391610370718798704527),(5077075845851184483/1000000000000000000),(11/10),(372928483107552780407595695806272596159/225647815371163754800000000000000000000),false,MergedCutProfiles.Batch318.profile12729,(fun _ => MergedCutProfiles.Batch318.profile12729)⟩
theorem profilesValid2037 : retention2037.ProfilesValid := by
  exact MergedCutProfiles.Batch318.valid12729
theorem numericValid2037 : retention2037.NumericValid := by decide +kernel
def certificate2037 : RatCutBinCertificate := ⟨⟨retention2037,(2161117728523397901/1000000000000000000),(12019078477736559/1000000000000000000),(4056637588455089877/500000000000000000),(3192136288045801448521/1000000000000000000),(1649179849323093853/1000000000000000000)⟩,(199866032987692849/200000000000000000),(7256151182987787/50000000000000000),(573635532727755467/1000000000000000000),(169381666193440769/250000000000000000)⟩
theorem valid2037 : certificate2037.Valid := by decide +kernel
theorem sound2037 : certificate2037.Sound := rat_cut_bin_certificate_sound certificate2037 profilesValid2037 numericValid2037 valid2037

def retention2038 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(1/2),64,1,(408592521868712119380352324506759031/409600000000000000000000000000000000),false,MergedCutProfiles.Batch020.profile830,(fun _ => MergedCutProfiles.Batch020.profile830)⟩
theorem profilesValid2038 : retention2038.ProfilesValid := by
  exact MergedCutProfiles.Batch020.valid830
theorem numericValid2038 : retention2038.NumericValid := by decide +kernel
def certificate2038 : RatCutBinCertificate := ⟨⟨retention2038,(2161117728523397901/1000000000000000000),(12019078477736559/1000000000000000000),(4056637588455089877/500000000000000000),(3192136288045801448521/1000000000000000000),(994338837255660251/1000000000000000000)⟩,(199866032987692849/200000000000000000),(120348294427008891/500000000000000000),(416391435596674863/1000000000000000000),(81484969503048279/200000000000000000)⟩
theorem valid2038 : certificate2038.Valid := by decide +kernel
theorem sound2038 : certificate2038.Sound := rat_cut_bin_certificate_sound certificate2038 profilesValid2038 numericValid2038 valid2038

def retention2039 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(313104822038109286/173833819108730224839),(122774168037686221/200000000000000000),4,(579842300138213656817/256000000000000000000),true,MergedCutProfiles.Batch318.profile12730,![MergedCutProfiles.Batch318.profile12730,MergedCutProfiles.Batch318.profile12731,MergedCutProfiles.Batch318.profile12732,MergedCutProfiles.Batch318.profile12733,MergedCutProfiles.Batch318.profile12734,MergedCutProfiles.Batch020.profile833,MergedCutProfiles.Batch318.profile12735,MergedCutProfiles.Batch318.profile12736,MergedCutProfiles.Batch318.profile12737,MergedCutProfiles.Batch318.profile12738,MergedCutProfiles.Batch318.profile12739,MergedCutProfiles.Batch021.profile874,MergedCutProfiles.Batch318.profile12740,MergedCutProfiles.Batch318.profile12741,MergedCutProfiles.Batch318.profile12742,MergedCutProfiles.Batch318.profile12743]⟩
theorem profilesValid2039 : retention2039.ProfilesValid := by
  change ∀ j : Fin 16, (retention2039.fine j).Valid
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
  · exact MergedCutProfiles.Batch318.valid12738
  · exact MergedCutProfiles.Batch318.valid12739
  · exact MergedCutProfiles.Batch021.valid874
  · exact MergedCutProfiles.Batch318.valid12740
  · exact MergedCutProfiles.Batch318.valid12741
  · exact MergedCutProfiles.Batch318.valid12742
  · exact MergedCutProfiles.Batch318.valid12743
theorem numericValid2039 : retention2039.NumericValid := by decide +kernel
def certificate2039 : RatCutBinCertificate := ⟨⟨retention2039,(1885819660274741523/1000000000000000000),(13522397103991873/1000000000000000000),(8218226185730691081/1000000000000000000),(179417633552813698357/62500000000000000),(1126298566590644771/500000000000000000)⟩,(7807429426585233/7812500000000000),(266178741190626403/500000000000000000),(66011510602098737/500000000000000000),(15108006211007083/250000000000000000)⟩
theorem valid2039 : certificate2039.Valid := by decide +kernel
theorem sound2039 : certificate2039.Sound := rat_cut_bin_certificate_sound certificate2039 profilesValid2039 numericValid2039 valid2039

def certificates : List RatCutBinCertificate := [certificate2028,certificate2029,certificate2030,certificate2031,certificate2032,certificate2033,certificate2034,certificate2035,certificate2036,certificate2037,certificate2038,certificate2039]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2028,List.forall_mem_cons.mpr ⟨sound2029,List.forall_mem_cons.mpr ⟨sound2030,List.forall_mem_cons.mpr ⟨sound2031,List.forall_mem_cons.mpr ⟨sound2032,List.forall_mem_cons.mpr ⟨sound2033,List.forall_mem_cons.mpr ⟨sound2034,List.forall_mem_cons.mpr ⟨sound2035,List.forall_mem_cons.mpr ⟨sound2036,List.forall_mem_cons.mpr ⟨sound2037,List.forall_mem_cons.mpr ⟨sound2038,List.forall_mem_cons.mpr ⟨sound2039,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch169
