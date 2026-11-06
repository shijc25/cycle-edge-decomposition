import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch342
import Cycle12.MergedCutProfiles.Batch343
import Cycle12.MergedCutProfiles.Batch344

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch185

def retention2220 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(4063270083383103944/9391002167823000265),(7223277064277708643/1000000000000000000),(21/20),(4301459256512967345697558005447501165957/3852414434281444609600000000000000000000),false,MergedCutProfiles.Batch342.profile13709,(fun _ => MergedCutProfiles.Batch342.profile13709)⟩
theorem profilesValid2220 : retention2220.ProfilesValid := by
  exact MergedCutProfiles.Batch342.valid13709
theorem numericValid2220 : retention2220.NumericValid := by decide +kernel
def certificate2220 : RatCutBinCertificate := ⟨⟨retention2220,(2005697646422337791/1000000000000000000),(853665110250683/15625000000000000),(2594303627910352299/250000000000000000),(440822031069632704001/500000000000000000),(1105474128957288073/1000000000000000000)⟩,(99784158436982813/100000000000000000),(228272169476542267/500000000000000000),(185492964766941039/1000000000000000000),(17109407261819889/100000000000000000)⟩
theorem valid2220 : certificate2220.Valid := by decide +kernel
theorem sound2220 : certificate2220.Sound := rat_cut_bin_certificate_sound certificate2220 profilesValid2220 numericValid2220 valid2220

def retention2221 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(42035617640418852742/84519019510407002385),(4571178843805991937/125000000000000000),1,(36564707030425258020944571589267408991/36569430750447935496000000000000000000),false,MergedCutProfiles.Batch342.profile13710,(fun _ => MergedCutProfiles.Batch342.profile13710)⟩
theorem profilesValid2221 : retention2221.ProfilesValid := by
  exact MergedCutProfiles.Batch342.valid13710
theorem numericValid2221 : retention2221.NumericValid := by decide +kernel
def certificate2221 : RatCutBinCertificate := ⟨⟨retention2221,(2005697646422337791/1000000000000000000),(853665110250683/15625000000000000),(2594303627910352299/250000000000000000),(440822031069632704001/500000000000000000),(989311096329332947/1000000000000000000)⟩,(99784158436982813/100000000000000000),(233237261043646843/500000000000000000),(5556696710742733/31250000000000000),(170904876583700189/1000000000000000000)⟩
theorem valid2221 : certificate2221.Valid := by decide +kernel
theorem sound2221 : certificate2221.Sound := rat_cut_bin_certificate_sound certificate2221 profilesValid2221 numericValid2221 valid2221

def retention2222 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(1/2),(21017808820209426371/500000000000000000),1,(10461907797258764511833857144311041157/10508904410104713185500000000000000000),false,MergedCutProfiles.Batch342.profile13711,(fun _ => MergedCutProfiles.Batch342.profile13711)⟩
theorem profilesValid2222 : retention2222.ProfilesValid := by
  exact MergedCutProfiles.Batch342.valid13711
theorem numericValid2222 : retention2222.NumericValid := by decide +kernel
def certificate2222 : RatCutBinCertificate := ⟨⟨retention2222,(2005697646422337791/1000000000000000000),(853665110250683/15625000000000000),(2594303627910352299/250000000000000000),(440822031069632704001/500000000000000000),(196993638907292209/200000000000000000)⟩,(99784158436982813/100000000000000000),(233563580735482961/500000000000000000),(22164635400191521/125000000000000000),(85139952079135713/500000000000000000)⟩
theorem valid2222 : certificate2222.Valid := by decide +kernel
theorem sound2222 : certificate2222.Sound := rat_cut_bin_certificate_sound certificate2222 profilesValid2222 numericValid2222 valid2222

def retention2223 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(12067903503261287204/28173006503469000795),(2760472614039432963/500000000000000000),(21/20),(2455604601914439067203749863689799851071/2208378091231546370400000000000000000000),false,MergedCutProfiles.Batch342.profile13712,(fun _ => MergedCutProfiles.Batch342.profile13712)⟩
theorem profilesValid2223 : retention2223.ProfilesValid := by
  exact MergedCutProfiles.Batch342.valid13712
theorem numericValid2223 : retention2223.NumericValid := by decide +kernel
def certificate2223 : RatCutBinCertificate := ⟨⟨retention2223,(2305090954422337791/1000000000000000000),(853665110250683/15625000000000000),(2594303627910352299/250000000000000000),(440822031069632704001/500000000000000000),(549603222735966869/500000000000000000)⟩,(997519351383130449/1000000000000000000),(219068884353483171/1000000000000000000),(22405928567911771/50000000000000000),(99076363127371127/250000000000000000)⟩
theorem valid2223 : certificate2223.Valid := by decide +kernel
theorem sound2223 : certificate2223.Sound := rat_cut_bin_certificate_sound certificate2223 profilesValid2223 numericValid2223 valid2223

def retention2224 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(4670153774562400773/9391002167823000265),(9050927627445965403/250000000000000000),1,(2413338907969104431599707650547438417/2413580700652257440800000000000000000),false,MergedCutProfiles.Batch342.profile13713,(fun _ => MergedCutProfiles.Batch342.profile13713)⟩
theorem profilesValid2224 : retention2224.ProfilesValid := by
  exact MergedCutProfiles.Batch342.valid13713
theorem numericValid2224 : retention2224.NumericValid := by decide +kernel
def certificate2224 : RatCutBinCertificate := ⟨⟨retention2224,(2305090954422337791/1000000000000000000),(853665110250683/15625000000000000),(2594303627910352299/250000000000000000),(440822031069632704001/500000000000000000),(987763821224282797/1000000000000000000)⟩,(997519351383130449/1000000000000000000),(243784925616361071/1000000000000000000),(82404159709527407/200000000000000000),(197587413468868129/500000000000000000)⟩
theorem valid2224 : certificate2224.Valid := by decide +kernel
theorem sound2224 : certificate2224.Sound := rat_cut_bin_certificate_sound certificate2224 profilesValid2224 numericValid2224 valid2224

def retention2225 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(1/2),(42031383971061606957/1000000000000000000),1,(145289552773138297245315082373649961/145942305455075024156250000000000000),false,MergedCutProfiles.Batch342.profile13711,(fun _ => MergedCutProfiles.Batch342.profile13711)⟩
theorem profilesValid2225 : retention2225.ProfilesValid := by
  exact MergedCutProfiles.Batch342.valid13711
theorem numericValid2225 : retention2225.NumericValid := by decide +kernel
def certificate2225 : RatCutBinCertificate := ⟨⟨retention2225,(2305090954422337791/1000000000000000000),(853665110250683/15625000000000000),(2594303627910352299/250000000000000000),(440822031069632704001/500000000000000000),(983391327934855841/1000000000000000000)⟩,(997519351383130449/1000000000000000000),(244868876553328863/1000000000000000000),(410495941895723033/1000000000000000000),(49182489821081807/125000000000000000)⟩
theorem valid2225 : certificate2225.Valid := by decide +kernel
theorem sound2225 : certificate2225.Sound := rat_cut_bin_certificate_sound certificate2225 profilesValid2225 numericValid2225 valid2225

def retention2226 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(737818536411765067/79471930445769645646),(182628350596971551/250000000000000000),(73/20),(725479140672128871231/320000000000000000000),true,MergedCutProfiles.Batch342.profile13714,![MergedCutProfiles.Batch342.profile13714,MergedCutProfiles.Batch342.profile13715,MergedCutProfiles.Batch342.profile13716,MergedCutProfiles.Batch342.profile13717,MergedCutProfiles.Batch342.profile13718,MergedCutProfiles.Batch342.profile13719,MergedCutProfiles.Batch343.profile13720,MergedCutProfiles.Batch343.profile13721,MergedCutProfiles.Batch343.profile13722,MergedCutProfiles.Batch343.profile13723,MergedCutProfiles.Batch343.profile13724,MergedCutProfiles.Batch343.profile13725,MergedCutProfiles.Batch343.profile13726,MergedCutProfiles.Batch343.profile13727,MergedCutProfiles.Batch343.profile13728,MergedCutProfiles.Batch343.profile13729]⟩
theorem profilesValid2226 : retention2226.ProfilesValid := by
  change ∀ j : Fin 16, (retention2226.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch342.valid13714
  · exact MergedCutProfiles.Batch342.valid13715
  · exact MergedCutProfiles.Batch342.valid13716
  · exact MergedCutProfiles.Batch342.valid13717
  · exact MergedCutProfiles.Batch342.valid13718
  · exact MergedCutProfiles.Batch342.valid13719
  · exact MergedCutProfiles.Batch343.valid13720
  · exact MergedCutProfiles.Batch343.valid13721
  · exact MergedCutProfiles.Batch343.valid13722
  · exact MergedCutProfiles.Batch343.valid13723
  · exact MergedCutProfiles.Batch343.valid13724
  · exact MergedCutProfiles.Batch343.valid13725
  · exact MergedCutProfiles.Batch343.valid13726
  · exact MergedCutProfiles.Batch343.valid13727
  · exact MergedCutProfiles.Batch343.valid13728
  · exact MergedCutProfiles.Batch343.valid13729
theorem numericValid2226 : retention2226.NumericValid := by decide +kernel
def certificate2226 : RatCutBinCertificate := ⟨⟨retention2226,(1006489985065161273/500000000000000000),(3628243259175483/62500000000000000),(5265300122017051847/500000000000000000),(168255263760065364129/200000000000000000),(2226617484929461181/1000000000000000000)⟩,(124717207640455853/125000000000000000),(439015935751195539/1000000000000000000),(7983086310621117/40000000000000000),(49409020847909571/500000000000000000)⟩
theorem valid2226 : certificate2226.Valid := by decide +kernel
theorem sound2226 : certificate2226.Sound := rat_cut_bin_certificate_sound certificate2226 profilesValid2226 numericValid2226 valid2226

def retention2227 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(459187216944968174/39735965222884822823),(737818536411765067/1000000000000000000),(18/5),(2880025836636553116623/1280000000000000000000),true,MergedCutProfiles.Batch343.profile13730,![MergedCutProfiles.Batch343.profile13730,MergedCutProfiles.Batch343.profile13731,MergedCutProfiles.Batch343.profile13732,MergedCutProfiles.Batch342.profile13718,MergedCutProfiles.Batch343.profile13733,MergedCutProfiles.Batch343.profile13734,MergedCutProfiles.Batch343.profile13735,MergedCutProfiles.Batch343.profile13736,MergedCutProfiles.Batch343.profile13737,MergedCutProfiles.Batch343.profile13738,MergedCutProfiles.Batch343.profile13739,MergedCutProfiles.Batch343.profile13740,MergedCutProfiles.Batch343.profile13741,MergedCutProfiles.Batch343.profile13742,MergedCutProfiles.Batch343.profile13743,MergedCutProfiles.Batch343.profile13744]⟩
theorem profilesValid2227 : retention2227.ProfilesValid := by
  change ∀ j : Fin 16, (retention2227.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch343.valid13730
  · exact MergedCutProfiles.Batch343.valid13731
  · exact MergedCutProfiles.Batch343.valid13732
  · exact MergedCutProfiles.Batch342.valid13718
  · exact MergedCutProfiles.Batch343.valid13733
  · exact MergedCutProfiles.Batch343.valid13734
  · exact MergedCutProfiles.Batch343.valid13735
  · exact MergedCutProfiles.Batch343.valid13736
  · exact MergedCutProfiles.Batch343.valid13737
  · exact MergedCutProfiles.Batch343.valid13738
  · exact MergedCutProfiles.Batch343.valid13739
  · exact MergedCutProfiles.Batch343.valid13740
  · exact MergedCutProfiles.Batch343.valid13741
  · exact MergedCutProfiles.Batch343.valid13742
  · exact MergedCutProfiles.Batch343.valid13743
  · exact MergedCutProfiles.Batch343.valid13744
theorem numericValid2227 : retention2227.NumericValid := by decide +kernel
def certificate2227 : RatCutBinCertificate := ⟨⟨retention2227,(1006489985065161273/500000000000000000),(3628243259175483/62500000000000000),(5265300122017051847/500000000000000000),(168255263760065364129/200000000000000000),(22100702119010291/10000000000000000)⟩,(124717207640455853/125000000000000000),(109985910938962211/250000000000000000),(198814441587360227/1000000000000000000),(9887750422263041/100000000000000000)⟩
theorem valid2227 : certificate2227.Valid := by decide +kernel
theorem sound2227 : certificate2227.Sound := rat_cut_bin_certificate_sound certificate2227 profilesValid2227 numericValid2227 valid2227

def retention2228 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(541217680500000000/39735965222884822823),(229593608472484087/250000000000000000),3,(142653709867441875479/64000000000000000000),true,MergedCutProfiles.Batch343.profile13745,![MergedCutProfiles.Batch343.profile13745,MergedCutProfiles.Batch343.profile13746,MergedCutProfiles.Batch343.profile13747,MergedCutProfiles.Batch343.profile13748,MergedCutProfiles.Batch343.profile13749,MergedCutProfiles.Batch343.profile13750,MergedCutProfiles.Batch343.profile13751,MergedCutProfiles.Batch343.profile13752,MergedCutProfiles.Batch343.profile13753,MergedCutProfiles.Batch343.profile13754,MergedCutProfiles.Batch343.profile13741,MergedCutProfiles.Batch343.profile13755,MergedCutProfiles.Batch343.profile13756,MergedCutProfiles.Batch343.profile13757,MergedCutProfiles.Batch343.profile13758,MergedCutProfiles.Batch343.profile13759]⟩
theorem profilesValid2228 : retention2228.ProfilesValid := by
  change ∀ j : Fin 16, (retention2228.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch343.valid13745
  · exact MergedCutProfiles.Batch343.valid13746
  · exact MergedCutProfiles.Batch343.valid13747
  · exact MergedCutProfiles.Batch343.valid13748
  · exact MergedCutProfiles.Batch343.valid13749
  · exact MergedCutProfiles.Batch343.valid13750
  · exact MergedCutProfiles.Batch343.valid13751
  · exact MergedCutProfiles.Batch343.valid13752
  · exact MergedCutProfiles.Batch343.valid13753
  · exact MergedCutProfiles.Batch343.valid13754
  · exact MergedCutProfiles.Batch343.valid13741
  · exact MergedCutProfiles.Batch343.valid13755
  · exact MergedCutProfiles.Batch343.valid13756
  · exact MergedCutProfiles.Batch343.valid13757
  · exact MergedCutProfiles.Batch343.valid13758
  · exact MergedCutProfiles.Batch343.valid13759
theorem numericValid2228 : retention2228.NumericValid := by decide +kernel
def certificate2228 : RatCutBinCertificate := ⟨⟨retention2228,(1006489985065161273/500000000000000000),(3628243259175483/62500000000000000),(5265300122017051847/500000000000000000),(168255263760065364129/200000000000000000),(2195672603606027811/1000000000000000000)⟩,(124717207640455853/125000000000000000),(396139598291655193/1000000000000000000),(237038135713426389/1000000000000000000),(68356733737056483/500000000000000000)⟩
theorem valid2228 : certificate2228.Valid := by decide +kernel
theorem sound2228 : certificate2228.Sound := rat_cut_bin_certificate_sound certificate2228 profilesValid2228 numericValid2228 valid2228

def retention2229 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(577273187641551615/39735965222884822823),(1082435361/1000000000),(13/5),(2210351778619330567/1000000000000000000),true,MergedCutProfiles.Batch344.profile13760,![MergedCutProfiles.Batch344.profile13760,MergedCutProfiles.Batch344.profile13761,MergedCutProfiles.Batch344.profile13762,MergedCutProfiles.Batch343.profile13733,MergedCutProfiles.Batch344.profile13763,MergedCutProfiles.Batch344.profile13764,MergedCutProfiles.Batch343.profile13724,MergedCutProfiles.Batch343.profile13738,MergedCutProfiles.Batch344.profile13765,MergedCutProfiles.Batch344.profile13766,MergedCutProfiles.Batch344.profile13767,MergedCutProfiles.Batch343.profile13743,MergedCutProfiles.Batch344.profile13768,MergedCutProfiles.Batch344.profile13769,MergedCutProfiles.Batch343.profile13759,MergedCutProfiles.Batch344.profile13770]⟩
theorem profilesValid2229 : retention2229.ProfilesValid := by
  change ∀ j : Fin 16, (retention2229.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch344.valid13760
  · exact MergedCutProfiles.Batch344.valid13761
  · exact MergedCutProfiles.Batch344.valid13762
  · exact MergedCutProfiles.Batch343.valid13733
  · exact MergedCutProfiles.Batch344.valid13763
  · exact MergedCutProfiles.Batch344.valid13764
  · exact MergedCutProfiles.Batch343.valid13724
  · exact MergedCutProfiles.Batch343.valid13738
  · exact MergedCutProfiles.Batch344.valid13765
  · exact MergedCutProfiles.Batch344.valid13766
  · exact MergedCutProfiles.Batch344.valid13767
  · exact MergedCutProfiles.Batch343.valid13743
  · exact MergedCutProfiles.Batch344.valid13768
  · exact MergedCutProfiles.Batch344.valid13769
  · exact MergedCutProfiles.Batch343.valid13759
  · exact MergedCutProfiles.Batch344.valid13770
theorem numericValid2229 : retention2229.NumericValid := by decide +kernel
def certificate2229 : RatCutBinCertificate := ⟨⟨retention2229,(1006489985065161273/500000000000000000),(3628243259175483/62500000000000000),(5265300122017051847/500000000000000000),(168255263760065364129/200000000000000000),(2181499062492373817/1000000000000000000)⟩,(124717207640455853/125000000000000000),(92402104696458539/250000000000000000),(10500515422019689/40000000000000000),(169231237362699279/1000000000000000000)⟩
theorem valid2229 : certificate2229.Valid := by decide +kernel
theorem sound2229 : certificate2229.Sound := rat_cut_bin_certificate_sound certificate2229 profilesValid2229 numericValid2229 valid2229

def retention2230 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(1279650259523263046/39735965222884822823),(115454637528310323/100000000000000000),(49/20),(271977434213072181283/128000000000000000000),true,MergedCutProfiles.Batch344.profile13771,![MergedCutProfiles.Batch344.profile13771,MergedCutProfiles.Batch344.profile13772,MergedCutProfiles.Batch344.profile13773,MergedCutProfiles.Batch344.profile13774,MergedCutProfiles.Batch343.profile13742,MergedCutProfiles.Batch344.profile13775,MergedCutProfiles.Batch344.profile13776,MergedCutProfiles.Batch344.profile13777,MergedCutProfiles.Batch344.profile13778,MergedCutProfiles.Batch344.profile13779,MergedCutProfiles.Batch344.profile13780,MergedCutProfiles.Batch344.profile13781,MergedCutProfiles.Batch344.profile13782,MergedCutProfiles.Batch344.profile13783,MergedCutProfiles.Batch344.profile13784,MergedCutProfiles.Batch344.profile13785]⟩
theorem profilesValid2230 : retention2230.ProfilesValid := by
  change ∀ j : Fin 16, (retention2230.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch344.valid13771
  · exact MergedCutProfiles.Batch344.valid13772
  · exact MergedCutProfiles.Batch344.valid13773
  · exact MergedCutProfiles.Batch344.valid13774
  · exact MergedCutProfiles.Batch343.valid13742
  · exact MergedCutProfiles.Batch344.valid13775
  · exact MergedCutProfiles.Batch344.valid13776
  · exact MergedCutProfiles.Batch344.valid13777
  · exact MergedCutProfiles.Batch344.valid13778
  · exact MergedCutProfiles.Batch344.valid13779
  · exact MergedCutProfiles.Batch344.valid13780
  · exact MergedCutProfiles.Batch344.valid13781
  · exact MergedCutProfiles.Batch344.valid13782
  · exact MergedCutProfiles.Batch344.valid13783
  · exact MergedCutProfiles.Batch344.valid13784
  · exact MergedCutProfiles.Batch344.valid13785
theorem numericValid2230 : retention2230.NumericValid := by decide +kernel
def certificate2230 : RatCutBinCertificate := ⟨⟨retention2230,(1006489985065161273/500000000000000000),(3628243259175483/62500000000000000),(5265300122017051847/500000000000000000),(168255263760065364129/200000000000000000),(2097635571810798193/1000000000000000000)⟩,(124717207640455853/125000000000000000),(186901329020629459/500000000000000000),(129181200743772029/500000000000000000),(42341158034024417/250000000000000000)⟩
theorem valid2230 : certificate2230.Valid := by decide +kernel
theorem sound2230 : certificate2230.Sound := rat_cut_bin_certificate_sound certificate2230 profilesValid2230 numericValid2230 valid2230

def retention2231 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(10868926511665134579/39735965222884822823),(639825129761631523/250000000000000000),(3/2),(3761268708114536059397071375583120471/2559300519046526092000000000000000000),false,MergedCutProfiles.Batch344.profile13786,(fun _ => MergedCutProfiles.Batch344.profile13786)⟩
theorem profilesValid2231 : retention2231.ProfilesValid := by
  exact MergedCutProfiles.Batch344.valid13786
theorem numericValid2231 : retention2231.NumericValid := by decide +kernel
def certificate2231 : RatCutBinCertificate := ⟨⟨retention2231,(1006489985065161273/500000000000000000),(3628243259175483/62500000000000000),(5265300122017051847/500000000000000000),(168255263760065364129/200000000000000000),(290600291787722871/200000000000000000)⟩,(124717207640455853/125000000000000000),(103441890810412191/250000000000000000),(110550997164339083/500000000000000000),(170589591901737499/1000000000000000000)⟩
theorem valid2231 : certificate2231.Valid := by decide +kernel
theorem sound2231 : certificate2231.Sound := rat_cut_bin_certificate_sound certificate2231 profilesValid2231 numericValid2231 valid2231

def certificates : List RatCutBinCertificate := [certificate2220,certificate2221,certificate2222,certificate2223,certificate2224,certificate2225,certificate2226,certificate2227,certificate2228,certificate2229,certificate2230,certificate2231]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2220,List.forall_mem_cons.mpr ⟨sound2221,List.forall_mem_cons.mpr ⟨sound2222,List.forall_mem_cons.mpr ⟨sound2223,List.forall_mem_cons.mpr ⟨sound2224,List.forall_mem_cons.mpr ⟨sound2225,List.forall_mem_cons.mpr ⟨sound2226,List.forall_mem_cons.mpr ⟨sound2227,List.forall_mem_cons.mpr ⟨sound2228,List.forall_mem_cons.mpr ⟨sound2229,List.forall_mem_cons.mpr ⟨sound2230,List.forall_mem_cons.mpr ⟨sound2231,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch185
