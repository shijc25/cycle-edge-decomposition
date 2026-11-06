import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch419
import Cycle12.MergedCutProfiles.Batch420
import Cycle12.MergedCutProfiles.Batch421

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch222

def retention2664 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(947807991218610967/21411968900245842514),(234605938420448259/250000000000000000),(13/5),(1059725046689225451/512000000000000000),true,MergedCutProfiles.Batch419.profile16780,![MergedCutProfiles.Batch419.profile16780,MergedCutProfiles.Batch419.profile16781,MergedCutProfiles.Batch419.profile16782,MergedCutProfiles.Batch419.profile16783,MergedCutProfiles.Batch419.profile16784,MergedCutProfiles.Batch419.profile16785,MergedCutProfiles.Batch419.profile16786,MergedCutProfiles.Batch419.profile16787,MergedCutProfiles.Batch419.profile16788,MergedCutProfiles.Batch419.profile16789,MergedCutProfiles.Batch419.profile16790,MergedCutProfiles.Batch419.profile16791,MergedCutProfiles.Batch419.profile16792,MergedCutProfiles.Batch419.profile16793,MergedCutProfiles.Batch419.profile16794,MergedCutProfiles.Batch419.profile16795]⟩
theorem profilesValid2664 : retention2664.ProfilesValid := by
  change ∀ j : Fin 16, (retention2664.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch419.valid16780
  · exact MergedCutProfiles.Batch419.valid16781
  · exact MergedCutProfiles.Batch419.valid16782
  · exact MergedCutProfiles.Batch419.valid16783
  · exact MergedCutProfiles.Batch419.valid16784
  · exact MergedCutProfiles.Batch419.valid16785
  · exact MergedCutProfiles.Batch419.valid16786
  · exact MergedCutProfiles.Batch419.valid16787
  · exact MergedCutProfiles.Batch419.valid16788
  · exact MergedCutProfiles.Batch419.valid16789
  · exact MergedCutProfiles.Batch419.valid16790
  · exact MergedCutProfiles.Batch419.valid16791
  · exact MergedCutProfiles.Batch419.valid16792
  · exact MergedCutProfiles.Batch419.valid16793
  · exact MergedCutProfiles.Batch419.valid16794
  · exact MergedCutProfiles.Batch419.valid16795
theorem numericValid2664 : retention2664.NumericValid := by decide +kernel
def certificate2664 : RatCutBinCertificate := ⟨⟨retention2664,(145042793394951413/62500000000000000),(106411689904918233/500000000000000000),(8467007229966131563/500000000000000000),(181865074432318742627/500000000000000000),(199392592784596307/100000000000000000)⟩,(99494530254522077/100000000000000000),(285673816440855879/1000000000000000000),(356370476409480737/1000000000000000000),(103336638316744547/500000000000000000)⟩
theorem valid2664 : certificate2664.Valid := by decide +kernel
theorem sound2664 : certificate2664.Sound := rat_cut_bin_certificate_sound certificate2664 profilesValid2664 numericValid2664 valid2664

def retention2665 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(492824206000000000/10705984450122921257),(947807991218610967/1000000000000000000),(13/5),(165496331053135179079/80000000000000000000),true,MergedCutProfiles.Batch419.profile16796,![MergedCutProfiles.Batch419.profile16796,MergedCutProfiles.Batch419.profile16797,MergedCutProfiles.Batch419.profile16798,MergedCutProfiles.Batch419.profile16799,MergedCutProfiles.Batch420.profile16800,MergedCutProfiles.Batch420.profile16801,MergedCutProfiles.Batch420.profile16802,MergedCutProfiles.Batch420.profile16803,MergedCutProfiles.Batch420.profile16804,MergedCutProfiles.Batch420.profile16805,MergedCutProfiles.Batch420.profile16806,MergedCutProfiles.Batch420.profile16807,MergedCutProfiles.Batch420.profile16808,MergedCutProfiles.Batch420.profile16809,MergedCutProfiles.Batch420.profile16810,MergedCutProfiles.Batch420.profile16811]⟩
theorem profilesValid2665 : retention2665.ProfilesValid := by
  change ∀ j : Fin 16, (retention2665.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch419.valid16796
  · exact MergedCutProfiles.Batch419.valid16797
  · exact MergedCutProfiles.Batch419.valid16798
  · exact MergedCutProfiles.Batch419.valid16799
  · exact MergedCutProfiles.Batch420.valid16800
  · exact MergedCutProfiles.Batch420.valid16801
  · exact MergedCutProfiles.Batch420.valid16802
  · exact MergedCutProfiles.Batch420.valid16803
  · exact MergedCutProfiles.Batch420.valid16804
  · exact MergedCutProfiles.Batch420.valid16805
  · exact MergedCutProfiles.Batch420.valid16806
  · exact MergedCutProfiles.Batch420.valid16807
  · exact MergedCutProfiles.Batch420.valid16808
  · exact MergedCutProfiles.Batch420.valid16809
  · exact MergedCutProfiles.Batch420.valid16810
  · exact MergedCutProfiles.Batch420.valid16811
theorem numericValid2665 : retention2665.NumericValid := by decide +kernel
def certificate2665 : RatCutBinCertificate := ⟨⟨retention2665,(145042793394951413/62500000000000000),(106411689904918233/500000000000000000),(8467007229966131563/500000000000000000),(181865074432318742627/500000000000000000),(62276711382691449/31250000000000000)⟩,(99494530254522077/100000000000000000),(284718337301633701/1000000000000000000),(357568341849477803/1000000000000000000),(41555314105444553/200000000000000000)⟩
theorem valid2665 : certificate2665.Valid := by decide +kernel
theorem sound2665 : certificate2665.Sound := rat_cut_bin_certificate_sound certificate2665 profilesValid2665 numericValid2665 valid2665

def retention2666 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(539346952973437666/10705984450122921257),(246412103/250000000),(5/2),(102457950911074573/50000000000000000),true,MergedCutProfiles.Batch420.profile16812,![MergedCutProfiles.Batch420.profile16812,MergedCutProfiles.Batch420.profile16813,MergedCutProfiles.Batch420.profile16814,MergedCutProfiles.Batch420.profile16815,MergedCutProfiles.Batch420.profile16816,MergedCutProfiles.Batch420.profile16817,MergedCutProfiles.Batch419.profile16787,MergedCutProfiles.Batch420.profile16818,MergedCutProfiles.Batch420.profile16819,MergedCutProfiles.Batch420.profile16820,MergedCutProfiles.Batch420.profile16821,MergedCutProfiles.Batch420.profile16822,MergedCutProfiles.Batch420.profile16823,MergedCutProfiles.Batch420.profile16824,MergedCutProfiles.Batch420.profile16825,MergedCutProfiles.Batch420.profile16826]⟩
theorem profilesValid2666 : retention2666.ProfilesValid := by
  change ∀ j : Fin 16, (retention2666.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch420.valid16812
  · exact MergedCutProfiles.Batch420.valid16813
  · exact MergedCutProfiles.Batch420.valid16814
  · exact MergedCutProfiles.Batch420.valid16815
  · exact MergedCutProfiles.Batch420.valid16816
  · exact MergedCutProfiles.Batch420.valid16817
  · exact MergedCutProfiles.Batch419.valid16787
  · exact MergedCutProfiles.Batch420.valid16818
  · exact MergedCutProfiles.Batch420.valid16819
  · exact MergedCutProfiles.Batch420.valid16820
  · exact MergedCutProfiles.Batch420.valid16821
  · exact MergedCutProfiles.Batch420.valid16822
  · exact MergedCutProfiles.Batch420.valid16823
  · exact MergedCutProfiles.Batch420.valid16824
  · exact MergedCutProfiles.Batch420.valid16825
  · exact MergedCutProfiles.Batch420.valid16826
theorem numericValid2666 : retention2666.NumericValid := by decide +kernel
def certificate2666 : RatCutBinCertificate := ⟨⟨retention2666,(145042793394951413/62500000000000000),(106411689904918233/500000000000000000),(8467007229966131563/500000000000000000),(181865074432318742627/500000000000000000),(395245385330556367/200000000000000000)⟩,(99494530254522077/100000000000000000),(282820394684874013/1000000000000000000),(179978606694415219/500000000000000000),(107061459454226569/500000000000000000)⟩
theorem valid2666 : certificate2666.Valid := by decide +kernel
theorem sound2666 : certificate2666.Sound := rat_cut_bin_certificate_sound certificate2666 profilesValid2666 numericValid2666 valid2666

def retention2667 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(932274461841938076/10705984450122921257),(269673476486718833/250000000000000000),(23/10),(620113336317902318621/320000000000000000000),true,MergedCutProfiles.Batch420.profile16827,![MergedCutProfiles.Batch420.profile16827,MergedCutProfiles.Batch420.profile16828,MergedCutProfiles.Batch420.profile16829,MergedCutProfiles.Batch420.profile16830,MergedCutProfiles.Batch420.profile16831,MergedCutProfiles.Batch420.profile16832,MergedCutProfiles.Batch420.profile16833,MergedCutProfiles.Batch420.profile16834,MergedCutProfiles.Batch420.profile16835,MergedCutProfiles.Batch420.profile16836,MergedCutProfiles.Batch420.profile16837,MergedCutProfiles.Batch420.profile16838,MergedCutProfiles.Batch420.profile16839,MergedCutProfiles.Batch421.profile16840,MergedCutProfiles.Batch421.profile16841,MergedCutProfiles.Batch421.profile16842]⟩
theorem profilesValid2667 : retention2667.ProfilesValid := by
  change ∀ j : Fin 16, (retention2667.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch420.valid16827
  · exact MergedCutProfiles.Batch420.valid16828
  · exact MergedCutProfiles.Batch420.valid16829
  · exact MergedCutProfiles.Batch420.valid16830
  · exact MergedCutProfiles.Batch420.valid16831
  · exact MergedCutProfiles.Batch420.valid16832
  · exact MergedCutProfiles.Batch420.valid16833
  · exact MergedCutProfiles.Batch420.valid16834
  · exact MergedCutProfiles.Batch420.valid16835
  · exact MergedCutProfiles.Batch420.valid16836
  · exact MergedCutProfiles.Batch420.valid16837
  · exact MergedCutProfiles.Batch420.valid16838
  · exact MergedCutProfiles.Batch420.valid16839
  · exact MergedCutProfiles.Batch421.valid16840
  · exact MergedCutProfiles.Batch421.valid16841
  · exact MergedCutProfiles.Batch421.valid16842
theorem numericValid2667 : retention2667.NumericValid := by decide +kernel
def certificate2667 : RatCutBinCertificate := ⟨⟨retention2667,(145042793394951413/62500000000000000),(106411689904918233/500000000000000000),(8467007229966131563/500000000000000000),(181865074432318742627/500000000000000000),(467689190023124303/250000000000000000)⟩,(99494530254522077/100000000000000000),(72241499851342997/250000000000000000),(352267386032586751/1000000000000000000),(107236796272773447/500000000000000000)⟩
theorem valid2667 : certificate2667.Valid := by decide +kernel
theorem sound2667 : certificate2667.Sound := rat_cut_bin_certificate_sound certificate2667 profilesValid2667 numericValid2667 valid2667

def retention2668 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(2898547346714823925/10705984450122921257),(233068615460484519/125000000000000000),(31/20),(234304614066528492381/160000000000000000000),true,MergedCutProfiles.Batch421.profile16843,![MergedCutProfiles.Batch421.profile16843,MergedCutProfiles.Batch421.profile16844,MergedCutProfiles.Batch421.profile16845,MergedCutProfiles.Batch421.profile16846,MergedCutProfiles.Batch421.profile16847,MergedCutProfiles.Batch421.profile16848,MergedCutProfiles.Batch421.profile16849,MergedCutProfiles.Batch421.profile16850,MergedCutProfiles.Batch421.profile16851,MergedCutProfiles.Batch421.profile16852,MergedCutProfiles.Batch421.profile16853,MergedCutProfiles.Batch421.profile16854,MergedCutProfiles.Batch421.profile16855,MergedCutProfiles.Batch421.profile16856,MergedCutProfiles.Batch421.profile16857,MergedCutProfiles.Batch421.profile16858]⟩
theorem profilesValid2668 : retention2668.ProfilesValid := by
  change ∀ j : Fin 16, (retention2668.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch421.valid16843
  · exact MergedCutProfiles.Batch421.valid16844
  · exact MergedCutProfiles.Batch421.valid16845
  · exact MergedCutProfiles.Batch421.valid16846
  · exact MergedCutProfiles.Batch421.valid16847
  · exact MergedCutProfiles.Batch421.valid16848
  · exact MergedCutProfiles.Batch421.valid16849
  · exact MergedCutProfiles.Batch421.valid16850
  · exact MergedCutProfiles.Batch421.valid16851
  · exact MergedCutProfiles.Batch421.valid16852
  · exact MergedCutProfiles.Batch421.valid16853
  · exact MergedCutProfiles.Batch421.valid16854
  · exact MergedCutProfiles.Batch421.valid16855
  · exact MergedCutProfiles.Batch421.valid16856
  · exact MergedCutProfiles.Batch421.valid16857
  · exact MergedCutProfiles.Batch421.valid16858
theorem numericValid2668 : retention2668.NumericValid := by decide +kernel
def certificate2668 : RatCutBinCertificate := ⟨⟨retention2668,(145042793394951413/62500000000000000),(106411689904918233/500000000000000000),(8467007229966131563/500000000000000000),(181865074432318742627/500000000000000000),(44349610099512979/31250000000000000)⟩,(99494530254522077/100000000000000000),(12929562016491679/40000000000000000),(311694424336147489/1000000000000000000),(107720999954231651/500000000000000000)⟩
theorem valid2668 : certificate2668.Valid := by decide +kernel
theorem sound2668 : certificate2668.Sound := rat_cut_bin_certificate_sound certificate2668 profilesValid2668 numericValid2668 valid2668

def retention2669 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(9822978759276926917/21411968900245842514),(115941893868592957/20000000000000000),1,(26587115235357376073/25600000000000000000),true,MergedCutProfiles.Batch421.profile16859,![MergedCutProfiles.Batch421.profile16859,MergedCutProfiles.Batch421.profile16860,MergedCutProfiles.Batch421.profile16861,MergedCutProfiles.Batch421.profile16862,MergedCutProfiles.Batch421.profile16863,MergedCutProfiles.Batch421.profile16864,MergedCutProfiles.Batch421.profile16865,MergedCutProfiles.Batch421.profile16866,MergedCutProfiles.Batch421.profile16867,MergedCutProfiles.Batch421.profile16868,MergedCutProfiles.Batch421.profile16869,MergedCutProfiles.Batch421.profile16870,MergedCutProfiles.Batch421.profile16871,MergedCutProfiles.Batch421.profile16872,MergedCutProfiles.Batch421.profile16873,MergedCutProfiles.Batch421.profile16874]⟩
theorem profilesValid2669 : retention2669.ProfilesValid := by
  change ∀ j : Fin 16, (retention2669.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch421.valid16859
  · exact MergedCutProfiles.Batch421.valid16860
  · exact MergedCutProfiles.Batch421.valid16861
  · exact MergedCutProfiles.Batch421.valid16862
  · exact MergedCutProfiles.Batch421.valid16863
  · exact MergedCutProfiles.Batch421.valid16864
  · exact MergedCutProfiles.Batch421.valid16865
  · exact MergedCutProfiles.Batch421.valid16866
  · exact MergedCutProfiles.Batch421.valid16867
  · exact MergedCutProfiles.Batch421.valid16868
  · exact MergedCutProfiles.Batch421.valid16869
  · exact MergedCutProfiles.Batch421.valid16870
  · exact MergedCutProfiles.Batch421.valid16871
  · exact MergedCutProfiles.Batch421.valid16872
  · exact MergedCutProfiles.Batch421.valid16873
  · exact MergedCutProfiles.Batch421.valid16874
theorem numericValid2669 : retention2669.NumericValid := by decide +kernel
def certificate2669 : RatCutBinCertificate := ⟨⟨retention2669,(145042793394951413/62500000000000000),(106411689904918233/500000000000000000),(8467007229966131563/500000000000000000),(181865074432318742627/500000000000000000),(504695167006629531/500000000000000000)⟩,(99494530254522077/100000000000000000),(378965281632075953/1000000000000000000),(253318138420522897/1000000000000000000),(27071265342244947/125000000000000000)⟩
theorem valid2669 : certificate2669.Valid := by decide +kernel
theorem sound2669 : certificate2669.Sound := rat_cut_bin_certificate_sound certificate2669 profilesValid2669 numericValid2669 valid2669

def retention2670 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(5265781395408524133/10705984450122921257),(9822978759276926917/1000000000000000000),(21/20),(15888142422982393738009435852023576851591/15716766014843083067200000000000000000000),false,MergedCutProfiles.Batch421.profile16875,(fun _ => MergedCutProfiles.Batch421.profile16875)⟩
theorem profilesValid2670 : retention2670.ProfilesValid := by
  exact MergedCutProfiles.Batch421.valid16875
theorem numericValid2670 : retention2670.NumericValid := by decide +kernel
def certificate2670 : RatCutBinCertificate := ⟨⟨retention2670,(145042793394951413/62500000000000000),(106411689904918233/500000000000000000),(8467007229966131563/500000000000000000),(181865074432318742627/500000000000000000),(490139053213711017/500000000000000000)⟩,(99494530254522077/100000000000000000),(75022419315060141/200000000000000000),(64269069792257033/250000000000000000),(218907039773727451/1000000000000000000)⟩
theorem valid2670 : certificate2670.Valid := by decide +kernel
theorem sound2670 : certificate2670.Sound := rat_cut_bin_certificate_sound certificate2670 profilesValid2670 numericValid2670 valid2670

def retention2671 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(10636878418725218749/21411968900245842514),(5265781395408524133/500000000000000000),(21/20),(4223551446185393703246390931083038017271/4212625116326819306400000000000000000000),false,MergedCutProfiles.Batch421.profile16876,(fun _ => MergedCutProfiles.Batch421.profile16876)⟩
theorem profilesValid2671 : retention2671.ProfilesValid := by
  exact MergedCutProfiles.Batch421.valid16876
theorem numericValid2671 : retention2671.NumericValid := by decide +kernel
def certificate2671 : RatCutBinCertificate := ⟨⟨retention2671,(145042793394951413/62500000000000000),(106411689904918233/500000000000000000),(8467007229966131563/500000000000000000),(181865074432318742627/500000000000000000),(485983941710895613/500000000000000000)⟩,(99494530254522077/100000000000000000),(376843074666229839/1000000000000000000),(255383129782509317/1000000000000000000),(43395966945227167/200000000000000000)⟩
theorem valid2671 : certificate2671.Valid := by decide +kernel
theorem sound2671 : certificate2671.Sound := rat_cut_bin_certificate_sound certificate2671 profilesValid2671 numericValid2671 valid2671

def retention2672 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(1/2),(10636878418725218749/1000000000000000000),(21/20),(16958453028141950084815804381652970249479/17019005469960349998400000000000000000000),false,MergedCutProfiles.Batch421.profile16877,(fun _ => MergedCutProfiles.Batch421.profile16877)⟩
theorem profilesValid2672 : retention2672.ProfilesValid := by
  exact MergedCutProfiles.Batch421.valid16877
theorem numericValid2672 : retention2672.NumericValid := by decide +kernel
def certificate2672 : RatCutBinCertificate := ⟨⟨retention2672,(145042793394951413/62500000000000000),(106411689904918233/500000000000000000),(8467007229966131563/500000000000000000),(181865074432318742627/500000000000000000),(482908129155749773/500000000000000000)⟩,(99494530254522077/100000000000000000),(189519707614508569/500000000000000000),(126623109268886557/500000000000000000),(107035167603099237/500000000000000000)⟩
theorem valid2672 : certificate2672.Valid := by decide +kernel
theorem sound2672 : certificate2672.Sound := rat_cut_bin_certificate_sound certificate2672 profilesValid2672 numericValid2672 valid2672

def retention2673 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(9705929419252730899/21411968900245842514),(986764932678296411/200000000000000000),(21/20),(334507209002734687812327212787983340759/315764778457054851520000000000000000000),false,MergedCutProfiles.Batch421.profile16878,(fun _ => MergedCutProfiles.Batch421.profile16878)⟩
theorem profilesValid2673 : retention2673.ProfilesValid := by
  exact MergedCutProfiles.Batch421.valid16878
theorem numericValid2673 : retention2673.NumericValid := by decide +kernel
def certificate2673 : RatCutBinCertificate := ⟨⟨retention2673,(160366804707451413/62500000000000000),(106411689904918233/500000000000000000),(8467007229966131563/500000000000000000),(181865074432318742627/500000000000000000),(512746071346817857/500000000000000000)⟩,(994410477574723427/1000000000000000000),(11200285546797801/50000000000000000),(55087415842925563/125000000000000000),(1439681416471289/4000000000000000)⟩
theorem valid2673 : certificate2673.Valid := by decide +kernel
theorem sound2673 : certificate2673.Sound := rat_cut_bin_certificate_sound certificate2673 profilesValid2673 numericValid2673 valid2673

def retention2674 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(5307616031775291818/10705984450122921257),(9705929419252730899/1000000000000000000),1,(7639291796776172232934820463503409927/7764743535402184719200000000000000000),false,MergedCutProfiles.Batch421.profile16879,(fun _ => MergedCutProfiles.Batch421.profile16879)⟩
theorem profilesValid2674 : retention2674.ProfilesValid := by
  exact MergedCutProfiles.Batch421.valid16879
theorem numericValid2674 : retention2674.NumericValid := by decide +kernel
def certificate2674 : RatCutBinCertificate := ⟨⟨retention2674,(160366804707451413/62500000000000000),(106411689904918233/500000000000000000),(8467007229966131563/500000000000000000),(181865074432318742627/500000000000000000),(190318826628609609/200000000000000000)⟩,(994410477574723427/1000000000000000000),(150875835927937/625000000000000),(103847663311763383/250000000000000000),(357864410404375759/1000000000000000000)⟩
theorem valid2674 : certificate2674.Valid := by decide +kernel
theorem sound2674 : certificate2674.Sound := rat_cut_bin_certificate_sound certificate2674 profilesValid2674 numericValid2674 valid2674

def retention2675 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(1/2),(2653808015887645909/250000000000000000),1,(10381710818727438780436886027870542287/10615232063550583636000000000000000000),false,MergedCutProfiles.Batch421.profile16877,(fun _ => MergedCutProfiles.Batch421.profile16877)⟩
theorem profilesValid2675 : retention2675.ProfilesValid := by
  exact MergedCutProfiles.Batch421.valid16877
theorem numericValid2675 : retention2675.NumericValid := by decide +kernel
def certificate2675 : RatCutBinCertificate := ⟨⟨retention2675,(160366804707451413/62500000000000000),(106411689904918233/500000000000000000),(8467007229966131563/500000000000000000),(181865074432318742627/500000000000000000),(472876095176101157/500000000000000000)⟩,(994410477574723427/1000000000000000000),(7590390049670987/31250000000000000),(1614374270818863/3906250000000000),(89194096568664371/250000000000000000)⟩
theorem valid2675 : certificate2675.Valid := by decide +kernel
theorem sound2675 : certificate2675.Sound := rat_cut_bin_certificate_sound certificate2675 profilesValid2675 numericValid2675 valid2675

def certificates : List RatCutBinCertificate := [certificate2664,certificate2665,certificate2666,certificate2667,certificate2668,certificate2669,certificate2670,certificate2671,certificate2672,certificate2673,certificate2674,certificate2675]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2664,List.forall_mem_cons.mpr ⟨sound2665,List.forall_mem_cons.mpr ⟨sound2666,List.forall_mem_cons.mpr ⟨sound2667,List.forall_mem_cons.mpr ⟨sound2668,List.forall_mem_cons.mpr ⟨sound2669,List.forall_mem_cons.mpr ⟨sound2670,List.forall_mem_cons.mpr ⟨sound2671,List.forall_mem_cons.mpr ⟨sound2672,List.forall_mem_cons.mpr ⟨sound2673,List.forall_mem_cons.mpr ⟨sound2674,List.forall_mem_cons.mpr ⟨sound2675,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch222
