import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch365
import Cycle12.MergedCutProfiles.Batch366
import Cycle12.MergedCutProfiles.Batch367

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch197

def retention2364 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(899777950838174174/1844418587063087577),(33919518282275889/1953125000000000),1,(70215761030012303889890246464563501167/69467173442101020672000000000000000000),false,MergedCutProfiles.Batch365.profile14639,(fun _ => MergedCutProfiles.Batch365.profile14639)⟩
theorem profilesValid2364 : retention2364.ProfilesValid := by
  exact MergedCutProfiles.Batch365.valid14639
theorem numericValid2364 : retention2364.NumericValid := by decide +kernel
def certificate2364 : RatCutBinCertificate := ⟨⟨retention2364,(210123274202006859/100000000000000000),(19858540071699249/200000000000000000),(3069225442730234251/250000000000000000),(284626370994771218563/500000000000000000),(496890843140974843/500000000000000000)⟩,(199331326118458419/200000000000000000),(91258055941201103/200000000000000000),(1450720575543537/7812500000000000),(21743419548507523/125000000000000000)⟩
theorem valid2364 : certificate2364.Valid := by decide +kernel
theorem sound2364 : certificate2364.Sound := rat_cut_bin_certificate_sound certificate2364 profilesValid2364 numericValid2364 valid2364

def retention2365 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(7648862397083512291/15370154892192396475),(449888975419087087/20000000000000000),1,(3581112429039506400196999556807639871/3599111803352696696000000000000000000),false,MergedCutProfiles.Batch366.profile14640,(fun _ => MergedCutProfiles.Batch366.profile14640)⟩
theorem profilesValid2365 : retention2365.ProfilesValid := by
  exact MergedCutProfiles.Batch366.valid14640
theorem numericValid2365 : retention2365.NumericValid := by decide +kernel
def certificate2365 : RatCutBinCertificate := ⟨⟨retention2365,(210123274202006859/100000000000000000),(19858540071699249/200000000000000000),(3069225442730234251/250000000000000000),(284626370994771218563/500000000000000000),(489002265430212793/500000000000000000)⟩,(199331326118458419/200000000000000000),(459281398382332707/1000000000000000000),(91677563890026649/500000000000000000),(34252361331887863/200000000000000000)⟩
theorem valid2365 : certificate2365.Valid := by decide +kernel
theorem sound2365 : certificate2365.Sound := rat_cut_bin_certificate_sound certificate2365 profilesValid2365 numericValid2365 valid2365

def retention2366 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(1/2),(22946587191250536873/1000000000000000000),1,(6061589021101410635413151254051014477/6119089917666809832800000000000000000),false,MergedCutProfiles.Batch366.profile14641,(fun _ => MergedCutProfiles.Batch366.profile14641)⟩
theorem profilesValid2366 : retention2366.ProfilesValid := by
  exact MergedCutProfiles.Batch366.valid14641
theorem numericValid2366 : retention2366.NumericValid := by decide +kernel
def certificate2366 : RatCutBinCertificate := ⟨⟨retention2366,(210123274202006859/100000000000000000),(19858540071699249/200000000000000000),(3069225442730234251/250000000000000000),(284626370994771218563/500000000000000000),(97360862480073313/100000000000000000)⟩,(199331326118458419/200000000000000000),(7204096116516953/15625000000000000),(90986498649719691/500000000000000000),(169377269215809109/1000000000000000000)⟩
theorem valid2366 : certificate2366.Valid := by decide +kernel
theorem sound2366 : certificate2366.Sound := rat_cut_bin_certificate_sound certificate2366 profilesValid2366 numericValid2366 valid2366

def retention2367 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(20188939282539317596/46110464676577189425),(5537769948008627787/1000000000000000000),(21/20),(1077468425387493950096020473388396361999/984492435201533828800000000000000000000),false,MergedCutProfiles.Batch366.profile14642,(fun _ => MergedCutProfiles.Batch366.profile14642)⟩
theorem profilesValid2367 : retention2367.ProfilesValid := by
  exact MergedCutProfiles.Batch366.valid14642
theorem numericValid2367 : retention2367.NumericValid := by decide +kernel
def certificate2367 : RatCutBinCertificate := ⟨⟨retention2367,(238976252602006859/100000000000000000),(19858540071699249/200000000000000000),(3069225442730234251/250000000000000000),(284626370994771218563/500000000000000000),(1074145693688104549/1000000000000000000)⟩,(124524669386905273/125000000000000000),(224691448259002399/1000000000000000000),(439677238175556427/1000000000000000000),(380931830015838983/1000000000000000000)⟩
theorem valid2367 : certificate2367.Valid := by decide +kernel
theorem sound2367 : certificate2367.Sound := rat_cut_bin_certificate_sound certificate2367 profilesValid2367 numericValid2367 valid2367

def retention2368 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(22749402115379873708/46110464676577189425),(5047234820634829399/250000000000000000),1,(20230815567298587594824059848817526127/20188939282539317596000000000000000000),false,MergedCutProfiles.Batch366.profile14643,(fun _ => MergedCutProfiles.Batch366.profile14643)⟩
theorem profilesValid2368 : retention2368.ProfilesValid := by
  exact MergedCutProfiles.Batch366.valid14643
theorem numericValid2368 : retention2368.NumericValid := by decide +kernel
def certificate2368 : RatCutBinCertificate := ⟨⟨retention2368,(238976252602006859/100000000000000000),(19858540071699249/200000000000000000),(3069225442730234251/250000000000000000),(284626370994771218563/500000000000000000),(245686553425095009/250000000000000000)⟩,(124524669386905273/125000000000000000),(61397171566598947/250000000000000000),(102371489231837981/250000000000000000),(191123504295231601/500000000000000000)⟩
theorem valid2368 : certificate2368.Valid := by decide +kernel
theorem sound2368 : certificate2368.Sound := rat_cut_bin_certificate_sound certificate2368 profilesValid2368 numericValid2368 valid2368

def retention2369 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(7658965378844557482/15370154892192396475),(5687350528844968427/250000000000000000),1,(22609195361816886428531036044602153639/22749402115379873708000000000000000000),false,MergedCutProfiles.Batch366.profile14644,(fun _ => MergedCutProfiles.Batch366.profile14644)⟩
theorem profilesValid2369 : retention2369.ProfilesValid := by
  exact MergedCutProfiles.Batch366.valid14644
theorem numericValid2369 : retention2369.NumericValid := by decide +kernel
def certificate2369 : RatCutBinCertificate := ⟨⟨retention2369,(238976252602006859/100000000000000000),(19858540071699249/200000000000000000),(3069225442730234251/250000000000000000),(284626370994771218563/500000000000000000),(974508917138258673/1000000000000000000)⟩,(124524669386905273/125000000000000000),(247664590145263089/1000000000000000000),(50823102771282163/125000000000000000),(378469243477363161/1000000000000000000)⟩
theorem valid2369 : certificate2369.Valid := by decide +kernel
theorem sound2369 : certificate2369.Sound := rat_cut_bin_certificate_sound certificate2369 profilesValid2369 numericValid2369 valid2369

def retention2370 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(1/2),(11488448068266836223/500000000000000000),1,(2023227927660817234379564781740192923/2042390767691881995200000000000000000),false,MergedCutProfiles.Batch366.profile14641,(fun _ => MergedCutProfiles.Batch366.profile14641)⟩
theorem profilesValid2370 : retention2370.ProfilesValid := by
  exact MergedCutProfiles.Batch366.valid14641
theorem numericValid2370 : retention2370.NumericValid := by decide +kernel
def certificate2370 : RatCutBinCertificate := ⟨⟨retention2370,(238976252602006859/100000000000000000),(19858540071699249/200000000000000000),(3069225442730234251/250000000000000000),(284626370994771218563/500000000000000000),(121411182699895259/125000000000000000)⟩,(124524669386905273/125000000000000000),(62121376041335399/250000000000000000),(202721156317312647/500000000000000000),(188181419908175597/500000000000000000)⟩
theorem valid2370 : certificate2370.Valid := by decide +kernel
theorem sound2370 : certificate2370.Sound := rat_cut_bin_certificate_sound certificate2370 profilesValid2370 numericValid2370 valid2370

def retention2371 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(817291859555774136/43922520259805796461),(32367994437852441/40000000000000000),(16/5),(7038195409834575009/3200000000000000000),true,MergedCutProfiles.Batch366.profile14645,![MergedCutProfiles.Batch366.profile14645,MergedCutProfiles.Batch366.profile14646,MergedCutProfiles.Batch366.profile14647,MergedCutProfiles.Batch366.profile14648,MergedCutProfiles.Batch366.profile14649,MergedCutProfiles.Batch366.profile14650,MergedCutProfiles.Batch366.profile14651,MergedCutProfiles.Batch366.profile14652,MergedCutProfiles.Batch366.profile14653,MergedCutProfiles.Batch366.profile14654,MergedCutProfiles.Batch366.profile14655,MergedCutProfiles.Batch366.profile14656,MergedCutProfiles.Batch366.profile14657,MergedCutProfiles.Batch366.profile14658,MergedCutProfiles.Batch366.profile14659,MergedCutProfiles.Batch366.profile14660]⟩
theorem profilesValid2371 : retention2371.ProfilesValid := by
  change ∀ j : Fin 16, (retention2371.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch366.valid14645
  · exact MergedCutProfiles.Batch366.valid14646
  · exact MergedCutProfiles.Batch366.valid14647
  · exact MergedCutProfiles.Batch366.valid14648
  · exact MergedCutProfiles.Batch366.valid14649
  · exact MergedCutProfiles.Batch366.valid14650
  · exact MergedCutProfiles.Batch366.valid14651
  · exact MergedCutProfiles.Batch366.valid14652
  · exact MergedCutProfiles.Batch366.valid14653
  · exact MergedCutProfiles.Batch366.valid14654
  · exact MergedCutProfiles.Batch366.valid14655
  · exact MergedCutProfiles.Batch366.valid14656
  · exact MergedCutProfiles.Batch366.valid14657
  · exact MergedCutProfiles.Batch366.valid14658
  · exact MergedCutProfiles.Batch366.valid14659
  · exact MergedCutProfiles.Batch366.valid14660
theorem numericValid2371 : retention2371.NumericValid := by decide +kernel
def certificate2371 : RatCutBinCertificate := ⟨⟨retention2371,(2113123257850819737/1000000000000000000),(6511012982960937/62500000000000000),(12475637297761025987/1000000000000000000),(551038808552737177489/1000000000000000000),(16741927942771903/7812500000000000)⟩,(249136159241087007/250000000000000000),(38505536194301767/100000000000000000),(123728978891389611/500000000000000000),(6556495094708041/50000000000000000)⟩
theorem valid2371 : certificate2371.Valid := by decide +kernel
theorem sound2371 : certificate2371.Sound := rat_cut_bin_certificate_sound certificate2371 profilesValid2371 numericValid2371 valid2371

def retention2372 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(939455917248386793/43922520259805796461),(102161482444471767/125000000000000000),(16/5),(350655023443298277241/160000000000000000000),true,MergedCutProfiles.Batch366.profile14661,![MergedCutProfiles.Batch366.profile14661,MergedCutProfiles.Batch366.profile14662,MergedCutProfiles.Batch366.profile14663,MergedCutProfiles.Batch366.profile14664,MergedCutProfiles.Batch366.profile14665,MergedCutProfiles.Batch366.profile14666,MergedCutProfiles.Batch366.profile14667,MergedCutProfiles.Batch366.profile14668,MergedCutProfiles.Batch366.profile14669,MergedCutProfiles.Batch366.profile14670,MergedCutProfiles.Batch366.profile14671,MergedCutProfiles.Batch366.profile14672,MergedCutProfiles.Batch366.profile14673,MergedCutProfiles.Batch366.profile14674,MergedCutProfiles.Batch366.profile14675,MergedCutProfiles.Batch366.profile14676]⟩
theorem profilesValid2372 : retention2372.ProfilesValid := by
  change ∀ j : Fin 16, (retention2372.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch366.valid14661
  · exact MergedCutProfiles.Batch366.valid14662
  · exact MergedCutProfiles.Batch366.valid14663
  · exact MergedCutProfiles.Batch366.valid14664
  · exact MergedCutProfiles.Batch366.valid14665
  · exact MergedCutProfiles.Batch366.valid14666
  · exact MergedCutProfiles.Batch366.valid14667
  · exact MergedCutProfiles.Batch366.valid14668
  · exact MergedCutProfiles.Batch366.valid14669
  · exact MergedCutProfiles.Batch366.valid14670
  · exact MergedCutProfiles.Batch366.valid14671
  · exact MergedCutProfiles.Batch366.valid14672
  · exact MergedCutProfiles.Batch366.valid14673
  · exact MergedCutProfiles.Batch366.valid14674
  · exact MergedCutProfiles.Batch366.valid14675
  · exact MergedCutProfiles.Batch366.valid14676
theorem numericValid2372 : retention2372.NumericValid := by decide +kernel
def certificate2372 : RatCutBinCertificate := ⟨⟨retention2372,(2113123257850819737/1000000000000000000),(6511012982960937/62500000000000000),(12475637297761025987/1000000000000000000),(551038808552737177489/1000000000000000000),(2135124648438994409/1000000000000000000)⟩,(249136159241087007/250000000000000000),(384641086636383883/1000000000000000000),(123926762935597087/500000000000000000),(131224122279565659/1000000000000000000)⟩
theorem valid2372 : certificate2372.Valid := by decide +kernel
theorem sound2372 : certificate2372.Sound := rat_cut_bin_certificate_sound certificate2372 profilesValid2372 numericValid2372 valid2372

def retention2373 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(1009318818000000000/43922520259805796461),(939455917248386793/1000000000000000000),(57/20),(2787430615847814177617/1280000000000000000000),true,MergedCutProfiles.Batch366.profile14677,![MergedCutProfiles.Batch366.profile14677,MergedCutProfiles.Batch366.profile14678,MergedCutProfiles.Batch366.profile14679,MergedCutProfiles.Batch367.profile14680,MergedCutProfiles.Batch367.profile14681,MergedCutProfiles.Batch367.profile14682,MergedCutProfiles.Batch367.profile14683,MergedCutProfiles.Batch367.profile14684,MergedCutProfiles.Batch367.profile14685,MergedCutProfiles.Batch367.profile14686,MergedCutProfiles.Batch367.profile14687,MergedCutProfiles.Batch367.profile14688,MergedCutProfiles.Batch366.profile14660,MergedCutProfiles.Batch366.profile14675,MergedCutProfiles.Batch367.profile14689,MergedCutProfiles.Batch367.profile14690]⟩
theorem profilesValid2373 : retention2373.ProfilesValid := by
  change ∀ j : Fin 16, (retention2373.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch366.valid14677
  · exact MergedCutProfiles.Batch366.valid14678
  · exact MergedCutProfiles.Batch366.valid14679
  · exact MergedCutProfiles.Batch367.valid14680
  · exact MergedCutProfiles.Batch367.valid14681
  · exact MergedCutProfiles.Batch367.valid14682
  · exact MergedCutProfiles.Batch367.valid14683
  · exact MergedCutProfiles.Batch367.valid14684
  · exact MergedCutProfiles.Batch367.valid14685
  · exact MergedCutProfiles.Batch367.valid14686
  · exact MergedCutProfiles.Batch367.valid14687
  · exact MergedCutProfiles.Batch367.valid14688
  · exact MergedCutProfiles.Batch366.valid14660
  · exact MergedCutProfiles.Batch366.valid14675
  · exact MergedCutProfiles.Batch367.valid14689
  · exact MergedCutProfiles.Batch367.valid14690
theorem numericValid2373 : retention2373.NumericValid := by decide +kernel
def certificate2373 : RatCutBinCertificate := ⟨⟨retention2373,(2113123257850819737/1000000000000000000),(6511012982960937/62500000000000000),(12475637297761025987/1000000000000000000),(551038808552737177489/1000000000000000000),(425477465778875291/200000000000000000)⟩,(249136159241087007/250000000000000000),(181087811039237229/500000000000000000),(269985279677928737/1000000000000000000),(156958095315100377/1000000000000000000)⟩
theorem valid2373 : certificate2373.Valid := by decide +kernel
theorem sound2373 : certificate2373.Sound := rat_cut_bin_certificate_sound certificate2373 profilesValid2373 numericValid2373 valid2373

def retention2374 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(1037743792041045687/43922520259805796461),(504659409/500000000),(53/20),(1081395566151234297/500000000000000000),true,MergedCutProfiles.Batch367.profile14691,![MergedCutProfiles.Batch367.profile14691,MergedCutProfiles.Batch367.profile14692,MergedCutProfiles.Batch367.profile14693,MergedCutProfiles.Batch367.profile14694,MergedCutProfiles.Batch367.profile14695,MergedCutProfiles.Batch367.profile14696,MergedCutProfiles.Batch367.profile14697,MergedCutProfiles.Batch367.profile14698,MergedCutProfiles.Batch366.profile14670,MergedCutProfiles.Batch366.profile14671,MergedCutProfiles.Batch366.profile14658,MergedCutProfiles.Batch367.profile14699,MergedCutProfiles.Batch367.profile14700,MergedCutProfiles.Batch367.profile14701,MergedCutProfiles.Batch367.profile14702,MergedCutProfiles.Batch367.profile14703]⟩
theorem profilesValid2374 : retention2374.ProfilesValid := by
  change ∀ j : Fin 16, (retention2374.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch367.valid14691
  · exact MergedCutProfiles.Batch367.valid14692
  · exact MergedCutProfiles.Batch367.valid14693
  · exact MergedCutProfiles.Batch367.valid14694
  · exact MergedCutProfiles.Batch367.valid14695
  · exact MergedCutProfiles.Batch367.valid14696
  · exact MergedCutProfiles.Batch367.valid14697
  · exact MergedCutProfiles.Batch367.valid14698
  · exact MergedCutProfiles.Batch366.valid14670
  · exact MergedCutProfiles.Batch366.valid14671
  · exact MergedCutProfiles.Batch366.valid14658
  · exact MergedCutProfiles.Batch367.valid14699
  · exact MergedCutProfiles.Batch367.valid14700
  · exact MergedCutProfiles.Batch367.valid14701
  · exact MergedCutProfiles.Batch367.valid14702
  · exact MergedCutProfiles.Batch367.valid14703
theorem numericValid2374 : retention2374.NumericValid := by decide +kernel
def certificate2374 : RatCutBinCertificate := ⟨⟨retention2374,(2113123257850819737/1000000000000000000),(6511012982960937/62500000000000000),(12475637297761025987/1000000000000000000),(551038808552737177489/1000000000000000000),(211602761125228817/100000000000000000)⟩,(249136159241087007/250000000000000000),(35300957913104477/100000000000000000),(27941030013871503/100000000000000000),(171122974745497201/1000000000000000000)⟩
theorem valid2374 : certificate2374.Valid := by decide +kernel
theorem sound2374 : certificate2374.Sound := rat_cut_bin_certificate_sound certificate2374 profilesValid2374 numericValid2374 valid2374

def retention2375 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(1412709062940939656/43922520259805796461),(1037743792041045687/1000000000000000000),(13/5),(2725700168522633752203/1280000000000000000000),true,MergedCutProfiles.Batch367.profile14704,![MergedCutProfiles.Batch367.profile14704,MergedCutProfiles.Batch366.profile14663,MergedCutProfiles.Batch367.profile14705,MergedCutProfiles.Batch366.profile14666,MergedCutProfiles.Batch367.profile14683,MergedCutProfiles.Batch366.profile14669,MergedCutProfiles.Batch367.profile14706,MergedCutProfiles.Batch366.profile14672,MergedCutProfiles.Batch367.profile14707,MergedCutProfiles.Batch366.profile14675,MergedCutProfiles.Batch367.profile14702,MergedCutProfiles.Batch367.profile14708,MergedCutProfiles.Batch367.profile14709,MergedCutProfiles.Batch367.profile14710,MergedCutProfiles.Batch367.profile14711,MergedCutProfiles.Batch367.profile14712]⟩
theorem profilesValid2375 : retention2375.ProfilesValid := by
  change ∀ j : Fin 16, (retention2375.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch367.valid14704
  · exact MergedCutProfiles.Batch366.valid14663
  · exact MergedCutProfiles.Batch367.valid14705
  · exact MergedCutProfiles.Batch366.valid14666
  · exact MergedCutProfiles.Batch367.valid14683
  · exact MergedCutProfiles.Batch366.valid14669
  · exact MergedCutProfiles.Batch367.valid14706
  · exact MergedCutProfiles.Batch366.valid14672
  · exact MergedCutProfiles.Batch367.valid14707
  · exact MergedCutProfiles.Batch366.valid14675
  · exact MergedCutProfiles.Batch367.valid14702
  · exact MergedCutProfiles.Batch367.valid14708
  · exact MergedCutProfiles.Batch367.valid14709
  · exact MergedCutProfiles.Batch367.valid14710
  · exact MergedCutProfiles.Batch367.valid14711
  · exact MergedCutProfiles.Batch367.valid14712
theorem numericValid2375 : retention2375.NumericValid := by decide +kernel
def certificate2375 : RatCutBinCertificate := ⟨⟨retention2375,(2113123257850819737/1000000000000000000),(6511012982960937/62500000000000000),(12475637297761025987/1000000000000000000),(551038808552737177489/1000000000000000000),(1041786047182141599/500000000000000000)⟩,(249136159241087007/250000000000000000),(354352314785911599/1000000000000000000),(278014913662102463/1000000000000000000),(427707820303969/2500000000000000)⟩
theorem valid2375 : certificate2375.Valid := by decide +kernel
theorem sound2375 : certificate2375.Sound := rat_cut_bin_certificate_sound certificate2375 profilesValid2375 numericValid2375 valid2375

def certificates : List RatCutBinCertificate := [certificate2364,certificate2365,certificate2366,certificate2367,certificate2368,certificate2369,certificate2370,certificate2371,certificate2372,certificate2373,certificate2374,certificate2375]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2364,List.forall_mem_cons.mpr ⟨sound2365,List.forall_mem_cons.mpr ⟨sound2366,List.forall_mem_cons.mpr ⟨sound2367,List.forall_mem_cons.mpr ⟨sound2368,List.forall_mem_cons.mpr ⟨sound2369,List.forall_mem_cons.mpr ⟨sound2370,List.forall_mem_cons.mpr ⟨sound2371,List.forall_mem_cons.mpr ⟨sound2372,List.forall_mem_cons.mpr ⟨sound2373,List.forall_mem_cons.mpr ⟨sound2374,List.forall_mem_cons.mpr ⟨sound2375,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch197
