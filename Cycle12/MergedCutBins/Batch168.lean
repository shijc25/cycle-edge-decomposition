import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch016
import Cycle12.MergedCutProfiles.Batch017
import Cycle12.MergedCutProfiles.Batch018
import Cycle12.MergedCutProfiles.Batch316
import Cycle12.MergedCutProfiles.Batch317

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch168

def retention2016 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(1/2),64,1,(255369632393373974456752157088663284991/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch016.profile655,(fun _ => MergedCutProfiles.Batch016.profile655)⟩
theorem profilesValid2016 : retention2016.ProfilesValid := by
  exact MergedCutProfiles.Batch016.valid655
theorem numericValid2016 : retention2016.NumericValid := by decide +kernel
def certificate2016 : RatCutBinCertificate := ⟨⟨retention2016,(2139093607225949127/1000000000000000000),(1008381335301397/125000000000000000),(244078099696727509/31250000000000000),(4594407606916828314031/1000000000000000000),(995328270054155861/1000000000000000000)⟩,(62471102478511477/62500000000000000),(4944630008904063/20000000000000000),(407188656611345519/1000000000000000000),(199447011564918093/500000000000000000)⟩
theorem valid2016 : certificate2016.Valid := by decide +kernel
theorem sound2016 : certificate2016.Sound := rat_cut_bin_certificate_sound certificate2016 profilesValid2016 numericValid2016 valid2016

def retention2017 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(312125967324169814/253857478123666143223),(149973459800606483/250000000000000000),4,(269607166960637752742634039144389003/119978767840485186400000000000000000),true,MergedCutProfiles.Batch316.profile12642,![MergedCutProfiles.Batch316.profile12642,MergedCutProfiles.Batch016.profile656,MergedCutProfiles.Batch316.profile12643,MergedCutProfiles.Batch016.profile672,MergedCutProfiles.Batch316.profile12644,MergedCutProfiles.Batch316.profile12645,MergedCutProfiles.Batch316.profile12646,MergedCutProfiles.Batch016.profile673,MergedCutProfiles.Batch316.profile12647,MergedCutProfiles.Batch316.profile12648,MergedCutProfiles.Batch316.profile12649,MergedCutProfiles.Batch016.profile661,MergedCutProfiles.Batch316.profile12650,MergedCutProfiles.Batch016.profile662,MergedCutProfiles.Batch316.profile12651,MergedCutProfiles.Batch016.profile675]⟩
theorem profilesValid2017 : retention2017.ProfilesValid := by
  change ∀ j : Fin 16, (retention2017.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch316.valid12642
  · exact MergedCutProfiles.Batch016.valid656
  · exact MergedCutProfiles.Batch316.valid12643
  · exact MergedCutProfiles.Batch016.valid672
  · exact MergedCutProfiles.Batch316.valid12644
  · exact MergedCutProfiles.Batch316.valid12645
  · exact MergedCutProfiles.Batch316.valid12646
  · exact MergedCutProfiles.Batch016.valid673
  · exact MergedCutProfiles.Batch316.valid12647
  · exact MergedCutProfiles.Batch316.valid12648
  · exact MergedCutProfiles.Batch316.valid12649
  · exact MergedCutProfiles.Batch016.valid661
  · exact MergedCutProfiles.Batch316.valid12650
  · exact MergedCutProfiles.Batch016.valid662
  · exact MergedCutProfiles.Batch316.valid12651
  · exact MergedCutProfiles.Batch016.valid675
theorem numericValid2017 : retention2017.NumericValid := by decide +kernel
def certificate2017 : RatCutBinCertificate := ⟨⟨retention2017,(1865775524103878461/1000000000000000000),(9292470143341151/1000000000000000000),(790946366227552651/100000000000000000),(4034362102860816049913/1000000000000000000),(2238355916863309283/1000000000000000000)⟩,(999541258051910417/1000000000000000000),(137087452183012581/250000000000000000),(61089332347710117/500000000000000000),(55410724665425839/1000000000000000000)⟩
theorem valid2017 : certificate2017.Valid := by decide +kernel
theorem sound2017 : certificate2017.Sound := rat_cut_bin_certificate_sound certificate2017 profilesValid2017 numericValid2017 valid2017

def retention2018 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(627005863000000000/253857478123666143223),(156062983662084907/250000000000000000),4,(36340631187910837427/16000000000000000000),true,MergedCutProfiles.Batch016.profile656,![MergedCutProfiles.Batch016.profile656,MergedCutProfiles.Batch016.profile672,MergedCutProfiles.Batch016.profile658,MergedCutProfiles.Batch016.profile673,MergedCutProfiles.Batch316.profile12648,MergedCutProfiles.Batch016.profile661,MergedCutProfiles.Batch016.profile662,MergedCutProfiles.Batch016.profile675,MergedCutProfiles.Batch016.profile664,MergedCutProfiles.Batch016.profile665,MergedCutProfiles.Batch016.profile666,MergedCutProfiles.Batch016.profile667,MergedCutProfiles.Batch316.profile12652,MergedCutProfiles.Batch016.profile669,MergedCutProfiles.Batch316.profile12653,MergedCutProfiles.Batch017.profile691]⟩
theorem profilesValid2018 : retention2018.ProfilesValid := by
  change ∀ j : Fin 16, (retention2018.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch016.valid656
  · exact MergedCutProfiles.Batch016.valid672
  · exact MergedCutProfiles.Batch016.valid658
  · exact MergedCutProfiles.Batch016.valid673
  · exact MergedCutProfiles.Batch316.valid12648
  · exact MergedCutProfiles.Batch016.valid661
  · exact MergedCutProfiles.Batch016.valid662
  · exact MergedCutProfiles.Batch016.valid675
  · exact MergedCutProfiles.Batch016.valid664
  · exact MergedCutProfiles.Batch016.valid665
  · exact MergedCutProfiles.Batch016.valid666
  · exact MergedCutProfiles.Batch016.valid667
  · exact MergedCutProfiles.Batch316.valid12652
  · exact MergedCutProfiles.Batch016.valid669
  · exact MergedCutProfiles.Batch316.valid12653
  · exact MergedCutProfiles.Batch017.valid691
theorem numericValid2018 : retention2018.NumericValid := by decide +kernel
def certificate2018 : RatCutBinCertificate := ⟨⟨retention2018,(1865775524103878461/1000000000000000000),(9292470143341151/1000000000000000000),(790946366227552651/100000000000000000),(4034362102860816049913/1000000000000000000),(226252138097325207/100000000000000000)⟩,(999541258051910417/1000000000000000000),(52867864917137601/100000000000000000),(67177521653903437/500000000000000000),(30963220299646717/500000000000000000)⟩
theorem valid2018 : certificate2018.Valid := by decide +kernel
theorem sound2018 : certificate2018.Sound := rat_cut_bin_certificate_sound certificate2018 profilesValid2018 numericValid2018 valid2018

def retention2019 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(1040437816532946302/253857478123666143223),(627005863/500000000),(49/20),(9143792013994421343/4000000000000000000),true,MergedCutProfiles.Batch316.profile12654,![MergedCutProfiles.Batch316.profile12654,MergedCutProfiles.Batch316.profile12655,MergedCutProfiles.Batch316.profile12648,MergedCutProfiles.Batch316.profile12656,MergedCutProfiles.Batch316.profile12657,MergedCutProfiles.Batch016.profile665,MergedCutProfiles.Batch316.profile12658,MergedCutProfiles.Batch016.profile668,MergedCutProfiles.Batch316.profile12653,MergedCutProfiles.Batch316.profile12659,MergedCutProfiles.Batch316.profile12660,MergedCutProfiles.Batch316.profile12661,MergedCutProfiles.Batch316.profile12662,MergedCutProfiles.Batch316.profile12663,MergedCutProfiles.Batch316.profile12664,MergedCutProfiles.Batch316.profile12665]⟩
theorem profilesValid2019 : retention2019.ProfilesValid := by
  change ∀ j : Fin 16, (retention2019.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch316.valid12654
  · exact MergedCutProfiles.Batch316.valid12655
  · exact MergedCutProfiles.Batch316.valid12648
  · exact MergedCutProfiles.Batch316.valid12656
  · exact MergedCutProfiles.Batch316.valid12657
  · exact MergedCutProfiles.Batch016.valid665
  · exact MergedCutProfiles.Batch316.valid12658
  · exact MergedCutProfiles.Batch016.valid668
  · exact MergedCutProfiles.Batch316.valid12653
  · exact MergedCutProfiles.Batch316.valid12659
  · exact MergedCutProfiles.Batch316.valid12660
  · exact MergedCutProfiles.Batch316.valid12661
  · exact MergedCutProfiles.Batch316.valid12662
  · exact MergedCutProfiles.Batch316.valid12663
  · exact MergedCutProfiles.Batch316.valid12664
  · exact MergedCutProfiles.Batch316.valid12665
theorem numericValid2019 : retention2019.NumericValid := by decide +kernel
def certificate2019 : RatCutBinCertificate := ⟨⟨retention2019,(1865775524103878461/1000000000000000000),(9292470143341151/1000000000000000000),(790946366227552651/100000000000000000),(4034362102860816049913/1000000000000000000),(285072195326271239/125000000000000000)⟩,(999541258051910417/1000000000000000000),(354987670222628307/1000000000000000000),(277356416944798081/1000000000000000000),(49510063443074783/250000000000000000)⟩
theorem valid2019 : certificate2019.Valid := by decide +kernel
theorem sound2019 : certificate2019.Sound := rat_cut_bin_certificate_sound certificate2019 profilesValid2019 numericValid2019 valid2019

def retention2020 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(32000000000000000000/253857478123666143223),(520218908266473151/250000000000000000),(9/5),(94648361302381718786675053847943400151/52021890826647315100000000000000000000),false,MergedCutProfiles.Batch316.profile12666,(fun _ => MergedCutProfiles.Batch316.profile12666)⟩
theorem profilesValid2020 : retention2020.ProfilesValid := by
  exact MergedCutProfiles.Batch316.valid12666
theorem numericValid2020 : retention2020.NumericValid := by decide +kernel
def certificate2020 : RatCutBinCertificate := ⟨⟨retention2020,(1865775524103878461/1000000000000000000),(9292470143341151/1000000000000000000),(790946366227552651/100000000000000000),(4034362102860816049913/1000000000000000000),(181544924058116273/100000000000000000)⟩,(999541258051910417/1000000000000000000),(362065563678722723/1000000000000000000),(135048530778485733/500000000000000000),(335177051081869/1562500000000000)⟩
theorem valid2020 : certificate2020.Valid := by decide +kernel
theorem sound2020 : certificate2020.Sound := rat_cut_bin_certificate_sound certificate2020 profilesValid2020 numericValid2020 valid2020

def retention2021 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(1/2),64,1,(255369839288059878534814821034680834799/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch017.profile702,(fun _ => MergedCutProfiles.Batch017.profile702)⟩
theorem profilesValid2021 : retention2021.ProfilesValid := by
  exact MergedCutProfiles.Batch017.valid702
theorem numericValid2021 : retention2021.NumericValid := by decide +kernel
def certificate2021 : RatCutBinCertificate := ⟨⟨retention2021,(1865775524103878461/1000000000000000000),(9292470143341151/1000000000000000000),(790946366227552651/100000000000000000),(4034362102860816049913/1000000000000000000),(995346419594294831/1000000000000000000)⟩,(999541258051910417/1000000000000000000),(435924798921761221/1000000000000000000),(101066354348928121/500000000000000000),(49504836101345359/250000000000000000)⟩
theorem valid2021 : certificate2021.Valid := by decide +kernel
theorem sound2021 : certificate2021.Sound := rat_cut_bin_certificate_sound certificate2021 profilesValid2021 numericValid2021 valid2021

def retention2022 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(32000000000000000000/253857478123666143223),(1237710374622032713/250000000000000000),(11/10),(26818420541994777171510125031409471237/15471379682775408912500000000000000000),false,MergedCutProfiles.Batch316.profile12666,(fun _ => MergedCutProfiles.Batch316.profile12666)⟩
theorem profilesValid2022 : retention2022.ProfilesValid := by
  exact MergedCutProfiles.Batch316.valid12666
theorem numericValid2022 : retention2022.NumericValid := by decide +kernel
def certificate2022 : RatCutBinCertificate := ⟨⟨retention2022,(2146477017103878461/1000000000000000000),(9292470143341151/1000000000000000000),(790946366227552651/100000000000000000),(4034362102860816049913/1000000000000000000),(1730647414811872543/1000000000000000000)⟩,(499736120559969857/500000000000000000),(28170221034170567/200000000000000000),(290910953604884091/500000000000000000),(177452762844727973/250000000000000000)⟩
theorem valid2022 : certificate2022.Valid := by decide +kernel
theorem sound2022 : certificate2022.Sound := rat_cut_bin_certificate_sound certificate2022 profilesValid2022 numericValid2022 valid2022

def retention2023 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(1/2),64,1,(255369839288059878534814821034680834799/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch017.profile702,(fun _ => MergedCutProfiles.Batch017.profile702)⟩
theorem profilesValid2023 : retention2023.ProfilesValid := by
  exact MergedCutProfiles.Batch017.valid702
theorem numericValid2023 : retention2023.NumericValid := by decide +kernel
def certificate2023 : RatCutBinCertificate := ⟨⟨retention2023,(2146477017103878461/1000000000000000000),(9292470143341151/1000000000000000000),(790946366227552651/100000000000000000),(4034362102860816049913/1000000000000000000),(497508318064398823/500000000000000000)⟩,(499736120559969857/500000000000000000),(61246111920730291/250000000000000000),(8206672810119579/20000000000000000),(401824528913359609/1000000000000000000)⟩
theorem valid2023 : certificate2023.Valid := by decide +kernel
theorem sound2023 : certificate2023.Sound := rat_cut_bin_certificate_sound certificate2023 profilesValid2023 numericValid2023 valid2023

def retention2024 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(628771778278051904/444163735094597351287),(302118660045357649/500000000000000000),4,(288392805920302912057/128000000000000000000),true,MergedCutProfiles.Batch316.profile12667,![MergedCutProfiles.Batch316.profile12667,MergedCutProfiles.Batch017.profile703,MergedCutProfiles.Batch316.profile12668,MergedCutProfiles.Batch017.profile704,MergedCutProfiles.Batch316.profile12669,MergedCutProfiles.Batch017.profile705,MergedCutProfiles.Batch316.profile12670,MergedCutProfiles.Batch017.profile706,MergedCutProfiles.Batch316.profile12671,MergedCutProfiles.Batch316.profile12672,MergedCutProfiles.Batch316.profile12673,MergedCutProfiles.Batch316.profile12674,MergedCutProfiles.Batch316.profile12675,MergedCutProfiles.Batch017.profile709,MergedCutProfiles.Batch316.profile12676,MergedCutProfiles.Batch017.profile710]⟩
theorem profilesValid2024 : retention2024.ProfilesValid := by
  change ∀ j : Fin 16, (retention2024.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch316.valid12667
  · exact MergedCutProfiles.Batch017.valid703
  · exact MergedCutProfiles.Batch316.valid12668
  · exact MergedCutProfiles.Batch017.valid704
  · exact MergedCutProfiles.Batch316.valid12669
  · exact MergedCutProfiles.Batch017.valid705
  · exact MergedCutProfiles.Batch316.valid12670
  · exact MergedCutProfiles.Batch017.valid706
  · exact MergedCutProfiles.Batch316.valid12671
  · exact MergedCutProfiles.Batch316.valid12672
  · exact MergedCutProfiles.Batch316.valid12673
  · exact MergedCutProfiles.Batch316.valid12674
  · exact MergedCutProfiles.Batch316.valid12675
  · exact MergedCutProfiles.Batch017.valid709
  · exact MergedCutProfiles.Batch316.valid12676
  · exact MergedCutProfiles.Batch017.valid710
theorem numericValid2024 : retention2024.NumericValid := by decide +kernel
def certificate2024 : RatCutBinCertificate := ⟨⟨retention2024,(1872801735989206349/1000000000000000000),(1060946273715283/100000000000000000),(8010371959623307101/1000000000000000000),(714899821114160991899/200000000000000000),(560786734393967093/250000000000000000)⟩,(499740466038570041/500000000000000000),(543134215464032337/1000000000000000000),(62668646236635417/500000000000000000),(3563466333004491/62500000000000000)⟩
theorem valid2024 : certificate2024.Valid := by decide +kernel
theorem sound2024 : certificate2024.Sound := rat_cut_bin_certificate_sound certificate2024 profilesValid2024 numericValid2024 valid2024

def retention2025 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(1235712959000000000/444163735094597351287),(9824559035594561/15625000000000000),4,(9100263617861335979/4000000000000000000),true,MergedCutProfiles.Batch017.profile703,![MergedCutProfiles.Batch017.profile703,MergedCutProfiles.Batch017.profile704,MergedCutProfiles.Batch316.profile12677,MergedCutProfiles.Batch017.profile706,MergedCutProfiles.Batch316.profile12672,MergedCutProfiles.Batch316.profile12674,MergedCutProfiles.Batch018.profile736,MergedCutProfiles.Batch316.profile12678,MergedCutProfiles.Batch316.profile12679,MergedCutProfiles.Batch317.profile12680,MergedCutProfiles.Batch317.profile12681,MergedCutProfiles.Batch317.profile12682,MergedCutProfiles.Batch317.profile12683,MergedCutProfiles.Batch018.profile737,MergedCutProfiles.Batch317.profile12684,MergedCutProfiles.Batch317.profile12685]⟩
theorem profilesValid2025 : retention2025.ProfilesValid := by
  change ∀ j : Fin 16, (retention2025.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch017.valid703
  · exact MergedCutProfiles.Batch017.valid704
  · exact MergedCutProfiles.Batch316.valid12677
  · exact MergedCutProfiles.Batch017.valid706
  · exact MergedCutProfiles.Batch316.valid12672
  · exact MergedCutProfiles.Batch316.valid12674
  · exact MergedCutProfiles.Batch018.valid736
  · exact MergedCutProfiles.Batch316.valid12678
  · exact MergedCutProfiles.Batch316.valid12679
  · exact MergedCutProfiles.Batch317.valid12680
  · exact MergedCutProfiles.Batch317.valid12681
  · exact MergedCutProfiles.Batch317.valid12682
  · exact MergedCutProfiles.Batch317.valid12683
  · exact MergedCutProfiles.Batch018.valid737
  · exact MergedCutProfiles.Batch317.valid12684
  · exact MergedCutProfiles.Batch317.valid12685
theorem numericValid2025 : retention2025.NumericValid := by decide +kernel
def certificate2025 : RatCutBinCertificate := ⟨⟨retention2025,(1872801735989206349/1000000000000000000),(1060946273715283/100000000000000000),(8010371959623307101/1000000000000000000),(714899821114160991899/200000000000000000),(2265144046264265881/1000000000000000000)⟩,(499740466038570041/500000000000000000),(524253850791095301/1000000000000000000),(137193862410407763/1000000000000000000),(31687203209586999/500000000000000000)⟩
theorem valid2025 : certificate2025.Valid := by decide +kernel
theorem sound2025 : certificate2025.Sound := rat_cut_bin_certificate_sound certificate2025 profilesValid2025 numericValid2025 valid2025

def retention2026 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(1450402161764687628/444163735094597351287),(1235712959/1000000000),(49/20),(7326338399289667433/3200000000000000000),true,MergedCutProfiles.Batch317.profile12686,![MergedCutProfiles.Batch317.profile12686,MergedCutProfiles.Batch018.profile734,MergedCutProfiles.Batch316.profile12670,MergedCutProfiles.Batch018.profile735,MergedCutProfiles.Batch018.profile721,MergedCutProfiles.Batch018.profile736,MergedCutProfiles.Batch017.profile710,MergedCutProfiles.Batch017.profile711,MergedCutProfiles.Batch317.profile12687,MergedCutProfiles.Batch018.profile724,MergedCutProfiles.Batch317.profile12683,MergedCutProfiles.Batch018.profile737,MergedCutProfiles.Batch317.profile12688,MergedCutProfiles.Batch017.profile718,MergedCutProfiles.Batch018.profile726,MergedCutProfiles.Batch018.profile738]⟩
theorem profilesValid2026 : retention2026.ProfilesValid := by
  change ∀ j : Fin 16, (retention2026.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch317.valid12686
  · exact MergedCutProfiles.Batch018.valid734
  · exact MergedCutProfiles.Batch316.valid12670
  · exact MergedCutProfiles.Batch018.valid735
  · exact MergedCutProfiles.Batch018.valid721
  · exact MergedCutProfiles.Batch018.valid736
  · exact MergedCutProfiles.Batch017.valid710
  · exact MergedCutProfiles.Batch017.valid711
  · exact MergedCutProfiles.Batch317.valid12687
  · exact MergedCutProfiles.Batch018.valid724
  · exact MergedCutProfiles.Batch317.valid12683
  · exact MergedCutProfiles.Batch018.valid737
  · exact MergedCutProfiles.Batch317.valid12688
  · exact MergedCutProfiles.Batch017.valid718
  · exact MergedCutProfiles.Batch018.valid726
  · exact MergedCutProfiles.Batch018.valid738
theorem numericValid2026 : retention2026.NumericValid := by decide +kernel
def certificate2026 : RatCutBinCertificate := ⟨⟨retention2026,(1872801735989206349/1000000000000000000),(1060946273715283/100000000000000000),(8010371959623307101/1000000000000000000),(714899821114160991899/200000000000000000),(456680722568739091/200000000000000000)⟩,(499740466038570041/500000000000000000),(356793585547391137/1000000000000000000),(68872729966879277/250000000000000000),(98102689449015781/500000000000000000)⟩
theorem valid2026 : certificate2026.Valid := by decide +kernel
theorem sound2026 : certificate2026.Sound := rat_cut_bin_certificate_sound certificate2026 profilesValid2026 numericValid2026 valid2026

def retention2027 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(17451464737028060880/444163735094597351287),(362600540441171907/250000000000000000),(11/5),(669182494352938775307/320000000000000000000),true,MergedCutProfiles.Batch018.profile737,![MergedCutProfiles.Batch018.profile737,MergedCutProfiles.Batch018.profile741,MergedCutProfiles.Batch317.profile12689,MergedCutProfiles.Batch317.profile12690,MergedCutProfiles.Batch317.profile12691,MergedCutProfiles.Batch317.profile12692,MergedCutProfiles.Batch317.profile12693,MergedCutProfiles.Batch317.profile12694,MergedCutProfiles.Batch317.profile12695,MergedCutProfiles.Batch317.profile12696,MergedCutProfiles.Batch317.profile12697,MergedCutProfiles.Batch317.profile12698,MergedCutProfiles.Batch317.profile12699,MergedCutProfiles.Batch317.profile12700,MergedCutProfiles.Batch317.profile12701,MergedCutProfiles.Batch317.profile12702]⟩
theorem profilesValid2027 : retention2027.ProfilesValid := by
  change ∀ j : Fin 16, (retention2027.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch018.valid737
  · exact MergedCutProfiles.Batch018.valid741
  · exact MergedCutProfiles.Batch317.valid12689
  · exact MergedCutProfiles.Batch317.valid12690
  · exact MergedCutProfiles.Batch317.valid12691
  · exact MergedCutProfiles.Batch317.valid12692
  · exact MergedCutProfiles.Batch317.valid12693
  · exact MergedCutProfiles.Batch317.valid12694
  · exact MergedCutProfiles.Batch317.valid12695
  · exact MergedCutProfiles.Batch317.valid12696
  · exact MergedCutProfiles.Batch317.valid12697
  · exact MergedCutProfiles.Batch317.valid12698
  · exact MergedCutProfiles.Batch317.valid12699
  · exact MergedCutProfiles.Batch317.valid12700
  · exact MergedCutProfiles.Batch317.valid12701
  · exact MergedCutProfiles.Batch317.valid12702
theorem numericValid2027 : retention2027.NumericValid := by decide +kernel
def certificate2027 : RatCutBinCertificate := ⟨⟨retention2027,(1872801735989206349/1000000000000000000),(1060946273715283/100000000000000000),(8010371959623307101/1000000000000000000),(714899821114160991899/200000000000000000),(1042869137103128419/500000000000000000)⟩,(499740466038570041/500000000000000000),(363197967366068291/1000000000000000000),(134474259926812779/500000000000000000),(24557396609850991/125000000000000000)⟩
theorem valid2027 : certificate2027.Valid := by decide +kernel
theorem sound2027 : certificate2027.Sound := rat_cut_bin_certificate_sound certificate2027 profilesValid2027 numericValid2027 valid2027

def certificates : List RatCutBinCertificate := [certificate2016,certificate2017,certificate2018,certificate2019,certificate2020,certificate2021,certificate2022,certificate2023,certificate2024,certificate2025,certificate2026,certificate2027]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2016,List.forall_mem_cons.mpr ⟨sound2017,List.forall_mem_cons.mpr ⟨sound2018,List.forall_mem_cons.mpr ⟨sound2019,List.forall_mem_cons.mpr ⟨sound2020,List.forall_mem_cons.mpr ⟨sound2021,List.forall_mem_cons.mpr ⟨sound2022,List.forall_mem_cons.mpr ⟨sound2023,List.forall_mem_cons.mpr ⟨sound2024,List.forall_mem_cons.mpr ⟨sound2025,List.forall_mem_cons.mpr ⟨sound2026,List.forall_mem_cons.mpr ⟨sound2027,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch168
