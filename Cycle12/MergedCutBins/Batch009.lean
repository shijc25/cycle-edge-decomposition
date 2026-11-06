import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch019
import Cycle12.MergedCutProfiles.Batch020

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch009

def retention108 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(64000000000000000000/222081867547298675643),(1421556576180837469/125000000000000000),(21/20),(1617096007563837127016193420113715500951/1137245260944669975200000000000000000000),false,MergedCutProfiles.Batch019.profile762,(fun _ => MergedCutProfiles.Batch019.profile762)⟩
theorem profilesValid108 : retention108.ProfilesValid := by
  exact MergedCutProfiles.Batch019.valid762
theorem numericValid108 : retention108.NumericValid := by decide +kernel
def certificate108 : RatCutBinCertificate := ⟨⟨retention108,(947937277989206349/500000000000000000),(1060946273715283/100000000000000000),(2002589223420813337/250000000000000000),(893623095659599263587/500000000000000000),(141930472436986507/100000000000000000)⟩,(998949067136812011/1000000000000000000),(13337183842500463/40000000000000000),(75086894346399143/250000000000000000),(364302787784966793/1000000000000000000)⟩
theorem valid108 : certificate108.Valid := by decide +kernel
theorem sound108 : certificate108.Sound := rat_cut_bin_certificate_sound certificate108 profilesValid108 numericValid108 valid108

def retention109 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(1/2),64,1,(255370070520985369056173916463207973031/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch019.profile763,(fun _ => MergedCutProfiles.Batch019.profile763)⟩
theorem profilesValid109 : retention109.ProfilesValid := by
  exact MergedCutProfiles.Batch019.valid763
theorem numericValid109 : retention109.NumericValid := by decide +kernel
def certificate109 : RatCutBinCertificate := ⟨⟨retention109,(947937277989206349/500000000000000000),(1060946273715283/100000000000000000),(2002589223420813337/250000000000000000),(893623095659599263587/500000000000000000),(497514156117859903/500000000000000000)⟩,(998949067136812011/1000000000000000000),(221557129638313837/500000000000000000),(196222457098516703/1000000000000000000),(12003380281682173/62500000000000000)⟩
theorem valid109 : certificate109.Valid := by decide +kernel
theorem sound109 : certificate109.Sound := rat_cut_bin_certificate_sound certificate109 profilesValid109 numericValid109 valid109

def retention110 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(64000000000000000000/222081867547298675643),(1725175270069206853/500000000000000000),(13/10),(61536280495656723005334108051624219063/43129381751730171325000000000000000000),false,MergedCutProfiles.Batch019.profile762,(fun _ => MergedCutProfiles.Batch019.profile762)⟩
theorem profilesValid110 : retention110.ProfilesValid := by
  exact MergedCutProfiles.Batch019.valid762
theorem numericValid110 : retention110.NumericValid := by decide +kernel
def certificate110 : RatCutBinCertificate := ⟨⟨retention110,(1129938938489206349/500000000000000000),(1060946273715283/100000000000000000),(2002589223420813337/250000000000000000),(893623095659599263587/500000000000000000),(1422892191507483897/1000000000000000000)⟩,(249686822050662827/250000000000000000),(275775047790379469/1000000000000000000),(73787244043860997/200000000000000000),(81041000157467147/250000000000000000)⟩
theorem valid110 : certificate110.Valid := by decide +kernel
theorem sound110 : certificate110.Sound := rat_cut_bin_certificate_sound certificate110 profilesValid110 numericValid110 valid110

def retention111 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(1/2),64,1,(255370070520985369056173916463207973031/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch019.profile763,(fun _ => MergedCutProfiles.Batch019.profile763)⟩
theorem profilesValid111 : retention111.ProfilesValid := by
  exact MergedCutProfiles.Batch019.valid763
theorem numericValid111 : retention111.NumericValid := by decide +kernel
def certificate111 : RatCutBinCertificate := ⟨⟨retention111,(1129938938489206349/500000000000000000),(1060946273715283/100000000000000000),(2002589223420813337/250000000000000000),(893623095659599263587/500000000000000000),(497273100689256181/500000000000000000)⟩,(249686822050662827/250000000000000000),(394549958131298629/1000000000000000000),(47702648826293227/200000000000000000),(233287973577997729/1000000000000000000)⟩
theorem valid111 : certificate111.Valid := by decide +kernel
theorem sound111 : certificate111.Sound := rat_cut_bin_certificate_sound certificate111 profilesValid111 numericValid111 valid111

def retention112 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(635677176362200955/195805185359399352263),(78672917866609029/125000000000000000),4,(72727713362658005263/32000000000000000000),true,MergedCutProfiles.Batch019.profile764,![MergedCutProfiles.Batch019.profile764,MergedCutProfiles.Batch019.profile765,MergedCutProfiles.Batch019.profile766,MergedCutProfiles.Batch019.profile767,MergedCutProfiles.Batch019.profile768,MergedCutProfiles.Batch019.profile769,MergedCutProfiles.Batch019.profile770,MergedCutProfiles.Batch019.profile771,MergedCutProfiles.Batch019.profile772,MergedCutProfiles.Batch019.profile773,MergedCutProfiles.Batch019.profile774,MergedCutProfiles.Batch019.profile775,MergedCutProfiles.Batch019.profile776,MergedCutProfiles.Batch019.profile777,MergedCutProfiles.Batch019.profile778,MergedCutProfiles.Batch019.profile779]⟩
theorem profilesValid112 : retention112.ProfilesValid := by
  change ∀ j : Fin 16, (retention112.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch019.valid764
  · exact MergedCutProfiles.Batch019.valid765
  · exact MergedCutProfiles.Batch019.valid766
  · exact MergedCutProfiles.Batch019.valid767
  · exact MergedCutProfiles.Batch019.valid768
  · exact MergedCutProfiles.Batch019.valid769
  · exact MergedCutProfiles.Batch019.valid770
  · exact MergedCutProfiles.Batch019.valid771
  · exact MergedCutProfiles.Batch019.valid772
  · exact MergedCutProfiles.Batch019.valid773
  · exact MergedCutProfiles.Batch019.valid774
  · exact MergedCutProfiles.Batch019.valid775
  · exact MergedCutProfiles.Batch019.valid776
  · exact MergedCutProfiles.Batch019.valid777
  · exact MergedCutProfiles.Batch019.valid778
  · exact MergedCutProfiles.Batch019.valid779
theorem numericValid112 : retention112.NumericValid := by decide +kernel
def certificate112 : RatCutBinCertificate := ⟨⟨retention112,(1899803599046795801/1000000000000000000),(12019078477736559/1000000000000000000),(4056627898521048907/500000000000000000),(199508041444546027759/125000000000000000),(2261483437783620169/1000000000000000000)⟩,(249705577108024753/250000000000000000),(251871339782784079/500000000000000000),(75423055209897891/500000000000000000),(869343813249167/12500000000000000)⟩
theorem valid112 : certificate112.Valid := by decide +kernel
theorem sound112 : certificate112.Sound := rat_cut_bin_certificate_sound certificate112 profilesValid112 numericValid112 valid112

def retention113 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(1109771456338856001/195805185359399352263),(127135435272440191/200000000000000000),4,(578979252637301626499/256000000000000000000),true,MergedCutProfiles.Batch019.profile780,![MergedCutProfiles.Batch019.profile780,MergedCutProfiles.Batch019.profile781,MergedCutProfiles.Batch019.profile782,MergedCutProfiles.Batch019.profile770,MergedCutProfiles.Batch019.profile783,MergedCutProfiles.Batch019.profile784,MergedCutProfiles.Batch019.profile775,MergedCutProfiles.Batch019.profile777,MergedCutProfiles.Batch019.profile785,MergedCutProfiles.Batch019.profile786,MergedCutProfiles.Batch019.profile787,MergedCutProfiles.Batch019.profile788,MergedCutProfiles.Batch019.profile789,MergedCutProfiles.Batch019.profile790,MergedCutProfiles.Batch019.profile791,MergedCutProfiles.Batch019.profile792]⟩
theorem profilesValid113 : retention113.ProfilesValid := by
  change ∀ j : Fin 16, (retention113.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch019.valid780
  · exact MergedCutProfiles.Batch019.valid781
  · exact MergedCutProfiles.Batch019.valid782
  · exact MergedCutProfiles.Batch019.valid770
  · exact MergedCutProfiles.Batch019.valid783
  · exact MergedCutProfiles.Batch019.valid784
  · exact MergedCutProfiles.Batch019.valid775
  · exact MergedCutProfiles.Batch019.valid777
  · exact MergedCutProfiles.Batch019.valid785
  · exact MergedCutProfiles.Batch019.valid786
  · exact MergedCutProfiles.Batch019.valid787
  · exact MergedCutProfiles.Batch019.valid788
  · exact MergedCutProfiles.Batch019.valid789
  · exact MergedCutProfiles.Batch019.valid790
  · exact MergedCutProfiles.Batch019.valid791
  · exact MergedCutProfiles.Batch019.valid792
theorem numericValid113 : retention113.NumericValid := by decide +kernel
def certificate113 : RatCutBinCertificate := ⟨⟨retention113,(1899803599046795801/1000000000000000000),(12019078477736559/1000000000000000000),(4056627898521048907/500000000000000000),(199508041444546027759/125000000000000000),(281297512643552437/125000000000000000)⟩,(249705577108024753/250000000000000000),(503138947051222213/1000000000000000000),(151260444544239433/1000000000000000000),(6958461773434549/100000000000000000)⟩
theorem valid113 : certificate113.Valid := by decide +kernel
theorem sound113 : certificate113.Sound := rat_cut_bin_certificate_sound certificate113 profilesValid113 numericValid113 valid113

def retention114 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(1192657342000000000/195805185359399352263),(1109771456338856001/1000000000000000000),(53/20),(2901875071833198607001/1280000000000000000000),true,MergedCutProfiles.Batch019.profile793,![MergedCutProfiles.Batch019.profile793,MergedCutProfiles.Batch019.profile794,MergedCutProfiles.Batch019.profile795,MergedCutProfiles.Batch019.profile796,MergedCutProfiles.Batch019.profile797,MergedCutProfiles.Batch019.profile798,MergedCutProfiles.Batch019.profile776,MergedCutProfiles.Batch019.profile799,MergedCutProfiles.Batch020.profile800,MergedCutProfiles.Batch020.profile801,MergedCutProfiles.Batch020.profile802,MergedCutProfiles.Batch019.profile789,MergedCutProfiles.Batch019.profile790,MergedCutProfiles.Batch019.profile791,MergedCutProfiles.Batch019.profile792,MergedCutProfiles.Batch020.profile803]⟩
theorem profilesValid114 : retention114.ProfilesValid := by
  change ∀ j : Fin 16, (retention114.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch019.valid793
  · exact MergedCutProfiles.Batch019.valid794
  · exact MergedCutProfiles.Batch019.valid795
  · exact MergedCutProfiles.Batch019.valid796
  · exact MergedCutProfiles.Batch019.valid797
  · exact MergedCutProfiles.Batch019.valid798
  · exact MergedCutProfiles.Batch019.valid776
  · exact MergedCutProfiles.Batch019.valid799
  · exact MergedCutProfiles.Batch020.valid800
  · exact MergedCutProfiles.Batch020.valid801
  · exact MergedCutProfiles.Batch020.valid802
  · exact MergedCutProfiles.Batch019.valid789
  · exact MergedCutProfiles.Batch019.valid790
  · exact MergedCutProfiles.Batch019.valid791
  · exact MergedCutProfiles.Batch019.valid792
  · exact MergedCutProfiles.Batch020.valid803
theorem numericValid114 : retention114.NumericValid := by decide +kernel
def certificate114 : RatCutBinCertificate := ⟨⟨retention114,(1899803599046795801/1000000000000000000),(12019078477736559/1000000000000000000),(4056627898521048907/500000000000000000),(199508041444546027759/125000000000000000),(2259631739901552871/1000000000000000000)⟩,(249705577108024753/250000000000000000),(369649084151670987/1000000000000000000),(65618104251342287/250000000000000000),(173268879606744889/1000000000000000000)⟩
theorem valid114 : certificate114.Valid := by decide +kernel
theorem sound114 : certificate114.Sound := rat_cut_bin_certificate_sound certificate114 profilesValid114 numericValid114 valid114

def retention115 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(1213740697843282049/195805185359399352263),(596328671/500000000),(5/2),(3618320058491704997/1600000000000000000),true,MergedCutProfiles.Batch020.profile804,![MergedCutProfiles.Batch020.profile804,MergedCutProfiles.Batch020.profile805,MergedCutProfiles.Batch019.profile795,MergedCutProfiles.Batch020.profile806,MergedCutProfiles.Batch020.profile807,MergedCutProfiles.Batch020.profile808,MergedCutProfiles.Batch020.profile809,MergedCutProfiles.Batch020.profile810,MergedCutProfiles.Batch020.profile811,MergedCutProfiles.Batch019.profile787,MergedCutProfiles.Batch019.profile788,MergedCutProfiles.Batch020.profile812,MergedCutProfiles.Batch020.profile813,MergedCutProfiles.Batch020.profile814,MergedCutProfiles.Batch020.profile815,MergedCutProfiles.Batch020.profile816]⟩
theorem profilesValid115 : retention115.ProfilesValid := by
  change ∀ j : Fin 16, (retention115.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch020.valid804
  · exact MergedCutProfiles.Batch020.valid805
  · exact MergedCutProfiles.Batch019.valid795
  · exact MergedCutProfiles.Batch020.valid806
  · exact MergedCutProfiles.Batch020.valid807
  · exact MergedCutProfiles.Batch020.valid808
  · exact MergedCutProfiles.Batch020.valid809
  · exact MergedCutProfiles.Batch020.valid810
  · exact MergedCutProfiles.Batch020.valid811
  · exact MergedCutProfiles.Batch019.valid787
  · exact MergedCutProfiles.Batch019.valid788
  · exact MergedCutProfiles.Batch020.valid812
  · exact MergedCutProfiles.Batch020.valid813
  · exact MergedCutProfiles.Batch020.valid814
  · exact MergedCutProfiles.Batch020.valid815
  · exact MergedCutProfiles.Batch020.valid816
theorem numericValid115 : retention115.NumericValid := by decide +kernel
def certificate115 : RatCutBinCertificate := ⟨⟨retention115,(1899803599046795801/1000000000000000000),(12019078477736559/1000000000000000000),(4056627898521048907/500000000000000000),(199508041444546027759/125000000000000000),(450882807366720113/200000000000000000)⟩,(249705577108024753/250000000000000000),(71645847600117777/200000000000000000),(274014416774876353/1000000000000000000),(18946408466385091/100000000000000000)⟩
theorem valid115 : certificate115.Valid := by decide +kernel
theorem sound115 : certificate115.Sound := rat_cut_bin_certificate_sound certificate115 profilesValid115 numericValid115 valid115

def retention116 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(1825165452068910816/195805185359399352263),(1213740697843282049/1000000000000000000),(49/20),(2860138033469445678297/1280000000000000000000),true,MergedCutProfiles.Batch020.profile817,![MergedCutProfiles.Batch020.profile817,MergedCutProfiles.Batch019.profile795,MergedCutProfiles.Batch020.profile818,MergedCutProfiles.Batch020.profile808,MergedCutProfiles.Batch020.profile819,MergedCutProfiles.Batch019.profile786,MergedCutProfiles.Batch020.profile820,MergedCutProfiles.Batch020.profile812,MergedCutProfiles.Batch020.profile821,MergedCutProfiles.Batch020.profile815,MergedCutProfiles.Batch020.profile822,MergedCutProfiles.Batch020.profile823,MergedCutProfiles.Batch020.profile824,MergedCutProfiles.Batch020.profile825,MergedCutProfiles.Batch020.profile826,MergedCutProfiles.Batch020.profile827]⟩
theorem profilesValid116 : retention116.ProfilesValid := by
  change ∀ j : Fin 16, (retention116.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch020.valid817
  · exact MergedCutProfiles.Batch019.valid795
  · exact MergedCutProfiles.Batch020.valid818
  · exact MergedCutProfiles.Batch020.valid808
  · exact MergedCutProfiles.Batch020.valid819
  · exact MergedCutProfiles.Batch019.valid786
  · exact MergedCutProfiles.Batch020.valid820
  · exact MergedCutProfiles.Batch020.valid812
  · exact MergedCutProfiles.Batch020.valid821
  · exact MergedCutProfiles.Batch020.valid815
  · exact MergedCutProfiles.Batch020.valid822
  · exact MergedCutProfiles.Batch020.valid823
  · exact MergedCutProfiles.Batch020.valid824
  · exact MergedCutProfiles.Batch020.valid825
  · exact MergedCutProfiles.Batch020.valid826
  · exact MergedCutProfiles.Batch020.valid827
theorem numericValid116 : retention116.NumericValid := by decide +kernel
def certificate116 : RatCutBinCertificate := ⟨⟨retention116,(1899803599046795801/1000000000000000000),(12019078477736559/1000000000000000000),(4056627898521048907/500000000000000000),(199508041444546027759/125000000000000000),(1113793779436019139/500000000000000000)⟩,(249705577108024753/250000000000000000),(179826991327436271/500000000000000000),(272554812754886103/1000000000000000000),(94764868579808649/500000000000000000)⟩
theorem valid116 : certificate116.Valid := by decide +kernel
theorem sound116 : certificate116.Sound := rat_cut_bin_certificate_sound certificate116 profilesValid116 numericValid116 valid116

def retention117 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(25495661939753012082/195805185359399352263),(57036420377153463/31250000000000000),(19/10),(329982059126234013211151857207140045311/182516545206891081600000000000000000000),false,MergedCutProfiles.Batch020.profile828,(fun _ => MergedCutProfiles.Batch020.profile828)⟩
theorem profilesValid117 : retention117.ProfilesValid := by
  exact MergedCutProfiles.Batch020.valid828
theorem numericValid117 : retention117.NumericValid := by decide +kernel
def certificate117 : RatCutBinCertificate := ⟨⟨retention117,(1899803599046795801/1000000000000000000),(12019078477736559/1000000000000000000),(4056627898521048907/500000000000000000),(199508041444546027759/125000000000000000),(1802609607057864667/1000000000000000000)⟩,(249705577108024753/250000000000000000),(376782093528541817/1000000000000000000),(6386066075513841/25000000000000000),(47509381548198939/250000000000000000)⟩
theorem valid117 : certificate117.Valid := by decide +kernel
theorem sound117 : certificate117.Sound := rat_cut_bin_certificate_sound certificate117 profilesValid117 numericValid117 valid117

def retention118 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(64000000000000000000/195805185359399352263),(12747830969876506041/500000000000000000),1,(136451038730400414505986178350702518567/101982647759012048328000000000000000000),false,MergedCutProfiles.Batch020.profile829,(fun _ => MergedCutProfiles.Batch020.profile829)⟩
theorem profilesValid118 : retention118.ProfilesValid := by
  exact MergedCutProfiles.Batch020.valid829
theorem numericValid118 : retention118.NumericValid := by decide +kernel
def certificate118 : RatCutBinCertificate := ⟨⟨retention118,(1899803599046795801/1000000000000000000),(12019078477736559/1000000000000000000),(4056627898521048907/500000000000000000),(199508041444546027759/125000000000000000),(1335168505721674891/1000000000000000000)⟩,(249705577108024753/250000000000000000),(340332728850820019/1000000000000000000),(292838295472913881/1000000000000000000),(371085586003553833/1000000000000000000)⟩
theorem valid118 : certificate118.Valid := by decide +kernel
theorem sound118 : certificate118.Sound := rat_cut_bin_certificate_sound certificate118 profilesValid118 numericValid118 valid118

def retention119 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(1/2),64,1,(408592521868712119380352324506759031/409600000000000000000000000000000000),false,MergedCutProfiles.Batch020.profile830,(fun _ => MergedCutProfiles.Batch020.profile830)⟩
theorem profilesValid119 : retention119.ProfilesValid := by
  exact MergedCutProfiles.Batch020.valid830
theorem numericValid119 : retention119.NumericValid := by decide +kernel
def certificate119 : RatCutBinCertificate := ⟨⟨retention119,(1899803599046795801/1000000000000000000),(12019078477736559/1000000000000000000),(4056627898521048907/500000000000000000),(199508041444546027759/125000000000000000),(994725943480937689/1000000000000000000)⟩,(249705577108024753/250000000000000000),(446327509034072203/1000000000000000000),(193618761285090577/1000000000000000000),(189424753706340717/1000000000000000000)⟩
theorem valid119 : certificate119.Valid := by decide +kernel
theorem sound119 : certificate119.Sound := rat_cut_bin_certificate_sound certificate119 profilesValid119 numericValid119 valid119

def certificates : List RatCutBinCertificate := [certificate108,certificate109,certificate110,certificate111,certificate112,certificate113,certificate114,certificate115,certificate116,certificate117,certificate118,certificate119]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound108,List.forall_mem_cons.mpr ⟨sound109,List.forall_mem_cons.mpr ⟨sound110,List.forall_mem_cons.mpr ⟨sound111,List.forall_mem_cons.mpr ⟨sound112,List.forall_mem_cons.mpr ⟨sound113,List.forall_mem_cons.mpr ⟨sound114,List.forall_mem_cons.mpr ⟨sound115,List.forall_mem_cons.mpr ⟨sound116,List.forall_mem_cons.mpr ⟨sound117,List.forall_mem_cons.mpr ⟨sound118,List.forall_mem_cons.mpr ⟨sound119,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch009
