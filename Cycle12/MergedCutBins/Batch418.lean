import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch384
import Cycle12.MergedCutProfiles.Batch699
import Cycle12.MergedCutProfiles.Batch700
import Cycle12.MergedCutProfiles.Batch701

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch418

def retention5016 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(38711383479004545473/1668693111133782522381),(3381443348407215257/1000000000000000000),(8/5),(752978057610894320303256302713467441159/338144334840721525700000000000000000000),false,MergedCutProfiles.Batch699.profile27983,(fun _ => MergedCutProfiles.Batch699.profile27983)⟩
theorem profilesValid5016 : retention5016.ProfilesValid := by
  exact MergedCutProfiles.Batch699.valid27983
theorem numericValid5016 : retention5016.NumericValid := by decide +kernel
def certificate5016 : RatCutBinCertificate := ⟨⟨retention5016,(959159135682956873/500000000000000000),(136712609017002193/1000000000000000000),(13779447163723159963/1000000000000000000),(23127892970843726925201/1000000000000000000),(109817134365400123/50000000000000000)⟩,(499963955845201769/500000000000000000),(45150514148241711/62500000000000000),(8537996521305369/200000000000000000),(46738031432105569/1000000000000000000)⟩
theorem valid5016 : certificate5016.Valid := by decide +kernel
theorem sound5016 : certificate5016.Sound := rat_cut_bin_certificate_sound certificate5016 profilesValid5016 numericValid5016 valid5016

def retention5017 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(1/40),(38711383479004545473/1000000000000000000),(21/20),(137434263500560524121856291875140209370911/61938213566407272756800000000000000000000),false,MergedCutProfiles.Batch699.profile27984,(fun _ => MergedCutProfiles.Batch699.profile27984)⟩
theorem profilesValid5017 : retention5017.ProfilesValid := by
  exact MergedCutProfiles.Batch699.valid27984
theorem numericValid5017 : retention5017.NumericValid := by decide +kernel
def certificate5017 : RatCutBinCertificate := ⟨⟨retention5017,(959159135682956873/500000000000000000),(136712609017002193/1000000000000000000),(13779447163723159963/1000000000000000000),(23127892970843726925201/1000000000000000000),(2198908717398815131/1000000000000000000)⟩,(499963955845201769/500000000000000000),(682417562181842287/1000000000000000000),(56821442423071369/1000000000000000000),(113156660469279179/1000000000000000000)⟩
theorem valid5017 : certificate5017.Valid := by decide +kernel
theorem sound5017 : certificate5017.Sound := rat_cut_bin_certificate_sound certificate5017 profilesValid5017 numericValid5017 valid5017

def retention5018 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(637861157811696181/1598071968182840789846),(60690300511494241/100000000000000000),4,(918471057324032737/400000000000000000),true,MergedCutProfiles.Batch699.profile27985,![MergedCutProfiles.Batch699.profile27985,MergedCutProfiles.Batch699.profile27986,MergedCutProfiles.Batch699.profile27987,MergedCutProfiles.Batch699.profile27988,MergedCutProfiles.Batch699.profile27989,MergedCutProfiles.Batch699.profile27990,MergedCutProfiles.Batch699.profile27991,MergedCutProfiles.Batch699.profile27992,MergedCutProfiles.Batch699.profile27993,MergedCutProfiles.Batch699.profile27994,MergedCutProfiles.Batch699.profile27995,MergedCutProfiles.Batch699.profile27996,MergedCutProfiles.Batch699.profile27997,MergedCutProfiles.Batch699.profile27998,MergedCutProfiles.Batch699.profile27999,MergedCutProfiles.Batch700.profile28000]⟩
theorem profilesValid5018 : retention5018.ProfilesValid := by
  change ∀ j : Fin 16, (retention5018.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch699.valid27985
  · exact MergedCutProfiles.Batch699.valid27986
  · exact MergedCutProfiles.Batch699.valid27987
  · exact MergedCutProfiles.Batch699.valid27988
  · exact MergedCutProfiles.Batch699.valid27989
  · exact MergedCutProfiles.Batch699.valid27990
  · exact MergedCutProfiles.Batch699.valid27991
  · exact MergedCutProfiles.Batch699.valid27992
  · exact MergedCutProfiles.Batch699.valid27993
  · exact MergedCutProfiles.Batch699.valid27994
  · exact MergedCutProfiles.Batch699.valid27995
  · exact MergedCutProfiles.Batch699.valid27996
  · exact MergedCutProfiles.Batch699.valid27997
  · exact MergedCutProfiles.Batch699.valid27998
  · exact MergedCutProfiles.Batch699.valid27999
  · exact MergedCutProfiles.Batch700.valid28000
theorem numericValid5018 : retention5018.NumericValid := by decide +kernel
def certificate5018 : RatCutBinCertificate := ⟨⟨retention5018,(966575898523034543/500000000000000000),(142705547327693923/1000000000000000000),(14016825076817498371/1000000000000000000),(5632878126100667510879/250000000000000000),(2217451625542984389/1000000000000000000)⟩,(999925931064165539/1000000000000000000),(174376882083882921/250000000000000000),(51220984142038367/1000000000000000000),(45144812831971/1953125000000000)⟩
theorem valid5018 : certificate5018.Valid := by decide +kernel
theorem sound5018 : certificate5018.Sound := rat_cut_bin_certificate_sound certificate5018 profilesValid5018 numericValid5018 valid5018

def retention5019 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(548259148500000000/799035984091420394923),(637861157811696181/1000000000000000000),4,(1493905984184147661366272949445586163/637861157811696181000000000000000000),true,MergedCutProfiles.Batch700.profile28001,![MergedCutProfiles.Batch700.profile28001,MergedCutProfiles.Batch700.profile28002,MergedCutProfiles.Batch700.profile28003,MergedCutProfiles.Batch700.profile28004,MergedCutProfiles.Batch700.profile28005,MergedCutProfiles.Batch699.profile27994,MergedCutProfiles.Batch699.profile27996,MergedCutProfiles.Batch700.profile28006,MergedCutProfiles.Batch700.profile28000,MergedCutProfiles.Batch700.profile28007,MergedCutProfiles.Batch700.profile28008,MergedCutProfiles.Batch700.profile28009,MergedCutProfiles.Batch700.profile28010,MergedCutProfiles.Batch700.profile28011,MergedCutProfiles.Batch700.profile28012,MergedCutProfiles.Batch700.profile28013]⟩
theorem profilesValid5019 : retention5019.ProfilesValid := by
  change ∀ j : Fin 16, (retention5019.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch700.valid28001
  · exact MergedCutProfiles.Batch700.valid28002
  · exact MergedCutProfiles.Batch700.valid28003
  · exact MergedCutProfiles.Batch700.valid28004
  · exact MergedCutProfiles.Batch700.valid28005
  · exact MergedCutProfiles.Batch699.valid27994
  · exact MergedCutProfiles.Batch699.valid27996
  · exact MergedCutProfiles.Batch700.valid28006
  · exact MergedCutProfiles.Batch700.valid28000
  · exact MergedCutProfiles.Batch700.valid28007
  · exact MergedCutProfiles.Batch700.valid28008
  · exact MergedCutProfiles.Batch700.valid28009
  · exact MergedCutProfiles.Batch700.valid28010
  · exact MergedCutProfiles.Batch700.valid28011
  · exact MergedCutProfiles.Batch700.valid28012
  · exact MergedCutProfiles.Batch700.valid28013
theorem numericValid5019 : retention5019.NumericValid := by decide +kernel
def certificate5019 : RatCutBinCertificate := ⟨⟨retention5019,(966575898523034543/500000000000000000),(142705547327693923/1000000000000000000),(14016825076817498371/1000000000000000000),(5632878126100667510879/250000000000000000),(2263329102296810869/1000000000000000000)⟩,(999925931064165539/1000000000000000000),(661624954587168449/1000000000000000000),(65086611928009429/1000000000000000000),(1883783244324863/62500000000000000)⟩
theorem valid5019 : certificate5019.Valid := by decide +kernel
theorem sound5019 : certificate5019.Sound := rat_cut_bin_certificate_sound certificate5019 profilesValid5019 numericValid5019 valid5019

def retention5020 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(1432925470343382562/799035984091420394923),(1096518297/1000000000),(29/10),(4798310437698506841/2000000000000000000),true,MergedCutProfiles.Batch700.profile28014,![MergedCutProfiles.Batch700.profile28014,MergedCutProfiles.Batch699.profile27993,MergedCutProfiles.Batch700.profile28006,MergedCutProfiles.Batch700.profile28015,MergedCutProfiles.Batch700.profile28010,MergedCutProfiles.Batch700.profile28013,MergedCutProfiles.Batch700.profile28016,MergedCutProfiles.Batch700.profile28017,MergedCutProfiles.Batch700.profile28018,MergedCutProfiles.Batch700.profile28019,MergedCutProfiles.Batch700.profile28020,MergedCutProfiles.Batch700.profile28021,MergedCutProfiles.Batch700.profile28022,MergedCutProfiles.Batch700.profile28023,MergedCutProfiles.Batch700.profile28024,MergedCutProfiles.Batch700.profile28025]⟩
theorem profilesValid5020 : retention5020.ProfilesValid := by
  change ∀ j : Fin 16, (retention5020.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch700.valid28014
  · exact MergedCutProfiles.Batch699.valid27993
  · exact MergedCutProfiles.Batch700.valid28006
  · exact MergedCutProfiles.Batch700.valid28015
  · exact MergedCutProfiles.Batch700.valid28010
  · exact MergedCutProfiles.Batch700.valid28013
  · exact MergedCutProfiles.Batch700.valid28016
  · exact MergedCutProfiles.Batch700.valid28017
  · exact MergedCutProfiles.Batch700.valid28018
  · exact MergedCutProfiles.Batch700.valid28019
  · exact MergedCutProfiles.Batch700.valid28020
  · exact MergedCutProfiles.Batch700.valid28021
  · exact MergedCutProfiles.Batch700.valid28022
  · exact MergedCutProfiles.Batch700.valid28023
  · exact MergedCutProfiles.Batch700.valid28024
  · exact MergedCutProfiles.Batch700.valid28025
theorem numericValid5020 : retention5020.NumericValid := by decide +kernel
def certificate5020 : RatCutBinCertificate := ⟨⟨retention5020,(966575898523034543/500000000000000000),(142705547327693923/1000000000000000000),(14016825076817498371/1000000000000000000),(5632878126100667510879/250000000000000000),(2342078891196952091/1000000000000000000)⟩,(999925931064165539/1000000000000000000),(233535299252951307/500000000000000000),(88680069719482247/500000000000000000),(5710882775053017/50000000000000000)⟩
theorem valid5020 : certificate5020.Valid := by decide +kernel
theorem sound5020 : certificate5020.Sound := rat_cut_bin_certificate_sound certificate5020 profilesValid5020 numericValid5020 valid5020

def retention5021 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(32000000000000000000/799035984091420394923),(716462735171691281/250000000000000000),(31/20),(678507322495761246869/320000000000000000000),true,MergedCutProfiles.Batch700.profile28026,![MergedCutProfiles.Batch700.profile28026,MergedCutProfiles.Batch700.profile28027,MergedCutProfiles.Batch700.profile28028,MergedCutProfiles.Batch700.profile28029,MergedCutProfiles.Batch700.profile28030,MergedCutProfiles.Batch700.profile28031,MergedCutProfiles.Batch700.profile28032,MergedCutProfiles.Batch700.profile28033,MergedCutProfiles.Batch700.profile28034,MergedCutProfiles.Batch700.profile28035,MergedCutProfiles.Batch700.profile28036,MergedCutProfiles.Batch700.profile28037,MergedCutProfiles.Batch700.profile28038,MergedCutProfiles.Batch700.profile28039,MergedCutProfiles.Batch701.profile28040,MergedCutProfiles.Batch701.profile28041]⟩
theorem profilesValid5021 : retention5021.ProfilesValid := by
  change ∀ j : Fin 16, (retention5021.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch700.valid28026
  · exact MergedCutProfiles.Batch700.valid28027
  · exact MergedCutProfiles.Batch700.valid28028
  · exact MergedCutProfiles.Batch700.valid28029
  · exact MergedCutProfiles.Batch700.valid28030
  · exact MergedCutProfiles.Batch700.valid28031
  · exact MergedCutProfiles.Batch700.valid28032
  · exact MergedCutProfiles.Batch700.valid28033
  · exact MergedCutProfiles.Batch700.valid28034
  · exact MergedCutProfiles.Batch700.valid28035
  · exact MergedCutProfiles.Batch700.valid28036
  · exact MergedCutProfiles.Batch700.valid28037
  · exact MergedCutProfiles.Batch700.valid28038
  · exact MergedCutProfiles.Batch700.valid28039
  · exact MergedCutProfiles.Batch701.valid28040
  · exact MergedCutProfiles.Batch701.valid28041
theorem numericValid5021 : retention5021.NumericValid := by decide +kernel
def certificate5021 : RatCutBinCertificate := ⟨⟨retention5021,(966575898523034543/500000000000000000),(142705547327693923/1000000000000000000),(14016825076817498371/1000000000000000000),(5632878126100667510879/250000000000000000),(2089829087008317937/1000000000000000000)⟩,(999925931064165539/1000000000000000000),(357645602601866209/1000000000000000000),(68653491178583493/250000000000000000),(142009211962487163/500000000000000000)⟩
theorem valid5021 : certificate5021.Valid := by decide +kernel
theorem sound5021 : certificate5021.Sound := rat_cut_bin_certificate_sound certificate5021 profilesValid5021 numericValid5021 valid5021

def retention5022 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(1/2),64,1,(63849569515282557958871863662194948511/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch384.profile15388,(fun _ => MergedCutProfiles.Batch384.profile15388)⟩
theorem profilesValid5022 : retention5022.ProfilesValid := by
  exact MergedCutProfiles.Batch384.valid15388
theorem numericValid5022 : retention5022.NumericValid := by decide +kernel
def certificate5022 : RatCutBinCertificate := ⟨⟨retention5022,(966575898523034543/500000000000000000),(142705547327693923/1000000000000000000),(14016825076817498371/1000000000000000000),(5632878126100667510879/250000000000000000),(61123004289710289/62500000000000000)⟩,(999925931064165539/1000000000000000000),(554513764806664703/1000000000000000000),(118509618850320063/1000000000000000000),(114145715845270057/1000000000000000000)⟩
theorem valid5022 : certificate5022.Valid := by decide +kernel
theorem sound5022 : certificate5022.Sound := rat_cut_bin_certificate_sound certificate5022 profilesValid5022 numericValid5022 valid5022

def retention5023 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(32000000000000000000/799035984091420394923),(19888301767217360797/500000000000000000),1,(2630095416713949182602104013635097581/1243018860451085049812500000000000000),false,MergedCutProfiles.Batch701.profile28042,(fun _ => MergedCutProfiles.Batch701.profile28042)⟩
theorem profilesValid5023 : retention5023.ProfilesValid := by
  exact MergedCutProfiles.Batch701.valid28042
theorem numericValid5023 : retention5023.NumericValid := by decide +kernel
def certificate5023 : RatCutBinCertificate := ⟨⟨retention5023,(867804430523034543/500000000000000000),(142705547327693923/1000000000000000000),(14016825076817498371/1000000000000000000),(5632878126100667510879/250000000000000000),(209822314337514409/100000000000000000)⟩,(999933500024431729/1000000000000000000),(17433844684673829/1000000000000000000),(881840719267052597/1000000000000000000),(1757466632483849321/1000000000000000000)⟩
theorem valid5023 : certificate5023.Valid := by decide +kernel
theorem sound5023 : certificate5023.Sound := rat_cut_bin_certificate_sound certificate5023 profilesValid5023 numericValid5023 valid5023

def retention5024 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(1/2),64,1,(63849569515282557958871863662194948511/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch384.profile15388,(fun _ => MergedCutProfiles.Batch384.profile15388)⟩
theorem profilesValid5024 : retention5024.ProfilesValid := by
  exact MergedCutProfiles.Batch384.valid15388
theorem numericValid5024 : retention5024.NumericValid := by decide +kernel
def certificate5024 : RatCutBinCertificate := ⟨⟨retention5024,(867804430523034543/500000000000000000),(142705547327693923/1000000000000000000),(14016825076817498371/1000000000000000000),(5632878126100667510879/250000000000000000),(244994814251583343/250000000000000000)⟩,(999933500024431729/1000000000000000000),(18663709529493623/500000000000000000),(164649570565104077/200000000000000000),(158909064370538601/200000000000000000)⟩
theorem valid5024 : certificate5024.Valid := by decide +kernel
theorem sound5024 : certificate5024.Sound := rat_cut_bin_certificate_sound certificate5024 profilesValid5024 numericValid5024 valid5024

def retention5025 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(734559413108013899/1598071968182840789846),(727286547631696929/1000000000000000000),4,(1964883918312841584439223285897057/808096164035218810000000000000000),false,MergedCutProfiles.Batch701.profile28043,(fun _ => MergedCutProfiles.Batch701.profile28043)⟩
theorem profilesValid5025 : retention5025.ProfilesValid := by
  exact MergedCutProfiles.Batch701.valid28043
theorem numericValid5025 : retention5025.NumericValid := by decide +kernel
def certificate5025 : RatCutBinCertificate := ⟨⟨retention5025,(963364464023034543/500000000000000000),(142705547327693923/1000000000000000000),(14016825076817498371/1000000000000000000),(5632878126100667510879/250000000000000000),(1176516612677873221/500000000000000000)⟩,(12499077214500187/12500000000000000),(408133105806863261/500000000000000000),(18019717705446677/1000000000000000000),(4408261787047253/500000000000000000)⟩
theorem valid5025 : certificate5025.Valid := by decide +kernel
theorem sound5025 : certificate5025.Sound := rat_cut_bin_certificate_sound certificate5025 profilesValid5025 numericValid5025 valid5025

def retention5026 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(869941968050523637/1598071968182840789846),(734559413108013899/1000000000000000000),4,(1787228416415995921396139366382368043/734559413108013899000000000000000000),false,MergedCutProfiles.Batch701.profile28044,(fun _ => MergedCutProfiles.Batch701.profile28044)⟩
theorem profilesValid5026 : retention5026.ProfilesValid := by
  exact MergedCutProfiles.Batch701.valid28044
theorem numericValid5026 : retention5026.NumericValid := by decide +kernel
def certificate5026 : RatCutBinCertificate := ⟨⟨retention5026,(963364464023034543/500000000000000000),(142705547327693923/1000000000000000000),(14016825076817498371/1000000000000000000),(5632878126100667510879/250000000000000000),(94183893642306117/40000000000000000)⟩,(12499077214500187/12500000000000000),(813902069341065773/1000000000000000000),(18503100357193869/1000000000000000000),(9073152925031667/1000000000000000000)⟩
theorem valid5026 : certificate5026.Valid := by decide +kernel
theorem sound5026 : certificate5026.Sound := rat_cut_bin_certificate_sound certificate5026 profilesValid5026 numericValid5026 valid5026

def retention5027 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(3203245673722268563/1598071968182840789846),(869941968050523637/1000000000000000000),(73/20),(3360985388668983244344345629590120842559/1391907148880837819200000000000000000000),false,MergedCutProfiles.Batch701.profile28045,(fun _ => MergedCutProfiles.Batch701.profile28045)⟩
theorem profilesValid5027 : retention5027.ProfilesValid := by
  exact MergedCutProfiles.Batch701.valid28045
theorem numericValid5027 : retention5027.NumericValid := by decide +kernel
def certificate5027 : RatCutBinCertificate := ⟨⟨retention5027,(963364464023034543/500000000000000000),(142705547327693923/1000000000000000000),(14016825076817498371/1000000000000000000),(5632878126100667510879/250000000000000000),(2343063295555355899/1000000000000000000)⟩,(12499077214500187/12500000000000000),(789415993716578271/1000000000000000000),(747413617448259/31250000000000000),(12770264301868091/1000000000000000000)⟩
theorem valid5027 : certificate5027.Valid := by decide +kernel
theorem sound5027 : certificate5027.Sound := rat_cut_bin_certificate_sound certificate5027 profilesValid5027 numericValid5027 valid5027

def certificates : List RatCutBinCertificate := [certificate5016,certificate5017,certificate5018,certificate5019,certificate5020,certificate5021,certificate5022,certificate5023,certificate5024,certificate5025,certificate5026,certificate5027]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound5016,List.forall_mem_cons.mpr ⟨sound5017,List.forall_mem_cons.mpr ⟨sound5018,List.forall_mem_cons.mpr ⟨sound5019,List.forall_mem_cons.mpr ⟨sound5020,List.forall_mem_cons.mpr ⟨sound5021,List.forall_mem_cons.mpr ⟨sound5022,List.forall_mem_cons.mpr ⟨sound5023,List.forall_mem_cons.mpr ⟨sound5024,List.forall_mem_cons.mpr ⟨sound5025,List.forall_mem_cons.mpr ⟨sound5026,List.forall_mem_cons.mpr ⟨sound5027,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch418
