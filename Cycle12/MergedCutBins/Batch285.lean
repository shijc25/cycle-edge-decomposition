import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch226
import Cycle12.MergedCutProfiles.Batch227
import Cycle12.MergedCutProfiles.Batch402
import Cycle12.MergedCutProfiles.Batch404
import Cycle12.MergedCutProfiles.Batch405
import Cycle12.MergedCutProfiles.Batch524
import Cycle12.MergedCutProfiles.Batch525
import Cycle12.MergedCutProfiles.Batch526

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch285

def retention3420 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(535652170632272051/7652404641951072865),(1285543060824298273/1000000000000000000),(9/4),(514886896170763880613/256000000000000000000),true,MergedCutProfiles.Batch524.profile20990,![MergedCutProfiles.Batch524.profile20990,MergedCutProfiles.Batch525.profile21023,MergedCutProfiles.Batch525.profile21020,MergedCutProfiles.Batch525.profile21000,MergedCutProfiles.Batch525.profile21024,MergedCutProfiles.Batch525.profile21025,MergedCutProfiles.Batch402.profile16103,MergedCutProfiles.Batch525.profile21026,MergedCutProfiles.Batch525.profile21027,MergedCutProfiles.Batch525.profile21028,MergedCutProfiles.Batch525.profile21029,MergedCutProfiles.Batch525.profile21030,MergedCutProfiles.Batch525.profile21031,MergedCutProfiles.Batch525.profile21032,MergedCutProfiles.Batch525.profile21033,MergedCutProfiles.Batch226.profile9057]⟩
theorem profilesValid3420 : retention3420.ProfilesValid := by
  change ∀ j : Fin 16, (retention3420.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch524.valid20990
  · exact MergedCutProfiles.Batch525.valid21023
  · exact MergedCutProfiles.Batch525.valid21020
  · exact MergedCutProfiles.Batch525.valid21000
  · exact MergedCutProfiles.Batch525.valid21024
  · exact MergedCutProfiles.Batch525.valid21025
  · exact MergedCutProfiles.Batch402.valid16103
  · exact MergedCutProfiles.Batch525.valid21026
  · exact MergedCutProfiles.Batch525.valid21027
  · exact MergedCutProfiles.Batch525.valid21028
  · exact MergedCutProfiles.Batch525.valid21029
  · exact MergedCutProfiles.Batch525.valid21030
  · exact MergedCutProfiles.Batch525.valid21031
  · exact MergedCutProfiles.Batch525.valid21032
  · exact MergedCutProfiles.Batch525.valid21033
  · exact MergedCutProfiles.Batch226.valid9057
theorem numericValid3420 : retention3420.NumericValid := by decide +kernel
def certificate3420 : RatCutBinCertificate := ⟨⟨retention3420,(1105383553373305141/500000000000000000),(93024059904071007/500000000000000000),(15867731911002727811/1000000000000000000),(19487824611421009993/20000000000000000),(976475306740939871/500000000000000000)⟩,(124768032825785277/125000000000000000),(313992851139963407/1000000000000000000),(322266742643690447/1000000000000000000),(214687178288936717/1000000000000000000)⟩
theorem valid3420 : certificate3420.Valid := by decide +kernel
theorem sound3420 : certificate3420.Sound := rat_cut_bin_certificate_sound certificate3420 profilesValid3420 numericValid3420 valid3420

def retention3421 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(23492420885566310613/61219237135608582920),(535652170632272051/125000000000000000),(23/20),(522181123558191547966995235909149246559/428521736505817640800000000000000000000),false,MergedCutProfiles.Batch525.profile21034,(fun _ => MergedCutProfiles.Batch525.profile21034)⟩
theorem profilesValid3421 : retention3421.ProfilesValid := by
  exact MergedCutProfiles.Batch525.valid21034
theorem numericValid3421 : retention3421.NumericValid := by decide +kernel
def certificate3421 : RatCutBinCertificate := ⟨⟨retention3421,(1105383553373305141/500000000000000000),(93024059904071007/500000000000000000),(15867731911002727811/1000000000000000000),(19487824611421009993/20000000000000000),(594376746023915691/500000000000000000)⟩,(124768032825785277/125000000000000000),(75925652441598987/200000000000000000),(252675469546553417/1000000000000000000),(53864451918022847/250000000000000000)⟩
theorem valid3421 : certificate3421.Valid := by decide +kernel
theorem sound3421 : certificate3421.Sound := rat_cut_bin_certificate_sound certificate3421 profilesValid3421 numericValid3421 valid3421

def retention3422 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(15063716092030664871/30609618567804291460),(23492420885566310613/1000000000000000000),1,(31523308089860888637158352132931725849/31323227847421747484000000000000000000),false,MergedCutProfiles.Batch525.profile21035,(fun _ => MergedCutProfiles.Batch525.profile21035)⟩
theorem profilesValid3422 : retention3422.ProfilesValid := by
  exact MergedCutProfiles.Batch525.valid21035
theorem numericValid3422 : retention3422.NumericValid := by decide +kernel
def certificate3422 : RatCutBinCertificate := ⟨⟨retention3422,(1105383553373305141/500000000000000000),(93024059904071007/500000000000000000),(15867731911002727811/1000000000000000000),(19487824611421009993/20000000000000000),(980466289207065831/1000000000000000000)⟩,(124768032825785277/125000000000000000),(402407307681751343/1000000000000000000),(57820973370209747/250000000000000000),(217266266534451123/1000000000000000000)⟩
theorem valid3422 : certificate3422.Valid := by decide +kernel
theorem sound3422 : certificate3422.Sound := rat_cut_bin_certificate_sound certificate3422 profilesValid3422 numericValid3422 valid3422

def retention3423 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(760717662647548576/1530480928390214573),(15063716092030664871/500000000000000000),1,(120401978774893360468088584424460716087/120509728736245318968000000000000000000),false,MergedCutProfiles.Batch525.profile21036,(fun _ => MergedCutProfiles.Batch525.profile21036)⟩
theorem profilesValid3423 : retention3423.ProfilesValid := by
  exact MergedCutProfiles.Batch525.valid21036
theorem numericValid3423 : retention3423.NumericValid := by decide +kernel
def certificate3423 : RatCutBinCertificate := ⟨⟨retention3423,(1105383553373305141/500000000000000000),(93024059904071007/500000000000000000),(15867731911002727811/1000000000000000000),(19487824611421009993/20000000000000000),(38927384699592231/40000000000000000)⟩,(124768032825785277/125000000000000000),(402553643851869723/1000000000000000000),(5778767930153483/25000000000000000),(217500313498339549/1000000000000000000)⟩
theorem valid3423 : certificate3423.Valid := by decide +kernel
theorem sound3423 : certificate3423.Sound := rat_cut_bin_certificate_sound certificate3423 profilesValid3423 numericValid3423 valid3423

def retention3424 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(1/2),(23772426957735893/781250000000000),1,(4836288805533752902379781094970482431/4868593040944310886400000000000000000),false,MergedCutProfiles.Batch227.profile9095,(fun _ => MergedCutProfiles.Batch227.profile9095)⟩
theorem profilesValid3424 : retention3424.ProfilesValid := by
  exact MergedCutProfiles.Batch227.valid9095
theorem numericValid3424 : retention3424.NumericValid := by decide +kernel
def certificate3424 : RatCutBinCertificate := ⟨⟨retention3424,(1105383553373305141/500000000000000000),(93024059904071007/500000000000000000),(15867731911002727811/1000000000000000000),(19487824611421009993/20000000000000000),(967443507313217893/1000000000000000000)⟩,(124768032825785277/125000000000000000),(50605188028750441/125000000000000000),(45815100857343533/200000000000000000),(2143817504517861/10000000000000000)⟩
theorem valid3424 : certificate3424.Valid := by decide +kernel
theorem sound3424 : certificate3424.Sound := rat_cut_bin_certificate_sound certificate3424 profilesValid3424 numericValid3424 valid3424

def retention3425 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(28238365078293161229/61219237135608582920),(1853001115189166351/200000000000000000),1,(151743721134580161329737241990967699/144765712124153621171875000000000000),false,MergedCutProfiles.Batch525.profile21037,(fun _ => MergedCutProfiles.Batch525.profile21037)⟩
theorem profilesValid3425 : retention3425.ProfilesValid := by
  exact MergedCutProfiles.Batch525.valid21037
theorem numericValid3425 : retention3425.NumericValid := by decide +kernel
def certificate3425 : RatCutBinCertificate := ⟨⟨retention3425,(1140490438373305141/500000000000000000),(93024059904071007/500000000000000000),(15867731911002727811/1000000000000000000),(19487824611421009993/20000000000000000),(1021457181066563821/1000000000000000000)⟩,(249521324842224003/250000000000000000),(118654343618909591/1000000000000000000),(626289526534611891/1000000000000000000),(287515415060753997/500000000000000000)⟩
theorem valid3425 : certificate3425.Valid := by decide +kernel
theorem sound3425 : certificate3425.Sound := rat_cut_bin_certificate_sound certificate3425 profilesValid3425 numericValid3425 valid3425

def retention3426 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(6055069897228426685/12243847427121716584),(28238365078293161229/1000000000000000000),1,(1180689192788251242730473430107583203/1176598544928881717875000000000000000),false,MergedCutProfiles.Batch525.profile21038,(fun _ => MergedCutProfiles.Batch525.profile21038)⟩
theorem profilesValid3426 : retention3426.ProfilesValid := by
  exact MergedCutProfiles.Batch525.valid21038
theorem numericValid3426 : retention3426.NumericValid := by decide +kernel
def certificate3426 : RatCutBinCertificate := ⟨⟨retention3426,(1140490438373305141/500000000000000000),(93024059904071007/500000000000000000),(15867731911002727811/1000000000000000000),(19487824611421009993/20000000000000000),(488366069988694211/500000000000000000)⟩,(249521324842224003/250000000000000000),(24817516777338899/200000000000000000),(615094356300968363/1000000000000000000),(579560754843341843/1000000000000000000)⟩
theorem valid3426 : certificate3426.Valid := by decide +kernel
theorem sound3426 : certificate3426.Sound := rat_cut_bin_certificate_sound certificate3426 profilesValid3426 numericValid3426 valid3426

def retention3427 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(764452574525088869/1530480928390214573),(1211013979445685337/40000000000000000),1,(120415634293091513355557508834845908651/121101397944568533700000000000000000000),false,MergedCutProfiles.Batch525.profile21039,(fun _ => MergedCutProfiles.Batch525.profile21039)⟩
theorem profilesValid3427 : retention3427.ProfilesValid := by
  exact MergedCutProfiles.Batch525.valid21039
theorem numericValid3427 : retention3427.NumericValid := by decide +kernel
def certificate3427 : RatCutBinCertificate := ⟨⟨retention3427,(1140490438373305141/500000000000000000),(93024059904071007/500000000000000000),(15867731911002727811/1000000000000000000),(19487824611421009993/20000000000000000),(241898189190755339/250000000000000000)⟩,(249521324842224003/250000000000000000),(62629825671565397/500000000000000000),(306353220989064811/500000000000000000),(573367412774688221/1000000000000000000)⟩
theorem valid3427 : certificate3427.Valid := by decide +kernel
theorem sound3427 : certificate3427.Sound := rat_cut_bin_certificate_sound certificate3427 profilesValid3427 numericValid3427 valid3427

def retention3428 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(1/2),(764452574525088869/25000000000000000),1,(4860230657361178592967134633069225887/4892496476960568761600000000000000000),false,MergedCutProfiles.Batch227.profile9095,(fun _ => MergedCutProfiles.Batch227.profile9095)⟩
theorem profilesValid3428 : retention3428.ProfilesValid := by
  exact MergedCutProfiles.Batch227.valid9095
theorem numericValid3428 : retention3428.NumericValid := by decide +kernel
def certificate3428 : RatCutBinCertificate := ⟨⟨retention3428,(1140490438373305141/500000000000000000),(93024059904071007/500000000000000000),(15867731911002727811/1000000000000000000),(19487824611421009993/20000000000000000),(966660521056611683/1000000000000000000)⟩,(249521324842224003/250000000000000000),(125380450234790149/1000000000000000000),(306230436377200157/500000000000000000),(572778184105341389/1000000000000000000)⟩
theorem valid3428 : certificate3428.Valid := by decide +kernel
theorem sound3428 : certificate3428.Sound := rat_cut_bin_certificate_sound certificate3428 profilesValid3428 numericValid3428 valid3428

def retention3429 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(447651393257145649/30017456134998216493),(221609600622349331/250000000000000000),(59/20),(142539519228891604019/64000000000000000000),true,MergedCutProfiles.Batch526.profile21040,![MergedCutProfiles.Batch526.profile21040,MergedCutProfiles.Batch526.profile21041,MergedCutProfiles.Batch526.profile21042,MergedCutProfiles.Batch526.profile21043,MergedCutProfiles.Batch526.profile21044,MergedCutProfiles.Batch526.profile21045,MergedCutProfiles.Batch526.profile21046,MergedCutProfiles.Batch526.profile21047,MergedCutProfiles.Batch526.profile21048,MergedCutProfiles.Batch526.profile21049,MergedCutProfiles.Batch526.profile21050,MergedCutProfiles.Batch526.profile21051,MergedCutProfiles.Batch404.profile16186,MergedCutProfiles.Batch405.profile16218,MergedCutProfiles.Batch526.profile21052,MergedCutProfiles.Batch526.profile21053]⟩
theorem profilesValid3429 : retention3429.ProfilesValid := by
  change ∀ j : Fin 16, (retention3429.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch526.valid21040
  · exact MergedCutProfiles.Batch526.valid21041
  · exact MergedCutProfiles.Batch526.valid21042
  · exact MergedCutProfiles.Batch526.valid21043
  · exact MergedCutProfiles.Batch526.valid21044
  · exact MergedCutProfiles.Batch526.valid21045
  · exact MergedCutProfiles.Batch526.valid21046
  · exact MergedCutProfiles.Batch526.valid21047
  · exact MergedCutProfiles.Batch526.valid21048
  · exact MergedCutProfiles.Batch526.valid21049
  · exact MergedCutProfiles.Batch526.valid21050
  · exact MergedCutProfiles.Batch526.valid21051
  · exact MergedCutProfiles.Batch404.valid16186
  · exact MergedCutProfiles.Batch405.valid16218
  · exact MergedCutProfiles.Batch526.valid21052
  · exact MergedCutProfiles.Batch526.valid21053
theorem numericValid3429 : retention3429.NumericValid := by decide +kernel
def certificate3429 : RatCutBinCertificate := ⟨⟨retention3429,(2217465728453509257/1000000000000000000),(9485872639178457/50000000000000000),(3202793912973537903/200000000000000000),(964357342583473521597/1000000000000000000),(1074838371163504111/500000000000000000)⟩,(249531892927526829/250000000000000000),(41182311117505479/125000000000000000),(12189272150958569/40000000000000000),(86637946260295483/500000000000000000)⟩
theorem valid3429 : certificate3429.Valid := by decide +kernel
theorem sound3429 : certificate3429.Sound := rat_cut_bin_certificate_sound certificate3429 profilesValid3429 numericValid3429 valid3429

def retention3430 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(530155528744706218/30017456134998216493),(447651393257145649/500000000000000000),(59/20),(44389852406725504873/20000000000000000000),true,MergedCutProfiles.Batch526.profile21054,![MergedCutProfiles.Batch526.profile21054,MergedCutProfiles.Batch526.profile21055,MergedCutProfiles.Batch526.profile21056,MergedCutProfiles.Batch526.profile21057,MergedCutProfiles.Batch526.profile21058,MergedCutProfiles.Batch526.profile21059,MergedCutProfiles.Batch405.profile16216,MergedCutProfiles.Batch526.profile21060,MergedCutProfiles.Batch405.profile16231,MergedCutProfiles.Batch526.profile21061,MergedCutProfiles.Batch404.profile16186,MergedCutProfiles.Batch526.profile21062,MergedCutProfiles.Batch526.profile21063,MergedCutProfiles.Batch526.profile21064,MergedCutProfiles.Batch526.profile21065,MergedCutProfiles.Batch405.profile16204]⟩
theorem profilesValid3430 : retention3430.ProfilesValid := by
  change ∀ j : Fin 16, (retention3430.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch526.valid21054
  · exact MergedCutProfiles.Batch526.valid21055
  · exact MergedCutProfiles.Batch526.valid21056
  · exact MergedCutProfiles.Batch526.valid21057
  · exact MergedCutProfiles.Batch526.valid21058
  · exact MergedCutProfiles.Batch526.valid21059
  · exact MergedCutProfiles.Batch405.valid16216
  · exact MergedCutProfiles.Batch526.valid21060
  · exact MergedCutProfiles.Batch405.valid16231
  · exact MergedCutProfiles.Batch526.valid21061
  · exact MergedCutProfiles.Batch404.valid16186
  · exact MergedCutProfiles.Batch526.valid21062
  · exact MergedCutProfiles.Batch526.valid21063
  · exact MergedCutProfiles.Batch526.valid21064
  · exact MergedCutProfiles.Batch526.valid21065
  · exact MergedCutProfiles.Batch405.valid16204
theorem numericValid3430 : retention3430.NumericValid := by decide +kernel
def certificate3430 : RatCutBinCertificate := ⟨⟨retention3430,(2217465728453509257/1000000000000000000),(9485872639178457/50000000000000000),(3202793912973537903/200000000000000000),(964357342583473521597/1000000000000000000),(1070994716218467173/500000000000000000)⟩,(249531892927526829/250000000000000000),(4113942514553577/12500000000000000),(305112816112374111/1000000000000000000),(43345117981944761/250000000000000000)⟩
theorem valid3430 : certificate3430.Valid := by decide +kernel
theorem sound3430 : certificate3430.Sound := rat_cut_bin_certificate_sound certificate3430 profilesValid3430 numericValid3430 valid3430

def retention3431 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(553031032500000000/30017456134998216493),(265077764372353109/250000000000000000),(51/20),(5502373075721959983/2500000000000000000),true,MergedCutProfiles.Batch526.profile21066,![MergedCutProfiles.Batch526.profile21066,MergedCutProfiles.Batch526.profile21067,MergedCutProfiles.Batch526.profile21068,MergedCutProfiles.Batch526.profile21069,MergedCutProfiles.Batch526.profile21070,MergedCutProfiles.Batch526.profile21071,MergedCutProfiles.Batch526.profile21072,MergedCutProfiles.Batch526.profile21073,MergedCutProfiles.Batch405.profile16217,MergedCutProfiles.Batch526.profile21074,MergedCutProfiles.Batch405.profile16202,MergedCutProfiles.Batch526.profile21075,MergedCutProfiles.Batch526.profile21053,MergedCutProfiles.Batch526.profile21076,MergedCutProfiles.Batch526.profile21077,MergedCutProfiles.Batch526.profile21078]⟩
theorem profilesValid3431 : retention3431.ProfilesValid := by
  change ∀ j : Fin 16, (retention3431.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch526.valid21066
  · exact MergedCutProfiles.Batch526.valid21067
  · exact MergedCutProfiles.Batch526.valid21068
  · exact MergedCutProfiles.Batch526.valid21069
  · exact MergedCutProfiles.Batch526.valid21070
  · exact MergedCutProfiles.Batch526.valid21071
  · exact MergedCutProfiles.Batch526.valid21072
  · exact MergedCutProfiles.Batch526.valid21073
  · exact MergedCutProfiles.Batch405.valid16217
  · exact MergedCutProfiles.Batch526.valid21074
  · exact MergedCutProfiles.Batch405.valid16202
  · exact MergedCutProfiles.Batch526.valid21075
  · exact MergedCutProfiles.Batch526.valid21053
  · exact MergedCutProfiles.Batch526.valid21076
  · exact MergedCutProfiles.Batch526.valid21077
  · exact MergedCutProfiles.Batch526.valid21078
theorem numericValid3431 : retention3431.NumericValid := by decide +kernel
def certificate3431 : RatCutBinCertificate := ⟨⟨retention3431,(2217465728453509257/1000000000000000000),(9485872639178457/50000000000000000),(3202793912973537903/200000000000000000),(964357342583473521597/1000000000000000000),(106697753242125331/50000000000000000)⟩,(249531892927526829/250000000000000000),(306525402208960403/1000000000000000000),(41375362523793323/125000000000000000),(42211745002811481/200000000000000000)⟩
theorem valid3431 : certificate3431.Valid := by decide +kernel
theorem sound3431 : certificate3431.Sound := rat_cut_bin_certificate_sound certificate3431 profilesValid3431 numericValid3431 valid3431

def certificates : List RatCutBinCertificate := [certificate3420,certificate3421,certificate3422,certificate3423,certificate3424,certificate3425,certificate3426,certificate3427,certificate3428,certificate3429,certificate3430,certificate3431]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3420,List.forall_mem_cons.mpr ⟨sound3421,List.forall_mem_cons.mpr ⟨sound3422,List.forall_mem_cons.mpr ⟨sound3423,List.forall_mem_cons.mpr ⟨sound3424,List.forall_mem_cons.mpr ⟨sound3425,List.forall_mem_cons.mpr ⟨sound3426,List.forall_mem_cons.mpr ⟨sound3427,List.forall_mem_cons.mpr ⟨sound3428,List.forall_mem_cons.mpr ⟨sound3429,List.forall_mem_cons.mpr ⟨sound3430,List.forall_mem_cons.mpr ⟨sound3431,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch285
