import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs040

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch040

def certificate800 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs040.envelope800,(230821/100000),(169457813/1000000000),(3897625990151809333379/1000000000000000000),(129143197/62500000),(101/10),(216724413/500000000),0,1,(613390657350913/500000000000000000)⟩
theorem valid800 : certificate800.Valid := by
  refine ⟨MajorityCertificates.Inputs040.inputs_valid800,?_⟩
  decide +kernel
theorem sound800 : certificate800.Sound :=
  rat_witness_certificate_sound certificate800 valid800 MajorityCertificates.Inputs040.envelope_sound800

def certificate801 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs040.envelope801,(230821/100000),(169457813/1000000000),(3897625990151809333379/1000000000000000000),(956094403/500000000),(101/10),(706528221/500000000),0,(7033595259825429/6250000000000000),(255251207916713/100000000000000000)⟩
theorem valid801 : certificate801.Valid := by
  refine ⟨MajorityCertificates.Inputs040.inputs_valid801,?_⟩
  decide +kernel
theorem sound801 : certificate801.Sound :=
  rat_witness_certificate_sound certificate801 valid801 MajorityCertificates.Inputs040.envelope_sound801

def certificate802 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs040.envelope802,(7212/3125),(26907/160000),(1928745821128284453269/500000000000000000),(2073325733/1000000000),(203/20),(429361833/1000000000),0,1,(247922355618977/200000000000000000)⟩
theorem valid802 : certificate802.Valid := by
  refine ⟨MajorityCertificates.Inputs040.inputs_valid802,?_⟩
  decide +kernel
theorem sound802 : certificate802.Sound :=
  rat_witness_certificate_sound certificate802 valid802 MajorityCertificates.Inputs040.envelope_sound802

def certificate803 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs040.envelope803,(7212/3125),(26907/160000),(1928745821128284453269/500000000000000000),(957497011/500000000),(203/20),(282521809/200000000),0,(140672400938544819/125000000000000000),(258773048786209/100000000000000000)⟩
theorem valid803 : certificate803.Valid := by
  refine ⟨MajorityCertificates.Inputs040.inputs_valid803,?_⟩
  decide +kernel
theorem sound803 : certificate803.Sound :=
  rat_witness_certificate_sound certificate803 valid803 MajorityCertificates.Inputs040.envelope_sound803

def certificate804 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs040.envelope804,(57687/25000),(20859961/125000000),(3818410446601521484933/1000000000000000000),(2079911283/1000000000),(41/4),(212661159/500000000),0,1,(1250362852372561/1000000000000000000)⟩
theorem valid804 : certificate804.Valid := by
  refine ⟨MajorityCertificates.Inputs040.inputs_valid804,?_⟩
  decide +kernel
theorem sound804 : certificate804.Sound :=
  rat_witness_certificate_sound certificate804 valid804 MajorityCertificates.Inputs040.envelope_sound804

def certificate805 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs040.envelope805,(57687/25000),(20859961/125000000),(3818410446601521484933/1000000000000000000),(479794337/250000000),(41/4),(282214027/200000000),0,(22507662989701129/20000000000000000),(654051383473447/250000000000000000)⟩
theorem valid805 : certificate805.Valid := by
  refine ⟨MajorityCertificates.Inputs040.inputs_valid805,?_⟩
  decide +kernel
theorem sound805 : certificate805.Sound :=
  rat_witness_certificate_sound certificate805 valid805 MajorityCertificates.Inputs040.envelope_sound805

def certificate806 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs040.envelope806,(230713/100000),(52989/320000),(3780351506350753384643/1000000000000000000),(130449017/62500000),(103/10),(421254939/1000000000),0,1,(316454364911641/250000000000000000)⟩
theorem valid806 : certificate806.Valid := by
  refine ⟨MajorityCertificates.Inputs040.inputs_valid806,?_⟩
  decide +kernel
theorem sound806 : certificate806.Sound :=
  rat_witness_certificate_sound certificate806 valid806 MajorityCertificates.Inputs040.envelope_sound806

def certificate807 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs040.envelope807,(230713/100000),(52989/320000),(3780351506350753384643/1000000000000000000),(960985547/500000000),(103/10),(1410662547/1000000000),0,(1125387066626238257/1000000000000000000),(1325808174422199/500000000000000000)⟩
theorem valid807 : certificate807.Valid := by
  refine ⟨MajorityCertificates.Inputs040.inputs_valid807,?_⟩
  decide +kernel
theorem sound807 : certificate807.Sound :=
  rat_witness_certificate_sound certificate807 valid807 MajorityCertificates.Inputs040.envelope_sound807

def certificate808 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs040.envelope808,(46117/20000),(163657031/1000000000),(1842051788571481264403/500000000000000000),(2094489317/1000000000),(207/20),(207742577/500000000),0,1,(1301905121148313/1000000000000000000)⟩
theorem valid808 : certificate808.Valid := by
  refine ⟨MajorityCertificates.Inputs040.inputs_valid808,?_⟩
  decide +kernel
theorem sound808 : certificate808.Sound :=
  rat_witness_certificate_sound certificate808 valid808 MajorityCertificates.Inputs040.envelope_sound808

def certificate809 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs040.envelope809,(46117/20000),(163657031/1000000000),(1842051788571481264403/500000000000000000),(240620849/125000000),(207/20),(352944599/250000000),0,(28134935053361211/25000000000000000),(2733641689880967/1000000000000000000)⟩
theorem valid809 : certificate809.Valid := by
  refine ⟨MajorityCertificates.Inputs040.inputs_valid809,?_⟩
  decide +kernel
theorem sound809 : certificate809.Sound :=
  rat_witness_certificate_sound certificate809 valid809 MajorityCertificates.Inputs040.envelope_sound809

def certificate810 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs040.envelope810,(230613/100000),(80539453/500000000),(91800435768608139787/25000000000000000),(2109130813/1000000000),(21/2),(203680859/500000000),0,1,(1303026524955953/1000000000000000000)⟩
theorem valid810 : certificate810.Valid := by
  refine ⟨MajorityCertificates.Inputs040.inputs_valid810,?_⟩
  decide +kernel
theorem sound810 : certificate810.Sound :=
  rat_witness_certificate_sound certificate810 valid810 MajorityCertificates.Inputs040.envelope_sound810

def certificate811 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs040.envelope811,(230613/100000),(80539453/500000000),(91800435768608139787/25000000000000000),(1932494759/1000000000),(21/2),(704270797/500000000),0,(1125398662088767727/1000000000000000000),(344021006510519/125000000000000000)⟩
theorem valid811 : certificate811.Valid := by
  refine ⟨MajorityCertificates.Inputs040.inputs_valid811,?_⟩
  decide +kernel
theorem sound811 : certificate811.Sound :=
  rat_witness_certificate_sound certificate811 valid811 MajorityCertificates.Inputs040.envelope_sound811

def certificate812 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs040.envelope812,(230581/100000),(39947461/250000000),(3637762398317120126113/1000000000000000000),(2115990773/1000000000),(211/20),(403395341/1000000000),0,1,(658062068302939/500000000000000000)⟩
theorem valid812 : certificate812.Valid := by
  refine ⟨MajorityCertificates.Inputs040.inputs_valid812,?_⟩
  decide +kernel
theorem sound812 : certificate812.Sound :=
  rat_witness_certificate_sound certificate812 valid812 MajorityCertificates.Inputs040.envelope_sound812

def certificate813 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs040.envelope813,(230581/100000),(39947461/250000000),(3637762398317120126113/1000000000000000000),(193528497/100000000),(211/20),(704104829/500000000),0,(1125402473002323699/1000000000000000000),(2788204056555609/1000000000000000000)⟩
theorem valid813 : certificate813.Valid := by
  refine ⟨MajorityCertificates.Inputs040.inputs_valid813,?_⟩
  decide +kernel
theorem sound813 : certificate813.Sound :=
  rat_witness_certificate_sound certificate813 valid813 MajorityCertificates.Inputs040.envelope_sound813

def certificate814 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs040.envelope814,(4611/2000),(25257/160000),(3604392558273399597219/1000000000000000000),(2124450483/1000000000),(53/5),(198786471/500000000),0,1,(664999745471141/500000000000000000)⟩
theorem valid814 : certificate814.Valid := by
  refine ⟨MajorityCertificates.Inputs040.inputs_valid814,?_⟩
  decide +kernel
theorem sound814 : certificate814.Sound :=
  rat_witness_certificate_sound certificate814 valid814 MajorityCertificates.Inputs040.envelope_sound814

def certificate815 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs040.envelope815,(4611/2000),(25257/160000),(3604392558273399597219/1000000000000000000),(1938908197/1000000000),(53/5),(1407957277/1000000000),0,(45016250192757033/40000000000000000),(706188113260397/250000000000000000)⟩
theorem valid815 : certificate815.Valid := by
  refine ⟨MajorityCertificates.Inputs040.inputs_valid815,?_⟩
  decide +kernel
theorem sound815 : certificate815.Sound :=
  rat_witness_certificate_sound certificate815 valid815 MajorityCertificates.Inputs040.envelope_sound815

def certificate816 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs040.envelope816,(5763/2500),(39141797/250000000),(3571883622372616586479/1000000000000000000),(532815531/250000000),(107/10),(98412031/250000000),0,1,(167892119511463/125000000000000000)⟩
theorem valid816 : certificate816.Valid := by
  refine ⟨MajorityCertificates.Inputs040.inputs_valid816,?_⟩
  decide +kernel
theorem sound816 : certificate816.Sound :=
  rat_witness_certificate_sound certificate816 valid816 MajorityCertificates.Inputs040.envelope_sound816

def certificate817 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs040.envelope817,(5763/2500),(39141797/250000000),(3571883622372616586479/1000000000000000000),(971525281/500000000),(107/10),(1406611637/1000000000),0,(70338125418607377/62500000000000000),(2853650365823821/1000000000000000000)⟩
theorem valid817 : certificate817.Valid := by
  refine ⟨MajorityCertificates.Inputs040.inputs_valid817,?_⟩
  decide +kernel
theorem sound817 : certificate817.Sound :=
  rat_witness_certificate_sound certificate817 valid817 MajorityCertificates.Inputs040.envelope_sound817

def certificate818 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs040.envelope818,(230491/100000),(77316797/500000000),(3540212236440684184697/1000000000000000000),(2140106941/1000000000),(43/4),(24241151/62500000),0,1,(680160128145933/500000000000000000)⟩
theorem valid818 : certificate818.Valid := by
  refine ⟨MajorityCertificates.Inputs040.inputs_valid818,?_⟩
  decide +kernel
theorem sound818 : certificate818.Sound :=
  rat_witness_certificate_sound certificate818 valid818 MajorityCertificates.Inputs040.envelope_sound818

def certificate819 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs040.envelope819,(230491/100000),(77316797/500000000),(3540212236440684184697/1000000000000000000),(1946706407/1000000000),(43/4),(1406396221/1000000000),0,(562706863902239857/500000000000000000),(2890443226439313/1000000000000000000)⟩
theorem valid819 : certificate819.Valid := by
  refine ⟨MajorityCertificates.Inputs040.inputs_valid819,?_⟩
  decide +kernel
theorem sound819 : certificate819.Sound :=
  rat_witness_certificate_sound certificate819 valid819 MajorityCertificates.Inputs040.envelope_sound819

def certificates : List RatWitnessCertificate := [certificate800,certificate801,certificate802,certificate803,certificate804,certificate805,certificate806,certificate807,certificate808,certificate809,certificate810,certificate811,certificate812,certificate813,certificate814,certificate815,certificate816,certificate817,certificate818,certificate819]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound800,List.forall_mem_cons.mpr ⟨sound801,List.forall_mem_cons.mpr ⟨sound802,List.forall_mem_cons.mpr ⟨sound803,List.forall_mem_cons.mpr ⟨sound804,List.forall_mem_cons.mpr ⟨sound805,List.forall_mem_cons.mpr ⟨sound806,List.forall_mem_cons.mpr ⟨sound807,List.forall_mem_cons.mpr ⟨sound808,List.forall_mem_cons.mpr ⟨sound809,List.forall_mem_cons.mpr ⟨sound810,List.forall_mem_cons.mpr ⟨sound811,List.forall_mem_cons.mpr ⟨sound812,List.forall_mem_cons.mpr ⟨sound813,List.forall_mem_cons.mpr ⟨sound814,List.forall_mem_cons.mpr ⟨sound815,List.forall_mem_cons.mpr ⟨sound816,List.forall_mem_cons.mpr ⟨sound817,List.forall_mem_cons.mpr ⟨sound818,List.forall_mem_cons.mpr ⟨sound819,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch040
