import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch040
import Cycle12.MergedCutProfiles.Batch041
import Cycle12.MergedCutProfiles.Batch042

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch021

def retention252 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(867431889708215588/63476256200139309633),(718007998690644917/1000000000000000000),(73/20),(2851260801763459426797/1280000000000000000000),true,MergedCutProfiles.Batch041.profile1640,![MergedCutProfiles.Batch041.profile1640,MergedCutProfiles.Batch041.profile1641,MergedCutProfiles.Batch041.profile1642,MergedCutProfiles.Batch041.profile1643,MergedCutProfiles.Batch040.profile1629,MergedCutProfiles.Batch041.profile1644,MergedCutProfiles.Batch041.profile1645,MergedCutProfiles.Batch041.profile1646,MergedCutProfiles.Batch041.profile1647,MergedCutProfiles.Batch041.profile1648,MergedCutProfiles.Batch041.profile1649,MergedCutProfiles.Batch041.profile1650,MergedCutProfiles.Batch041.profile1651,MergedCutProfiles.Batch041.profile1652,MergedCutProfiles.Batch041.profile1653,MergedCutProfiles.Batch041.profile1654]⟩
theorem profilesValid252 : retention252.ProfilesValid := by
  change ∀ j : Fin 16, (retention252.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch041.valid1640
  · exact MergedCutProfiles.Batch041.valid1641
  · exact MergedCutProfiles.Batch041.valid1642
  · exact MergedCutProfiles.Batch041.valid1643
  · exact MergedCutProfiles.Batch040.valid1629
  · exact MergedCutProfiles.Batch041.valid1644
  · exact MergedCutProfiles.Batch041.valid1645
  · exact MergedCutProfiles.Batch041.valid1646
  · exact MergedCutProfiles.Batch041.valid1647
  · exact MergedCutProfiles.Batch041.valid1648
  · exact MergedCutProfiles.Batch041.valid1649
  · exact MergedCutProfiles.Batch041.valid1650
  · exact MergedCutProfiles.Batch041.valid1651
  · exact MergedCutProfiles.Batch041.valid1652
  · exact MergedCutProfiles.Batch041.valid1653
  · exact MergedCutProfiles.Batch041.valid1654
theorem numericValid252 : retention252.NumericValid := by decide +kernel
def certificate252 : RatCutBinCertificate := ⟨⟨retention252,(991191016586418053/500000000000000000),(36585906920747501/1000000000000000000),(4762395989857947939/500000000000000000),(121527652363862859971/200000000000000000),(2199753663456719543/1000000000000000000)⟩,(996848037382240881/1000000000000000000),(112050222899036519/250000000000000000),(48027861006012997/250000000000000000),(1172332116485891/12500000000000000)⟩
theorem valid252 : certificate252.Valid := by decide +kernel
theorem sound252 : certificate252.Sound := rat_cut_bin_certificate_sound certificate252 profilesValid252 numericValid252 valid252

def retention253 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(1053615059000000000/63476256200139309633),(216857972427053897/250000000000000000),(31/10),(704700609522886697993/320000000000000000000),true,MergedCutProfiles.Batch041.profile1655,![MergedCutProfiles.Batch041.profile1655,MergedCutProfiles.Batch041.profile1656,MergedCutProfiles.Batch041.profile1657,MergedCutProfiles.Batch041.profile1658,MergedCutProfiles.Batch041.profile1659,MergedCutProfiles.Batch041.profile1660,MergedCutProfiles.Batch041.profile1661,MergedCutProfiles.Batch041.profile1662,MergedCutProfiles.Batch041.profile1663,MergedCutProfiles.Batch041.profile1664,MergedCutProfiles.Batch041.profile1665,MergedCutProfiles.Batch041.profile1666,MergedCutProfiles.Batch041.profile1667,MergedCutProfiles.Batch041.profile1668,MergedCutProfiles.Batch041.profile1669,MergedCutProfiles.Batch041.profile1670]⟩
theorem profilesValid253 : retention253.ProfilesValid := by
  change ∀ j : Fin 16, (retention253.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch041.valid1655
  · exact MergedCutProfiles.Batch041.valid1656
  · exact MergedCutProfiles.Batch041.valid1657
  · exact MergedCutProfiles.Batch041.valid1658
  · exact MergedCutProfiles.Batch041.valid1659
  · exact MergedCutProfiles.Batch041.valid1660
  · exact MergedCutProfiles.Batch041.valid1661
  · exact MergedCutProfiles.Batch041.valid1662
  · exact MergedCutProfiles.Batch041.valid1663
  · exact MergedCutProfiles.Batch041.valid1664
  · exact MergedCutProfiles.Batch041.valid1665
  · exact MergedCutProfiles.Batch041.valid1666
  · exact MergedCutProfiles.Batch041.valid1667
  · exact MergedCutProfiles.Batch041.valid1668
  · exact MergedCutProfiles.Batch041.valid1669
  · exact MergedCutProfiles.Batch041.valid1670
theorem numericValid253 : retention253.NumericValid := by decide +kernel
def certificate253 : RatCutBinCertificate := ⟨⟨retention253,(991191016586418053/500000000000000000),(36585906920747501/1000000000000000000),(4762395989857947939/500000000000000000),(121527652363862859971/200000000000000000),(2178583693177976953/1000000000000000000)⟩,(996848037382240881/1000000000000000000),(205568224934225167/500000000000000000),(55858032858694741/250000000000000000),(31008014120809373/250000000000000000)⟩
theorem valid253 : certificate253.Valid := by decide +kernel
theorem sound253 : certificate253.Sound := rat_cut_bin_certificate_sound certificate253 profilesValid253 numericValid253 valid253

def retention254 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(1204594064925074960/63476256200139309633),(1053615059/1000000000),(53/20),(2181715834031425959/1000000000000000000),true,MergedCutProfiles.Batch041.profile1671,![MergedCutProfiles.Batch041.profile1671,MergedCutProfiles.Batch041.profile1672,MergedCutProfiles.Batch041.profile1673,MergedCutProfiles.Batch041.profile1674,MergedCutProfiles.Batch041.profile1675,MergedCutProfiles.Batch040.profile1633,MergedCutProfiles.Batch041.profile1662,MergedCutProfiles.Batch041.profile1676,MergedCutProfiles.Batch041.profile1677,MergedCutProfiles.Batch041.profile1652,MergedCutProfiles.Batch041.profile1678,MergedCutProfiles.Batch041.profile1679,MergedCutProfiles.Batch042.profile1680,MergedCutProfiles.Batch041.profile1670,MergedCutProfiles.Batch042.profile1681,MergedCutProfiles.Batch042.profile1682]⟩
theorem profilesValid254 : retention254.ProfilesValid := by
  change ∀ j : Fin 16, (retention254.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch041.valid1671
  · exact MergedCutProfiles.Batch041.valid1672
  · exact MergedCutProfiles.Batch041.valid1673
  · exact MergedCutProfiles.Batch041.valid1674
  · exact MergedCutProfiles.Batch041.valid1675
  · exact MergedCutProfiles.Batch040.valid1633
  · exact MergedCutProfiles.Batch041.valid1662
  · exact MergedCutProfiles.Batch041.valid1676
  · exact MergedCutProfiles.Batch041.valid1677
  · exact MergedCutProfiles.Batch041.valid1652
  · exact MergedCutProfiles.Batch041.valid1678
  · exact MergedCutProfiles.Batch041.valid1679
  · exact MergedCutProfiles.Batch042.valid1680
  · exact MergedCutProfiles.Batch041.valid1670
  · exact MergedCutProfiles.Batch042.valid1681
  · exact MergedCutProfiles.Batch042.valid1682
theorem numericValid254 : retention254.NumericValid := by decide +kernel
def certificate254 : RatCutBinCertificate := ⟨⟨retention254,(991191016586418053/500000000000000000),(36585906920747501/1000000000000000000),(4762395989857947939/500000000000000000),(121527652363862859971/200000000000000000),(2161536774676692257/1000000000000000000)⟩,(996848037382240881/1000000000000000000),(9473281887590891/25000000000000000),(253351133934901647/1000000000000000000),(159350539655953797/1000000000000000000)⟩
theorem valid254 : certificate254.Valid := by decide +kernel
theorem sound254 : certificate254.Sound := rat_cut_bin_certificate_sound certificate254 profilesValid254 numericValid254 valid254

def retention255 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(3820498890024396611/63476256200139309633),(15057425811563437/12500000000000000),(47/20),(16108390019993617573/8000000000000000000),true,MergedCutProfiles.Batch042.profile1683,![MergedCutProfiles.Batch042.profile1683,MergedCutProfiles.Batch042.profile1684,MergedCutProfiles.Batch040.profile1639,MergedCutProfiles.Batch042.profile1685,MergedCutProfiles.Batch042.profile1686,MergedCutProfiles.Batch042.profile1687,MergedCutProfiles.Batch042.profile1688,MergedCutProfiles.Batch042.profile1689,MergedCutProfiles.Batch042.profile1690,MergedCutProfiles.Batch042.profile1691,MergedCutProfiles.Batch042.profile1692,MergedCutProfiles.Batch042.profile1693,MergedCutProfiles.Batch042.profile1694,MergedCutProfiles.Batch042.profile1695,MergedCutProfiles.Batch042.profile1696,MergedCutProfiles.Batch042.profile1697]⟩
theorem profilesValid255 : retention255.ProfilesValid := by
  change ∀ j : Fin 16, (retention255.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch042.valid1683
  · exact MergedCutProfiles.Batch042.valid1684
  · exact MergedCutProfiles.Batch040.valid1639
  · exact MergedCutProfiles.Batch042.valid1685
  · exact MergedCutProfiles.Batch042.valid1686
  · exact MergedCutProfiles.Batch042.valid1687
  · exact MergedCutProfiles.Batch042.valid1688
  · exact MergedCutProfiles.Batch042.valid1689
  · exact MergedCutProfiles.Batch042.valid1690
  · exact MergedCutProfiles.Batch042.valid1691
  · exact MergedCutProfiles.Batch042.valid1692
  · exact MergedCutProfiles.Batch042.valid1693
  · exact MergedCutProfiles.Batch042.valid1694
  · exact MergedCutProfiles.Batch042.valid1695
  · exact MergedCutProfiles.Batch042.valid1696
  · exact MergedCutProfiles.Batch042.valid1697
theorem numericValid255 : retention255.NumericValid := by decide +kernel
def certificate255 : RatCutBinCertificate := ⟨⟨retention255,(991191016586418053/500000000000000000),(36585906920747501/1000000000000000000),(4762395989857947939/500000000000000000),(121527652363862859971/200000000000000000),(997827060117914953/500000000000000000)⟩,(996848037382240881/1000000000000000000),(48501101965552779/125000000000000000),(48930150065115501/200000000000000000),(159239404541472483/1000000000000000000)⟩
theorem valid255 : certificate255.Valid := by decide +kernel
theorem sound255 : certificate255.Sound := rat_cut_bin_certificate_sound certificate255 profilesValid255 numericValid255 valid255

def retention256 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(23367384582966574808/63476256200139309633),(3820498890024396611/1000000000000000000),(5/4),(61794139961749880381804558365928536531/48902385792312276620800000000000000000),false,MergedCutProfiles.Batch042.profile1698,(fun _ => MergedCutProfiles.Batch042.profile1698)⟩
theorem profilesValid256 : retention256.ProfilesValid := by
  exact MergedCutProfiles.Batch042.valid1698
theorem numericValid256 : retention256.NumericValid := by decide +kernel
def certificate256 : RatCutBinCertificate := ⟨⟨retention256,(991191016586418053/500000000000000000),(36585906920747501/1000000000000000000),(4762395989857947939/500000000000000000),(121527652363862859971/200000000000000000),(50164154148012079/40000000000000000)⟩,(996848037382240881/1000000000000000000),(89393131121808091/200000000000000000),(193104429434422191/1000000000000000000),(79775681094021439/500000000000000000)⟩
theorem valid256 : certificate256.Valid := by decide +kernel
theorem sound256 : certificate256.Sound := rat_cut_bin_certificate_sound certificate256 profilesValid256 numericValid256 valid256

def retention257 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(31183865311206296755/63476256200139309633),(2920923072870821851/125000000000000000),1,(94205474217319866523145049766294235847/93469538331866299232000000000000000000),false,MergedCutProfiles.Batch042.profile1699,(fun _ => MergedCutProfiles.Batch042.profile1699)⟩
theorem profilesValid257 : retention257.ProfilesValid := by
  exact MergedCutProfiles.Batch042.valid1699
theorem numericValid257 : retention257.NumericValid := by decide +kernel
def certificate257 : RatCutBinCertificate := ⟨⟨retention257,(991191016586418053/500000000000000000),(36585906920747501/1000000000000000000),(4762395989857947939/500000000000000000),(121527652363862859971/200000000000000000),(125032367798477851/125000000000000000)⟩,(996848037382240881/1000000000000000000),(478065642006216789/1000000000000000000),(21139793615811419/125000000000000000),(80847801217109411/500000000000000000)⟩
theorem valid257 : certificate257.Valid := by decide +kernel
theorem sound257 : certificate257.Sound := rat_cut_bin_certificate_sound certificate257 profilesValid257 numericValid257 valid257

def retention258 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(31495703964318359723/63476256200139309633),(6236773062241259351/200000000000000000),1,(124855966537491645843829714055774493819/124735461244825187020000000000000000000),false,MergedCutProfiles.Batch042.profile1700,(fun _ => MergedCutProfiles.Batch042.profile1700)⟩
theorem profilesValid258 : retention258.ProfilesValid := by
  exact MergedCutProfiles.Batch042.valid1700
theorem numericValid258 : retention258.NumericValid := by decide +kernel
def certificate258 : RatCutBinCertificate := ⟨⟨retention258,(991191016586418053/500000000000000000),(36585906920747501/1000000000000000000),(4762395989857947939/500000000000000000),(121527652363862859971/200000000000000000),(496675748502173079/500000000000000000)⟩,(996848037382240881/1000000000000000000),(477328380009258397/1000000000000000000),(169663019608802499/1000000000000000000),(81404325102578061/500000000000000000)⟩
theorem valid258 : certificate258.Valid := by decide +kernel
theorem sound258 : certificate258.Sound := rat_cut_bin_certificate_sound certificate258 profilesValid258 numericValid258 valid258

def retention259 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(1/2),(31495703964318359723/1000000000000000000),1,(125166023607700738623723992025629313427/125982815857273438892000000000000000000),false,MergedCutProfiles.Batch042.profile1701,(fun _ => MergedCutProfiles.Batch042.profile1701)⟩
theorem profilesValid259 : retention259.ProfilesValid := by
  exact MergedCutProfiles.Batch042.valid1701
theorem numericValid259 : retention259.NumericValid := by decide +kernel
def certificate259 : RatCutBinCertificate := ⟨⟨retention259,(991191016586418053/500000000000000000),(36585906920747501/1000000000000000000),(4762395989857947939/500000000000000000),(121527652363862859971/200000000000000000),(985902047883522319/1000000000000000000)⟩,(996848037382240881/1000000000000000000),(480813933218435859/1000000000000000000),(83548992262237019/500000000000000000),(79614998330981259/500000000000000000)⟩
theorem valid259 : certificate259.Valid := by decide +kernel
theorem sound259 : certificate259.Sound := rat_cut_bin_certificate_sound certificate259 profilesValid259 numericValid259 valid259

def retention260 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(8864036748649885680/21158752066713103211),(227173706247332241/62500000000000000),(5/4),(468821068751910874203887847547479791/403864366661923984000000000000000000),false,MergedCutProfiles.Batch042.profile1702,(fun _ => MergedCutProfiles.Batch042.profile1702)⟩
theorem profilesValid260 : retention260.ProfilesValid := by
  exact MergedCutProfiles.Batch042.valid1702
theorem numericValid260 : retention260.NumericValid := by decide +kernel
def certificate260 : RatCutBinCertificate := ⟨⟨retention260,(1182909096586418053/500000000000000000),(36585906920747501/1000000000000000000),(4762395989857947939/500000000000000000),(121527652363862859971/200000000000000000),(1149478511758743807/1000000000000000000)⟩,(62264893627702791/62500000000000000),(1773162599930997/5000000000000000),(277724362566572389/1000000000000000000),(211536006036257747/1000000000000000000)⟩
theorem valid260 : certificate260.Valid := by decide +kernel
theorem sound260 : certificate260.Sound := rat_cut_bin_certificate_sound certificate260 profilesValid260 numericValid260 valid260

def retention261 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(31493154003835820725/63476256200139309633),(332401378074370713/12500000000000000),1,(106329655906653452875661490297183937079/106368440983798628160000000000000000000),false,MergedCutProfiles.Batch042.profile1703,(fun _ => MergedCutProfiles.Batch042.profile1703)⟩
theorem profilesValid261 : retention261.ProfilesValid := by
  exact MergedCutProfiles.Batch042.valid1703
theorem numericValid261 : retention261.NumericValid := by decide +kernel
def certificate261 : RatCutBinCertificate := ⟨⟨retention261,(1182909096586418053/500000000000000000),(36585906920747501/1000000000000000000),(4762395989857947939/500000000000000000),(121527652363862859971/200000000000000000),(123818493608242883/125000000000000000)⟩,(62264893627702791/62500000000000000),(411532285500858891/1000000000000000000),(1394253143010693/6250000000000000),(42444368309992113/200000000000000000)⟩
theorem valid261 : certificate261.Valid := by decide +kernel
theorem sound261 : certificate261.Sound := rat_cut_bin_certificate_sound certificate261 profilesValid261 numericValid261 valid261

def retention262 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(1/2),(1259726160153432829/40000000000000000),1,(125155808693420803413195955954829796459/125972616015343282900000000000000000000),false,MergedCutProfiles.Batch042.profile1701,(fun _ => MergedCutProfiles.Batch042.profile1701)⟩
theorem profilesValid262 : retention262.ProfilesValid := by
  exact MergedCutProfiles.Batch042.valid1701
theorem numericValid262 : retention262.NumericValid := by decide +kernel
def certificate262 : RatCutBinCertificate := ⟨⟨retention262,(1182909096586418053/500000000000000000),(36585906920747501/1000000000000000000),(4762395989857947939/500000000000000000),(121527652363862859971/200000000000000000),(984428574638421439/1000000000000000000)⟩,(62264893627702791/62500000000000000),(51761304958655289/125000000000000000),(8832688257448077/40000000000000000),(104992898906550259/500000000000000000)⟩
theorem valid262 : certificate262.Valid := by decide +kernel
theorem sound262 : certificate262.Sound := rat_cut_bin_certificate_sound certificate262 profilesValid262 numericValid262 valid262

def retention263 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(361183457578753937/29508253281651770749),(715214767482681063/1000000000000000000),(73/20),(89386220485168562937/40000000000000000000),true,MergedCutProfiles.Batch042.profile1704,![MergedCutProfiles.Batch042.profile1704,MergedCutProfiles.Batch042.profile1705,MergedCutProfiles.Batch042.profile1706,MergedCutProfiles.Batch042.profile1707,MergedCutProfiles.Batch042.profile1708,MergedCutProfiles.Batch042.profile1709,MergedCutProfiles.Batch042.profile1710,MergedCutProfiles.Batch042.profile1711,MergedCutProfiles.Batch042.profile1712,MergedCutProfiles.Batch042.profile1713,MergedCutProfiles.Batch042.profile1714,MergedCutProfiles.Batch042.profile1715,MergedCutProfiles.Batch042.profile1716,MergedCutProfiles.Batch042.profile1717,MergedCutProfiles.Batch042.profile1718,MergedCutProfiles.Batch042.profile1719]⟩
theorem profilesValid263 : retention263.ProfilesValid := by
  change ∀ j : Fin 16, (retention263.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch042.valid1704
  · exact MergedCutProfiles.Batch042.valid1705
  · exact MergedCutProfiles.Batch042.valid1706
  · exact MergedCutProfiles.Batch042.valid1707
  · exact MergedCutProfiles.Batch042.valid1708
  · exact MergedCutProfiles.Batch042.valid1709
  · exact MergedCutProfiles.Batch042.valid1710
  · exact MergedCutProfiles.Batch042.valid1711
  · exact MergedCutProfiles.Batch042.valid1712
  · exact MergedCutProfiles.Batch042.valid1713
  · exact MergedCutProfiles.Batch042.valid1714
  · exact MergedCutProfiles.Batch042.valid1715
  · exact MergedCutProfiles.Batch042.valid1716
  · exact MergedCutProfiles.Batch042.valid1717
  · exact MergedCutProfiles.Batch042.valid1718
  · exact MergedCutProfiles.Batch042.valid1719
theorem numericValid263 : retention263.NumericValid := by decide +kernel
def certificate263 : RatCutBinCertificate := ⟨⟨retention263,(1991563315965953267/1000000000000000000),(39310593322721927/1000000000000000000),(9659167729003702169/1000000000000000000),(22917354861350491377/40000000000000000),(220507073593702991/100000000000000000)⟩,(249162666740009357/250000000000000000),(222607041066348919/500000000000000000),(4862958591958497/25000000000000000),(47528192782702063/500000000000000000)⟩
theorem valid263 : certificate263.Valid := by decide +kernel
theorem sound263 : certificate263.Sound := rat_cut_bin_certificate_sound certificate263 profilesValid263 numericValid263 valid263

def certificates : List RatCutBinCertificate := [certificate252,certificate253,certificate254,certificate255,certificate256,certificate257,certificate258,certificate259,certificate260,certificate261,certificate262,certificate263]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound252,List.forall_mem_cons.mpr ⟨sound253,List.forall_mem_cons.mpr ⟨sound254,List.forall_mem_cons.mpr ⟨sound255,List.forall_mem_cons.mpr ⟨sound256,List.forall_mem_cons.mpr ⟨sound257,List.forall_mem_cons.mpr ⟨sound258,List.forall_mem_cons.mpr ⟨sound259,List.forall_mem_cons.mpr ⟨sound260,List.forall_mem_cons.mpr ⟨sound261,List.forall_mem_cons.mpr ⟨sound262,List.forall_mem_cons.mpr ⟨sound263,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch021
