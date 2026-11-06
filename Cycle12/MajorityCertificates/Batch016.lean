import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch016

def certificate640 : RatMajorityCertificate := ⟨0,(1008909678696544539/1000000000000000000),(1125965561/970275000),(21635292497440868047/50000000000000000000),(8654116998976347219/20000000000000000000),(69014065371773783/100000000000000000),false⟩
theorem valid640 : certificate640.Valid := by decide +kernel
theorem bound640 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate640.a certificate640.b certificate640.c x ≤ (certificate640.bound:ℝ) :=
  rat_majority_certificate_sound certificate640 valid640 x hx0 hx1

def certificate641 : RatMajorityCertificate := ⟨(175004776982235091/1000000000000000000),(832345665381037299913000549349781951/1000000000000000000000000000000000000),(1125965561/970275000),(19781778559220249157/50000000000000000000),(7912711423688099663/20000000000000000000),(69014065371773783/100000000000000000),false⟩
theorem valid641 : certificate641.Valid := by decide +kernel
theorem bound641 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate641.a certificate641.b certificate641.c x ≤ (certificate641.bound:ℝ) :=
  rat_majority_certificate_sound certificate641 valid641 x hx0 hx1

def certificate642 : RatMajorityCertificate := ⟨0,(1008909678696544539/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543106189370015597/1000000000000000000),false⟩
theorem valid642 : certificate642.Valid := by decide +kernel
theorem bound642 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate642.a certificate642.b certificate642.c x ≤ (certificate642.bound:ℝ) :=
  rat_majority_certificate_sound certificate642 valid642 x hx0 hx1

def certificate643 : RatMajorityCertificate := ⟨(58868194935002261/500000000000000000),(445062147710953587722454757147797321/500000000000000000000000000000000000),1,(4600614273959400083/12500000000000000000),(7360982838335040133/20000000000000000000),(543106189370015597/1000000000000000000),false⟩
theorem valid643 : certificate643.Valid := by decide +kernel
theorem bound643 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate643.a certificate643.b certificate643.c x ≤ (certificate643.bound:ℝ) :=
  rat_majority_certificate_sound certificate643 valid643 x hx0 hx1

def certificate644 : RatMajorityCertificate := ⟨0,(504464866165454599/500000000000000000),(30834529/26580000),(43261379086177016771/100000000000000000000),(10815344771544254193/25000000000000000000),(68974907736119761/100000000000000000),false⟩
theorem valid644 : certificate644.Valid := by decide +kernel
theorem bound644 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate644.a certificate644.b certificate644.c x ≤ (certificate644.bound:ℝ) :=
  rat_majority_certificate_sound certificate644 valid644 x hx0 hx1

def certificate645 : RatMajorityCertificate := ⟨(174495997702400563/1000000000000000000),(416437766038105625780924835511460763/500000000000000000000000000000000000),(30834529/26580000),(39566687629529666299/100000000000000000000),(395666876295296663/1000000000000000000),(68974907736119761/100000000000000000),false⟩
theorem valid645 : certificate645.Valid := by decide +kernel
theorem bound645 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate645.a certificate645.b certificate645.c x ≤ (certificate645.bound:ℝ) :=
  rat_majority_certificate_sound certificate645 valid645 x hx0 hx1

def certificate646 : RatMajorityCertificate := ⟨0,(504464866165454599/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543100466852331251/1000000000000000000),false⟩
theorem valid646 : certificate646.Valid := by decide +kernel
theorem bound646 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate646.a certificate646.b certificate646.c x ≤ (certificate646.bound:ℝ) :=
  rat_majority_certificate_sound certificate646 valid646 x hx0 hx1

def certificate647 : RatMajorityCertificate := ⟨(117587004342296011/1000000000000000000),(445146353757121513027484628760695411/500000000000000000000000000000000000),1,(18404183832987598183/50000000000000000000),(36808367665975196367/100000000000000000000),(543100466852331251/1000000000000000000),false⟩
theorem valid647 : certificate647.Valid := by decide +kernel
theorem bound647 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate647.a certificate647.b certificate647.c x ≤ (certificate647.bound:ℝ) :=
  rat_majority_certificate_sound certificate647 valid647 x hx0 hx1

def certificate648 : RatMajorityCertificate := ⟨0,(1008949747642008609/1000000000000000000),(281262653/242516250),(108136158852525427/250000000000000000),(43254463541010170801/100000000000000000000),(689497200867490629/1000000000000000000),false⟩
theorem valid648 : certificate648.Valid := by decide +kernel
theorem bound648 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate648.a certificate648.b certificate648.c x ≤ (certificate648.bound:ℝ) :=
  rat_majority_certificate_sound certificate648 valid648 x hx0 hx1

def certificate649 : RatMajorityCertificate := ⟨(174549822689817037/1000000000000000000),(832837748088160361176274286611128467/1000000000000000000000000000000000000),(281262653/242516250),(39558289869535496813/100000000000000000000),(19779144934767748407/50000000000000000000),(689497200867490629/1000000000000000000),false⟩
theorem valid649 : certificate649.Valid := by decide +kernel
theorem bound649 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate649.a certificate649.b certificate649.c x ≤ (certificate649.bound:ℝ) :=
  rat_majority_certificate_sound certificate649 valid649 x hx0 hx1

def certificate650 : RatMajorityCertificate := ⟨0,(1008949747642008609/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543094807086635051/1000000000000000000),false⟩
theorem valid650 : certificate650.Valid := by decide +kernel
theorem bound650 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate650.a certificate650.b certificate650.c x ≤ (certificate650.bound:ℝ) :=
  rat_majority_certificate_sound certificate650 valid650 x hx0 hx1

def certificate651 : RatMajorityCertificate := ⟨(117438329347916833/1000000000000000000),(890460374882928826899668785997984703/1000000000000000000000000000000000000),1,(36811803821041881183/100000000000000000000),(1150368869407558787/3125000000000000000),(543094807086635051/1000000000000000000),false⟩
theorem valid651 : certificate651.Valid := by decide +kernel
theorem bound651 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate651.a certificate651.b certificate651.c x ≤ (certificate651.bound:ℝ) :=
  rat_majority_certificate_sound certificate651 valid651 x hx0 hx1

def certificate652 : RatMajorityCertificate := ⟨0,(50448486218276981/50000000000000000),(187441677/161660000),(43247764366707945207/100000000000000000000),(5405970545838493151/12500000000000000000),(344629298808358149/500000000000000000),false⟩
theorem valid652 : certificate652.Valid := by decide +kernel
theorem bound652 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate652.a certificate652.b certificate652.c x ≤ (certificate652.bound:ℝ) :=
  rat_majority_certificate_sound certificate652 valid652 x hx0 hx1

def certificate653 : RatMajorityCertificate := ⟨(174656929680335101/1000000000000000000),(41637308508372023860540073085389919/50000000000000000000000000000000000),(187441677/161660000),(39548799642258451497/100000000000000000000),(19774399821129225749/50000000000000000000),(344629298808358149/500000000000000000),false⟩
theorem valid653 : certificate653.Valid := by decide +kernel
theorem bound653 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate653.a certificate653.b certificate653.c x ≤ (certificate653.bound:ℝ) :=
  rat_majority_certificate_sound certificate653 valid653 x hx0 hx1

def certificate654 : RatMajorityCertificate := ⟨0,(50448486218276981/50000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271546557278438607/500000000000000000),false⟩
theorem valid654 : certificate654.Valid := by decide +kernel
theorem bound654 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate654.a certificate654.b certificate654.c x ≤ (certificate654.bound:ℝ) :=
  rat_majority_certificate_sound certificate654 valid654 x hx0 hx1

def certificate655 : RatMajorityCertificate := ⟨(117329195688412897/1000000000000000000),(44529405906588559985451074161376043/50000000000000000000000000000000000),1,(36814337811655764389/100000000000000000000),(3681433781165576439/10000000000000000000),(271546557278438607/500000000000000000),false⟩
theorem valid655 : certificate655.Valid := by decide +kernel
theorem bound655 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate655.a certificate655.b certificate655.c x ≤ (certificate655.bound:ℝ) :=
  rat_majority_certificate_sound certificate655 valid655 x hx0 hx1

def certificate656 : RatMajorityCertificate := ⟨0,(50449483111882777/50000000000000000),(149891021/129314000),(43239454445813375039/100000000000000000000),(135123295143166797/312500000000000000),(344460742716788117/500000000000000000),false⟩
theorem valid656 : certificate656.Valid := by decide +kernel
theorem bound656 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate656.a certificate656.b certificate656.c x ≤ (certificate656.bound:ℝ) :=
  rat_majority_certificate_sound certificate656 valid656 x hx0 hx1

def certificate657 : RatMajorityCertificate := ⟨(43590880383494419/250000000000000000),(10413233394231490328884442438278437/12500000000000000000000000000000000),(149891021/129314000),(1581901388754149963/4000000000000000000),(9886883679713437269/25000000000000000000),(344460742716788117/500000000000000000),false⟩
theorem valid657 : certificate657.Valid := by decide +kernel
theorem bound657 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate657.a certificate657.b certificate657.c x ≤ (certificate657.bound:ℝ) :=
  rat_majority_certificate_sound certificate657 valid657 x hx0 hx1

def certificate658 : RatMajorityCertificate := ⟨0,(50449483111882777/50000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(33942973971399099/62500000000000000),false⟩
theorem valid658 : certificate658.Valid := by decide +kernel
theorem bound658 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate658.a certificate658.b certificate658.c x ≤ (certificate658.bound:ℝ) :=
  rat_majority_certificate_sound certificate658 valid658 x hx0 hx1

def certificate659 : RatMajorityCertificate := ⟨(14647750022933887/125000000000000000),(5567213971576263433301922035035801/6250000000000000000000000000000000),1,(23011086429342189638343/62500000000000000000000),(368177382869475034213489/1000000000000000000000000),(33942973971399099/62500000000000000),false⟩
theorem valid659 : certificate659.Valid := by decide +kernel
theorem bound659 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate659.a certificate659.b certificate659.c x ≤ (certificate659.bound:ℝ) :=
  rat_majority_certificate_sound certificate659 valid659 x hx0 hx1

def certificate660 : RatMajorityCertificate := ⟨0,(504583926555805491/500000000000000000),(2245786591/1927630000),(5422157882744678553/12500000000000000000),(1735090522478297137/4000000000000000000),(138946164767612497/200000000000000000),false⟩
theorem valid660 : certificate660.Valid := by decide +kernel
theorem bound660 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate660.a certificate660.b certificate660.c x ≤ (certificate660.bound:ℝ) :=
  rat_majority_certificate_sound certificate660 valid660 x hx0 hx1

def certificate661 : RatMajorityCertificate := ⟨(89177951744438919/500000000000000000),(207294202224489611828091826105695771/250000000000000000000000000000000000),(2245786591/1927630000),(19795834610867332027/50000000000000000000),(7918333844346932811/20000000000000000000),(138946164767612497/200000000000000000),false⟩
theorem valid661 : certificate661.Valid := by decide +kernel
theorem bound661 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate661.a certificate661.b certificate661.c x ≤ (certificate661.bound:ℝ) :=
  rat_majority_certificate_sound certificate661 valid661 x hx0 hx1

def certificate662 : RatMajorityCertificate := ⟨0,(504583926555805491/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(21735010186180659/40000000000000000),false⟩
theorem valid662 : certificate662.Valid := by decide +kernel
theorem bound662 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate662.a certificate662.b certificate662.c x ≤ (certificate662.bound:ℝ) :=
  rat_majority_certificate_sound certificate662 valid662 x hx0 hx1

def certificate663 : RatMajorityCertificate := ⟨(11921656324158951/100000000000000000),(44442916496487574909595953077400059/50000000000000000000000000000000000),1,(36771726987304142829/100000000000000000000),(3677172698730414283/10000000000000000000),(21735010186180659/40000000000000000),false⟩
theorem valid663 : certificate663.Valid := by decide +kernel
theorem bound663 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate663.a certificate663.b certificate663.c x ≤ (certificate663.bound:ℝ) :=
  rat_majority_certificate_sound certificate663 valid663 x hx0 hx1

def certificate664 : RatMajorityCertificate := ⟨0,(1009247763510066357/1000000000000000000),(448212971/385356000),(43332314369323829577/100000000000000000000),(21666157184661914789/50000000000000000000),(69290194296159687/100000000000000000),false⟩
theorem valid664 : certificate664.Valid := by decide +kernel
theorem bound664 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate664.a certificate664.b certificate664.c x ≤ (certificate664.bound:ℝ) :=
  rat_majority_certificate_sound certificate664 valid664 x hx0 hx1

def certificate665 : RatMajorityCertificate := ⟨(176985874927019853/1000000000000000000),(830625165067099241638678503713614479/1000000000000000000000000000000000000),(448212971/385356000),(4947437102289698571/12500000000000000000),(39579496818317588569/100000000000000000000),(69290194296159687/100000000000000000),false⟩
theorem valid665 : certificate665.Valid := by decide +kernel
theorem bound665 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate665.a certificate665.b certificate665.c x ≤ (certificate665.bound:ℝ) :=
  rat_majority_certificate_sound certificate665 valid665 x hx0 hx1

def certificate666 : RatMajorityCertificate := ⟨0,(1009247763510066357/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(8489730736124957/15625000000000000),false⟩
theorem valid666 : certificate666.Valid := by decide +kernel
theorem bound666 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate666.a certificate666.b certificate666.c x ≤ (certificate666.bound:ℝ) :=
  rat_majority_certificate_sound certificate666 valid666 x hx0 hx1

def certificate667 : RatMajorityCertificate := ⟨(118526679078321653/1000000000000000000),(889624977733994855510500117780071879/1000000000000000000000000000000000000),1,(36787677412427008913/100000000000000000000),(18393838706213504457/50000000000000000000),(8489730736124957/15625000000000000),false⟩
theorem valid667 : certificate667.Valid := by decide +kernel
theorem bound667 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate667.a certificate667.b certificate667.c x ≤ (certificate667.bound:ℝ) :=
  rat_majority_certificate_sound certificate667 valid667 x hx0 hx1

def certificate668 : RatMajorityCertificate := ⟨0,(1000024211291334813/1000000000000000000),(2740003739/2377450000),(43084409337393849197/100000000000000000000),(21542204668696924599/50000000000000000000),(680657092636126727/1000000000000000000),false⟩
theorem valid668 : certificate668.Valid := by decide +kernel
theorem bound668 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate668.a certificate668.b certificate668.c x ≤ (certificate668.bound:ℝ) :=
  rat_majority_certificate_sound certificate668 valid668 x hx0 hx1

def certificate669 : RatMajorityCertificate := ⟨(49971117742477117/250000000000000000),(200033725215066596893614759962025879/250000000000000000000000000000000000),(2740003739/2377450000),(4837973588923011719/12500000000000000000),(38703788711384093753/100000000000000000000),(680657092636126727/1000000000000000000),false⟩
theorem valid669 : certificate669.Valid := by decide +kernel
theorem bound669 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate669.a certificate669.b certificate669.c x ≤ (certificate669.bound:ℝ) :=
  rat_majority_certificate_sound certificate669 valid669 x hx0 hx1

def certificate670 : RatMajorityCertificate := ⟨0,(1000024211291334813/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(67618593501901901/125000000000000000),false⟩
theorem valid670 : certificate670.Valid := by decide +kernel
theorem bound670 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate670.a certificate670.b certificate670.c x ≤ (certificate670.bound:ℝ) :=
  rat_majority_certificate_sound certificate670 valid670 x hx0 hx1

def certificate671 : RatMajorityCertificate := ⟨(135973660777477027/1000000000000000000),(864047258415942841468167598727159049/1000000000000000000000000000000000000),1,(454469275351573323/1250000000000000000),(36357542028125865841/100000000000000000000),(67618593501901901/125000000000000000),false⟩
theorem valid671 : certificate671.Valid := by decide +kernel
theorem bound671 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate671.a certificate671.b certificate671.c x ≤ (certificate671.bound:ℝ) :=
  rat_majority_certificate_sound certificate671 valid671 x hx0 hx1

def certificate672 : RatMajorityCertificate := ⟨0,(40001508676367787/40000000000000000),(683037811/591735000),(2695413313954123561/6250000000000000000),(43126613023265976977/100000000000000000000),(34125890082390087/50000000000000000),false⟩
theorem valid672 : certificate672.Valid := by decide +kernel
theorem bound672 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate672.a certificate672.b certificate672.c x ≤ (certificate672.bound:ℝ) :=
  rat_majority_certificate_sound certificate672 valid672 x hx0 hx1

def certificate673 : RatMajorityCertificate := ⟨(158020355011827/781250000000000),(24930126051364017938330213183151/31250000000000000000000000000000),(683037811/591735000),(38685131331909115409/100000000000000000000),(3868513133190911541/10000000000000000000),(34125890082390087/50000000000000000),false⟩
theorem valid673 : certificate673.Valid := by decide +kernel
theorem bound673 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate673.a certificate673.b certificate673.c x ≤ (certificate673.bound:ℝ) :=
  rat_majority_certificate_sound certificate673 valid673 x hx0 hx1

def certificate674 : RatMajorityCertificate := ⟨0,(40001508676367787/40000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(54083984792946873/100000000000000000),false⟩
theorem valid674 : certificate674.Valid := by decide +kernel
theorem bound674 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate674.a certificate674.b certificate674.c x ≤ (certificate674.bound:ℝ) :=
  rat_majority_certificate_sound certificate674 valid674 x hx0 hx1

def certificate675 : RatMajorityCertificate := ⟨(134931189502082927/1000000000000000000),(34604057528787590738144622774527451/40000000000000000000000000000000000),1,(1819116356237628907/5000000000000000000),(36382327124752578141/100000000000000000000),(54083984792946873/100000000000000000),false⟩
theorem valid675 : certificate675.Valid := by decide +kernel
theorem bound675 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate675.a certificate675.b certificate675.c x ≤ (certificate675.bound:ℝ) :=
  rat_majority_certificate_sound certificate675 valid675 x hx0 hx1

def certificate676 : RatMajorityCertificate := ⟨0,(500027069470782717/500000000000000000),(2725879747/2356830000),(8636043380777855967/20000000000000000000),(10795054225972319959/25000000000000000000),(21395529313434383/31250000000000000),false⟩
theorem valid676 : certificate676.Valid := by decide +kernel
theorem bound676 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate676.a certificate676.b certificate676.c x ≤ (certificate676.bound:ℝ) :=
  rat_majority_certificate_sound certificate676 valid676 x hx0 hx1

def certificate677 : RatMajorityCertificate := ⟨(20313824650273667/100000000000000000),(39845244737458582380590565256186761/50000000000000000000000000000000000),(2725879747/2356830000),(19358942913562167333/50000000000000000000),(38717885827124334667/100000000000000000000),(21395529313434383/31250000000000000),false⟩
theorem valid677 : certificate677.Valid := by decide +kernel
theorem bound677 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate677.a certificate677.b certificate677.c x ≤ (certificate677.bound:ℝ) :=
  rat_majority_certificate_sound certificate677 valid677 x hx0 hx1

def certificate678 : RatMajorityCertificate := ⟨0,(500027069470782717/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540907112027960153/1000000000000000000),false⟩
theorem valid678 : certificate678.Valid := by decide +kernel
theorem bound678 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate678.a certificate678.b certificate678.c x ≤ (certificate678.bound:ℝ) :=
  rat_majority_certificate_sound certificate678 valid678 x hx0 hx1

def certificate679 : RatMajorityCertificate := ⟨(135473413241614767/1000000000000000000),(432286695656373754662720899524418061/500000000000000000000000000000000000),1,(36369506666078607421/100000000000000000000),(18184753333039303711/50000000000000000000),(540907112027960153/1000000000000000000),false⟩
theorem valid679 : certificate679.Valid := by decide +kernel
theorem bound679 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate679.a certificate679.b certificate679.c x ≤ (certificate679.bound:ℝ) :=
  rat_majority_certificate_sound certificate679 valid679 x hx0 hx1

end Cycle12.MajorityCertificates.Batch016
