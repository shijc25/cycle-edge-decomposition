import Cycle12.FinitePotentialPayments.Interval00
import Cycle12.FinitePotentialPayments.Interval01
import Cycle12.FinitePotentialPayments.Interval02
import Cycle12.FinitePotentialPayments.Interval03
import Cycle12.FinitePotentialPayments.Interval04
import Cycle12.FinitePotentialPayments.Interval05
import Cycle12.FinitePotentialPayments.Interval06
import Cycle12.FinitePotentialPayments.Interval07
import Cycle12.FinitePotentialPayments.Interval08
import Cycle12.FinitePotentialPayments.Interval09
import Cycle12.FinitePotentialPayments.Interval10
import Cycle12.FinitePotentialPayments.Interval11
import Cycle12.FinitePotentialPayments.Interval12
import Cycle12.FinitePotentialPayments.Interval13
import Cycle12.FinitePotentialPayments.Interval14
import Cycle12.FinitePotentialPayments.Interval15
import Cycle12.FinitePotentialPayments.Interval16
import Cycle12.FinitePotentialPayments.Interval17
import Cycle12.FinitePotentialPayments.Interval18
import Cycle12.FinitePotentialPayments.Interval19
import Cycle12.FinitePotentialPayments.Interval20
import Cycle12.FinitePotentialPayments.Interval21
import Cycle12.FinitePotentialPayments.Interval22
import Cycle12.FinitePotentialPayments.Interval23
import Cycle12.FinitePotentialPayments.Interval24
import Cycle12.FinitePotentialPayments.Interval25
import Cycle12.FinitePotentialPayments.Interval26
import Cycle12.FinitePotentialPayments.Interval27
import Cycle12.FinitePotentialPayments.Interval28
import Cycle12.FinitePotentialPayments.Interval29
import Cycle12.FinitePotentialPayments.Interval30
import Cycle12.FinitePotentialPayments.Interval31
import Cycle12.FinitePotentialPayments.Interval32
import Cycle12.FinitePotentialPayments.Interval33
import Cycle12.FinitePotentialPayments.Interval34
import Cycle12.FinitePotentialPayments.Interval35
import Cycle12.FinitePotentialPayments.Interval36
import Cycle12.FinitePotentialPayments.Interval37
import Cycle12.FinitePotentialPayments.Interval38
import Cycle12.FinitePotentialPayments.Interval39
import Cycle12.FinitePotentialPayments.Interval40
import Cycle12.FinitePotentialPayments.Interval41
import Cycle12.FinitePotentialPayments.Interval42
import Cycle12.FinitePotentialPayments.Interval43
import Cycle12.FinitePotentialPayments.Interval44

namespace Cycle12.Global12
open Real
noncomputable section

def mainDegreeLog : ℝ := (((158387/1000):ℚ):ℝ)

/-- The complete finite-order range, with the current potential and no
induction hypothesis. Every interval uses its own certified average-degree bound. -/
theorem finite_order_potential {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hn : (Fintype.card V:ℝ)≤(2:ℝ)^mainDegreeLog) :
    ∃ P : Cycle13.CyclePacking G,
      P.weight≤C*orderPotential (Fintype.card V)*Fintype.card V := by
  by_cases hz : Fintype.card V=0
  · apply FinitePayment00.graph_bound G
    rw [hz,Nat.cast_zero]
    exact rpow_nonneg (by norm_num) _
  have hpos : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)
  have hlog := (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mpr hn
  by_cases h0 : logb 2 (Fintype.card V)≤(((13888667319631906663815/116779687257754820648):ℚ):ℝ)
  · apply FinitePayment00.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h0
  by_cases h1 : logb 2 (Fintype.card V)≤(((56888125332368729135802307493/478329599007763745374208000):ℚ):ℝ)
  · apply FinitePayment01.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h1
  by_cases h2 : logb 2 (Fintype.card V)≤(((1673184391868387311077011029/14068517617875404275712000):ℚ):ℝ)
  · apply FinitePayment02.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h2
  by_cases h3 : logb 2 (Fintype.card V)≤(((14222139326459511864562627493/119582399751940936343552000):ℚ):ℝ)
  · apply FinitePayment03.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h3
  by_cases h4 : logb 2 (Fintype.card V)≤(((7111141658807975652689347493/59791199875970468171776000):ℚ):ℝ)
  · apply FinitePayment04.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h4
  by_cases h5 : logb 2 (Fintype.card V)≤(((3555642824982207546752707493/29895599937985234085888000):ℚ):ℝ)
  · apply FinitePayment05.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h5
  by_cases h6 : logb 2 (Fintype.card V)≤(((1777893408069323493784387493/14947799968992617042944000):ℚ):ℝ)
  · apply FinitePayment06.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h6
  by_cases h7 : logb 2 (Fintype.card V)≤(((889018699612881467300227493/7473899984496308521472000):ℚ):ℝ)
  · apply FinitePayment07.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h7
  by_cases h8 : logb 2 (Fintype.card V)≤(((444581345384660454058147493/3736949992248154260736000):ℚ):ℝ)
  · apply FinitePayment08.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h8
  by_cases h9 : logb 2 (Fintype.card V)≤(((222362668270549947437107493/1868474996124077130368000):ℚ):ℝ)
  · apply FinitePayment09.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h9
    · exact (lt_of_not_ge h8).le
  by_cases h10 : logb 2 (Fintype.card V)≤(((6544313512558511419211029/54955146944825797952000):ℚ):ℝ)
  · apply FinitePayment10.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h10
    · exact (lt_of_not_ge h9).le
  by_cases h11 : logb 2 (Fintype.card V)≤(((55698660434967067471327493/467118749031019282592000):ℚ):ℝ)
  · apply FinitePayment11.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h11
    · exact (lt_of_not_ge h10).le
  by_cases h12 : logb 2 (Fintype.card V)≤(((27921325795703254143697493/233559374515509641296000):ℚ):ℝ)
  · apply FinitePayment12.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h12
    · exact (lt_of_not_ge h11).le
  by_cases h13 : logb 2 (Fintype.card V)≤(((14032658476071347479882493/116779687257754820648000):ℚ):ℝ)
  · apply FinitePayment13.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h13
    · exact (lt_of_not_ge h12).le
  by_cases h14 : logb 2 (Fintype.card V)≤(((7088324816255394147974993/58389843628877410324000):ℚ):ℝ)
  · apply FinitePayment14.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h14
    · exact (lt_of_not_ge h13).le
  by_cases h15 : logb 2 (Fintype.card V)≤(((14320640788950229112017479/116779687257754820648000):ℚ):ℝ)
  · apply FinitePayment15.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h15
    · exact (lt_of_not_ge h14).le
  by_cases h16 : logb 2 (Fintype.card V)≤(((3616157986347417482021243/29194921814438705162000):ℚ):ℝ)
  · apply FinitePayment16.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h16
    · exact (lt_of_not_ge h15).le
  by_cases h17 : logb 2 (Fintype.card V)≤(((2921724620365822148830493/23355937451550964129600):ℚ):ℝ)
  · apply FinitePayment17.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h17
    · exact (lt_of_not_ge h16).le
  by_cases h18 : logb 2 (Fintype.card V)≤(((7376307129134275780109979/58389843628877410324000):ℚ):ℝ)
  · apply FinitePayment18.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h18
    · exact (lt_of_not_ge h17).le
  by_cases h19 : logb 2 (Fintype.card V)≤(((14896605414707992376287451/116779687257754820648000):ℚ):ℝ)
  · apply FinitePayment19.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h19
    · exact (lt_of_not_ge h18).le
  by_cases h20 : logb 2 (Fintype.card V)≤(((235009321424178643630546/1824682613402419072625):ℚ):ℝ)
  · apply FinitePayment20.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h20
    · exact (lt_of_not_ge h19).le
  by_cases h21 : logb 2 (Fintype.card V)≤(((15184587727586874008422437/116779687257754820648000):ℚ):ℝ)
  · apply FinitePayment21.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h21
    · exact (lt_of_not_ge h20).le
  by_cases h22 : logb 2 (Fintype.card V)≤(((1532857888402631482448993/11677968725775482064800):ℚ):ℝ)
  · apply FinitePayment22.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h22
    · exact (lt_of_not_ge h21).le
  by_cases h23 : logb 2 (Fintype.card V)≤(((15472570040465755640557423/116779687257754820648000):ℚ):ℝ)
  · apply FinitePayment23.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h23
    · exact (lt_of_not_ge h22).le
  by_cases h24 : logb 2 (Fintype.card V)≤(((3904140299226299114156229/29194921814438705162000):ℚ):ℝ)
  · apply FinitePayment24.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h24
    · exact (lt_of_not_ge h23).le
  by_cases h25 : logb 2 (Fintype.card V)≤(((15760552353344637272692409/116779687257754820648000):ℚ):ℝ)
  · apply FinitePayment25.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h25
    · exact (lt_of_not_ge h24).le
  by_cases h26 : logb 2 (Fintype.card V)≤(((7952271754892039044379951/58389843628877410324000):ℚ):ℝ)
  · apply FinitePayment26.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h26
    · exact (lt_of_not_ge h25).le
  by_cases h27 : logb 2 (Fintype.card V)≤(((188806290190864928292087/1373878673620644948800):ℚ):ℝ)
  · apply FinitePayment27.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h27
    · exact (lt_of_not_ge h26).le
  by_cases h28 : logb 2 (Fintype.card V)≤(((2024065727832869965111861/14597460907219352581000):ℚ):ℝ)
  · apply FinitePayment28.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h28
    · exact (lt_of_not_ge h27).le
  by_cases h29 : logb 2 (Fintype.card V)≤(((16336516979102400536962381/116779687257754820648000):ℚ):ℝ)
  · apply FinitePayment29.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h29
    · exact (lt_of_not_ge h28).le
  by_cases h30 : logb 2 (Fintype.card V)≤(((8240254067770920676514937/58389843628877410324000):ℚ):ℝ)
  · apply FinitePayment30.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h30
    · exact (lt_of_not_ge h29).le
  by_cases h31 : logb 2 (Fintype.card V)≤(((16624499291981282169097367/116779687257754820648000):ℚ):ℝ)
  · apply FinitePayment31.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h31
    · exact (lt_of_not_ge h30).le
  by_cases h32 : logb 2 (Fintype.card V)≤(((838424522421036149258243/5838984362887741032400):ℚ):ℝ)
  · apply FinitePayment32.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h32
    · exact (lt_of_not_ge h31).le
  by_cases h33 : logb 2 (Fintype.card V)≤(((16912481604860163801232353/116779687257754820648000):ℚ):ℝ)
  · apply FinitePayment33.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h33
    · exact (lt_of_not_ge h32).le
  by_cases h34 : logb 2 (Fintype.card V)≤(((8528236380649802308649923/58389843628877410324000):ℚ):ℝ)
  · apply FinitePayment34.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h34
    · exact (lt_of_not_ge h33).le
  by_cases h35 : logb 2 (Fintype.card V)≤(((17200463917739045433367339/116779687257754820648000):ℚ):ℝ)
  · apply FinitePayment35.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h35
    · exact (lt_of_not_ge h34).le
  by_cases h36 : logb 2 (Fintype.card V)≤(((1084028442136155390589677/7298730453609676290500):ℚ):ℝ)
  · apply FinitePayment36.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h36
    · exact (lt_of_not_ge h35).le
  by_cases h37 : logb 2 (Fintype.card V)≤(((699537849224717082620093/4671187490310192825920):ℚ):ℝ)
  · apply FinitePayment37.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h37
    · exact (lt_of_not_ge h36).le
  by_cases h38 : logb 2 (Fintype.card V)≤(((8816218693528683940784909/58389843628877410324000):ℚ):ℝ)
  · apply FinitePayment38.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h38
    · exact (lt_of_not_ge h37).le
  by_cases h39 : logb 2 (Fintype.card V)≤(((17776428543496808697637311/116779687257754820648000):ℚ):ℝ)
  · apply FinitePayment39.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h39
    · exact (lt_of_not_ge h38).le
  by_cases h40 : logb 2 (Fintype.card V)≤(((4480104924984062378426201/29194921814438705162000):ℚ):ℝ)
  · apply FinitePayment40.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h40
    · exact (lt_of_not_ge h39).le
  by_cases h41 : logb 2 (Fintype.card V)≤(((18064410856375690329772297/116779687257754820648000):ℚ):ℝ)
  · apply FinitePayment41.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h41
    · exact (lt_of_not_ge h40).le
  by_cases h42 : logb 2 (Fintype.card V)≤(((1820840201281513114583979/11677968725775482064800):ℚ):ℝ)
  · apply FinitePayment42.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h42
    · exact (lt_of_not_ge h41).le
  by_cases h43 : logb 2 (Fintype.card V)≤(((18352393169254571961907283/116779687257754820648000):ℚ):ℝ)
  · apply FinitePayment43.graph_bound G
    · exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp h43
    · exact (lt_of_not_ge h42).le
  exact FinitePayment44.graph_bound G hn (lt_of_not_ge h43).le

/-- The main finite-average-degree case is valid at every graph order.
For larger orders, monotonicity pays the last finite certificate. -/
theorem finite_degree_potential {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^mainDegreeLog*Fintype.card V) :
    ∃ P : Cycle13.CyclePacking G,
      P.weight≤C*orderPotential (Fintype.card V)*Fintype.card V := by
  by_cases hn : (Fintype.card V:ℝ)≤(2:ℝ)^mainDegreeLog
  · exact finite_order_potential G hn
  have hcard : (2:ℝ)^mainDegreeLog≤Fintype.card V := (lt_of_not_ge hn).le
  have hpos : (0:ℝ)<Fintype.card V := (rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).trans_le hcard
  have hlog : mainDegreeLog≤logb 2 (Fintype.card V) :=
    (le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) hpos).mpr hcard
  have hlo : (((18352393169254571961907283/116779687257754820648000):ℚ):ℝ)≤logb 2 (Fintype.card V) :=
    (show (((18352393169254571961907283/116779687257754820648000):ℚ):ℝ) ≤ mainDegreeLog by norm_num [mainDegreeLog]).trans hlog
  exact potential_weight_from_fee G FinitePayment44.fee_bound hlo
    (FiniteAverageBounds.cutoff042 G hd)

end
end Cycle12.Global12
