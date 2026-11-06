import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay075
import Cycle12.CutFailureCertificates.Decay076
import Cycle12.CutFailureCertificates.Decay077

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget030

def certificate600 : RatFailureBudget := ⟨(18356026277332973089/250000000000000000),(1155308916477511/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay075.certificate1500),(2,CutFailureCertificates.Decay075.certificate1501),(2,CutFailureCertificates.Decay075.certificate1502)]⟩
theorem numericValid600 : certificate600.NumericValid := by decide +kernel
theorem sound600 : certificate600.Sound := rat_failure_budget_sound certificate600 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay075.sound1500,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay075.sound1501,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay075.sound1502,List.forall_mem_nil _⟩⟩⟩) numericValid600

def certificate601 : RatFailureBudget := ⟨(18356026277332973089/250000000000000000),(5846688030570963/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay075.certificate1503),(2,CutFailureCertificates.Decay075.certificate1504)]⟩
theorem numericValid601 : certificate601.NumericValid := by decide +kernel
theorem sound601 : certificate601.Sound := rat_failure_budget_sound certificate601 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay075.sound1503,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay075.sound1504,List.forall_mem_nil _⟩⟩) numericValid601

def certificate602 : RatFailureBudget := ⟨(14383096214428220263/200000000000000000),(580607772467331/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay075.certificate1505),(2,CutFailureCertificates.Decay075.certificate1506),(2,CutFailureCertificates.Decay075.certificate1507)]⟩
theorem numericValid602 : certificate602.NumericValid := by decide +kernel
theorem sound602 : certificate602.Sound := rat_failure_budget_sound certificate602 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay075.sound1505,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay075.sound1506,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay075.sound1507,List.forall_mem_nil _⟩⟩⟩) numericValid602

def certificate603 : RatFailureBudget := ⟨(14383096214428220263/200000000000000000),(5901616025131987/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay075.certificate1508),(2,CutFailureCertificates.Decay075.certificate1509)]⟩
theorem numericValid603 : certificate603.NumericValid := by decide +kernel
theorem sound603 : certificate603.Sound := rat_failure_budget_sound certificate603 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay075.sound1508,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay075.sound1509,List.forall_mem_nil _⟩⟩) numericValid603

def certificate604 : RatFailureBudget := ⟨(35224094784572717727/500000000000000000),(469084398062279/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay075.certificate1510),(2,CutFailureCertificates.Decay075.certificate1511),(2,CutFailureCertificates.Decay075.certificate1512)]⟩
theorem numericValid604 : certificate604.NumericValid := by decide +kernel
theorem sound604 : certificate604.Sound := rat_failure_budget_sound certificate604 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay075.sound1510,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay075.sound1511,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay075.sound1512,List.forall_mem_nil _⟩⟩⟩) numericValid604

def certificate605 : RatFailureBudget := ⟨(35224094784572717727/500000000000000000),(238839527843059/40000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay075.certificate1513),(2,CutFailureCertificates.Decay075.certificate1514)]⟩
theorem numericValid605 : certificate605.NumericValid := by decide +kernel
theorem sound605 : certificate605.Sound := rat_failure_budget_sound certificate605 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay075.sound1513,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay075.sound1514,List.forall_mem_nil _⟩⟩) numericValid605

def certificate606 : RatFailureBudget := ⟨(269612376137375753/3906250000000000),(2384885914051837/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay075.certificate1515),(2,CutFailureCertificates.Decay075.certificate1516),(2,CutFailureCertificates.Decay075.certificate1517)]⟩
theorem numericValid606 : certificate606.NumericValid := by decide +kernel
theorem sound606 : certificate606.Sound := rat_failure_budget_sound certificate606 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay075.sound1515,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay075.sound1516,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay075.sound1517,List.forall_mem_nil _⟩⟩⟩) numericValid606

def certificate607 : RatFailureBudget := ⟨(269612376137375753/3906250000000000),(6072106757780307/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay075.certificate1518),(2,CutFailureCertificates.Decay075.certificate1519)]⟩
theorem numericValid607 : certificate607.NumericValid := by decide +kernel
theorem sound607 : certificate607.Sound := rat_failure_budget_sound certificate607 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay075.sound1518,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay075.sound1519,List.forall_mem_nil _⟩⟩) numericValid607

def certificate608 : RatFailureBudget := ⟨(67631818480710712871/1000000000000000000),(4837521270437589/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay076.certificate1520),(2,CutFailureCertificates.Decay076.certificate1521),(2,CutFailureCertificates.Decay076.certificate1522)]⟩
theorem numericValid608 : certificate608.NumericValid := by decide +kernel
theorem sound608 : certificate608.Sound := rat_failure_budget_sound certificate608 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay076.sound1520,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay076.sound1521,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay076.sound1522,List.forall_mem_nil _⟩⟩⟩) numericValid608

def certificate609 : RatFailureBudget := ⟨(67631818480710712871/1000000000000000000),(6140671009140629/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay076.certificate1523),(2,CutFailureCertificates.Decay076.certificate1524)]⟩
theorem numericValid609 : certificate609.NumericValid := by decide +kernel
theorem sound609 : certificate609.Sound := rat_failure_budget_sound certificate609 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay076.sound1523,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay076.sound1524,List.forall_mem_nil _⟩⟩) numericValid609

def certificate610 : RatFailureBudget := ⟨(33140000829945450993/500000000000000000),(1225895625067137/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay076.certificate1525),(2,CutFailureCertificates.Decay076.certificate1526),(2,CutFailureCertificates.Decay076.certificate1527)]⟩
theorem numericValid610 : certificate610.NumericValid := by decide +kernel
theorem sound610 : certificate610.Sound := rat_failure_budget_sound certificate610 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay076.sound1525,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay076.sound1526,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay076.sound1527,List.forall_mem_nil _⟩⟩⟩) numericValid610

def certificate611 : RatFailureBudget := ⟨(33140000829945450993/500000000000000000),(1551639855447429/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay076.certificate1528),(2,CutFailureCertificates.Decay076.certificate1529)]⟩
theorem numericValid611 : certificate611.NumericValid := by decide +kernel
theorem sound611 : certificate611.Sound := rat_failure_budget_sound certificate611 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay076.sound1528,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay076.sound1529,List.forall_mem_nil _⟩⟩) numericValid611

def certificate612 : RatFailureBudget := ⟨(64964036552798129819/1000000000000000000),(4965938582397393/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay076.certificate1530),(2,CutFailureCertificates.Decay076.certificate1531),(2,CutFailureCertificates.Decay076.certificate1532)]⟩
theorem numericValid612 : certificate612.NumericValid := by decide +kernel
theorem sound612 : certificate612.Sound := rat_failure_budget_sound certificate612 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay076.sound1530,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay076.sound1531,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay076.sound1532,List.forall_mem_nil _⟩⟩⟩) numericValid612

def certificate613 : RatFailureBudget := ⟨(64964036552798129819/1000000000000000000),(3154452329580357/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay076.certificate1533),(2,CutFailureCertificates.Decay076.certificate1534)]⟩
theorem numericValid613 : certificate613.NumericValid := by decide +kernel
theorem sound613 : certificate613.Sound := rat_failure_budget_sound certificate613 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay076.sound1533,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay076.sound1534,List.forall_mem_nil _⟩⟩) numericValid613

def certificate614 : RatFailureBudget := ⟨(63682696189192671051/1000000000000000000),(502618733902497/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay076.certificate1535),(2,CutFailureCertificates.Decay076.certificate1536),(2,CutFailureCertificates.Decay076.certificate1537)]⟩
theorem numericValid614 : certificate614.NumericValid := by decide +kernel
theorem sound614 : certificate614.Sound := rat_failure_budget_sound certificate614 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay076.sound1535,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay076.sound1536,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay076.sound1537,List.forall_mem_nil _⟩⟩⟩) numericValid614

def certificate615 : RatFailureBudget := ⟨(63682696189192671051/1000000000000000000),(3189931050218787/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay076.certificate1538),(2,CutFailureCertificates.Decay076.certificate1539)]⟩
theorem numericValid615 : certificate615.NumericValid := by decide +kernel
theorem sound615 : certificate615.Sound := rat_failure_budget_sound certificate615 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay076.sound1538,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay076.sound1539,List.forall_mem_nil _⟩⟩) numericValid615

def certificate616 : RatFailureBudget := ⟨(15608701294364362167/250000000000000000),(1019944663115687/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay077.certificate1540),(2,CutFailureCertificates.Decay077.certificate1541),(2,CutFailureCertificates.Decay077.certificate1542)]⟩
theorem numericValid616 : certificate616.NumericValid := by decide +kernel
theorem sound616 : certificate616.Sound := rat_failure_budget_sound certificate616 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay077.sound1540,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay077.sound1541,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay077.sound1542,List.forall_mem_nil _⟩⟩⟩) numericValid616

def certificate617 : RatFailureBudget := ⟨(15608701294364362167/250000000000000000),(81058557600049/12500000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay077.certificate1543),(2,CutFailureCertificates.Decay077.certificate1544)]⟩
theorem numericValid617 : certificate617.NumericValid := by decide +kernel
theorem sound617 : certificate617.Sound := rat_failure_budget_sound certificate617 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay077.sound1543,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay077.sound1544,List.forall_mem_nil _⟩⟩) numericValid617

def certificate618 : RatFailureBudget := ⟨(1530480928390214573/25000000000000000),(5169802094074843/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay077.certificate1545),(2,CutFailureCertificates.Decay077.certificate1546),(2,CutFailureCertificates.Decay077.certificate1547)]⟩
theorem numericValid618 : certificate618.NumericValid := by decide +kernel
theorem sound618 : certificate618.Sound := rat_failure_budget_sound certificate618 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay077.sound1545,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay077.sound1546,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay077.sound1547,List.forall_mem_nil _⟩⟩⟩) numericValid618

def certificate619 : RatFailureBudget := ⟨(1530480928390214573/25000000000000000),(6554328312906531/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay077.certificate1548),(2,CutFailureCertificates.Decay077.certificate1549)]⟩
theorem numericValid619 : certificate619.NumericValid := by decide +kernel
theorem sound619 : certificate619.Sound := rat_failure_budget_sound certificate619 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay077.sound1548,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay077.sound1549,List.forall_mem_nil _⟩⟩) numericValid619

end Cycle12.CutFailureCertificates.Budget030
