import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay097
import Cycle12.CutFailureCertificates.Decay098
import Cycle12.CutFailureCertificates.Decay099

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget039

def certificate780 : RatFailureBudget := ⟨(312854493878473221417/1000000000000000000),(1069050649535161/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay097.certificate1950),(2,CutFailureCertificates.Decay097.certificate1951),(2,CutFailureCertificates.Decay097.certificate1952)]⟩
theorem numericValid780 : certificate780.NumericValid := by decide +kernel
theorem sound780 : certificate780.Sound := rat_failure_budget_sound certificate780 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay097.sound1950,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay097.sound1951,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay097.sound1952,List.forall_mem_nil _⟩⟩⟩) numericValid780

def certificate781 : RatFailureBudget := ⟨(312854493878473221417/1000000000000000000),(1074418083213153/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay097.certificate1953),(2,CutFailureCertificates.Decay097.certificate1954)]⟩
theorem numericValid781 : certificate781.NumericValid := by decide +kernel
theorem sound781 : certificate781.Sound := rat_failure_budget_sound certificate781 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay097.sound1953,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay097.sound1954,List.forall_mem_nil _⟩⟩) numericValid781

def certificate782 : RatFailureBudget := ⟨(306286155555872753049/1000000000000000000),(2705616924123/2500000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay097.certificate1955),(2,CutFailureCertificates.Decay097.certificate1956),(2,CutFailureCertificates.Decay097.certificate1957)]⟩
theorem numericValid782 : certificate782.NumericValid := by decide +kernel
theorem sound782 : certificate782.Sound := rat_failure_budget_sound certificate782 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay097.sound1955,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay097.sound1956,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay097.sound1957,List.forall_mem_nil _⟩⟩⟩) numericValid782

def certificate783 : RatFailureBudget := ⟨(306286155555872753049/1000000000000000000),(2190173730289459/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay097.certificate1958),(2,CutFailureCertificates.Decay097.certificate1959)]⟩
theorem numericValid783 : certificate783.NumericValid := by decide +kernel
theorem sound783 : certificate783.Sound := rat_failure_budget_sound certificate783 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay097.sound1958,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay097.sound1959,List.forall_mem_nil _⟩⟩) numericValid783

def certificate784 : RatFailureBudget := ⟨(18356026277332973089/62500000000000000),(69920803186093/62500000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay098.certificate1960),(2,CutFailureCertificates.Decay098.certificate1961),(2,CutFailureCertificates.Decay098.certificate1962)]⟩
theorem numericValid784 : certificate784.NumericValid := by decide +kernel
theorem sound784 : certificate784.Sound := rat_failure_budget_sound certificate784 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay098.sound1960,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay098.sound1961,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay098.sound1962,List.forall_mem_nil _⟩⟩⟩) numericValid784

def certificate785 : RatFailureBudget := ⟨(18356026277332973089/62500000000000000),(2259092881473027/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay098.certificate1963),(2,CutFailureCertificates.Decay098.certificate1964)]⟩
theorem numericValid785 : certificate785.NumericValid := by decide +kernel
theorem sound785 : certificate785.Sound := rat_failure_budget_sound certificate785 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay098.sound1963,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay098.sound1964,List.forall_mem_nil _⟩⟩) numericValid785

def certificate786 : RatFailureBudget := ⟨(140896379138290870909/500000000000000000),(229339070448639/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay098.certificate1965),(2,CutFailureCertificates.Decay098.certificate1966),(2,CutFailureCertificates.Decay098.certificate1967)]⟩
theorem numericValid786 : certificate786.NumericValid := by decide +kernel
theorem sound786 : certificate786.Sound := rat_failure_budget_sound certificate786 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay098.sound1965,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay098.sound1966,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay098.sound1967,List.forall_mem_nil _⟩⟩⟩) numericValid786

def certificate787 : RatFailureBudget := ⟨(140896379138290870909/500000000000000000),(46555799185807/20000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay098.certificate1968),(2,CutFailureCertificates.Decay098.certificate1969)]⟩
theorem numericValid787 : certificate787.NumericValid := by decide +kernel
theorem sound787 : certificate787.Sound := rat_failure_budget_sound certificate787 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay098.sound1968,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay098.sound1969,List.forall_mem_nil _⟩⟩) numericValid787

def certificate788 : RatFailureBudget := ⟨(269612376137375753/976562500000000),(1147267020442819/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay098.certificate1970),(2,CutFailureCertificates.Decay098.certificate1971),(2,CutFailureCertificates.Decay098.certificate1972)]⟩
theorem numericValid788 : certificate788.NumericValid := by decide +kernel
theorem sound788 : certificate788.Sound := rat_failure_budget_sound certificate788 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay098.sound1970,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay098.sound1971,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay098.sound1972,List.forall_mem_nil _⟩⟩⟩) numericValid788

def certificate789 : RatFailureBudget := ⟨(269612376137375753/976562500000000),(1174765068759551/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay098.certificate1973),(2,CutFailureCertificates.Decay098.certificate1974)]⟩
theorem numericValid789 : certificate789.NumericValid := by decide +kernel
theorem sound789 : certificate789.Sound := rat_failure_budget_sound certificate789 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay098.sound1973,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay098.sound1974,List.forall_mem_nil _⟩⟩) numericValid789

def certificate790 : RatFailureBudget := ⟨(54105454784568570297/200000000000000000),(1161949960353931/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay098.certificate1975),(2,CutFailureCertificates.Decay098.certificate1976),(2,CutFailureCertificates.Decay098.certificate1977)]⟩
theorem numericValid790 : certificate790.NumericValid := by decide +kernel
theorem sound790 : certificate790.Sound := rat_failure_budget_sound certificate790 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay098.sound1975,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay098.sound1976,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay098.sound1977,List.forall_mem_nil _⟩⟩⟩) numericValid790

def certificate791 : RatFailureBudget := ⟨(54105454784568570297/200000000000000000),(477292950494341/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay098.certificate1978),(2,CutFailureCertificates.Decay098.certificate1979)]⟩
theorem numericValid791 : certificate791.NumericValid := by decide +kernel
theorem sound791 : certificate791.Sound := rat_failure_budget_sound certificate791 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay098.sound1978,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay098.sound1979,List.forall_mem_nil _⟩⟩) numericValid791

def certificate792 : RatFailureBudget := ⟨(265120006639563607947/1000000000000000000),(293722283976133/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay099.certificate1980),(2,CutFailureCertificates.Decay099.certificate1981),(2,CutFailureCertificates.Decay099.certificate1982)]⟩
theorem numericValid792 : certificate792.NumericValid := by decide +kernel
theorem sound792 : certificate792.Sound := rat_failure_budget_sound certificate792 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay099.sound1980,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay099.sound1981,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay099.sound1982,List.forall_mem_nil _⟩⟩⟩) numericValid792

def certificate793 : RatFailureBudget := ⟨(265120006639563607947/1000000000000000000),(2413241820361921/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay099.certificate1983),(2,CutFailureCertificates.Decay099.certificate1984)]⟩
theorem numericValid793 : certificate793.NumericValid := by decide +kernel
theorem sound793 : certificate793.Sound := rat_failure_budget_sound certificate793 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay099.sound1983,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay099.sound1984,List.forall_mem_nil _⟩⟩) numericValid793

def certificate794 : RatFailureBudget := ⟨(64964036552798129819/250000000000000000),(5929132921519/5000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay099.certificate1985),(2,CutFailureCertificates.Decay099.certificate1986),(2,CutFailureCertificates.Decay099.certificate1987)]⟩
theorem numericValid794 : certificate794.NumericValid := by decide +kernel
theorem sound794 : certificate794.Sound := rat_failure_budget_sound certificate794 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay099.sound1985,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay099.sound1986,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay099.sound1987,List.forall_mem_nil _⟩⟩⟩) numericValid794

def certificate795 : RatFailureBudget := ⟨(64964036552798129819/250000000000000000),(1223966172798099/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay099.certificate1988),(2,CutFailureCertificates.Decay099.certificate1989)]⟩
theorem numericValid795 : certificate795.NumericValid := by decide +kernel
theorem sound795 : certificate795.Sound := rat_failure_budget_sound certificate795 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay099.sound1988,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay099.sound1989,List.forall_mem_nil _⟩⟩) numericValid795

def certificate796 : RatFailureBudget := ⟨(254730784756770684207/1000000000000000000),(1200754754073243/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay099.certificate1990),(2,CutFailureCertificates.Decay099.certificate1991),(2,CutFailureCertificates.Decay099.certificate1992)]⟩
theorem numericValid796 : certificate796.NumericValid := by decide +kernel
theorem sound796 : certificate796.Sound := rat_failure_budget_sound certificate796 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay099.sound1990,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay099.sound1991,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay099.sound1992,List.forall_mem_nil _⟩⟩⟩) numericValid796

def certificate797 : RatFailureBudget := ⟨(254730784756770684207/1000000000000000000),(496523331325943/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay099.certificate1993),(2,CutFailureCertificates.Decay099.certificate1994)]⟩
theorem numericValid797 : certificate797.NumericValid := by decide +kernel
theorem sound797 : certificate797.Sound := rat_failure_budget_sound certificate797 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay099.sound1993,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay099.sound1994,List.forall_mem_nil _⟩⟩) numericValid797

def certificate798 : RatFailureBudget := ⟨(9989568828393191787/40000000000000000),(1211575020657649/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay099.certificate1995),(2,CutFailureCertificates.Decay099.certificate1996),(2,CutFailureCertificates.Decay099.certificate1997)]⟩
theorem numericValid798 : certificate798.NumericValid := by decide +kernel
theorem sound798 : certificate798.Sound := rat_failure_budget_sound certificate798 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay099.sound1995,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay099.sound1996,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay099.sound1997,List.forall_mem_nil _⟩⟩⟩) numericValid798

def certificate799 : RatFailureBudget := ⟨(9989568828393191787/40000000000000000),(629390440745259/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay099.certificate1998),(2,CutFailureCertificates.Decay099.certificate1999)]⟩
theorem numericValid799 : certificate799.NumericValid := by decide +kernel
theorem sound799 : certificate799.Sound := rat_failure_budget_sound certificate799 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay099.sound1998,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay099.sound1999,List.forall_mem_nil _⟩⟩) numericValid799

end Cycle12.CutFailureCertificates.Budget039
