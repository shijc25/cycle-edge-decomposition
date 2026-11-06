import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay010
import Cycle12.CutFailureCertificates.Decay011
import Cycle12.CutFailureCertificates.Decay012

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget004

def certificate80 : RatFailureBudget := ⟨(37419646445651247031/1000000000000000000),(2629018621975111/200000000000000000),(613976205110301607/1000000000000000000),[(2,CutFailureCertificates.Decay010.certificate200),(2,CutFailureCertificates.Decay010.certificate201),(2,CutFailureCertificates.Decay010.certificate202)]⟩
theorem numericValid80 : certificate80.NumericValid := by decide +kernel
theorem sound80 : certificate80.Sound := rat_failure_budget_sound certificate80 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay010.sound200,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay010.sound201,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay010.sound202,List.forall_mem_nil _⟩⟩⟩) numericValid80

def certificate81 : RatFailureBudget := ⟨(37419646445651247031/1000000000000000000),(10833550643570369/1000000000000000000),(31624953648677/1000000000000000000),[(2,CutFailureCertificates.Decay010.certificate203),(2,CutFailureCertificates.Decay010.certificate204)]⟩
theorem numericValid81 : certificate81.NumericValid := by decide +kernel
theorem sound81 : certificate81.Sound := rat_failure_budget_sound certificate81 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay010.sound203,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay010.sound204,List.forall_mem_nil _⟩⟩) numericValid81

def certificate82 : RatFailureBudget := ⟨(454153372289573681/12500000000000000),(12775448736124257/1000000000000000000),(179033632678931761/500000000000000000),[(2,CutFailureCertificates.Decay010.certificate205),(2,CutFailureCertificates.Decay010.certificate206),(2,CutFailureCertificates.Decay010.certificate207)]⟩
theorem numericValid82 : certificate82.NumericValid := by decide +kernel
theorem sound82 : certificate82.Sound := rat_failure_budget_sound certificate82 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay010.sound205,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay010.sound206,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay010.sound207,List.forall_mem_nil _⟩⟩⟩) numericValid82

def certificate83 : RatFailureBudget := ⟨(454153372289573681/12500000000000000),(11049719882304171/1000000000000000000),(693637831829/200000000000000000),[(2,CutFailureCertificates.Decay010.certificate208),(2,CutFailureCertificates.Decay010.certificate209)]⟩
theorem numericValid83 : certificate83.NumericValid := by decide +kernel
theorem sound83 : certificate83.Sound := rat_failure_budget_sound certificate83 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay010.sound208,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay010.sound209,List.forall_mem_nil _⟩⟩) numericValid83

def certificate84 : RatFailureBudget := ⟨(35288751458599140089/1000000000000000000),(6667288727164741/500000000000000000),(10528749200458689/25000000000000000),[(2,CutFailureCertificates.Decay010.certificate210),(2,CutFailureCertificates.Decay010.certificate211),(2,CutFailureCertificates.Decay010.certificate212)]⟩
theorem numericValid84 : certificate84.NumericValid := by decide +kernel
theorem sound84 : certificate84.Sound := rat_failure_budget_sound certificate84 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay010.sound210,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay010.sound211,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay010.sound212,List.forall_mem_nil _⟩⟩⟩) numericValid84

def certificate85 : RatFailureBudget := ⟨(35288751458599140089/1000000000000000000),(11328473703785713/1000000000000000000),(1334745861849/500000000000000000),[(2,CutFailureCertificates.Decay010.certificate213),(2,CutFailureCertificates.Decay010.certificate214)]⟩
theorem numericValid85 : certificate85.NumericValid := by decide +kernel
theorem sound85 : certificate85.Sound := rat_failure_budget_sound certificate85 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay010.sound213,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay010.sound214,List.forall_mem_nil _⟩⟩) numericValid85

def certificate86 : RatFailureBudget := ⟨(17143398367560799813/500000000000000000),(13621866736788031/1000000000000000000),(433575735585478869/1000000000000000000),[(2,CutFailureCertificates.Decay010.certificate215),(2,CutFailureCertificates.Decay010.certificate216),(2,CutFailureCertificates.Decay010.certificate217)]⟩
theorem numericValid86 : certificate86.NumericValid := by decide +kernel
theorem sound86 : certificate86.Sound := rat_failure_budget_sound certificate86 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay010.sound215,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay010.sound216,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay010.sound217,List.forall_mem_nil _⟩⟩⟩) numericValid86

def certificate87 : RatFailureBudget := ⟨(17143398367560799813/500000000000000000),(1452244448909963/125000000000000000),(396855011183/200000000000000000),[(2,CutFailureCertificates.Decay010.certificate218),(2,CutFailureCertificates.Decay010.certificate219)]⟩
theorem numericValid87 : certificate87.NumericValid := by decide +kernel
theorem sound87 : certificate87.Sound := rat_failure_budget_sound certificate87 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay010.sound218,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay010.sound219,List.forall_mem_nil _⟩⟩) numericValid87

def certificate88 : RatFailureBudget := ⟨(16662129108879638001/500000000000000000),(13894742652031287/1000000000000000000),(116835668920648213/250000000000000000),[(2,CutFailureCertificates.Decay011.certificate220),(2,CutFailureCertificates.Decay011.certificate221),(2,CutFailureCertificates.Decay011.certificate222)]⟩
theorem numericValid88 : certificate88.NumericValid := by decide +kernel
theorem sound88 : certificate88.Sound := rat_failure_budget_sound certificate88 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay011.sound220,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay011.sound221,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay011.sound222,List.forall_mem_nil _⟩⟩⟩) numericValid88

def certificate89 : RatFailureBudget := ⟨(16662129108879638001/500000000000000000),(11903381040463489/1000000000000000000),(1494981730533/1000000000000000000),[(2,CutFailureCertificates.Decay011.certificate223),(2,CutFailureCertificates.Decay011.certificate224)]⟩
theorem numericValid89 : certificate89.NumericValid := by decide +kernel
theorem sound89 : certificate89.Sound := rat_failure_budget_sound certificate89 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay011.sound223,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay011.sound224,List.forall_mem_nil _⟩⟩) numericValid89

def certificate90 : RatFailureBudget := ⟨(32399124674329550227/1000000000000000000),(7109919609915963/500000000000000000),(120611010908802259/250000000000000000),[(2,CutFailureCertificates.Decay011.certificate225),(2,CutFailureCertificates.Decay011.certificate226),(2,CutFailureCertificates.Decay011.certificate227)]⟩
theorem numericValid90 : certificate90.NumericValid := by decide +kernel
theorem sound90 : certificate90.Sound := rat_failure_budget_sound certificate90 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay011.sound225,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay011.sound226,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay011.sound227,List.forall_mem_nil _⟩⟩⟩) numericValid90

def certificate91 : RatFailureBudget := ⟨(32399124674329550227/1000000000000000000),(3047899281067909/250000000000000000),(11937515107/10000000000000000),[(2,CutFailureCertificates.Decay011.certificate228),(2,CutFailureCertificates.Decay011.certificate229)]⟩
theorem numericValid91 : certificate91.NumericValid := by decide +kernel
theorem sound91 : certificate91.Sound := rat_failure_budget_sound certificate91 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay011.sound228,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay011.sound229,List.forall_mem_nil _⟩⟩) numericValid91

def certificate92 : RatFailureBudget := ⟨(31509510832091315197/1000000000000000000),(14968935979477859/1000000000000000000),(494467725120332689/1000000000000000000),[(2,CutFailureCertificates.Decay011.certificate230),(2,CutFailureCertificates.Decay011.certificate231),(2,CutFailureCertificates.Decay011.certificate232)]⟩
theorem numericValid92 : certificate92.NumericValid := by decide +kernel
theorem sound92 : certificate92.Sound := rat_failure_budget_sound certificate92 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay011.sound230,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay011.sound231,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay011.sound232,List.forall_mem_nil _⟩⟩⟩) numericValid92

def certificate93 : RatFailureBudget := ⟨(31509510832091315197/1000000000000000000),(2500793808381299/200000000000000000),(48269508765411/1000000000000000000),[(2,CutFailureCertificates.Decay011.certificate233),(2,CutFailureCertificates.Decay011.certificate234)]⟩
theorem numericValid93 : certificate93.NumericValid := by decide +kernel
theorem sound93 : certificate93.Sound := rat_failure_budget_sound certificate93 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay011.sound233,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay011.sound234,List.forall_mem_nil _⟩⟩) numericValid93

def certificate94 : RatFailureBudget := ⟨(3831706006758833737/125000000000000000),(7425470907306759/500000000000000000),(484011691482895941/1000000000000000000),[(2,CutFailureCertificates.Decay011.certificate235),(2,CutFailureCertificates.Decay011.certificate236),(2,CutFailureCertificates.Decay011.certificate237)]⟩
theorem numericValid94 : certificate94.NumericValid := by decide +kernel
theorem sound94 : certificate94.Sound := rat_failure_budget_sound certificate94 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay011.sound235,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay011.sound236,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay011.sound237,List.forall_mem_nil _⟩⟩⟩) numericValid94

def certificate95 : RatFailureBudget := ⟨(3831706006758833737/125000000000000000),(12797195991526991/1000000000000000000),(17151551785911/500000000000000000),[(2,CutFailureCertificates.Decay011.certificate238),(2,CutFailureCertificates.Decay011.certificate239)]⟩
theorem numericValid95 : certificate95.NumericValid := by decide +kernel
theorem sound95 : certificate95.Sound := rat_failure_budget_sound certificate95 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay011.sound238,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay011.sound239,List.forall_mem_nil _⟩⟩) numericValid95

def certificate96 : RatFailureBudget := ⟨(29829875809522449283/1000000000000000000),(3835898736562463/250000000000000000),(48704100918499177/100000000000000000),[(2,CutFailureCertificates.Decay012.certificate240),(2,CutFailureCertificates.Decay012.certificate241),(2,CutFailureCertificates.Decay012.certificate242)]⟩
theorem numericValid96 : certificate96.NumericValid := by decide +kernel
theorem sound96 : certificate96.Sound := rat_failure_budget_sound certificate96 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay012.sound240,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay012.sound241,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay012.sound242,List.forall_mem_nil _⟩⟩⟩) numericValid96

def certificate97 : RatFailureBudget := ⟨(29829875809522449283/1000000000000000000),(6546955931491901/500000000000000000),(995813061759/40000000000000000),[(2,CutFailureCertificates.Decay012.certificate243),(2,CutFailureCertificates.Decay012.certificate244)]⟩
theorem numericValid97 : certificate97.NumericValid := by decide +kernel
theorem sound97 : certificate97.Sound := rat_failure_budget_sound certificate97 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay012.sound243,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay012.sound244,List.forall_mem_nil _⟩⟩) numericValid97

def certificate98 : RatFailureBudget := ⟨(14518316931113660067/500000000000000000),(15950810463922627/1000000000000000000),(497694712867358153/1000000000000000000),[(2,CutFailureCertificates.Decay012.certificate245),(2,CutFailureCertificates.Decay012.certificate246),(2,CutFailureCertificates.Decay012.certificate247)]⟩
theorem numericValid98 : certificate98.NumericValid := by decide +kernel
theorem sound98 : certificate98.Sound := rat_failure_budget_sound certificate98 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay012.sound245,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay012.sound246,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay012.sound247,List.forall_mem_nil _⟩⟩⟩) numericValid98

def certificate99 : RatFailureBudget := ⟨(14518316931113660067/500000000000000000),(13404455762886387/1000000000000000000),(4856286358381/250000000000000000),[(2,CutFailureCertificates.Decay012.certificate248),(2,CutFailureCertificates.Decay012.certificate249)]⟩
theorem numericValid99 : certificate99.NumericValid := by decide +kernel
theorem sound99 : certificate99.Sound := rat_failure_budget_sound certificate99 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay012.sound248,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay012.sound249,List.forall_mem_nil _⟩⟩) numericValid99

end Cycle12.CutFailureCertificates.Budget004
