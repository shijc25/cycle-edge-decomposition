import Cycle12.FiniteAverageBounds
import Cycle12.FiniteDegreeCaps.Cap000
import Cycle12.FiniteDegreeCaps.Cap001
import Cycle12.FiniteDegreeCaps.Cap002
import Cycle12.FiniteDegreeCaps.Cap003
import Cycle12.FiniteDegreeCaps.Cap004
import Cycle12.FiniteDegreeCaps.Cap005
import Cycle12.FiniteDegreeCaps.Cap006
import Cycle12.FiniteDegreeCaps.Cap007
import Cycle12.FiniteDegreeCaps.Cap008
import Cycle12.FiniteDegreeCaps.Cap009
import Cycle12.FiniteDegreeCaps.Cap010
import Cycle12.FiniteDegreeCaps.Cap011
import Cycle12.FiniteDegreeCaps.Cap012
import Cycle12.FiniteDegreeCaps.Cap013
import Cycle12.FiniteDegreeCaps.Cap014
import Cycle12.FiniteDegreeCaps.Cap015
import Cycle12.FiniteDegreeCaps.Cap016
import Cycle12.FiniteDegreeCaps.Cap017
import Cycle12.FiniteDegreeCaps.Cap018
import Cycle12.FiniteDegreeCaps.Cap019
import Cycle12.FiniteDegreeCaps.Cap020
import Cycle12.FiniteDegreeCaps.Cap021
import Cycle12.FiniteDegreeCaps.Cap022
import Cycle12.FiniteDegreeCaps.Cap023
import Cycle12.FiniteDegreeCaps.Cap024
import Cycle12.FiniteDegreeCaps.Cap025
import Cycle12.FiniteDegreeCaps.Cap026
import Cycle12.FiniteDegreeCaps.Cap027
import Cycle12.FiniteDegreeCaps.Cap028
import Cycle12.FiniteDegreeCaps.Cap029
import Cycle12.FiniteDegreeCaps.Cap030
import Cycle12.FiniteDegreeCaps.Cap031
import Cycle12.FiniteDegreeCaps.Cap032
import Cycle12.FiniteDegreeCaps.Cap033
import Cycle12.FiniteDegreeCaps.Cap034
import Cycle12.FiniteDegreeCaps.Cap035
import Cycle12.FiniteDegreeCaps.Cap036
import Cycle12.FiniteDegreeCaps.Cap037
import Cycle12.FiniteDegreeCaps.Cap038
import Cycle12.FiniteDegreeCaps.Cap039
import Cycle12.FiniteDegreeCaps.Cap040
import Cycle12.FiniteDegreeCaps.Cap041
import Cycle12.FiniteDegreeCaps.Cap042
import Cycle12.FiniteDegreeCaps.Cap043
import Cycle12.FiniteDegreeCaps.Cap044
import Cycle12.FiniteDegreeCaps.Cap045
import Cycle12.FiniteDegreeCaps.Cap046
import Cycle12.FiniteDegreeCaps.Cap047
import Cycle12.FiniteDegreeCaps.Cap048
import Cycle12.FiniteDegreeCaps.Cap049
import Cycle12.FiniteDegreeCaps.Cap050
import Cycle12.FiniteDegreeCaps.Cap051
import Cycle12.FiniteDegreeCaps.Cap052
import Cycle12.FiniteDegreeCaps.Cap053
import Cycle12.FiniteDegreeCaps.Cap054
import Cycle12.FiniteDegreeCaps.Cap055
import Cycle12.FiniteDegreeCaps.Cap056
import Cycle12.FiniteDegreeCaps.Cap057
import Cycle12.FiniteDegreeCaps.Cap058
import Cycle12.FiniteDegreeCaps.Cap059
import Cycle12.FiniteDegreeCaps.Cap060
import Cycle12.FiniteDegreeCaps.Cap061
import Cycle12.FiniteDegreeCaps.Cap062
import Cycle12.FiniteDegreeCaps.Cap063
import Cycle12.FiniteDegreeCaps.Cap064
import Cycle12.FiniteDegreeCaps.Cap065
import Cycle12.FiniteDegreeCaps.Cap066
import Cycle12.FiniteDegreeCaps.Cap067
import Cycle12.FiniteDegreeCaps.Cap068
import Cycle12.FiniteDegreeCaps.Cap069
import Cycle12.FiniteDegreeCaps.Cap070
import Cycle12.FiniteDegreeCaps.Cap071
import Cycle12.FiniteDegreeCaps.Cap072
import Cycle12.FiniteDegreeCaps.Cap073
import Cycle12.FiniteDegreeCaps.Cap074
import Cycle12.FiniteDegreeCaps.Cap075
import Cycle12.FiniteDegreeCaps.Cap076
import Cycle12.FiniteDegreeCaps.Cap077
import Cycle12.FiniteDegreeCaps.Cap078
import Cycle12.FiniteDegreeCaps.Cap079
import Cycle12.FiniteDegreeCaps.Cap080
import Cycle12.FiniteDegreeCaps.Cap081
import Cycle12.FiniteDegreeCaps.Cap082

namespace Cycle12.FiniteAverageBounds
open Cycle13
noncomputable section

theorem cutoff000 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((1091/8):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain000.costBound:ℝ)*Fintype.card V := by
  apply bound000 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap000.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤112970658092375372859298640165435821012540*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff001 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((1129/8):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain001.costBound:ℝ)*Fintype.card V := by
  apply bound001 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap001.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤3039891885399407640496161951118285510805163*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff002 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((118931/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain002.costBound:ℝ)*Fintype.card V := by
  apply bound002 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap002.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤633575557369027701215608323433572054*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff003 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((118933/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain003.costBound:ℝ)*Fintype.card V := by
  apply bound003 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap003.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤634454488679549842478997164029742901*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff004 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((118941/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain004.costBound:ℝ)*Fintype.card V := by
  apply bound004 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap004.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤637982423873021492762282650366549757*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff005 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((11897/100):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain005.costBound:ℝ)*Fintype.card V := by
  apply bound005 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap005.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤650936439596268340441058798985218262*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff006 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((119239/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain006.costBound:ℝ)*Fintype.card V := by
  apply bound006 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap006.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤784360388534779316570671974773397018*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff007 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((121397/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain007.costBound:ℝ)*Fintype.card V := by
  apply bound007 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap007.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤3500566913449360998380602532430756772*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff008 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((12263/100):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain008.costBound:ℝ)*Fintype.card V := by
  apply bound008 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap008.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤8228266858852988835091968937069229441*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff009 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((123863/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain009.costBound:ℝ)*Fintype.card V := by
  apply bound009 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap009.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤19340974526261641571430635405901671174*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff010 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((126329/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain010.costBound:ℝ)*Fintype.card V := by
  apply bound010 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap010.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤106860775661305767981799913138043897589*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff011 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((127383/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain011.costBound:ℝ)*Fintype.card V := by
  apply bound011 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap011.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤221872735389386493941675456855404527667*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff012 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((129381/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain012.costBound:ℝ)*Fintype.card V := by
  apply bound012 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap012.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤886261470271176549143066578794950581920*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff013 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((131261/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain013.costBound:ℝ)*Fintype.card V := by
  apply bound013 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap013.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤3262107440672726068804752957763647316036*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff014 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((131379/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain014.costBound:ℝ)*Fintype.card V := by
  apply bound014 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap014.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤3540134808852231766646792483867272115968*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff015 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((133377/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain015.costBound:ℝ)*Fintype.card V := by
  apply bound015 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap015.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤14140922160378405116442049797530735223634*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff016 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((133727/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain016.costBound:ℝ)*Fintype.card V := by
  apply bound016 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap016.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤18023462619604755705368505728554919441542*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff017 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((134377/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain017.costBound:ℝ)*Fintype.card V := by
  apply bound017 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap017.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤28281844320756810232884099595061470447267*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff018 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((136193/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain018.costBound:ℝ)*Fintype.card V := by
  apply bound018 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap018.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤99581393534143965369121777346071746617179*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff019 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((138373/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain019.costBound:ℝ)*Fintype.card V := by
  apply bound019 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap019.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤451256624040523736523531848712918757867505*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff020 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((138659/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain020.costBound:ℝ)*Fintype.card V := by
  apply bound020 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap020.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤550196937597083759137319138006078678769123*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff021 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((140371/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain021.costBound:ℝ)*Fintype.card V := by
  apply bound021 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap021.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤1802525931768420610924728584098284233749251*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff022 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((141371/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain022.costBound:ℝ)*Fintype.card V := by
  apply bound022 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap022.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤3605051863536841221849457168196568467498502*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff023 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((14237/100):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain023.costBound:ℝ)*Fintype.card V := by
  apply bound023 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap023.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤7205107795661628692346291366055370776205323*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff024 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((143369/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain024.costBound:ℝ)*Fintype.card V := by
  apply bound024 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap024.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤14400230651930939142935981534369464857602898*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff025 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((143591/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain025.costBound:ℝ)*Fintype.card V := by
  apply bound025 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap025.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤16795699945688221187876399706957768773641286*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff026 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((145367/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain026.costBound:ℝ)*Fintype.card V := by
  apply bound026 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap026.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤57521126097023267414344203098046682104218576*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff027 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((146057/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain027.costBound:ℝ)*Fintype.card V := by
  apply bound027 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap027.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤92797884694681216266763081339696743637575094*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff028 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((14729/100):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain028.costBound:ℝ)*Fintype.card V := by
  apply bound028 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap028.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤218126314418172357851918308863105554711732126*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff029 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((148523/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain029.costBound:ℝ)*Fintype.card V := by
  apply bound029 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap029.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤512717387882252224949043097362666392898070124*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff030 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((14867/125):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain030.costBound:ℝ)*Fintype.card V := by
  apply bound030 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap030.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤635775172365981020656871097119045640*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff031 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((14876/125):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain031.costBound:ℝ)*Fintype.card V := by
  apply bound031 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap031.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤668309637461686303667006309182830588*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff032 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((150363/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain032.costBound:ℝ)*Fintype.card V := by
  apply bound032 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap032.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤1835579665821270196720681221859538388573575915*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff033 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((150989/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain033.costBound:ℝ)*Fintype.card V := by
  apply bound033 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap033.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤2832813708003270942547750922133747110809466749*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff034 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((152361/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain034.costBound:ℝ)*Fintype.card V := by
  apply bound034 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap034.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤7332147100343783966064903925133557246958936853*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff035 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((155359/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain035.costBound:ℝ)*Fintype.card V := by
  apply bound035 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap035.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤58575917027307481933431853115410391538217977357*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff036 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((155921/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain036.costBound:ℝ)*Fintype.card V := by
  apply bound036 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap036.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤86476470133496381824622539010960141854697347951*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff037 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((15637/125):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain037.costBound:ℝ)*Fintype.card V := by
  apply bound037 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap037.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤45461979058570194230553750618457693529*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff038 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((157357/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain038.costBound:ℝ)*Fintype.card V := by
  apply bound038 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap038.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤233979079295144943249741056645766475990008683983*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff039 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((157857/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain039.costBound:ℝ)*Fintype.card V := by
  apply bound039 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap039.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤330896387250763815507700453637257128049470731007*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff040 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((158231/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain040.costBound:ℝ)*Fintype.card V := by
  apply bound040 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap040.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤428822183552157062742188631835523708768739838525*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff041 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((158341/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain041.costBound:ℝ)*Fintype.card V := by
  apply bound041 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap041.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤462797008928972250848313081703056790071330516294*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff042 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((158387/1000):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain042.costBound:ℝ)*Fintype.card V := by
  apply bound042 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap042.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤477790954244295732307933979555897304159874235279*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff043 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((16922/125):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain043.costBound:ℝ)*Fintype.card V := by
  apply bound043 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap043.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤56524495265168054610257913991056981438155*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff044 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((18046/125):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain044.costBound:ℝ)*Fintype.card V := by
  apply bound044 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap044.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤28780505262346231490450551414217538830476226*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff045 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((18103/125):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain045.costBound:ℝ)*Fintype.card V := by
  apply bound045 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap045.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤39479177130817191290082603947867834945483390*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff046 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((19336/125):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain046.costBound:ℝ)*Fintype.card V := by
  apply bound046 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap046.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤36789845946173851273415601531116182343975926952*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff047 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((19794/125):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain047.costBound:ℝ)*Fintype.card V := by
  apply bound047 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap047.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤466339146354012541410070058848129811602951175784*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff048 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((2379/20):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain048.costBound:ℝ)*Fintype.card V := by
  apply bound048 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap048.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤641974805276305857157267965746045865*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff049 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((23817/200):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain049.costBound:ℝ)*Fintype.card V := by
  apply bound049 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap049.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤704947920306252077728042299383419222*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff050 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((25759/200):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain050.costBound:ℝ)*Fintype.card V := by
  apply bound050 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap050.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤590416235719178453698163031795489042151*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff051 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((29473/200):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain051.costBound:ℝ)*Fintype.card V := by
  apply bound051 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap051.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤229765760524536285011143663458710300561139528*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff052 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((29673/200):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain052.costBound:ℝ)*Fintype.card V := by
  apply bound052 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap052.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤459531521049072570022287326917420601122279056*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff053 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((29733/250):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain053.costBound:ℝ)*Fintype.card V := by
  apply bound053 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap053.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤634014870717104921314378551967008356*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff054 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((29887/250):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain054.costBound:ℝ)*Fintype.card V := by
  apply bound054 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap054.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤971703845929592150492965803656520377*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff055 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((30041/250):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain055.costBound:ℝ)*Fintype.card V := by
  apply bound055 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap055.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤1489252709682361412914201481594710078*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff056 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((30691/200):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain056.costBound:ℝ)*Fintype.card V := by
  apply bound056 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap056.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤15651572764866283557533390975155428889086270833*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff057 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((32507/250):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain057.costBound:ℝ)*Fintype.card V := by
  apply bound057 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap057.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤1387804451510915920260764946966757483178*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff058 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((3374/25):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain058.costBound:ℝ)*Fintype.card V := by
  apply bound058 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap058.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤42365097945960121146926278486644754657825*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff059 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((34843/250):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain059.costBound:ℝ)*Fintype.card V := by
  apply bound059 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap059.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤901887890325242653234841072585542127242369*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff060 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((34973/250):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain060.costBound:ℝ)*Fintype.card V := by
  apply bound060 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap060.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤1293266873453804653556125559966894103654592*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff061 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((37341/250):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain061.costBound:ℝ)*Fintype.card V := by
  apply bound061 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap061.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤918426216874059306343638407390554876606939737*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff062 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((37439/250):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain062.costBound:ℝ)*Fintype.card V := by
  apply bound062 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap062.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤1205169218294457710660445741731530953061453634*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff063 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((3834/25):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain063.costBound:ℝ)*Fintype.card V := by
  apply bound063 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap063.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤14654133208445845084091815472796863769924657963*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff064 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((3859/25):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain064.costBound:ℝ)*Fintype.card V := by
  apply bound064 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap064.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤29308266416891690168183630945593727539849315925*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff065 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((39587/250):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain065.costBound:ℝ)*Fintype.card V := by
  apply bound065 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap065.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤465047970473067799169018204287490036104415588528*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff066 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((39589/250):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain066.costBound:ℝ)*Fintype.card V := by
  apply bound066 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap066.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤467633907102027744244712899001195203251276138272*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff067 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((6333/40):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain067.costBound:ℝ)*Fintype.card V := by
  apply bound067 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap067.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤457692782018839814581682734468571644584438050645*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff068 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((63781/500):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain068.costBound:ℝ)*Fintype.card V := by
  apply bound068 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap068.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤251181880142616485903247814849825681574*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff069 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((64191/500):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain069.costBound:ℝ)*Fintype.card V := by
  apply bound069 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap069.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤443437996431615430474331837214057154376*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff070 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((6519/50):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain070.costBound:ℝ)*Fintype.card V := by
  apply bound070 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap070.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤1771294746972267594110951210370077539383*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff071 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((66189/500):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain071.costBound:ℝ)*Fintype.card V := by
  apply bound071 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap071.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤7075363649256870067621444241642950425959*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff072 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((66247/500):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain072.costBound:ℝ)*Fintype.card V := by
  apply bound072 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap072.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤7667755311569313281707891913330983260422*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff073 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((68687/500):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain073.costBound:ℝ)*Fintype.card V := by
  apply bound073 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap073.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤225784759863019948870530981952638304322580*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff074 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((68713/500):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain074.costBound:ℝ)*Fintype.card V := by
  apply bound074 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap074.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤234071309143466037595495689614326634279890*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff075 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((71179/500):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain075.costBound:ℝ)*Fintype.card V := by
  apply bound075 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap075.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤7145425947730540662152473221134677343344963*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff076 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((73183/500):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain076.costBound:ℝ)*Fintype.card V := by
  apply bound076 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap076.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤114962538611107151245557099400631622119843401*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff077 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((75681/500):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain077.costBound:ℝ)*Fintype.card V := by
  apply bound077 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap077.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤3668615559608479642466654557436404169499093393*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff078 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((76111/500):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain078.costBound:ℝ)*Fintype.card V := by
  apply bound078 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap078.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤6658677787678561657711803870837937961122951918*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff079 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((78179/500):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain079.costBound:ℝ)*Fintype.card V := by
  apply bound079 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap079.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤117070658727617178208706121255070553593363867540*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff080 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((78577/500):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain080.costBound:ℝ)*Fintype.card V := by
  apply bound080 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap080.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤203267496626395180845420118032383754425194337737*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff081 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((79053/500):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain081.costBound:ℝ)*Fintype.card V := by
  apply bound081 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap081.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤393231676133183692412166711040079927132271328944*Fintype.card V
  exact_mod_cast hd.trans hh

theorem cutoff082 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*(G.edgeSet.ncard:ℝ)≤(2:ℝ)^(((79147/500):ℚ):ℝ)*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight≤(FiniteChains.Chain082.costBound:ℝ)*Fintype.card V := by
  apply bound082 G
  have hh := mul_le_mul_of_nonneg_right FiniteDegreeCaps.Cap082.degree_cap
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  change 2*G.edgeSet.ncard≤447962988848113113918344572173810198109414915141*Fintype.card V
  exact_mod_cast hd.trans hh

end
end Cycle12.FiniteAverageBounds
