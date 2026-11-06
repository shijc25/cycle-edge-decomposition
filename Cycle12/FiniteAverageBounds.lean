import Cycle12.MixedCover
import Cycle12.FiniteChains.Chain000
import Cycle12.FiniteChains.Chain001
import Cycle12.FiniteChains.Chain002
import Cycle12.FiniteChains.Chain003
import Cycle12.FiniteChains.Chain004
import Cycle12.FiniteChains.Chain005
import Cycle12.FiniteChains.Chain006
import Cycle12.FiniteChains.Chain007
import Cycle12.FiniteChains.Chain008
import Cycle12.FiniteChains.Chain009
import Cycle12.FiniteChains.Chain010
import Cycle12.FiniteChains.Chain011
import Cycle12.FiniteChains.Chain012
import Cycle12.FiniteChains.Chain013
import Cycle12.FiniteChains.Chain014
import Cycle12.FiniteChains.Chain015
import Cycle12.FiniteChains.Chain016
import Cycle12.FiniteChains.Chain017
import Cycle12.FiniteChains.Chain018
import Cycle12.FiniteChains.Chain019
import Cycle12.FiniteChains.Chain020
import Cycle12.FiniteChains.Chain021
import Cycle12.FiniteChains.Chain022
import Cycle12.FiniteChains.Chain023
import Cycle12.FiniteChains.Chain024
import Cycle12.FiniteChains.Chain025
import Cycle12.FiniteChains.Chain026
import Cycle12.FiniteChains.Chain027
import Cycle12.FiniteChains.Chain028
import Cycle12.FiniteChains.Chain029
import Cycle12.FiniteChains.Chain030
import Cycle12.FiniteChains.Chain031
import Cycle12.FiniteChains.Chain032
import Cycle12.FiniteChains.Chain033
import Cycle12.FiniteChains.Chain034
import Cycle12.FiniteChains.Chain035
import Cycle12.FiniteChains.Chain036
import Cycle12.FiniteChains.Chain037
import Cycle12.FiniteChains.Chain038
import Cycle12.FiniteChains.Chain039
import Cycle12.FiniteChains.Chain040
import Cycle12.FiniteChains.Chain041
import Cycle12.FiniteChains.Chain042
import Cycle12.FiniteChains.Chain043
import Cycle12.FiniteChains.Chain044
import Cycle12.FiniteChains.Chain045
import Cycle12.FiniteChains.Chain046
import Cycle12.FiniteChains.Chain047
import Cycle12.FiniteChains.Chain048
import Cycle12.FiniteChains.Chain049
import Cycle12.FiniteChains.Chain050
import Cycle12.FiniteChains.Chain051
import Cycle12.FiniteChains.Chain052
import Cycle12.FiniteChains.Chain053
import Cycle12.FiniteChains.Chain054
import Cycle12.FiniteChains.Chain055
import Cycle12.FiniteChains.Chain056
import Cycle12.FiniteChains.Chain057
import Cycle12.FiniteChains.Chain058
import Cycle12.FiniteChains.Chain059
import Cycle12.FiniteChains.Chain060
import Cycle12.FiniteChains.Chain061
import Cycle12.FiniteChains.Chain062
import Cycle12.FiniteChains.Chain063
import Cycle12.FiniteChains.Chain064
import Cycle12.FiniteChains.Chain065
import Cycle12.FiniteChains.Chain066
import Cycle12.FiniteChains.Chain067
import Cycle12.FiniteChains.Chain068
import Cycle12.FiniteChains.Chain069
import Cycle12.FiniteChains.Chain070
import Cycle12.FiniteChains.Chain071
import Cycle12.FiniteChains.Chain072
import Cycle12.FiniteChains.Chain073
import Cycle12.FiniteChains.Chain074
import Cycle12.FiniteChains.Chain075
import Cycle12.FiniteChains.Chain076
import Cycle12.FiniteChains.Chain077
import Cycle12.FiniteChains.Chain078
import Cycle12.FiniteChains.Chain079
import Cycle12.FiniteChains.Chain080
import Cycle12.FiniteChains.Chain081
import Cycle12.FiniteChains.Chain082

namespace Cycle12.FiniteAverageBounds
open Cycle13
noncomputable section

theorem bound000 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain000.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain000.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain000.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound001 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain001.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain001.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain001.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound002 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain002.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain002.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain002.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound003 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain003.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain003.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain003.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound004 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain004.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain004.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain004.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound005 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain005.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain005.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain005.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound006 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain006.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain006.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain006.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound007 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain007.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain007.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain007.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound008 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain008.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain008.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain008.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound009 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain009.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain009.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain009.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound010 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain010.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain010.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain010.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound011 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain011.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain011.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain011.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound012 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain012.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain012.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain012.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound013 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain013.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain013.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain013.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound014 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain014.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain014.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain014.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound015 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain015.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain015.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain015.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound016 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain016.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain016.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain016.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound017 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain017.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain017.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain017.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound018 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain018.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain018.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain018.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound019 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain019.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain019.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain019.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound020 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain020.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain020.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain020.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound021 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain021.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain021.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain021.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound022 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain022.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain022.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain022.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound023 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain023.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain023.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain023.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound024 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain024.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain024.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain024.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound025 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain025.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain025.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain025.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound026 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain026.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain026.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain026.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound027 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain027.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain027.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain027.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound028 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain028.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain028.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain028.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound029 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain029.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain029.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain029.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound030 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain030.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain030.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain030.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound031 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain031.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain031.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain031.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound032 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain032.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain032.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain032.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound033 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain033.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain033.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain033.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound034 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain034.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain034.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain034.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound035 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain035.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain035.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain035.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound036 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain036.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain036.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain036.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound037 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain037.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain037.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain037.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound038 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain038.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain038.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain038.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound039 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain039.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain039.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain039.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound040 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain040.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain040.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain040.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound041 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain041.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain041.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain041.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound042 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain042.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain042.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain042.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound043 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain043.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain043.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain043.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound044 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain044.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain044.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain044.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound045 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain045.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain045.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain045.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound046 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain046.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain046.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain046.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound047 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain047.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain047.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain047.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound048 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain048.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain048.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain048.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound049 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain049.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain049.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain049.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound050 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain050.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain050.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain050.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound051 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain051.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain051.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain051.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound052 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain052.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain052.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain052.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound053 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain053.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain053.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain053.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound054 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain054.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain054.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain054.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound055 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain055.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain055.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain055.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound056 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain056.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain056.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain056.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound057 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain057.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain057.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain057.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound058 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain058.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain058.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain058.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound059 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain059.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain059.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain059.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound060 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain060.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain060.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain060.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound061 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain061.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain061.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain061.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound062 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain062.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain062.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain062.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound063 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain063.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain063.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain063.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound064 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain064.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain064.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain064.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound065 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain065.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain065.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain065.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound066 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain066.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain066.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain066.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound067 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain067.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain067.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain067.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound068 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain068.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain068.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain068.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound069 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain069.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain069.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain069.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound070 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain070.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain070.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain070.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound071 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain071.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain071.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain071.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound072 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain072.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain072.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain072.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound073 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain073.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain073.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain073.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound074 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain074.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain074.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain074.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound075 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain075.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain075.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain075.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound076 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain076.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain076.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain076.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound077 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain077.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain077.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain077.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound078 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain078.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain078.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain078.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound079 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain079.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain079.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain079.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound080 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain080.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain080.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain080.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound081 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain081.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain081.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain081.graph_bound (fun _ _ _ H => mixed_cover H) G hd

theorem bound082 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hd : 2*G.edgeSet.ncard ≤ FiniteChains.Chain082.degreeCap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ (FiniteChains.Chain082.costBound:ℝ)*Fintype.card V :=
  FiniteChains.Chain082.graph_bound (fun _ _ _ H => mixed_cover H) G hd

end
end Cycle12.FiniteAverageBounds
