import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0029
import Cycle12.RoutedCases.Batch0030
import Cycle12.RoutedCases.Batch0031
import Cycle12.RoutedCases.Batch0032

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source016

def strip0 : RatCoverRectangle := ⟨(17/1000),(69/4000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0029.certificate599.rectangle,RoutedCases.Batch0030.certificate601.rectangle,RoutedCases.Batch0030.certificate610.rectangle,RoutedCases.Batch0030.certificate612.rectangle,RoutedCases.Batch0030.certificate619.rectangle,RoutedCases.Batch0031.certificate621.rectangle,RoutedCases.Batch0031.certificate627.rectangle,RoutedCases.Batch0031.certificate629.rectangle,RoutedCases.Batch0031.certificate635.rectangle,RoutedCases.Batch0031.certificate637.rectangle,RoutedCases.Batch0032.certificate646.rectangle,RoutedCases.Batch0032.certificate648.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0029.sound599,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0030.sound601,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0030.sound610,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0030.sound612,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0030.sound619,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0031.sound621,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0031.sound627,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0031.sound629,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0031.sound635,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0031.sound637,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0032.sound646,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0032.sound648,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(69/4000),(7/400),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0030.certificate600.rectangle,RoutedCases.Batch0030.certificate602.rectangle,RoutedCases.Batch0030.certificate611.rectangle,RoutedCases.Batch0030.certificate613.rectangle,RoutedCases.Batch0031.certificate620.rectangle,RoutedCases.Batch0031.certificate622.rectangle,RoutedCases.Batch0031.certificate628.rectangle,RoutedCases.Batch0031.certificate630.rectangle,RoutedCases.Batch0031.certificate636.rectangle,RoutedCases.Batch0031.certificate638.rectangle,RoutedCases.Batch0032.certificate647.rectangle,RoutedCases.Batch0032.certificate649.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0030.sound600,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0030.sound602,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0030.sound611,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0030.sound613,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0031.sound620,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0031.sound622,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0031.sound628,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0031.sound630,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0031.sound636,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0031.sound638,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0032.sound647,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0032.sound649,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(7/400),(71/4000),1,(some 2)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0030.certificate603.rectangle,RoutedCases.Batch0030.certificate604.rectangle,RoutedCases.Batch0030.certificate607.rectangle,RoutedCases.Batch0030.certificate614.rectangle,RoutedCases.Batch0030.certificate617.rectangle,RoutedCases.Batch0031.certificate623.rectangle,RoutedCases.Batch0031.certificate625.rectangle,RoutedCases.Batch0031.certificate631.rectangle,RoutedCases.Batch0031.certificate633.rectangle,RoutedCases.Batch0031.certificate639.rectangle,RoutedCases.Batch0032.certificate640.rectangle,RoutedCases.Batch0032.certificate643.rectangle,RoutedCases.Batch0032.certificate650.rectangle,RoutedCases.Batch0032.certificate653.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0030.sound603,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0030.sound604,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0030.sound607,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0030.sound614,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0030.sound617,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0031.sound623,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0031.sound625,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0031.sound631,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0031.sound633,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0031.sound639,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0032.sound640,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0032.sound643,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0032.sound650,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0032.sound653,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(71/4000),(9/500),1,(some 2)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0030.certificate605.rectangle,RoutedCases.Batch0030.certificate606.rectangle,RoutedCases.Batch0030.certificate608.rectangle,RoutedCases.Batch0030.certificate609.rectangle,RoutedCases.Batch0030.certificate615.rectangle,RoutedCases.Batch0030.certificate616.rectangle,RoutedCases.Batch0030.certificate618.rectangle,RoutedCases.Batch0031.certificate624.rectangle,RoutedCases.Batch0031.certificate626.rectangle,RoutedCases.Batch0031.certificate632.rectangle,RoutedCases.Batch0031.certificate634.rectangle,RoutedCases.Batch0032.certificate641.rectangle,RoutedCases.Batch0032.certificate642.rectangle,RoutedCases.Batch0032.certificate644.rectangle,RoutedCases.Batch0032.certificate645.rectangle,RoutedCases.Batch0032.certificate651.rectangle,RoutedCases.Batch0032.certificate652.rectangle,RoutedCases.Batch0032.certificate654.rectangle,RoutedCases.Batch0032.certificate655.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0030.sound605,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0030.sound606,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0030.sound608,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0030.sound609,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0030.sound615,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0030.sound616,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0030.sound618,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0031.sound624,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0031.sound626,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0031.sound632,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0031.sound634,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0032.sound641,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0032.sound642,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0032.sound644,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0032.sound645,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0032.sound651,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0032.sound652,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0032.sound654,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0032.sound655,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(17/1000),(9/500),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source016
