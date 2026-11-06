import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0480
import Cycle12.RoutedCases.Batch0481
import Cycle12.RoutedCases.Batch0482

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source177

def strip0 : RatCoverRectangle := ⟨(13/1000),(53/4000),2,(some 5)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0480.certificate9611.rectangle,RoutedCases.Batch0480.certificate9614.rectangle,RoutedCases.Batch0480.certificate9617.rectangle,RoutedCases.Batch0481.certificate9621.rectangle,RoutedCases.Batch0481.certificate9626.rectangle,RoutedCases.Batch0481.certificate9628.rectangle,RoutedCases.Batch0481.certificate9634.rectangle,RoutedCases.Batch0481.certificate9636.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9611,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9614,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9617,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9621,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9626,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9628,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9634,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9636,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(53/4000),(27/2000),2,(some 5)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0480.certificate9611.rectangle,RoutedCases.Batch0480.certificate9614.rectangle,RoutedCases.Batch0480.certificate9617.rectangle,RoutedCases.Batch0481.certificate9621.rectangle,RoutedCases.Batch0481.certificate9627.rectangle,RoutedCases.Batch0481.certificate9629.rectangle,RoutedCases.Batch0481.certificate9635.rectangle,RoutedCases.Batch0481.certificate9637.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9611,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9614,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9617,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9621,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9627,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9629,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9635,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9637,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(27/2000),(11/800),2,(some 5)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0480.certificate9612.rectangle,RoutedCases.Batch0480.certificate9613.rectangle,RoutedCases.Batch0480.certificate9615.rectangle,RoutedCases.Batch0480.certificate9616.rectangle,RoutedCases.Batch0480.certificate9618.rectangle,RoutedCases.Batch0480.certificate9619.rectangle,RoutedCases.Batch0481.certificate9622.rectangle,RoutedCases.Batch0481.certificate9624.rectangle,RoutedCases.Batch0481.certificate9630.rectangle,RoutedCases.Batch0481.certificate9632.rectangle,RoutedCases.Batch0481.certificate9638.rectangle,RoutedCases.Batch0482.certificate9641.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9612,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9613,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9615,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9616,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9618,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9619,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9622,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9624,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9630,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9632,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9638,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0482.sound9641,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(11/800),(111/8000),2,(some 5)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0480.certificate9612.rectangle,RoutedCases.Batch0480.certificate9613.rectangle,RoutedCases.Batch0480.certificate9615.rectangle,RoutedCases.Batch0480.certificate9616.rectangle,RoutedCases.Batch0480.certificate9618.rectangle,RoutedCases.Batch0481.certificate9620.rectangle,RoutedCases.Batch0481.certificate9623.rectangle,RoutedCases.Batch0481.certificate9625.rectangle,RoutedCases.Batch0481.certificate9631.rectangle,RoutedCases.Batch0481.certificate9633.rectangle,RoutedCases.Batch0481.certificate9639.rectangle,RoutedCases.Batch0482.certificate9640.rectangle,RoutedCases.Batch0482.certificate9642.rectangle,RoutedCases.Batch0482.certificate9643.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9612,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9613,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9615,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9616,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9618,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9620,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9623,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9625,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9631,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9633,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9639,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0482.sound9640,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0482.sound9642,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0482.sound9643,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(111/8000),(7/500),2,(some 5)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0480.certificate9612.rectangle,RoutedCases.Batch0480.certificate9613.rectangle,RoutedCases.Batch0480.certificate9615.rectangle,RoutedCases.Batch0480.certificate9616.rectangle,RoutedCases.Batch0480.certificate9618.rectangle,RoutedCases.Batch0481.certificate9620.rectangle,RoutedCases.Batch0481.certificate9623.rectangle,RoutedCases.Batch0481.certificate9625.rectangle,RoutedCases.Batch0481.certificate9631.rectangle,RoutedCases.Batch0481.certificate9633.rectangle,RoutedCases.Batch0481.certificate9639.rectangle,RoutedCases.Batch0482.certificate9640.rectangle,RoutedCases.Batch0482.certificate9642.rectangle,RoutedCases.Batch0482.certificate9644.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9612,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9613,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9615,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9616,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9618,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9620,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9623,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9625,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9631,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9633,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0481.sound9639,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0482.sound9640,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0482.sound9642,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0482.sound9644,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(13/1000),(7/500),2,(some 5)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_nil _⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source177
