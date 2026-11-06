import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0440
import Cycle12.RoutedCases.Batch0441

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source145

def strip0 : RatCoverRectangle := ⟨(129/2000),(1033/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0440.certificate8804.rectangle,RoutedCases.Batch0440.certificate8805.rectangle,RoutedCases.Batch0440.certificate8807.rectangle,RoutedCases.Batch0440.certificate8809.rectangle,RoutedCases.Batch0440.certificate8811.rectangle,RoutedCases.Batch0440.certificate8813.rectangle,RoutedCases.Batch0440.certificate8814.rectangle,RoutedCases.Batch0440.certificate8815.rectangle,RoutedCases.Batch0440.certificate8816.rectangle,RoutedCases.Batch0440.certificate8817.rectangle,RoutedCases.Batch0440.certificate8818.rectangle,RoutedCases.Batch0440.certificate8819.rectangle,RoutedCases.Batch0441.certificate8820.rectangle,RoutedCases.Batch0441.certificate8821.rectangle,RoutedCases.Batch0441.certificate8822.rectangle,RoutedCases.Batch0441.certificate8823.rectangle,RoutedCases.Batch0441.certificate8824.rectangle,RoutedCases.Batch0441.certificate8825.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8804,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8805,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8807,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8809,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8811,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8813,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8814,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8815,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8816,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8817,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8818,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8819,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8820,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8821,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8822,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8823,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8824,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8825,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1033/16000),(517/8000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0440.certificate8806.rectangle,RoutedCases.Batch0440.certificate8808.rectangle,RoutedCases.Batch0440.certificate8810.rectangle,RoutedCases.Batch0440.certificate8812.rectangle,RoutedCases.Batch0440.certificate8813.rectangle,RoutedCases.Batch0440.certificate8814.rectangle,RoutedCases.Batch0440.certificate8815.rectangle,RoutedCases.Batch0440.certificate8816.rectangle,RoutedCases.Batch0440.certificate8817.rectangle,RoutedCases.Batch0440.certificate8818.rectangle,RoutedCases.Batch0440.certificate8819.rectangle,RoutedCases.Batch0441.certificate8820.rectangle,RoutedCases.Batch0441.certificate8821.rectangle,RoutedCases.Batch0441.certificate8822.rectangle,RoutedCases.Batch0441.certificate8823.rectangle,RoutedCases.Batch0441.certificate8824.rectangle,RoutedCases.Batch0441.certificate8825.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8806,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8808,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8810,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8812,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8813,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8814,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8815,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8816,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8817,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8818,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8819,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8820,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8821,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8822,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8823,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8824,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8825,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(129/2000),(517/8000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source145
