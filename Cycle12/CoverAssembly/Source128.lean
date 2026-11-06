import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0419
import Cycle12.RoutedCases.Batch0420

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source128

def strip0 : RatCoverRectangle := ⟨(497/8000),(199/3200),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0419.certificate8381.rectangle,RoutedCases.Batch0419.certificate8382.rectangle,RoutedCases.Batch0419.certificate8384.rectangle,RoutedCases.Batch0419.certificate8386.rectangle,RoutedCases.Batch0419.certificate8388.rectangle,RoutedCases.Batch0419.certificate8390.rectangle,RoutedCases.Batch0419.certificate8391.rectangle,RoutedCases.Batch0419.certificate8392.rectangle,RoutedCases.Batch0419.certificate8393.rectangle,RoutedCases.Batch0419.certificate8394.rectangle,RoutedCases.Batch0419.certificate8395.rectangle,RoutedCases.Batch0419.certificate8396.rectangle,RoutedCases.Batch0419.certificate8397.rectangle,RoutedCases.Batch0419.certificate8398.rectangle,RoutedCases.Batch0419.certificate8399.rectangle,RoutedCases.Batch0420.certificate8400.rectangle,RoutedCases.Batch0420.certificate8401.rectangle,RoutedCases.Batch0420.certificate8402.rectangle,RoutedCases.Batch0420.certificate8403.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8381,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8382,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8384,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8386,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8388,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8390,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8391,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8392,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8393,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8394,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8395,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8396,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8397,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8398,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8399,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0420.sound8400,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0420.sound8401,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0420.sound8402,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0420.sound8403,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(199/3200),(249/4000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0419.certificate8383.rectangle,RoutedCases.Batch0419.certificate8385.rectangle,RoutedCases.Batch0419.certificate8387.rectangle,RoutedCases.Batch0419.certificate8389.rectangle,RoutedCases.Batch0419.certificate8390.rectangle,RoutedCases.Batch0419.certificate8391.rectangle,RoutedCases.Batch0419.certificate8392.rectangle,RoutedCases.Batch0419.certificate8393.rectangle,RoutedCases.Batch0419.certificate8394.rectangle,RoutedCases.Batch0419.certificate8395.rectangle,RoutedCases.Batch0419.certificate8396.rectangle,RoutedCases.Batch0419.certificate8397.rectangle,RoutedCases.Batch0419.certificate8398.rectangle,RoutedCases.Batch0419.certificate8399.rectangle,RoutedCases.Batch0420.certificate8400.rectangle,RoutedCases.Batch0420.certificate8401.rectangle,RoutedCases.Batch0420.certificate8402.rectangle,RoutedCases.Batch0420.certificate8403.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8383,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8385,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8387,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8389,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8390,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8391,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8392,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8393,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8394,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8395,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8396,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8397,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8398,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8399,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0420.sound8400,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0420.sound8401,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0420.sound8402,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0420.sound8403,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(497/8000),(249/4000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source128
