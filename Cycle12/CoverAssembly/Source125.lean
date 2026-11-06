import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0414
import Cycle12.RoutedCases.Batch0415

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source125

def strip0 : RatCoverRectangle := ⟨(493/8000),(987/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0414.certificate8287.rectangle,RoutedCases.Batch0414.certificate8288.rectangle,RoutedCases.Batch0414.certificate8290.rectangle,RoutedCases.Batch0414.certificate8292.rectangle,RoutedCases.Batch0414.certificate8294.rectangle,RoutedCases.Batch0414.certificate8296.rectangle,RoutedCases.Batch0414.certificate8297.rectangle,RoutedCases.Batch0414.certificate8298.rectangle,RoutedCases.Batch0414.certificate8299.rectangle,RoutedCases.Batch0415.certificate8300.rectangle,RoutedCases.Batch0415.certificate8301.rectangle,RoutedCases.Batch0415.certificate8302.rectangle,RoutedCases.Batch0415.certificate8303.rectangle,RoutedCases.Batch0415.certificate8304.rectangle,RoutedCases.Batch0415.certificate8305.rectangle,RoutedCases.Batch0415.certificate8306.rectangle,RoutedCases.Batch0415.certificate8307.rectangle,RoutedCases.Batch0415.certificate8308.rectangle,RoutedCases.Batch0415.certificate8309.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8287,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8288,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8290,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8292,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8294,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8296,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8297,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8298,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8299,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0415.sound8300,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0415.sound8301,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0415.sound8302,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0415.sound8303,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0415.sound8304,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0415.sound8305,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0415.sound8306,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0415.sound8307,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0415.sound8308,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0415.sound8309,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(987/16000),(247/4000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0414.certificate8289.rectangle,RoutedCases.Batch0414.certificate8291.rectangle,RoutedCases.Batch0414.certificate8293.rectangle,RoutedCases.Batch0414.certificate8295.rectangle,RoutedCases.Batch0414.certificate8296.rectangle,RoutedCases.Batch0414.certificate8297.rectangle,RoutedCases.Batch0414.certificate8298.rectangle,RoutedCases.Batch0414.certificate8299.rectangle,RoutedCases.Batch0415.certificate8300.rectangle,RoutedCases.Batch0415.certificate8301.rectangle,RoutedCases.Batch0415.certificate8302.rectangle,RoutedCases.Batch0415.certificate8303.rectangle,RoutedCases.Batch0415.certificate8304.rectangle,RoutedCases.Batch0415.certificate8305.rectangle,RoutedCases.Batch0415.certificate8306.rectangle,RoutedCases.Batch0415.certificate8307.rectangle,RoutedCases.Batch0415.certificate8308.rectangle,RoutedCases.Batch0415.certificate8309.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8289,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8291,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8293,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8295,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8296,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8297,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8298,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8299,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0415.sound8300,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0415.sound8301,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0415.sound8302,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0415.sound8303,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0415.sound8304,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0415.sound8305,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0415.sound8306,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0415.sound8307,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0415.sound8308,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0415.sound8309,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(493/8000),(247/4000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source125
