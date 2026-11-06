import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0472
import Cycle12.RoutedCases.Batch0473

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source172

def strip0 : RatCoverRectangle := ⟨(1/125),(17/2000),2,(some 5)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0472.certificate9448.rectangle,RoutedCases.Batch0472.certificate9451.rectangle,RoutedCases.Batch0472.certificate9454.rectangle,RoutedCases.Batch0472.certificate9459.rectangle,RoutedCases.Batch0473.certificate9464.rectangle,RoutedCases.Batch0473.certificate9465.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9448,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9451,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9454,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9459,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9464,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9465,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(17/2000),(7/800),2,(some 5)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0472.certificate9449.rectangle,RoutedCases.Batch0472.certificate9450.rectangle,RoutedCases.Batch0472.certificate9452.rectangle,RoutedCases.Batch0472.certificate9455.rectangle,RoutedCases.Batch0472.certificate9457.rectangle,RoutedCases.Batch0473.certificate9460.rectangle,RoutedCases.Batch0473.certificate9462.rectangle,RoutedCases.Batch0473.certificate9466.rectangle,RoutedCases.Batch0473.certificate9468.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9449,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9450,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9452,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9455,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9457,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9460,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9462,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9466,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9468,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(7/800),(9/1000),2,(some 5)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0472.certificate9449.rectangle,RoutedCases.Batch0472.certificate9450.rectangle,RoutedCases.Batch0472.certificate9453.rectangle,RoutedCases.Batch0472.certificate9456.rectangle,RoutedCases.Batch0472.certificate9458.rectangle,RoutedCases.Batch0473.certificate9461.rectangle,RoutedCases.Batch0473.certificate9463.rectangle,RoutedCases.Batch0473.certificate9467.rectangle,RoutedCases.Batch0473.certificate9469.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9449,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9450,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9453,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9456,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9458,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9461,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9463,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9467,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9469,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(1/125),(9/1000),2,(some 5)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source172
