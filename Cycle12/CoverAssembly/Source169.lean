import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0468
import Cycle12.RoutedCases.Batch0469

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source169

def strip0 : RatCoverRectangle := ⟨(1/200),(11/2000),2,(some 5)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0468.certificate9366.rectangle,RoutedCases.Batch0468.certificate9371.rectangle,RoutedCases.Batch0468.certificate9376.rectangle,RoutedCases.Batch0468.certificate9377.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0468.sound9366,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0468.sound9371,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0468.sound9376,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0468.sound9377,List.forall_mem_nil _⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(11/2000),(23/4000),2,(some 5)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0468.certificate9367.rectangle,RoutedCases.Batch0468.certificate9369.rectangle,RoutedCases.Batch0468.certificate9372.rectangle,RoutedCases.Batch0468.certificate9374.rectangle,RoutedCases.Batch0468.certificate9378.rectangle,RoutedCases.Batch0469.certificate9380.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0468.sound9367,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0468.sound9369,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0468.sound9372,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0468.sound9374,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0468.sound9378,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9380,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(23/4000),(3/500),2,(some 5)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0468.certificate9368.rectangle,RoutedCases.Batch0468.certificate9370.rectangle,RoutedCases.Batch0468.certificate9373.rectangle,RoutedCases.Batch0468.certificate9375.rectangle,RoutedCases.Batch0468.certificate9379.rectangle,RoutedCases.Batch0469.certificate9381.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0468.sound9368,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0468.sound9370,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0468.sound9373,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0468.sound9375,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0468.sound9379,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9381,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(1/200),(3/500),2,(some 5)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source169
