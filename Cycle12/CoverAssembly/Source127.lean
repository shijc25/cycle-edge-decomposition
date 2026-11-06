import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0417
import Cycle12.RoutedCases.Batch0418
import Cycle12.RoutedCases.Batch0419

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source127

def strip0 : RatCoverRectangle := ⟨(31/500),(993/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0417.certificate8359.rectangle,RoutedCases.Batch0418.certificate8360.rectangle,RoutedCases.Batch0418.certificate8362.rectangle,RoutedCases.Batch0418.certificate8364.rectangle,RoutedCases.Batch0418.certificate8366.rectangle,RoutedCases.Batch0418.certificate8368.rectangle,RoutedCases.Batch0418.certificate8369.rectangle,RoutedCases.Batch0418.certificate8370.rectangle,RoutedCases.Batch0418.certificate8371.rectangle,RoutedCases.Batch0418.certificate8372.rectangle,RoutedCases.Batch0418.certificate8373.rectangle,RoutedCases.Batch0418.certificate8374.rectangle,RoutedCases.Batch0418.certificate8375.rectangle,RoutedCases.Batch0418.certificate8376.rectangle,RoutedCases.Batch0418.certificate8377.rectangle,RoutedCases.Batch0418.certificate8378.rectangle,RoutedCases.Batch0418.certificate8379.rectangle,RoutedCases.Batch0419.certificate8380.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0417.sound8359,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8360,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8362,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8364,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8366,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8368,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8369,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8370,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8371,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8372,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8373,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8374,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8375,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8376,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8377,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8378,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8379,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8380,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(993/16000),(497/8000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0418.certificate8361.rectangle,RoutedCases.Batch0418.certificate8363.rectangle,RoutedCases.Batch0418.certificate8365.rectangle,RoutedCases.Batch0418.certificate8367.rectangle,RoutedCases.Batch0418.certificate8368.rectangle,RoutedCases.Batch0418.certificate8369.rectangle,RoutedCases.Batch0418.certificate8370.rectangle,RoutedCases.Batch0418.certificate8371.rectangle,RoutedCases.Batch0418.certificate8372.rectangle,RoutedCases.Batch0418.certificate8373.rectangle,RoutedCases.Batch0418.certificate8374.rectangle,RoutedCases.Batch0418.certificate8375.rectangle,RoutedCases.Batch0418.certificate8376.rectangle,RoutedCases.Batch0418.certificate8377.rectangle,RoutedCases.Batch0418.certificate8378.rectangle,RoutedCases.Batch0418.certificate8379.rectangle,RoutedCases.Batch0419.certificate8380.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8361,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8363,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8365,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8367,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8368,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8369,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8370,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8371,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8372,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8373,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8374,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8375,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8376,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8377,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8378,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0418.sound8379,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0419.sound8380,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(31/500),(497/8000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source127
