import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0781

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source293

def strip0 : RatCoverRectangle := ⟨(101/2000),(81/1600),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0781.certificate15622.rectangle,RoutedCases.Batch0781.certificate15623.rectangle,RoutedCases.Batch0781.certificate15624.rectangle,RoutedCases.Batch0781.certificate15625.rectangle,RoutedCases.Batch0781.certificate15626.rectangle,RoutedCases.Batch0781.certificate15627.rectangle,RoutedCases.Batch0781.certificate15628.rectangle,RoutedCases.Batch0781.certificate15629.rectangle,RoutedCases.Batch0781.certificate15631.rectangle,RoutedCases.Batch0781.certificate15633.rectangle,RoutedCases.Batch0781.certificate15635.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15622,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15623,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15624,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15625,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15626,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15627,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15628,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15629,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15631,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15633,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15635,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(81/1600),(203/4000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0781.certificate15622.rectangle,RoutedCases.Batch0781.certificate15623.rectangle,RoutedCases.Batch0781.certificate15624.rectangle,RoutedCases.Batch0781.certificate15625.rectangle,RoutedCases.Batch0781.certificate15626.rectangle,RoutedCases.Batch0781.certificate15627.rectangle,RoutedCases.Batch0781.certificate15628.rectangle,RoutedCases.Batch0781.certificate15629.rectangle,RoutedCases.Batch0781.certificate15631.rectangle,RoutedCases.Batch0781.certificate15634.rectangle,RoutedCases.Batch0781.certificate15635.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15622,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15623,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15624,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15625,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15626,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15627,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15628,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15629,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15631,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15634,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15635,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(203/4000),(51/1000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0781.certificate15622.rectangle,RoutedCases.Batch0781.certificate15623.rectangle,RoutedCases.Batch0781.certificate15624.rectangle,RoutedCases.Batch0781.certificate15625.rectangle,RoutedCases.Batch0781.certificate15626.rectangle,RoutedCases.Batch0781.certificate15627.rectangle,RoutedCases.Batch0781.certificate15628.rectangle,RoutedCases.Batch0781.certificate15630.rectangle,RoutedCases.Batch0781.certificate15632.rectangle,RoutedCases.Batch0781.certificate15636.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15622,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15623,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15624,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15625,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15626,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15627,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15628,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15630,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15632,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15636,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(101/2000),(51/1000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source293
