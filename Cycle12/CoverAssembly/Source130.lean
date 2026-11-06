import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0421
import Cycle12.RoutedCases.Batch0422

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source130

def strip0 : RatCoverRectangle := ⟨(499/8000),(999/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0421.certificate8429.rectangle,RoutedCases.Batch0421.certificate8431.rectangle,RoutedCases.Batch0421.certificate8433.rectangle,RoutedCases.Batch0421.certificate8435.rectangle,RoutedCases.Batch0421.certificate8436.rectangle,RoutedCases.Batch0421.certificate8437.rectangle,RoutedCases.Batch0421.certificate8438.rectangle,RoutedCases.Batch0421.certificate8439.rectangle,RoutedCases.Batch0422.certificate8440.rectangle,RoutedCases.Batch0422.certificate8441.rectangle,RoutedCases.Batch0422.certificate8442.rectangle,RoutedCases.Batch0422.certificate8443.rectangle,RoutedCases.Batch0422.certificate8444.rectangle,RoutedCases.Batch0422.certificate8445.rectangle,RoutedCases.Batch0422.certificate8446.rectangle,RoutedCases.Batch0422.certificate8447.rectangle,RoutedCases.Batch0422.certificate8448.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0421.sound8429,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0421.sound8431,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0421.sound8433,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0421.sound8435,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0421.sound8436,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0421.sound8437,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0421.sound8438,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0421.sound8439,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8440,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8441,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8442,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8443,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8444,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8445,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8446,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8447,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8448,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(999/16000),(1/16),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0421.certificate8430.rectangle,RoutedCases.Batch0421.certificate8432.rectangle,RoutedCases.Batch0421.certificate8434.rectangle,RoutedCases.Batch0421.certificate8435.rectangle,RoutedCases.Batch0421.certificate8436.rectangle,RoutedCases.Batch0421.certificate8437.rectangle,RoutedCases.Batch0421.certificate8438.rectangle,RoutedCases.Batch0421.certificate8439.rectangle,RoutedCases.Batch0422.certificate8440.rectangle,RoutedCases.Batch0422.certificate8441.rectangle,RoutedCases.Batch0422.certificate8442.rectangle,RoutedCases.Batch0422.certificate8443.rectangle,RoutedCases.Batch0422.certificate8444.rectangle,RoutedCases.Batch0422.certificate8445.rectangle,RoutedCases.Batch0422.certificate8446.rectangle,RoutedCases.Batch0422.certificate8447.rectangle,RoutedCases.Batch0422.certificate8448.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0421.sound8430,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0421.sound8432,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0421.sound8434,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0421.sound8435,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0421.sound8436,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0421.sound8437,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0421.sound8438,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0421.sound8439,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8440,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8441,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8442,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8443,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8444,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8445,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8446,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8447,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8448,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(499/8000),(1/16),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source130
