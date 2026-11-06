import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0831

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source339

def strip0 : RatCoverRectangle := ⟨(21/2000),(43/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0831.certificate16623.rectangle,RoutedCases.Batch0831.certificate16624.rectangle,RoutedCases.Batch0831.certificate16625.rectangle,RoutedCases.Batch0831.certificate16626.rectangle,RoutedCases.Batch0831.certificate16627.rectangle,RoutedCases.Batch0831.certificate16629.rectangle,RoutedCases.Batch0831.certificate16631.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16623,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16624,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16625,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16626,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16627,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16629,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16631,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(43/4000),(87/8000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0831.certificate16623.rectangle,RoutedCases.Batch0831.certificate16624.rectangle,RoutedCases.Batch0831.certificate16625.rectangle,RoutedCases.Batch0831.certificate16626.rectangle,RoutedCases.Batch0831.certificate16628.rectangle,RoutedCases.Batch0831.certificate16630.rectangle,RoutedCases.Batch0831.certificate16632.rectangle,RoutedCases.Batch0831.certificate16633.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16623,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16624,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16625,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16626,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16628,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16630,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16632,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16633,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(87/8000),(11/1000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0831.certificate16623.rectangle,RoutedCases.Batch0831.certificate16624.rectangle,RoutedCases.Batch0831.certificate16625.rectangle,RoutedCases.Batch0831.certificate16626.rectangle,RoutedCases.Batch0831.certificate16628.rectangle,RoutedCases.Batch0831.certificate16630.rectangle,RoutedCases.Batch0831.certificate16632.rectangle,RoutedCases.Batch0831.certificate16634.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16623,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16624,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16625,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16626,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16628,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16630,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16632,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16634,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(21/2000),(11/1000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source339
