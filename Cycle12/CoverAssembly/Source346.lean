import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0836
import Cycle12.RoutedCases.Batch0837

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source346

def strip0 : RatCoverRectangle := ⟨(3/200),(61/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0836.certificate16730.rectangle,RoutedCases.Batch0836.certificate16731.rectangle,RoutedCases.Batch0836.certificate16732.rectangle,RoutedCases.Batch0836.certificate16733.rectangle,RoutedCases.Batch0836.certificate16735.rectangle,RoutedCases.Batch0836.certificate16737.rectangle,RoutedCases.Batch0837.certificate16741.rectangle,RoutedCases.Batch0837.certificate16742.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16730,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16731,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16732,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16733,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16735,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16737,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16741,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16742,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(61/4000),(31/2000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0836.certificate16730.rectangle,RoutedCases.Batch0836.certificate16731.rectangle,RoutedCases.Batch0836.certificate16732.rectangle,RoutedCases.Batch0836.certificate16733.rectangle,RoutedCases.Batch0836.certificate16735.rectangle,RoutedCases.Batch0836.certificate16737.rectangle,RoutedCases.Batch0837.certificate16741.rectangle,RoutedCases.Batch0837.certificate16743.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16730,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16731,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16732,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16733,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16735,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16737,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16741,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16743,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(31/2000),(63/4000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0836.certificate16730.rectangle,RoutedCases.Batch0836.certificate16731.rectangle,RoutedCases.Batch0836.certificate16732.rectangle,RoutedCases.Batch0836.certificate16734.rectangle,RoutedCases.Batch0836.certificate16736.rectangle,RoutedCases.Batch0836.certificate16738.rectangle,RoutedCases.Batch0836.certificate16739.rectangle,RoutedCases.Batch0837.certificate16744.rectangle,RoutedCases.Batch0837.certificate16749.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16730,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16731,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16732,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16734,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16736,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16738,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16739,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16744,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16749,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(63/4000),(127/8000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0836.certificate16730.rectangle,RoutedCases.Batch0836.certificate16731.rectangle,RoutedCases.Batch0836.certificate16732.rectangle,RoutedCases.Batch0836.certificate16734.rectangle,RoutedCases.Batch0836.certificate16736.rectangle,RoutedCases.Batch0836.certificate16738.rectangle,RoutedCases.Batch0837.certificate16740.rectangle,RoutedCases.Batch0837.certificate16745.rectangle,RoutedCases.Batch0837.certificate16747.rectangle,RoutedCases.Batch0837.certificate16750.rectangle,RoutedCases.Batch0837.certificate16751.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16730,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16731,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16732,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16734,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16736,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16738,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16740,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16745,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16747,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16750,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16751,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(127/8000),(51/3200),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0836.certificate16730.rectangle,RoutedCases.Batch0836.certificate16731.rectangle,RoutedCases.Batch0836.certificate16732.rectangle,RoutedCases.Batch0836.certificate16734.rectangle,RoutedCases.Batch0836.certificate16736.rectangle,RoutedCases.Batch0836.certificate16738.rectangle,RoutedCases.Batch0837.certificate16740.rectangle,RoutedCases.Batch0837.certificate16746.rectangle,RoutedCases.Batch0837.certificate16748.rectangle,RoutedCases.Batch0837.certificate16750.rectangle,RoutedCases.Batch0837.certificate16752.rectangle,RoutedCases.Batch0837.certificate16754.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16730,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16731,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16732,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16734,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16736,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16738,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16740,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16746,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16748,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16750,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16752,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16754,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip5 : RatCoverRectangle := ⟨(51/3200),(2/125),20,(some 100)⟩
def pieces5 : List RatCoverRectangle := [RoutedCases.Batch0836.certificate16730.rectangle,RoutedCases.Batch0836.certificate16731.rectangle,RoutedCases.Batch0836.certificate16732.rectangle,RoutedCases.Batch0836.certificate16734.rectangle,RoutedCases.Batch0836.certificate16736.rectangle,RoutedCases.Batch0836.certificate16738.rectangle,RoutedCases.Batch0837.certificate16740.rectangle,RoutedCases.Batch0837.certificate16746.rectangle,RoutedCases.Batch0837.certificate16748.rectangle,RoutedCases.Batch0837.certificate16750.rectangle,RoutedCases.Batch0837.certificate16753.rectangle,RoutedCases.Batch0837.certificate16755.rectangle]
theorem valid5 : strip5.JoinS pieces5 := by decide +kernel
theorem sound5 : strip5.Sound := rat_cover_join_s_sound strip5 pieces5 valid5 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16730,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16731,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16732,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16734,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16736,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16738,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16740,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16746,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16748,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16750,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16753,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0837.sound16755,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/200),(2/125),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4,strip5]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source346
