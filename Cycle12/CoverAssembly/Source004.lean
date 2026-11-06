import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0001

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source004

def strip0 : RatCoverRectangle := ⟨(1/200),(21/4000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0001.certificate21.rectangle,RoutedCases.Batch0001.certificate23.rectangle,RoutedCases.Batch0001.certificate29.rectangle,RoutedCases.Batch0001.certificate30.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound21,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound23,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound29,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound30,List.forall_mem_nil _⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(21/4000),(11/2000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0001.certificate22.rectangle,RoutedCases.Batch0001.certificate23.rectangle,RoutedCases.Batch0001.certificate29.rectangle,RoutedCases.Batch0001.certificate30.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound22,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound23,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound29,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound30,List.forall_mem_nil _⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(11/2000),(23/4000),1,(some 2)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0001.certificate24.rectangle,RoutedCases.Batch0001.certificate27.rectangle,RoutedCases.Batch0001.certificate31.rectangle,RoutedCases.Batch0001.certificate33.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound24,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound27,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound31,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound33,List.forall_mem_nil _⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(23/4000),(3/500),1,(some 2)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0001.certificate25.rectangle,RoutedCases.Batch0001.certificate26.rectangle,RoutedCases.Batch0001.certificate28.rectangle,RoutedCases.Batch0001.certificate32.rectangle,RoutedCases.Batch0001.certificate34.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound25,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound26,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound28,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound32,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound34,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(1/200),(3/500),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source004
