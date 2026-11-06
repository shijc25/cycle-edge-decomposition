import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0912
import Cycle12.RoutedCases.Batch0913

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source407

def strip0 : RatCoverRectangle := ⟨(8/125),(513/8000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0912.certificate18249.rectangle,RoutedCases.Batch0912.certificate18250.rectangle,RoutedCases.Batch0912.certificate18251.rectangle,RoutedCases.Batch0912.certificate18252.rectangle,RoutedCases.Batch0912.certificate18253.rectangle,RoutedCases.Batch0912.certificate18255.rectangle,RoutedCases.Batch0912.certificate18257.rectangle,RoutedCases.Batch0912.certificate18259.rectangle,RoutedCases.Batch0913.certificate18261.rectangle,RoutedCases.Batch0913.certificate18262.rectangle,RoutedCases.Batch0913.certificate18265.rectangle,RoutedCases.Batch0913.certificate18267.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18249,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18250,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18251,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18252,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18253,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18255,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18257,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18259,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18261,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18262,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18265,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18267,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(513/8000),(257/4000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0912.certificate18249.rectangle,RoutedCases.Batch0912.certificate18250.rectangle,RoutedCases.Batch0912.certificate18251.rectangle,RoutedCases.Batch0912.certificate18252.rectangle,RoutedCases.Batch0912.certificate18253.rectangle,RoutedCases.Batch0912.certificate18255.rectangle,RoutedCases.Batch0912.certificate18257.rectangle,RoutedCases.Batch0912.certificate18259.rectangle,RoutedCases.Batch0913.certificate18261.rectangle,RoutedCases.Batch0913.certificate18263.rectangle,RoutedCases.Batch0913.certificate18266.rectangle,RoutedCases.Batch0913.certificate18268.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18249,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18250,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18251,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18252,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18253,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18255,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18257,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18259,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18261,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18263,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18266,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18268,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(257/4000),(129/2000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0912.certificate18249.rectangle,RoutedCases.Batch0912.certificate18250.rectangle,RoutedCases.Batch0912.certificate18251.rectangle,RoutedCases.Batch0912.certificate18252.rectangle,RoutedCases.Batch0912.certificate18254.rectangle,RoutedCases.Batch0912.certificate18256.rectangle,RoutedCases.Batch0912.certificate18258.rectangle,RoutedCases.Batch0913.certificate18260.rectangle,RoutedCases.Batch0913.certificate18264.rectangle,RoutedCases.Batch0913.certificate18269.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18249,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18250,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18251,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18252,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18254,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18256,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18258,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18260,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18264,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18269,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(8/125),(129/2000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source407
