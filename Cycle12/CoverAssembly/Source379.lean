import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0877
import Cycle12.RoutedCases.Batch0878

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source379

def strip0 : RatCoverRectangle := ⟨(11/250),(177/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0877.certificate17550.rectangle,RoutedCases.Batch0877.certificate17551.rectangle,RoutedCases.Batch0877.certificate17552.rectangle,RoutedCases.Batch0877.certificate17553.rectangle,RoutedCases.Batch0877.certificate17554.rectangle,RoutedCases.Batch0877.certificate17556.rectangle,RoutedCases.Batch0877.certificate17558.rectangle,RoutedCases.Batch0877.certificate17559.rectangle,RoutedCases.Batch0878.certificate17564.rectangle,RoutedCases.Batch0878.certificate17566.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17550,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17551,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17552,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17553,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17554,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17556,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17558,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17559,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17564,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17566,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(177/4000),(89/2000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0877.certificate17550.rectangle,RoutedCases.Batch0877.certificate17551.rectangle,RoutedCases.Batch0877.certificate17552.rectangle,RoutedCases.Batch0877.certificate17553.rectangle,RoutedCases.Batch0877.certificate17554.rectangle,RoutedCases.Batch0877.certificate17556.rectangle,RoutedCases.Batch0877.certificate17558.rectangle,RoutedCases.Batch0878.certificate17560.rectangle,RoutedCases.Batch0878.certificate17565.rectangle,RoutedCases.Batch0878.certificate17567.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17550,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17551,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17552,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17553,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17554,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17556,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17558,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17560,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17565,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17567,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(89/2000),(179/4000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0877.certificate17550.rectangle,RoutedCases.Batch0877.certificate17551.rectangle,RoutedCases.Batch0877.certificate17552.rectangle,RoutedCases.Batch0877.certificate17553.rectangle,RoutedCases.Batch0877.certificate17555.rectangle,RoutedCases.Batch0877.certificate17557.rectangle,RoutedCases.Batch0878.certificate17561.rectangle,RoutedCases.Batch0878.certificate17562.rectangle,RoutedCases.Batch0878.certificate17568.rectangle,RoutedCases.Batch0878.certificate17570.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17550,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17551,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17552,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17553,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17555,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17557,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17561,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17562,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17568,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17570,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(179/4000),(9/200),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0877.certificate17550.rectangle,RoutedCases.Batch0877.certificate17551.rectangle,RoutedCases.Batch0877.certificate17552.rectangle,RoutedCases.Batch0877.certificate17553.rectangle,RoutedCases.Batch0877.certificate17555.rectangle,RoutedCases.Batch0877.certificate17557.rectangle,RoutedCases.Batch0878.certificate17561.rectangle,RoutedCases.Batch0878.certificate17563.rectangle,RoutedCases.Batch0878.certificate17569.rectangle,RoutedCases.Batch0878.certificate17571.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17550,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17551,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17552,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17553,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17555,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0877.sound17557,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17561,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17563,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17569,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17571,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(11/250),(9/200),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source379
