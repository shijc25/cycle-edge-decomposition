import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0915
import Cycle12.RoutedCases.Batch0916

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source410

def strip0 : RatCoverRectangle := ⟨(131/2000),(21/320),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0915.certificate18308.rectangle,RoutedCases.Batch0915.certificate18309.rectangle,RoutedCases.Batch0915.certificate18310.rectangle,RoutedCases.Batch0915.certificate18311.rectangle,RoutedCases.Batch0915.certificate18312.rectangle,RoutedCases.Batch0915.certificate18314.rectangle,RoutedCases.Batch0915.certificate18316.rectangle,RoutedCases.Batch0915.certificate18318.rectangle,RoutedCases.Batch0916.certificate18320.rectangle,RoutedCases.Batch0916.certificate18322.rectangle,RoutedCases.Batch0916.certificate18323.rectangle,RoutedCases.Batch0916.certificate18326.rectangle,RoutedCases.Batch0916.certificate18328.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18308,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18309,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18310,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18311,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18312,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18314,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18316,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18318,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0916.sound18320,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0916.sound18322,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0916.sound18323,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0916.sound18326,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0916.sound18328,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(21/320),(1051/16000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0915.certificate18308.rectangle,RoutedCases.Batch0915.certificate18309.rectangle,RoutedCases.Batch0915.certificate18310.rectangle,RoutedCases.Batch0915.certificate18311.rectangle,RoutedCases.Batch0915.certificate18312.rectangle,RoutedCases.Batch0915.certificate18314.rectangle,RoutedCases.Batch0915.certificate18316.rectangle,RoutedCases.Batch0915.certificate18319.rectangle,RoutedCases.Batch0916.certificate18320.rectangle,RoutedCases.Batch0916.certificate18322.rectangle,RoutedCases.Batch0916.certificate18324.rectangle,RoutedCases.Batch0916.certificate18327.rectangle,RoutedCases.Batch0916.certificate18329.rectangle,RoutedCases.Batch0916.certificate18330.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18308,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18309,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18310,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18311,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18312,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18314,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18316,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18319,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0916.sound18320,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0916.sound18322,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0916.sound18324,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0916.sound18327,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0916.sound18329,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0916.sound18330,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(1051/16000),(263/4000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0915.certificate18308.rectangle,RoutedCases.Batch0915.certificate18309.rectangle,RoutedCases.Batch0915.certificate18310.rectangle,RoutedCases.Batch0915.certificate18311.rectangle,RoutedCases.Batch0915.certificate18312.rectangle,RoutedCases.Batch0915.certificate18314.rectangle,RoutedCases.Batch0915.certificate18316.rectangle,RoutedCases.Batch0915.certificate18319.rectangle,RoutedCases.Batch0916.certificate18320.rectangle,RoutedCases.Batch0916.certificate18322.rectangle,RoutedCases.Batch0916.certificate18324.rectangle,RoutedCases.Batch0916.certificate18327.rectangle,RoutedCases.Batch0916.certificate18329.rectangle,RoutedCases.Batch0916.certificate18331.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18308,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18309,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18310,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18311,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18312,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18314,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18316,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18319,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0916.sound18320,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0916.sound18322,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0916.sound18324,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0916.sound18327,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0916.sound18329,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0916.sound18331,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(263/4000),(33/500),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0915.certificate18308.rectangle,RoutedCases.Batch0915.certificate18309.rectangle,RoutedCases.Batch0915.certificate18310.rectangle,RoutedCases.Batch0915.certificate18311.rectangle,RoutedCases.Batch0915.certificate18313.rectangle,RoutedCases.Batch0915.certificate18315.rectangle,RoutedCases.Batch0915.certificate18317.rectangle,RoutedCases.Batch0916.certificate18321.rectangle,RoutedCases.Batch0916.certificate18325.rectangle,RoutedCases.Batch0916.certificate18332.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18308,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18309,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18310,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18311,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18313,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18315,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18317,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0916.sound18321,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0916.sound18325,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0916.sound18332,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(131/2000),(33/500),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source410
