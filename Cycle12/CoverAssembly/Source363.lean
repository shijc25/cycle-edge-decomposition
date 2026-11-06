import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0850
import Cycle12.RoutedCases.Batch0851
import Cycle12.RoutedCases.Batch0852

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source363

def strip0 : RatCoverRectangle := ⟨(7/250),(113/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0850.certificate17014.rectangle,RoutedCases.Batch0850.certificate17015.rectangle,RoutedCases.Batch0850.certificate17016.rectangle,RoutedCases.Batch0850.certificate17017.rectangle,RoutedCases.Batch0850.certificate17018.rectangle,RoutedCases.Batch0851.certificate17020.rectangle,RoutedCases.Batch0851.certificate17022.rectangle,RoutedCases.Batch0851.certificate17026.rectangle,RoutedCases.Batch0851.certificate17031.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17014,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17015,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17016,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17017,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17018,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17020,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17022,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17026,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17031,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(113/4000),(57/2000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0850.certificate17014.rectangle,RoutedCases.Batch0850.certificate17015.rectangle,RoutedCases.Batch0850.certificate17016.rectangle,RoutedCases.Batch0850.certificate17017.rectangle,RoutedCases.Batch0850.certificate17018.rectangle,RoutedCases.Batch0851.certificate17020.rectangle,RoutedCases.Batch0851.certificate17022.rectangle,RoutedCases.Batch0851.certificate17026.rectangle,RoutedCases.Batch0851.certificate17032.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17014,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17015,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17016,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17017,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17018,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17020,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17022,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17026,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17032,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(57/2000),(229/8000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0850.certificate17014.rectangle,RoutedCases.Batch0850.certificate17015.rectangle,RoutedCases.Batch0850.certificate17016.rectangle,RoutedCases.Batch0850.certificate17017.rectangle,RoutedCases.Batch0850.certificate17019.rectangle,RoutedCases.Batch0851.certificate17021.rectangle,RoutedCases.Batch0851.certificate17023.rectangle,RoutedCases.Batch0851.certificate17024.rectangle,RoutedCases.Batch0851.certificate17027.rectangle,RoutedCases.Batch0851.certificate17029.rectangle,RoutedCases.Batch0851.certificate17033.rectangle,RoutedCases.Batch0851.certificate17037.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17014,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17015,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17016,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17017,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17019,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17021,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17023,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17024,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17027,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17029,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17033,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17037,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(229/8000),(23/800),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0850.certificate17014.rectangle,RoutedCases.Batch0850.certificate17015.rectangle,RoutedCases.Batch0850.certificate17016.rectangle,RoutedCases.Batch0850.certificate17017.rectangle,RoutedCases.Batch0850.certificate17019.rectangle,RoutedCases.Batch0851.certificate17021.rectangle,RoutedCases.Batch0851.certificate17023.rectangle,RoutedCases.Batch0851.certificate17024.rectangle,RoutedCases.Batch0851.certificate17027.rectangle,RoutedCases.Batch0851.certificate17029.rectangle,RoutedCases.Batch0851.certificate17033.rectangle,RoutedCases.Batch0851.certificate17038.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17014,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17015,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17016,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17017,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17019,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17021,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17023,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17024,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17027,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17029,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17033,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17038,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(23/800),(231/8000),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0850.certificate17014.rectangle,RoutedCases.Batch0850.certificate17015.rectangle,RoutedCases.Batch0850.certificate17016.rectangle,RoutedCases.Batch0850.certificate17017.rectangle,RoutedCases.Batch0850.certificate17019.rectangle,RoutedCases.Batch0851.certificate17021.rectangle,RoutedCases.Batch0851.certificate17023.rectangle,RoutedCases.Batch0851.certificate17025.rectangle,RoutedCases.Batch0851.certificate17028.rectangle,RoutedCases.Batch0851.certificate17030.rectangle,RoutedCases.Batch0851.certificate17034.rectangle,RoutedCases.Batch0851.certificate17035.rectangle,RoutedCases.Batch0851.certificate17039.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17014,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17015,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17016,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17017,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17019,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17021,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17023,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17025,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17028,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17030,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17034,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17035,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17039,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip5 : RatCoverRectangle := ⟨(231/8000),(29/1000),20,(some 100)⟩
def pieces5 : List RatCoverRectangle := [RoutedCases.Batch0850.certificate17014.rectangle,RoutedCases.Batch0850.certificate17015.rectangle,RoutedCases.Batch0850.certificate17016.rectangle,RoutedCases.Batch0850.certificate17017.rectangle,RoutedCases.Batch0850.certificate17019.rectangle,RoutedCases.Batch0851.certificate17021.rectangle,RoutedCases.Batch0851.certificate17023.rectangle,RoutedCases.Batch0851.certificate17025.rectangle,RoutedCases.Batch0851.certificate17028.rectangle,RoutedCases.Batch0851.certificate17030.rectangle,RoutedCases.Batch0851.certificate17034.rectangle,RoutedCases.Batch0851.certificate17036.rectangle,RoutedCases.Batch0852.certificate17040.rectangle]
theorem valid5 : strip5.JoinS pieces5 := by decide +kernel
theorem sound5 : strip5.Sound := rat_cover_join_s_sound strip5 pieces5 valid5 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17014,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17015,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17016,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17017,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17019,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17021,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17023,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17025,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17028,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17030,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17034,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0851.sound17036,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17040,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(7/250),(29/1000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4,strip5]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source363
