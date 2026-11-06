import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0900
import Cycle12.RoutedCases.Batch0901

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source398

def strip0 : RatCoverRectangle := ⟨(59/1000),(189/3200),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0900.certificate18004.rectangle,RoutedCases.Batch0900.certificate18005.rectangle,RoutedCases.Batch0900.certificate18006.rectangle,RoutedCases.Batch0900.certificate18007.rectangle,RoutedCases.Batch0900.certificate18008.rectangle,RoutedCases.Batch0900.certificate18010.rectangle,RoutedCases.Batch0900.certificate18012.rectangle,RoutedCases.Batch0900.certificate18014.rectangle,RoutedCases.Batch0900.certificate18016.rectangle,RoutedCases.Batch0900.certificate18017.rectangle,RoutedCases.Batch0901.certificate18020.rectangle,RoutedCases.Batch0901.certificate18021.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18004,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18005,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18006,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18007,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18008,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18010,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18012,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18014,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18016,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18017,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18020,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18021,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(189/3200),(473/8000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0900.certificate18004.rectangle,RoutedCases.Batch0900.certificate18005.rectangle,RoutedCases.Batch0900.certificate18006.rectangle,RoutedCases.Batch0900.certificate18007.rectangle,RoutedCases.Batch0900.certificate18008.rectangle,RoutedCases.Batch0900.certificate18010.rectangle,RoutedCases.Batch0900.certificate18012.rectangle,RoutedCases.Batch0900.certificate18014.rectangle,RoutedCases.Batch0900.certificate18016.rectangle,RoutedCases.Batch0900.certificate18017.rectangle,RoutedCases.Batch0901.certificate18020.rectangle,RoutedCases.Batch0901.certificate18022.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18004,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18005,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18006,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18007,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18008,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18010,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18012,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18014,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18016,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18017,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18020,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18022,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(473/8000),(237/4000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0900.certificate18004.rectangle,RoutedCases.Batch0900.certificate18005.rectangle,RoutedCases.Batch0900.certificate18006.rectangle,RoutedCases.Batch0900.certificate18007.rectangle,RoutedCases.Batch0900.certificate18008.rectangle,RoutedCases.Batch0900.certificate18010.rectangle,RoutedCases.Batch0900.certificate18012.rectangle,RoutedCases.Batch0900.certificate18014.rectangle,RoutedCases.Batch0900.certificate18016.rectangle,RoutedCases.Batch0900.certificate18018.rectangle,RoutedCases.Batch0901.certificate18023.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18004,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18005,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18006,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18007,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18008,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18010,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18012,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18014,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18016,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18018,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18023,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(237/4000),(19/320),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0900.certificate18004.rectangle,RoutedCases.Batch0900.certificate18005.rectangle,RoutedCases.Batch0900.certificate18006.rectangle,RoutedCases.Batch0900.certificate18007.rectangle,RoutedCases.Batch0900.certificate18009.rectangle,RoutedCases.Batch0900.certificate18011.rectangle,RoutedCases.Batch0900.certificate18013.rectangle,RoutedCases.Batch0900.certificate18015.rectangle,RoutedCases.Batch0900.certificate18019.rectangle,RoutedCases.Batch0901.certificate18024.rectangle,RoutedCases.Batch0901.certificate18025.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18004,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18005,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18006,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18007,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18009,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18011,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18013,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18015,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18019,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18024,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18025,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(19/320),(119/2000),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0900.certificate18004.rectangle,RoutedCases.Batch0900.certificate18005.rectangle,RoutedCases.Batch0900.certificate18006.rectangle,RoutedCases.Batch0900.certificate18007.rectangle,RoutedCases.Batch0900.certificate18009.rectangle,RoutedCases.Batch0900.certificate18011.rectangle,RoutedCases.Batch0900.certificate18013.rectangle,RoutedCases.Batch0900.certificate18015.rectangle,RoutedCases.Batch0900.certificate18019.rectangle,RoutedCases.Batch0901.certificate18024.rectangle,RoutedCases.Batch0901.certificate18026.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18004,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18005,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18006,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18007,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18009,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18011,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18013,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18015,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18019,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18024,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18026,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(59/1000),(119/2000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_nil _⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source398
