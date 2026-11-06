import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0847
import Cycle12.RoutedCases.Batch0848

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source360

def strip0 : RatCoverRectangle := ⟨(1/40),(101/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0847.certificate16941.rectangle,RoutedCases.Batch0847.certificate16942.rectangle,RoutedCases.Batch0847.certificate16943.rectangle,RoutedCases.Batch0847.certificate16944.rectangle,RoutedCases.Batch0847.certificate16945.rectangle,RoutedCases.Batch0847.certificate16947.rectangle,RoutedCases.Batch0847.certificate16949.rectangle,RoutedCases.Batch0847.certificate16951.rectangle,RoutedCases.Batch0847.certificate16953.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16941,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16942,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16943,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16944,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16945,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16947,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16949,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16951,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16953,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(101/4000),(51/2000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0847.certificate16941.rectangle,RoutedCases.Batch0847.certificate16942.rectangle,RoutedCases.Batch0847.certificate16943.rectangle,RoutedCases.Batch0847.certificate16944.rectangle,RoutedCases.Batch0847.certificate16945.rectangle,RoutedCases.Batch0847.certificate16947.rectangle,RoutedCases.Batch0847.certificate16949.rectangle,RoutedCases.Batch0847.certificate16952.rectangle,RoutedCases.Batch0847.certificate16954.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16941,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16942,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16943,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16944,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16945,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16947,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16949,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16952,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16954,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(51/2000),(103/4000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0847.certificate16941.rectangle,RoutedCases.Batch0847.certificate16942.rectangle,RoutedCases.Batch0847.certificate16943.rectangle,RoutedCases.Batch0847.certificate16944.rectangle,RoutedCases.Batch0847.certificate16946.rectangle,RoutedCases.Batch0847.certificate16948.rectangle,RoutedCases.Batch0847.certificate16950.rectangle,RoutedCases.Batch0847.certificate16955.rectangle,RoutedCases.Batch0847.certificate16957.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16941,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16942,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16943,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16944,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16946,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16948,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16950,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16955,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16957,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(103/4000),(207/8000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0847.certificate16941.rectangle,RoutedCases.Batch0847.certificate16942.rectangle,RoutedCases.Batch0847.certificate16943.rectangle,RoutedCases.Batch0847.certificate16944.rectangle,RoutedCases.Batch0847.certificate16946.rectangle,RoutedCases.Batch0847.certificate16948.rectangle,RoutedCases.Batch0847.certificate16950.rectangle,RoutedCases.Batch0847.certificate16956.rectangle,RoutedCases.Batch0847.certificate16958.rectangle,RoutedCases.Batch0848.certificate16960.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16941,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16942,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16943,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16944,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16946,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16948,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16950,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16956,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16958,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16960,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(207/8000),(83/3200),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0847.certificate16941.rectangle,RoutedCases.Batch0847.certificate16942.rectangle,RoutedCases.Batch0847.certificate16943.rectangle,RoutedCases.Batch0847.certificate16944.rectangle,RoutedCases.Batch0847.certificate16946.rectangle,RoutedCases.Batch0847.certificate16948.rectangle,RoutedCases.Batch0847.certificate16950.rectangle,RoutedCases.Batch0847.certificate16956.rectangle,RoutedCases.Batch0847.certificate16959.rectangle,RoutedCases.Batch0848.certificate16961.rectangle,RoutedCases.Batch0848.certificate16962.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16941,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16942,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16943,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16944,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16946,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16948,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16950,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16956,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16959,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16961,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16962,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip5 : RatCoverRectangle := ⟨(83/3200),(13/500),20,(some 100)⟩
def pieces5 : List RatCoverRectangle := [RoutedCases.Batch0847.certificate16941.rectangle,RoutedCases.Batch0847.certificate16942.rectangle,RoutedCases.Batch0847.certificate16943.rectangle,RoutedCases.Batch0847.certificate16944.rectangle,RoutedCases.Batch0847.certificate16946.rectangle,RoutedCases.Batch0847.certificate16948.rectangle,RoutedCases.Batch0847.certificate16950.rectangle,RoutedCases.Batch0847.certificate16956.rectangle,RoutedCases.Batch0847.certificate16959.rectangle,RoutedCases.Batch0848.certificate16961.rectangle,RoutedCases.Batch0848.certificate16963.rectangle]
theorem valid5 : strip5.JoinS pieces5 := by decide +kernel
theorem sound5 : strip5.Sound := rat_cover_join_s_sound strip5 pieces5 valid5 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16941,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16942,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16943,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16944,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16946,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16948,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16950,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16956,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16959,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16961,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16963,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(1/40),(13/500),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4,strip5]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source360
