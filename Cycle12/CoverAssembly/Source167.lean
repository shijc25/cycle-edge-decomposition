import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0464
import Cycle12.RoutedCases.Batch0465
import Cycle12.RoutedCases.Batch0466

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source167

def strip0 : RatCoverRectangle := ⟨(3/1000),(13/4000),2,(some 5)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0464.certificate9299.rectangle,RoutedCases.Batch0465.certificate9302.rectangle,RoutedCases.Batch0465.certificate9317.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0464.sound9299,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9302,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9317,List.forall_mem_nil _⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(13/4000),(7/2000),2,(some 5)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0465.certificate9300.rectangle,RoutedCases.Batch0465.certificate9301.rectangle,RoutedCases.Batch0465.certificate9303.rectangle,RoutedCases.Batch0465.certificate9318.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9300,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9301,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9303,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9318,List.forall_mem_nil _⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(7/2000),(29/8000),2,(some 5)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0465.certificate9304.rectangle,RoutedCases.Batch0465.certificate9306.rectangle,RoutedCases.Batch0465.certificate9311.rectangle,RoutedCases.Batch0465.certificate9312.rectangle,RoutedCases.Batch0465.certificate9319.rectangle,RoutedCases.Batch0466.certificate9324.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9304,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9306,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9311,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9312,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9319,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0466.sound9324,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(29/8000),(3/800),2,(some 5)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0465.certificate9305.rectangle,RoutedCases.Batch0465.certificate9306.rectangle,RoutedCases.Batch0465.certificate9311.rectangle,RoutedCases.Batch0465.certificate9312.rectangle,RoutedCases.Batch0465.certificate9319.rectangle,RoutedCases.Batch0466.certificate9324.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9305,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9306,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9311,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9312,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9319,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0466.sound9324,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(3/800),(31/8000),2,(some 5)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0465.certificate9307.rectangle,RoutedCases.Batch0465.certificate9309.rectangle,RoutedCases.Batch0465.certificate9313.rectangle,RoutedCases.Batch0465.certificate9315.rectangle,RoutedCases.Batch0466.certificate9320.rectangle,RoutedCases.Batch0466.certificate9322.rectangle,RoutedCases.Batch0466.certificate9325.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9307,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9309,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9313,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9315,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0466.sound9320,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0466.sound9322,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0466.sound9325,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip5 : RatCoverRectangle := ⟨(31/8000),(1/250),2,(some 5)⟩
def pieces5 : List RatCoverRectangle := [RoutedCases.Batch0465.certificate9308.rectangle,RoutedCases.Batch0465.certificate9310.rectangle,RoutedCases.Batch0465.certificate9314.rectangle,RoutedCases.Batch0465.certificate9316.rectangle,RoutedCases.Batch0466.certificate9321.rectangle,RoutedCases.Batch0466.certificate9323.rectangle,RoutedCases.Batch0466.certificate9326.rectangle]
theorem valid5 : strip5.JoinS pieces5 := by decide +kernel
theorem sound5 : strip5.Sound := rat_cover_join_s_sound strip5 pieces5 valid5 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9308,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9310,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9314,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0465.sound9316,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0466.sound9321,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0466.sound9323,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0466.sound9326,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/1000),(1/250),2,(some 5)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4,strip5]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source167
