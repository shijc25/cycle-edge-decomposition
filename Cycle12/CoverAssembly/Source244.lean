import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0710
import Cycle12.RoutedCases.Batch0711

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source244

def strip0 : RatCoverRectangle := ⟨(1/200),(21/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0710.certificate14213.rectangle,RoutedCases.Batch0710.certificate14215.rectangle,RoutedCases.Batch0710.certificate14217.rectangle,RoutedCases.Batch0711.certificate14222.rectangle,RoutedCases.Batch0711.certificate14227.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14213,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14215,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14217,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14222,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14227,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(21/4000),(11/2000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0710.certificate14213.rectangle,RoutedCases.Batch0710.certificate14215.rectangle,RoutedCases.Batch0710.certificate14217.rectangle,RoutedCases.Batch0711.certificate14222.rectangle,RoutedCases.Batch0711.certificate14228.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14213,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14215,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14217,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14222,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14228,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(11/2000),(23/4000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0710.certificate14214.rectangle,RoutedCases.Batch0710.certificate14216.rectangle,RoutedCases.Batch0710.certificate14218.rectangle,RoutedCases.Batch0711.certificate14220.rectangle,RoutedCases.Batch0711.certificate14223.rectangle,RoutedCases.Batch0711.certificate14225.rectangle,RoutedCases.Batch0711.certificate14229.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14214,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14216,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14218,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14220,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14223,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14225,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14229,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(23/4000),(47/8000),5,(some 20)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0710.certificate14214.rectangle,RoutedCases.Batch0710.certificate14216.rectangle,RoutedCases.Batch0710.certificate14219.rectangle,RoutedCases.Batch0711.certificate14221.rectangle,RoutedCases.Batch0711.certificate14224.rectangle,RoutedCases.Batch0711.certificate14226.rectangle,RoutedCases.Batch0711.certificate14230.rectangle,RoutedCases.Batch0711.certificate14232.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14214,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14216,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14219,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14221,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14224,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14226,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14230,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14232,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(47/8000),(3/500),5,(some 20)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0710.certificate14214.rectangle,RoutedCases.Batch0710.certificate14216.rectangle,RoutedCases.Batch0710.certificate14219.rectangle,RoutedCases.Batch0711.certificate14221.rectangle,RoutedCases.Batch0711.certificate14224.rectangle,RoutedCases.Batch0711.certificate14226.rectangle,RoutedCases.Batch0711.certificate14231.rectangle,RoutedCases.Batch0711.certificate14232.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14214,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14216,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14219,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14221,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14224,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14226,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14231,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14232,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(1/200),(3/500),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_nil _⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source244
