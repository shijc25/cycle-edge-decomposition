import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0740
import Cycle12.RoutedCases.Batch0741

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source267

def strip0 : RatCoverRectangle := ⟨(13/500),(21/800),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0740.certificate14804.rectangle,RoutedCases.Batch0740.certificate14805.rectangle,RoutedCases.Batch0740.certificate14806.rectangle,RoutedCases.Batch0740.certificate14807.rectangle,RoutedCases.Batch0740.certificate14808.rectangle,RoutedCases.Batch0740.certificate14809.rectangle,RoutedCases.Batch0740.certificate14811.rectangle,RoutedCases.Batch0740.certificate14813.rectangle,RoutedCases.Batch0740.certificate14815.rectangle,RoutedCases.Batch0740.certificate14817.rectangle,RoutedCases.Batch0741.certificate14820.rectangle,RoutedCases.Batch0741.certificate14822.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14804,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14805,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14806,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14807,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14808,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14809,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14811,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14813,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14815,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14817,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14820,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14822,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(21/800),(53/2000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0740.certificate14804.rectangle,RoutedCases.Batch0740.certificate14805.rectangle,RoutedCases.Batch0740.certificate14806.rectangle,RoutedCases.Batch0740.certificate14807.rectangle,RoutedCases.Batch0740.certificate14808.rectangle,RoutedCases.Batch0740.certificate14809.rectangle,RoutedCases.Batch0740.certificate14811.rectangle,RoutedCases.Batch0740.certificate14813.rectangle,RoutedCases.Batch0740.certificate14815.rectangle,RoutedCases.Batch0740.certificate14817.rectangle,RoutedCases.Batch0741.certificate14821.rectangle,RoutedCases.Batch0741.certificate14823.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14804,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14805,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14806,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14807,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14808,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14809,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14811,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14813,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14815,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14817,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14821,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14823,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(53/2000),(107/4000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0740.certificate14804.rectangle,RoutedCases.Batch0740.certificate14805.rectangle,RoutedCases.Batch0740.certificate14806.rectangle,RoutedCases.Batch0740.certificate14807.rectangle,RoutedCases.Batch0740.certificate14808.rectangle,RoutedCases.Batch0740.certificate14810.rectangle,RoutedCases.Batch0740.certificate14812.rectangle,RoutedCases.Batch0740.certificate14814.rectangle,RoutedCases.Batch0740.certificate14816.rectangle,RoutedCases.Batch0740.certificate14818.rectangle,RoutedCases.Batch0741.certificate14824.rectangle,RoutedCases.Batch0741.certificate14826.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14804,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14805,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14806,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14807,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14808,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14810,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14812,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14814,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14816,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14818,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14824,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14826,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(107/4000),(27/1000),5,(some 20)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0740.certificate14804.rectangle,RoutedCases.Batch0740.certificate14805.rectangle,RoutedCases.Batch0740.certificate14806.rectangle,RoutedCases.Batch0740.certificate14807.rectangle,RoutedCases.Batch0740.certificate14808.rectangle,RoutedCases.Batch0740.certificate14810.rectangle,RoutedCases.Batch0740.certificate14812.rectangle,RoutedCases.Batch0740.certificate14814.rectangle,RoutedCases.Batch0740.certificate14816.rectangle,RoutedCases.Batch0740.certificate14819.rectangle,RoutedCases.Batch0741.certificate14825.rectangle,RoutedCases.Batch0741.certificate14827.rectangle,RoutedCases.Batch0741.certificate14828.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14804,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14805,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14806,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14807,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14808,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14810,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14812,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14814,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14816,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14819,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14825,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14827,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14828,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(13/500),(27/1000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source267
