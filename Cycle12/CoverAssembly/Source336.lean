import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0829
import Cycle12.RoutedCases.Batch0830

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source336

def strip0 : RatCoverRectangle := ⟨(9/1000),(37/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0829.certificate16588.rectangle,RoutedCases.Batch0829.certificate16589.rectangle,RoutedCases.Batch0829.certificate16590.rectangle,RoutedCases.Batch0829.certificate16591.rectangle,RoutedCases.Batch0829.certificate16593.rectangle,RoutedCases.Batch0829.certificate16597.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16588,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16589,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16590,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16591,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16593,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16597,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(37/4000),(3/320),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0829.certificate16588.rectangle,RoutedCases.Batch0829.certificate16589.rectangle,RoutedCases.Batch0829.certificate16590.rectangle,RoutedCases.Batch0829.certificate16592.rectangle,RoutedCases.Batch0829.certificate16594.rectangle,RoutedCases.Batch0829.certificate16595.rectangle,RoutedCases.Batch0829.certificate16598.rectangle,RoutedCases.Batch0830.certificate16600.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16588,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16589,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16590,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16592,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16594,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16595,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16598,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16600,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(3/320),(151/16000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0829.certificate16588.rectangle,RoutedCases.Batch0829.certificate16589.rectangle,RoutedCases.Batch0829.certificate16590.rectangle,RoutedCases.Batch0829.certificate16592.rectangle,RoutedCases.Batch0829.certificate16594.rectangle,RoutedCases.Batch0829.certificate16596.rectangle,RoutedCases.Batch0829.certificate16599.rectangle,RoutedCases.Batch0830.certificate16601.rectangle,RoutedCases.Batch0830.certificate16602.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16588,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16589,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16590,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16592,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16594,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16596,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16599,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16601,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16602,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(151/16000),(303/32000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0829.certificate16588.rectangle,RoutedCases.Batch0829.certificate16589.rectangle,RoutedCases.Batch0829.certificate16590.rectangle,RoutedCases.Batch0829.certificate16592.rectangle,RoutedCases.Batch0829.certificate16594.rectangle,RoutedCases.Batch0829.certificate16596.rectangle,RoutedCases.Batch0829.certificate16599.rectangle,RoutedCases.Batch0830.certificate16601.rectangle,RoutedCases.Batch0830.certificate16603.rectangle,RoutedCases.Batch0830.certificate16604.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16588,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16589,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16590,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16592,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16594,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16596,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16599,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16601,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16603,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16604,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(303/32000),(19/2000),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0829.certificate16588.rectangle,RoutedCases.Batch0829.certificate16589.rectangle,RoutedCases.Batch0829.certificate16590.rectangle,RoutedCases.Batch0829.certificate16592.rectangle,RoutedCases.Batch0829.certificate16594.rectangle,RoutedCases.Batch0829.certificate16596.rectangle,RoutedCases.Batch0829.certificate16599.rectangle,RoutedCases.Batch0830.certificate16601.rectangle,RoutedCases.Batch0830.certificate16603.rectangle,RoutedCases.Batch0830.certificate16605.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16588,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16589,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16590,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16592,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16594,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16596,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16599,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16601,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16603,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16605,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(9/1000),(19/2000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_nil _⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source336
