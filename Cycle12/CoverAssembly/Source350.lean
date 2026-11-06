import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0839
import Cycle12.RoutedCases.Batch0840

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source350

def strip0 : RatCoverRectangle := ⟨(9/500),(73/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0839.certificate16791.rectangle,RoutedCases.Batch0839.certificate16792.rectangle,RoutedCases.Batch0839.certificate16793.rectangle,RoutedCases.Batch0839.certificate16794.rectangle,RoutedCases.Batch0839.certificate16796.rectangle,RoutedCases.Batch0839.certificate16798.rectangle,RoutedCases.Batch0840.certificate16802.rectangle,RoutedCases.Batch0840.certificate16804.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16791,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16792,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16793,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16794,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16796,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16798,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16802,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16804,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(73/4000),(37/2000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0839.certificate16791.rectangle,RoutedCases.Batch0839.certificate16792.rectangle,RoutedCases.Batch0839.certificate16793.rectangle,RoutedCases.Batch0839.certificate16794.rectangle,RoutedCases.Batch0839.certificate16796.rectangle,RoutedCases.Batch0839.certificate16798.rectangle,RoutedCases.Batch0840.certificate16803.rectangle,RoutedCases.Batch0840.certificate16805.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16791,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16792,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16793,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16794,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16796,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16798,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16803,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16805,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(37/2000),(3/160),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0839.certificate16791.rectangle,RoutedCases.Batch0839.certificate16792.rectangle,RoutedCases.Batch0839.certificate16793.rectangle,RoutedCases.Batch0839.certificate16795.rectangle,RoutedCases.Batch0839.certificate16797.rectangle,RoutedCases.Batch0839.certificate16799.rectangle,RoutedCases.Batch0840.certificate16800.rectangle,RoutedCases.Batch0840.certificate16806.rectangle,RoutedCases.Batch0840.certificate16810.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16791,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16792,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16793,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16795,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16797,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16799,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16800,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16806,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16810,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(3/160),(151/8000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0839.certificate16791.rectangle,RoutedCases.Batch0839.certificate16792.rectangle,RoutedCases.Batch0839.certificate16793.rectangle,RoutedCases.Batch0839.certificate16795.rectangle,RoutedCases.Batch0839.certificate16797.rectangle,RoutedCases.Batch0839.certificate16799.rectangle,RoutedCases.Batch0840.certificate16801.rectangle,RoutedCases.Batch0840.certificate16807.rectangle,RoutedCases.Batch0840.certificate16809.rectangle,RoutedCases.Batch0840.certificate16811.rectangle,RoutedCases.Batch0840.certificate16815.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16791,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16792,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16793,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16795,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16797,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16799,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16801,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16807,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16809,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16811,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16815,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(151/8000),(303/16000),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0839.certificate16791.rectangle,RoutedCases.Batch0839.certificate16792.rectangle,RoutedCases.Batch0839.certificate16793.rectangle,RoutedCases.Batch0839.certificate16795.rectangle,RoutedCases.Batch0839.certificate16797.rectangle,RoutedCases.Batch0839.certificate16799.rectangle,RoutedCases.Batch0840.certificate16801.rectangle,RoutedCases.Batch0840.certificate16808.rectangle,RoutedCases.Batch0840.certificate16809.rectangle,RoutedCases.Batch0840.certificate16812.rectangle,RoutedCases.Batch0840.certificate16813.rectangle,RoutedCases.Batch0840.certificate16816.rectangle,RoutedCases.Batch0840.certificate16818.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16791,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16792,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16793,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16795,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16797,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16799,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16801,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16808,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16809,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16812,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16813,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16816,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16818,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip5 : RatCoverRectangle := ⟨(303/16000),(19/1000),20,(some 100)⟩
def pieces5 : List RatCoverRectangle := [RoutedCases.Batch0839.certificate16791.rectangle,RoutedCases.Batch0839.certificate16792.rectangle,RoutedCases.Batch0839.certificate16793.rectangle,RoutedCases.Batch0839.certificate16795.rectangle,RoutedCases.Batch0839.certificate16797.rectangle,RoutedCases.Batch0839.certificate16799.rectangle,RoutedCases.Batch0840.certificate16801.rectangle,RoutedCases.Batch0840.certificate16808.rectangle,RoutedCases.Batch0840.certificate16809.rectangle,RoutedCases.Batch0840.certificate16812.rectangle,RoutedCases.Batch0840.certificate16814.rectangle,RoutedCases.Batch0840.certificate16817.rectangle,RoutedCases.Batch0840.certificate16819.rectangle]
theorem valid5 : strip5.JoinS pieces5 := by decide +kernel
theorem sound5 : strip5.Sound := rat_cover_join_s_sound strip5 pieces5 valid5 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16791,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16792,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16793,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16795,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16797,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16799,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16801,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16808,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16809,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16812,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16814,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16817,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0840.sound16819,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(9/500),(19/1000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4,strip5]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source350
