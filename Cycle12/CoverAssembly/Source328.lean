import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0823
import Cycle12.RoutedCases.Batch0824

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source328

def strip0 : RatCoverRectangle := ⟨(3/1000),(7/2000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0823.certificate16476.rectangle,RoutedCases.Batch0823.certificate16478.rectangle,RoutedCases.Batch0824.certificate16480.rectangle,RoutedCases.Batch0824.certificate16485.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0823.sound16476,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0823.sound16478,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16480,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16485,List.forall_mem_nil _⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(7/2000),(3/800),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0823.certificate16477.rectangle,RoutedCases.Batch0823.certificate16479.rectangle,RoutedCases.Batch0824.certificate16481.rectangle,RoutedCases.Batch0824.certificate16483.rectangle,RoutedCases.Batch0824.certificate16486.rectangle,RoutedCases.Batch0824.certificate16488.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0823.sound16477,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0823.sound16479,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16481,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16483,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16486,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16488,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(3/800),(31/8000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0823.certificate16477.rectangle,RoutedCases.Batch0823.certificate16479.rectangle,RoutedCases.Batch0824.certificate16482.rectangle,RoutedCases.Batch0824.certificate16484.rectangle,RoutedCases.Batch0824.certificate16487.rectangle,RoutedCases.Batch0824.certificate16489.rectangle,RoutedCases.Batch0824.certificate16491.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0823.sound16477,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0823.sound16479,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16482,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16484,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16487,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16489,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16491,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(31/8000),(1/250),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0823.certificate16477.rectangle,RoutedCases.Batch0823.certificate16479.rectangle,RoutedCases.Batch0824.certificate16482.rectangle,RoutedCases.Batch0824.certificate16484.rectangle,RoutedCases.Batch0824.certificate16487.rectangle,RoutedCases.Batch0824.certificate16490.rectangle,RoutedCases.Batch0824.certificate16492.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0823.sound16477,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0823.sound16479,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16482,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16484,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16487,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16490,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16492,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/1000),(1/250),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source328
