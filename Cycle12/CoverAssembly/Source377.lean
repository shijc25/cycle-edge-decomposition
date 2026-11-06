import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0873
import Cycle12.RoutedCases.Batch0874
import Cycle12.RoutedCases.Batch0875

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source377

def strip0 : RatCoverRectangle := ⟨(21/500),(337/8000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0873.certificate17476.rectangle,RoutedCases.Batch0873.certificate17477.rectangle,RoutedCases.Batch0873.certificate17478.rectangle,RoutedCases.Batch0873.certificate17479.rectangle,RoutedCases.Batch0874.certificate17480.rectangle,RoutedCases.Batch0874.certificate17482.rectangle,RoutedCases.Batch0874.certificate17484.rectangle,RoutedCases.Batch0874.certificate17486.rectangle,RoutedCases.Batch0874.certificate17492.rectangle,RoutedCases.Batch0874.certificate17494.rectangle,RoutedCases.Batch0874.certificate17495.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17476,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17477,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17478,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17479,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17480,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17482,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17484,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17486,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17492,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17494,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17495,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(337/8000),(169/4000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0873.certificate17476.rectangle,RoutedCases.Batch0873.certificate17477.rectangle,RoutedCases.Batch0873.certificate17478.rectangle,RoutedCases.Batch0873.certificate17479.rectangle,RoutedCases.Batch0874.certificate17480.rectangle,RoutedCases.Batch0874.certificate17482.rectangle,RoutedCases.Batch0874.certificate17484.rectangle,RoutedCases.Batch0874.certificate17486.rectangle,RoutedCases.Batch0874.certificate17492.rectangle,RoutedCases.Batch0874.certificate17494.rectangle,RoutedCases.Batch0874.certificate17496.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17476,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17477,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17478,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17479,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17480,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17482,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17484,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17486,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17492,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17494,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17496,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(169/4000),(339/8000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0873.certificate17476.rectangle,RoutedCases.Batch0873.certificate17477.rectangle,RoutedCases.Batch0873.certificate17478.rectangle,RoutedCases.Batch0873.certificate17479.rectangle,RoutedCases.Batch0874.certificate17480.rectangle,RoutedCases.Batch0874.certificate17482.rectangle,RoutedCases.Batch0874.certificate17485.rectangle,RoutedCases.Batch0874.certificate17487.rectangle,RoutedCases.Batch0874.certificate17493.rectangle,RoutedCases.Batch0874.certificate17497.rectangle,RoutedCases.Batch0874.certificate17498.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17476,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17477,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17478,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17479,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17480,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17482,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17485,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17487,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17493,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17497,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17498,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(339/8000),(17/400),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0873.certificate17476.rectangle,RoutedCases.Batch0873.certificate17477.rectangle,RoutedCases.Batch0873.certificate17478.rectangle,RoutedCases.Batch0873.certificate17479.rectangle,RoutedCases.Batch0874.certificate17480.rectangle,RoutedCases.Batch0874.certificate17482.rectangle,RoutedCases.Batch0874.certificate17485.rectangle,RoutedCases.Batch0874.certificate17487.rectangle,RoutedCases.Batch0874.certificate17493.rectangle,RoutedCases.Batch0874.certificate17497.rectangle,RoutedCases.Batch0874.certificate17499.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17476,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17477,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17478,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17479,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17480,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17482,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17485,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17487,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17493,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17497,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17499,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(17/400),(341/8000),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0873.certificate17476.rectangle,RoutedCases.Batch0873.certificate17477.rectangle,RoutedCases.Batch0873.certificate17478.rectangle,RoutedCases.Batch0873.certificate17479.rectangle,RoutedCases.Batch0874.certificate17481.rectangle,RoutedCases.Batch0874.certificate17483.rectangle,RoutedCases.Batch0874.certificate17488.rectangle,RoutedCases.Batch0874.certificate17490.rectangle,RoutedCases.Batch0875.certificate17500.rectangle,RoutedCases.Batch0875.certificate17502.rectangle,RoutedCases.Batch0875.certificate17503.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17476,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17477,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17478,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17479,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17481,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17483,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17488,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17490,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0875.sound17500,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0875.sound17502,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0875.sound17503,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip5 : RatCoverRectangle := ⟨(341/8000),(171/4000),20,(some 100)⟩
def pieces5 : List RatCoverRectangle := [RoutedCases.Batch0873.certificate17476.rectangle,RoutedCases.Batch0873.certificate17477.rectangle,RoutedCases.Batch0873.certificate17478.rectangle,RoutedCases.Batch0873.certificate17479.rectangle,RoutedCases.Batch0874.certificate17481.rectangle,RoutedCases.Batch0874.certificate17483.rectangle,RoutedCases.Batch0874.certificate17488.rectangle,RoutedCases.Batch0874.certificate17490.rectangle,RoutedCases.Batch0875.certificate17500.rectangle,RoutedCases.Batch0875.certificate17502.rectangle,RoutedCases.Batch0875.certificate17504.rectangle]
theorem valid5 : strip5.JoinS pieces5 := by decide +kernel
theorem sound5 : strip5.Sound := rat_cover_join_s_sound strip5 pieces5 valid5 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17476,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17477,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17478,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17479,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17481,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17483,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17488,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17490,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0875.sound17500,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0875.sound17502,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0875.sound17504,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip6 : RatCoverRectangle := ⟨(171/4000),(343/8000),20,(some 100)⟩
def pieces6 : List RatCoverRectangle := [RoutedCases.Batch0873.certificate17476.rectangle,RoutedCases.Batch0873.certificate17477.rectangle,RoutedCases.Batch0873.certificate17478.rectangle,RoutedCases.Batch0873.certificate17479.rectangle,RoutedCases.Batch0874.certificate17481.rectangle,RoutedCases.Batch0874.certificate17483.rectangle,RoutedCases.Batch0874.certificate17489.rectangle,RoutedCases.Batch0874.certificate17491.rectangle,RoutedCases.Batch0875.certificate17501.rectangle,RoutedCases.Batch0875.certificate17505.rectangle,RoutedCases.Batch0875.certificate17507.rectangle]
theorem valid6 : strip6.JoinS pieces6 := by decide +kernel
theorem sound6 : strip6.Sound := rat_cover_join_s_sound strip6 pieces6 valid6 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17476,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17477,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17478,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17479,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17481,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17483,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17489,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17491,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0875.sound17501,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0875.sound17505,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0875.sound17507,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip7 : RatCoverRectangle := ⟨(343/8000),(43/1000),20,(some 100)⟩
def pieces7 : List RatCoverRectangle := [RoutedCases.Batch0873.certificate17476.rectangle,RoutedCases.Batch0873.certificate17477.rectangle,RoutedCases.Batch0873.certificate17478.rectangle,RoutedCases.Batch0873.certificate17479.rectangle,RoutedCases.Batch0874.certificate17481.rectangle,RoutedCases.Batch0874.certificate17483.rectangle,RoutedCases.Batch0874.certificate17489.rectangle,RoutedCases.Batch0874.certificate17491.rectangle,RoutedCases.Batch0875.certificate17501.rectangle,RoutedCases.Batch0875.certificate17506.rectangle,RoutedCases.Batch0875.certificate17508.rectangle]
theorem valid7 : strip7.JoinS pieces7 := by decide +kernel
theorem sound7 : strip7.Sound := rat_cover_join_s_sound strip7 pieces7 valid7 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17476,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17477,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17478,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0873.sound17479,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17481,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17483,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17489,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0874.sound17491,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0875.sound17501,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0875.sound17506,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0875.sound17508,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(21/500),(43/1000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4,strip5,strip6,strip7]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_cons.mpr ⟨sound6,List.forall_mem_cons.mpr ⟨sound7,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source377
