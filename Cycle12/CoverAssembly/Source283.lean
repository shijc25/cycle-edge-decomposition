import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0767
import Cycle12.RoutedCases.Batch0768

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source283

def strip0 : RatCoverRectangle := ⟨(21/500),(169/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0767.certificate15342.rectangle,RoutedCases.Batch0767.certificate15343.rectangle,RoutedCases.Batch0767.certificate15344.rectangle,RoutedCases.Batch0767.certificate15345.rectangle,RoutedCases.Batch0767.certificate15346.rectangle,RoutedCases.Batch0767.certificate15347.rectangle,RoutedCases.Batch0767.certificate15348.rectangle,RoutedCases.Batch0767.certificate15350.rectangle,RoutedCases.Batch0767.certificate15352.rectangle,RoutedCases.Batch0767.certificate15354.rectangle,RoutedCases.Batch0767.certificate15355.rectangle,RoutedCases.Batch0767.certificate15359.rectangle,RoutedCases.Batch0768.certificate15361.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15342,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15343,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15344,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15345,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15346,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15347,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15348,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15350,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15352,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15354,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15355,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15359,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0768.sound15361,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(169/4000),(17/400),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0767.certificate15342.rectangle,RoutedCases.Batch0767.certificate15343.rectangle,RoutedCases.Batch0767.certificate15344.rectangle,RoutedCases.Batch0767.certificate15345.rectangle,RoutedCases.Batch0767.certificate15346.rectangle,RoutedCases.Batch0767.certificate15347.rectangle,RoutedCases.Batch0767.certificate15348.rectangle,RoutedCases.Batch0767.certificate15350.rectangle,RoutedCases.Batch0767.certificate15352.rectangle,RoutedCases.Batch0767.certificate15354.rectangle,RoutedCases.Batch0767.certificate15356.rectangle,RoutedCases.Batch0768.certificate15360.rectangle,RoutedCases.Batch0768.certificate15362.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15342,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15343,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15344,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15345,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15346,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15347,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15348,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15350,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15352,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15354,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15356,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0768.sound15360,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0768.sound15362,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(17/400),(171/4000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0767.certificate15342.rectangle,RoutedCases.Batch0767.certificate15343.rectangle,RoutedCases.Batch0767.certificate15344.rectangle,RoutedCases.Batch0767.certificate15345.rectangle,RoutedCases.Batch0767.certificate15346.rectangle,RoutedCases.Batch0767.certificate15347.rectangle,RoutedCases.Batch0767.certificate15349.rectangle,RoutedCases.Batch0767.certificate15351.rectangle,RoutedCases.Batch0767.certificate15353.rectangle,RoutedCases.Batch0767.certificate15357.rectangle,RoutedCases.Batch0767.certificate15358.rectangle,RoutedCases.Batch0768.certificate15363.rectangle,RoutedCases.Batch0768.certificate15365.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15342,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15343,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15344,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15345,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15346,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15347,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15349,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15351,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15353,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15357,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15358,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0768.sound15363,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0768.sound15365,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(171/4000),(43/1000),5,(some 20)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0767.certificate15342.rectangle,RoutedCases.Batch0767.certificate15343.rectangle,RoutedCases.Batch0767.certificate15344.rectangle,RoutedCases.Batch0767.certificate15345.rectangle,RoutedCases.Batch0767.certificate15346.rectangle,RoutedCases.Batch0767.certificate15347.rectangle,RoutedCases.Batch0767.certificate15349.rectangle,RoutedCases.Batch0767.certificate15351.rectangle,RoutedCases.Batch0767.certificate15353.rectangle,RoutedCases.Batch0767.certificate15357.rectangle,RoutedCases.Batch0767.certificate15358.rectangle,RoutedCases.Batch0768.certificate15364.rectangle,RoutedCases.Batch0768.certificate15366.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15342,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15343,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15344,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15345,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15346,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15347,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15349,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15351,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15353,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15357,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0767.sound15358,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0768.sound15364,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0768.sound15366,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(21/500),(43/1000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source283
