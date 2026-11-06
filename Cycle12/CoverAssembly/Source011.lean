import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0016
import Cycle12.RoutedCases.Batch0017
import Cycle12.RoutedCases.Batch0018
import Cycle12.RoutedCases.Batch0019

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source011

def strip0 : RatCoverRectangle := ⟨(3/250),(49/4000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0016.certificate339.rectangle,RoutedCases.Batch0017.certificate341.rectangle,RoutedCases.Batch0017.certificate349.rectangle,RoutedCases.Batch0017.certificate355.rectangle,RoutedCases.Batch0017.certificate357.rectangle,RoutedCases.Batch0018.certificate365.rectangle,RoutedCases.Batch0018.certificate367.rectangle,RoutedCases.Batch0018.certificate374.rectangle,RoutedCases.Batch0018.certificate376.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound339,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0017.sound341,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0017.sound349,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0017.sound355,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0017.sound357,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0018.sound365,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0018.sound367,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0018.sound374,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0018.sound376,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(49/4000),(1/80),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0017.certificate340.rectangle,RoutedCases.Batch0017.certificate342.rectangle,RoutedCases.Batch0017.certificate350.rectangle,RoutedCases.Batch0017.certificate356.rectangle,RoutedCases.Batch0017.certificate358.rectangle,RoutedCases.Batch0018.certificate366.rectangle,RoutedCases.Batch0018.certificate368.rectangle,RoutedCases.Batch0018.certificate375.rectangle,RoutedCases.Batch0018.certificate377.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0017.sound340,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0017.sound342,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0017.sound350,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0017.sound356,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0017.sound358,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0018.sound366,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0018.sound368,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0018.sound375,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0018.sound377,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(1/80),(51/4000),1,(some 2)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0017.certificate343.rectangle,RoutedCases.Batch0017.certificate346.rectangle,RoutedCases.Batch0017.certificate351.rectangle,RoutedCases.Batch0017.certificate352.rectangle,RoutedCases.Batch0017.certificate359.rectangle,RoutedCases.Batch0018.certificate362.rectangle,RoutedCases.Batch0018.certificate369.rectangle,RoutedCases.Batch0018.certificate371.rectangle,RoutedCases.Batch0018.certificate378.rectangle,RoutedCases.Batch0019.certificate380.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0017.sound343,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0017.sound346,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0017.sound351,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0017.sound352,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0017.sound359,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0018.sound362,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0018.sound369,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0018.sound371,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0018.sound378,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0019.sound380,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(51/4000),(13/1000),1,(some 2)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0017.certificate344.rectangle,RoutedCases.Batch0017.certificate345.rectangle,RoutedCases.Batch0017.certificate347.rectangle,RoutedCases.Batch0017.certificate348.rectangle,RoutedCases.Batch0017.certificate353.rectangle,RoutedCases.Batch0017.certificate354.rectangle,RoutedCases.Batch0018.certificate360.rectangle,RoutedCases.Batch0018.certificate361.rectangle,RoutedCases.Batch0018.certificate363.rectangle,RoutedCases.Batch0018.certificate364.rectangle,RoutedCases.Batch0018.certificate370.rectangle,RoutedCases.Batch0018.certificate372.rectangle,RoutedCases.Batch0018.certificate373.rectangle,RoutedCases.Batch0018.certificate379.rectangle,RoutedCases.Batch0019.certificate381.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0017.sound344,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0017.sound345,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0017.sound347,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0017.sound348,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0017.sound353,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0017.sound354,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0018.sound360,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0018.sound361,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0018.sound363,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0018.sound364,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0018.sound370,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0018.sound372,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0018.sound373,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0018.sound379,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0019.sound381,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/250),(13/1000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source011
