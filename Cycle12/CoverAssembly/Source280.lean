import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0761
import Cycle12.RoutedCases.Batch0762

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source280

def strip0 : RatCoverRectangle := ⟨(39/1000),(157/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0761.certificate15230.rectangle,RoutedCases.Batch0761.certificate15231.rectangle,RoutedCases.Batch0761.certificate15232.rectangle,RoutedCases.Batch0761.certificate15233.rectangle,RoutedCases.Batch0761.certificate15234.rectangle,RoutedCases.Batch0761.certificate15236.rectangle,RoutedCases.Batch0761.certificate15238.rectangle,RoutedCases.Batch0762.certificate15240.rectangle,RoutedCases.Batch0762.certificate15242.rectangle,RoutedCases.Batch0762.certificate15243.rectangle,RoutedCases.Batch0762.certificate15245.rectangle,RoutedCases.Batch0762.certificate15247.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15230,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15231,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15232,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15233,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15234,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15236,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15238,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0762.sound15240,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0762.sound15242,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0762.sound15243,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0762.sound15245,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0762.sound15247,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(157/4000),(79/2000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0761.certificate15230.rectangle,RoutedCases.Batch0761.certificate15231.rectangle,RoutedCases.Batch0761.certificate15232.rectangle,RoutedCases.Batch0761.certificate15233.rectangle,RoutedCases.Batch0761.certificate15234.rectangle,RoutedCases.Batch0761.certificate15236.rectangle,RoutedCases.Batch0761.certificate15238.rectangle,RoutedCases.Batch0762.certificate15240.rectangle,RoutedCases.Batch0762.certificate15242.rectangle,RoutedCases.Batch0762.certificate15243.rectangle,RoutedCases.Batch0762.certificate15246.rectangle,RoutedCases.Batch0762.certificate15248.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15230,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15231,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15232,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15233,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15234,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15236,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15238,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0762.sound15240,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0762.sound15242,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0762.sound15243,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0762.sound15246,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0762.sound15248,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(79/2000),(159/4000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0761.certificate15230.rectangle,RoutedCases.Batch0761.certificate15231.rectangle,RoutedCases.Batch0761.certificate15232.rectangle,RoutedCases.Batch0761.certificate15233.rectangle,RoutedCases.Batch0761.certificate15235.rectangle,RoutedCases.Batch0761.certificate15237.rectangle,RoutedCases.Batch0761.certificate15239.rectangle,RoutedCases.Batch0762.certificate15241.rectangle,RoutedCases.Batch0762.certificate15244.rectangle,RoutedCases.Batch0762.certificate15249.rectangle,RoutedCases.Batch0762.certificate15251.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15230,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15231,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15232,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15233,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15235,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15237,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15239,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0762.sound15241,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0762.sound15244,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0762.sound15249,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0762.sound15251,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(159/4000),(1/25),5,(some 20)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0761.certificate15230.rectangle,RoutedCases.Batch0761.certificate15231.rectangle,RoutedCases.Batch0761.certificate15232.rectangle,RoutedCases.Batch0761.certificate15233.rectangle,RoutedCases.Batch0761.certificate15235.rectangle,RoutedCases.Batch0761.certificate15237.rectangle,RoutedCases.Batch0761.certificate15239.rectangle,RoutedCases.Batch0762.certificate15241.rectangle,RoutedCases.Batch0762.certificate15244.rectangle,RoutedCases.Batch0762.certificate15250.rectangle,RoutedCases.Batch0762.certificate15252.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15230,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15231,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15232,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15233,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15235,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15237,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0761.sound15239,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0762.sound15241,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0762.sound15244,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0762.sound15250,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0762.sound15252,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(39/1000),(1/25),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source280
