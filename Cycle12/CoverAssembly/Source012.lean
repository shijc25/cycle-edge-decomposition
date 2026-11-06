import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0019
import Cycle12.RoutedCases.Batch0020
import Cycle12.RoutedCases.Batch0021

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source012

def strip0 : RatCoverRectangle := ⟨(13/1000),(53/4000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0019.certificate382.rectangle,RoutedCases.Batch0019.certificate384.rectangle,RoutedCases.Batch0019.certificate392.rectangle,RoutedCases.Batch0019.certificate399.rectangle,RoutedCases.Batch0020.certificate401.rectangle,RoutedCases.Batch0020.certificate410.rectangle,RoutedCases.Batch0020.certificate412.rectangle,RoutedCases.Batch0021.certificate420.rectangle,RoutedCases.Batch0021.certificate422.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0019.sound382,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0019.sound384,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0019.sound392,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0019.sound399,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0020.sound401,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0020.sound410,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0020.sound412,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0021.sound420,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0021.sound422,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(53/4000),(27/2000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0019.certificate383.rectangle,RoutedCases.Batch0019.certificate385.rectangle,RoutedCases.Batch0019.certificate393.rectangle,RoutedCases.Batch0020.certificate400.rectangle,RoutedCases.Batch0020.certificate402.rectangle,RoutedCases.Batch0020.certificate411.rectangle,RoutedCases.Batch0020.certificate413.rectangle,RoutedCases.Batch0021.certificate421.rectangle,RoutedCases.Batch0021.certificate423.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0019.sound383,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0019.sound385,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0019.sound393,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0020.sound400,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0020.sound402,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0020.sound411,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0020.sound413,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0021.sound421,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0021.sound423,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(27/2000),(11/800),1,(some 2)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0019.certificate386.rectangle,RoutedCases.Batch0019.certificate389.rectangle,RoutedCases.Batch0019.certificate394.rectangle,RoutedCases.Batch0019.certificate397.rectangle,RoutedCases.Batch0020.certificate403.rectangle,RoutedCases.Batch0020.certificate404.rectangle,RoutedCases.Batch0020.certificate407.rectangle,RoutedCases.Batch0020.certificate414.rectangle,RoutedCases.Batch0020.certificate417.rectangle,RoutedCases.Batch0021.certificate424.rectangle,RoutedCases.Batch0021.certificate427.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0019.sound386,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0019.sound389,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0019.sound394,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0019.sound397,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0020.sound403,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0020.sound404,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0020.sound407,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0020.sound414,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0020.sound417,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0021.sound424,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0021.sound427,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(11/800),(7/500),1,(some 2)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0019.certificate387.rectangle,RoutedCases.Batch0019.certificate388.rectangle,RoutedCases.Batch0019.certificate390.rectangle,RoutedCases.Batch0019.certificate391.rectangle,RoutedCases.Batch0019.certificate395.rectangle,RoutedCases.Batch0019.certificate396.rectangle,RoutedCases.Batch0019.certificate398.rectangle,RoutedCases.Batch0020.certificate405.rectangle,RoutedCases.Batch0020.certificate406.rectangle,RoutedCases.Batch0020.certificate408.rectangle,RoutedCases.Batch0020.certificate409.rectangle,RoutedCases.Batch0020.certificate415.rectangle,RoutedCases.Batch0020.certificate416.rectangle,RoutedCases.Batch0020.certificate418.rectangle,RoutedCases.Batch0020.certificate419.rectangle,RoutedCases.Batch0021.certificate425.rectangle,RoutedCases.Batch0021.certificate426.rectangle,RoutedCases.Batch0021.certificate428.rectangle,RoutedCases.Batch0021.certificate429.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0019.sound387,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0019.sound388,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0019.sound390,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0019.sound391,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0019.sound395,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0019.sound396,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0019.sound398,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0020.sound405,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0020.sound406,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0020.sound408,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0020.sound409,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0020.sound415,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0020.sound416,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0020.sound418,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0020.sound419,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0021.sound425,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0021.sound426,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0021.sound428,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0021.sound429,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(13/1000),(7/500),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source012
