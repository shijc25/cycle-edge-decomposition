import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0793
import Cycle12.RoutedCases.Batch0794

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source303

def strip0 : RatCoverRectangle := ⟨(57/1000),(457/8000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0793.certificate15864.rectangle,RoutedCases.Batch0793.certificate15865.rectangle,RoutedCases.Batch0793.certificate15866.rectangle,RoutedCases.Batch0793.certificate15867.rectangle,RoutedCases.Batch0793.certificate15868.rectangle,RoutedCases.Batch0793.certificate15869.rectangle,RoutedCases.Batch0793.certificate15870.rectangle,RoutedCases.Batch0793.certificate15871.rectangle,RoutedCases.Batch0793.certificate15873.rectangle,RoutedCases.Batch0793.certificate15875.rectangle,RoutedCases.Batch0793.certificate15877.rectangle,RoutedCases.Batch0793.certificate15878.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15864,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15865,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15866,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15867,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15868,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15869,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15870,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15871,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15873,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15875,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15877,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15878,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(457/8000),(229/4000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0793.certificate15864.rectangle,RoutedCases.Batch0793.certificate15865.rectangle,RoutedCases.Batch0793.certificate15866.rectangle,RoutedCases.Batch0793.certificate15867.rectangle,RoutedCases.Batch0793.certificate15868.rectangle,RoutedCases.Batch0793.certificate15869.rectangle,RoutedCases.Batch0793.certificate15870.rectangle,RoutedCases.Batch0793.certificate15871.rectangle,RoutedCases.Batch0793.certificate15873.rectangle,RoutedCases.Batch0793.certificate15875.rectangle,RoutedCases.Batch0793.certificate15877.rectangle,RoutedCases.Batch0793.certificate15879.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15864,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15865,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15866,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15867,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15868,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15869,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15870,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15871,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15873,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15875,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15877,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15879,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(229/4000),(23/400),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0793.certificate15864.rectangle,RoutedCases.Batch0793.certificate15865.rectangle,RoutedCases.Batch0793.certificate15866.rectangle,RoutedCases.Batch0793.certificate15867.rectangle,RoutedCases.Batch0793.certificate15868.rectangle,RoutedCases.Batch0793.certificate15869.rectangle,RoutedCases.Batch0793.certificate15870.rectangle,RoutedCases.Batch0793.certificate15872.rectangle,RoutedCases.Batch0793.certificate15874.rectangle,RoutedCases.Batch0793.certificate15876.rectangle,RoutedCases.Batch0794.certificate15880.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15864,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15865,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15866,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15867,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15868,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15869,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15870,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15872,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15874,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15876,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15880,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(57/1000),(23/400),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source303
