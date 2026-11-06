import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0407

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source120

def strip0 : RatCoverRectangle := ⟨(121/2000),(97/1600),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0407.certificate8143.rectangle,RoutedCases.Batch0407.certificate8145.rectangle,RoutedCases.Batch0407.certificate8146.rectangle,RoutedCases.Batch0407.certificate8147.rectangle,RoutedCases.Batch0407.certificate8148.rectangle,RoutedCases.Batch0407.certificate8149.rectangle,RoutedCases.Batch0407.certificate8150.rectangle,RoutedCases.Batch0407.certificate8151.rectangle,RoutedCases.Batch0407.certificate8152.rectangle,RoutedCases.Batch0407.certificate8153.rectangle,RoutedCases.Batch0407.certificate8154.rectangle,RoutedCases.Batch0407.certificate8155.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8143,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8145,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8146,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8147,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8148,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8149,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8150,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8151,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8152,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8153,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8154,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8155,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(97/1600),(243/4000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0407.certificate8144.rectangle,RoutedCases.Batch0407.certificate8145.rectangle,RoutedCases.Batch0407.certificate8146.rectangle,RoutedCases.Batch0407.certificate8147.rectangle,RoutedCases.Batch0407.certificate8148.rectangle,RoutedCases.Batch0407.certificate8149.rectangle,RoutedCases.Batch0407.certificate8150.rectangle,RoutedCases.Batch0407.certificate8151.rectangle,RoutedCases.Batch0407.certificate8152.rectangle,RoutedCases.Batch0407.certificate8153.rectangle,RoutedCases.Batch0407.certificate8154.rectangle,RoutedCases.Batch0407.certificate8155.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8144,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8145,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8146,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8147,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8148,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8149,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8150,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8151,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8152,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8153,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8154,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8155,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(121/2000),(243/4000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source120
