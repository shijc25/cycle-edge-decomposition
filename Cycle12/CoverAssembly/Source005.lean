import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0001
import Cycle12.RoutedCases.Batch0002

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source005

def strip0 : RatCoverRectangle := ⟨(3/500),(1/160),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0001.certificate35.rectangle,RoutedCases.Batch0001.certificate36.rectangle,RoutedCases.Batch0002.certificate41.rectangle,RoutedCases.Batch0002.certificate46.rectangle,RoutedCases.Batch0002.certificate47.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound35,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound36,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound41,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound46,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound47,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1/160),(13/2000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0001.certificate35.rectangle,RoutedCases.Batch0001.certificate36.rectangle,RoutedCases.Batch0002.certificate42.rectangle,RoutedCases.Batch0002.certificate46.rectangle,RoutedCases.Batch0002.certificate47.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound35,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound36,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound42,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound46,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound47,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(13/2000),(27/4000),1,(some 2)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0001.certificate37.rectangle,RoutedCases.Batch0001.certificate39.rectangle,RoutedCases.Batch0002.certificate43.rectangle,RoutedCases.Batch0002.certificate48.rectangle,RoutedCases.Batch0002.certificate50.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound37,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound39,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound43,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound48,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound50,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(27/4000),(7/1000),1,(some 2)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0001.certificate38.rectangle,RoutedCases.Batch0002.certificate40.rectangle,RoutedCases.Batch0002.certificate44.rectangle,RoutedCases.Batch0002.certificate45.rectangle,RoutedCases.Batch0002.certificate49.rectangle,RoutedCases.Batch0002.certificate51.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound38,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound40,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound44,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound45,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound49,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound51,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/500),(7/1000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source005
