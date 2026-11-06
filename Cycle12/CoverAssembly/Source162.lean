import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0458
import Cycle12.RoutedCases.Batch0459

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source162

def strip0 : RatCoverRectangle := ⟨(533/8000),(1067/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0458.certificate9178.rectangle,RoutedCases.Batch0458.certificate9179.rectangle,RoutedCases.Batch0459.certificate9181.rectangle,RoutedCases.Batch0459.certificate9183.rectangle,RoutedCases.Batch0459.certificate9185.rectangle,RoutedCases.Batch0459.certificate9187.rectangle,RoutedCases.Batch0459.certificate9188.rectangle,RoutedCases.Batch0459.certificate9189.rectangle,RoutedCases.Batch0459.certificate9190.rectangle,RoutedCases.Batch0459.certificate9191.rectangle,RoutedCases.Batch0459.certificate9192.rectangle,RoutedCases.Batch0459.certificate9193.rectangle,RoutedCases.Batch0459.certificate9194.rectangle,RoutedCases.Batch0459.certificate9195.rectangle,RoutedCases.Batch0459.certificate9196.rectangle,RoutedCases.Batch0459.certificate9197.rectangle,RoutedCases.Batch0459.certificate9198.rectangle,RoutedCases.Batch0459.certificate9199.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0458.sound9178,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0458.sound9179,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9181,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9183,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9185,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9187,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9188,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9189,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9190,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9191,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9192,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9193,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9194,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9195,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9196,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9197,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9198,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9199,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1067/16000),(267/4000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0459.certificate9180.rectangle,RoutedCases.Batch0459.certificate9182.rectangle,RoutedCases.Batch0459.certificate9184.rectangle,RoutedCases.Batch0459.certificate9186.rectangle,RoutedCases.Batch0459.certificate9187.rectangle,RoutedCases.Batch0459.certificate9188.rectangle,RoutedCases.Batch0459.certificate9189.rectangle,RoutedCases.Batch0459.certificate9190.rectangle,RoutedCases.Batch0459.certificate9191.rectangle,RoutedCases.Batch0459.certificate9192.rectangle,RoutedCases.Batch0459.certificate9193.rectangle,RoutedCases.Batch0459.certificate9194.rectangle,RoutedCases.Batch0459.certificate9195.rectangle,RoutedCases.Batch0459.certificate9196.rectangle,RoutedCases.Batch0459.certificate9197.rectangle,RoutedCases.Batch0459.certificate9198.rectangle,RoutedCases.Batch0459.certificate9199.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9180,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9182,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9184,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9186,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9187,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9188,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9189,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9190,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9191,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9192,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9193,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9194,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9195,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9196,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9197,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9198,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0459.sound9199,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(533/8000),(267/4000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source162
