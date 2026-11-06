import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0449
import Cycle12.RoutedCases.Batch0450

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source153

def strip0 : RatCoverRectangle := ⟨(131/2000),(1049/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0449.certificate8980.rectangle,RoutedCases.Batch0449.certificate8981.rectangle,RoutedCases.Batch0449.certificate8983.rectangle,RoutedCases.Batch0449.certificate8985.rectangle,RoutedCases.Batch0449.certificate8987.rectangle,RoutedCases.Batch0449.certificate8989.rectangle,RoutedCases.Batch0449.certificate8990.rectangle,RoutedCases.Batch0449.certificate8991.rectangle,RoutedCases.Batch0449.certificate8992.rectangle,RoutedCases.Batch0449.certificate8993.rectangle,RoutedCases.Batch0449.certificate8994.rectangle,RoutedCases.Batch0449.certificate8995.rectangle,RoutedCases.Batch0449.certificate8996.rectangle,RoutedCases.Batch0449.certificate8997.rectangle,RoutedCases.Batch0449.certificate8998.rectangle,RoutedCases.Batch0449.certificate8999.rectangle,RoutedCases.Batch0450.certificate9000.rectangle,RoutedCases.Batch0450.certificate9001.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8980,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8981,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8983,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8985,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8987,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8989,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8990,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8991,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8992,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8993,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8994,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8995,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8996,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8997,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8998,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8999,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9000,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9001,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1049/16000),(21/320),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0449.certificate8982.rectangle,RoutedCases.Batch0449.certificate8984.rectangle,RoutedCases.Batch0449.certificate8986.rectangle,RoutedCases.Batch0449.certificate8988.rectangle,RoutedCases.Batch0449.certificate8989.rectangle,RoutedCases.Batch0449.certificate8990.rectangle,RoutedCases.Batch0449.certificate8991.rectangle,RoutedCases.Batch0449.certificate8992.rectangle,RoutedCases.Batch0449.certificate8993.rectangle,RoutedCases.Batch0449.certificate8994.rectangle,RoutedCases.Batch0449.certificate8995.rectangle,RoutedCases.Batch0449.certificate8996.rectangle,RoutedCases.Batch0449.certificate8997.rectangle,RoutedCases.Batch0449.certificate8998.rectangle,RoutedCases.Batch0449.certificate8999.rectangle,RoutedCases.Batch0450.certificate9000.rectangle,RoutedCases.Batch0450.certificate9001.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8982,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8984,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8986,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8988,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8989,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8990,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8991,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8992,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8993,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8994,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8995,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8996,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8997,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8998,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0449.sound8999,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9000,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9001,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(131/2000),(21/320),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source153
