import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0460
import Cycle12.RoutedCases.Batch0461

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source163

def strip0 : RatCoverRectangle := ⟨(267/4000),(1069/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0460.certificate9200.rectangle,RoutedCases.Batch0460.certificate9201.rectangle,RoutedCases.Batch0460.certificate9203.rectangle,RoutedCases.Batch0460.certificate9205.rectangle,RoutedCases.Batch0460.certificate9207.rectangle,RoutedCases.Batch0460.certificate9209.rectangle,RoutedCases.Batch0460.certificate9210.rectangle,RoutedCases.Batch0460.certificate9211.rectangle,RoutedCases.Batch0460.certificate9212.rectangle,RoutedCases.Batch0460.certificate9213.rectangle,RoutedCases.Batch0460.certificate9214.rectangle,RoutedCases.Batch0460.certificate9215.rectangle,RoutedCases.Batch0460.certificate9216.rectangle,RoutedCases.Batch0460.certificate9217.rectangle,RoutedCases.Batch0460.certificate9218.rectangle,RoutedCases.Batch0460.certificate9219.rectangle,RoutedCases.Batch0461.certificate9220.rectangle,RoutedCases.Batch0461.certificate9221.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9200,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9201,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9203,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9205,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9207,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9209,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9210,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9211,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9212,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9213,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9214,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9215,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9216,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9217,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9218,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9219,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9220,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9221,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1069/16000),(107/1600),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0460.certificate9202.rectangle,RoutedCases.Batch0460.certificate9204.rectangle,RoutedCases.Batch0460.certificate9206.rectangle,RoutedCases.Batch0460.certificate9208.rectangle,RoutedCases.Batch0460.certificate9209.rectangle,RoutedCases.Batch0460.certificate9210.rectangle,RoutedCases.Batch0460.certificate9211.rectangle,RoutedCases.Batch0460.certificate9212.rectangle,RoutedCases.Batch0460.certificate9213.rectangle,RoutedCases.Batch0460.certificate9214.rectangle,RoutedCases.Batch0460.certificate9215.rectangle,RoutedCases.Batch0460.certificate9216.rectangle,RoutedCases.Batch0460.certificate9217.rectangle,RoutedCases.Batch0460.certificate9218.rectangle,RoutedCases.Batch0460.certificate9219.rectangle,RoutedCases.Batch0461.certificate9220.rectangle,RoutedCases.Batch0461.certificate9221.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9202,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9204,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9206,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9208,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9209,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9210,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9211,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9212,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9213,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9214,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9215,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9216,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9217,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9218,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0460.sound9219,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9220,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9221,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(267/4000),(107/1600),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source163
