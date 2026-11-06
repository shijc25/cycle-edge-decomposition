import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0380
import Cycle12.RoutedCases.Batch0381

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source107

def strip0 : RatCoverRectangle := ⟨(459/8000),(919/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0380.certificate7600.rectangle,RoutedCases.Batch0380.certificate7601.rectangle,RoutedCases.Batch0380.certificate7603.rectangle,RoutedCases.Batch0380.certificate7605.rectangle,RoutedCases.Batch0380.certificate7607.rectangle,RoutedCases.Batch0380.certificate7609.rectangle,RoutedCases.Batch0380.certificate7611.rectangle,RoutedCases.Batch0380.certificate7612.rectangle,RoutedCases.Batch0380.certificate7613.rectangle,RoutedCases.Batch0380.certificate7614.rectangle,RoutedCases.Batch0380.certificate7615.rectangle,RoutedCases.Batch0380.certificate7616.rectangle,RoutedCases.Batch0380.certificate7617.rectangle,RoutedCases.Batch0380.certificate7618.rectangle,RoutedCases.Batch0380.certificate7619.rectangle,RoutedCases.Batch0381.certificate7620.rectangle,RoutedCases.Batch0381.certificate7621.rectangle,RoutedCases.Batch0381.certificate7622.rectangle,RoutedCases.Batch0381.certificate7623.rectangle,RoutedCases.Batch0381.certificate7624.rectangle,RoutedCases.Batch0381.certificate7625.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7600,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7601,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7603,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7605,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7607,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7609,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7611,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7612,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7613,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7614,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7615,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7616,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7617,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7618,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7619,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0381.sound7620,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0381.sound7621,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0381.sound7622,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0381.sound7623,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0381.sound7624,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0381.sound7625,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(919/16000),(23/400),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0380.certificate7602.rectangle,RoutedCases.Batch0380.certificate7604.rectangle,RoutedCases.Batch0380.certificate7606.rectangle,RoutedCases.Batch0380.certificate7608.rectangle,RoutedCases.Batch0380.certificate7610.rectangle,RoutedCases.Batch0380.certificate7611.rectangle,RoutedCases.Batch0380.certificate7612.rectangle,RoutedCases.Batch0380.certificate7613.rectangle,RoutedCases.Batch0380.certificate7614.rectangle,RoutedCases.Batch0380.certificate7615.rectangle,RoutedCases.Batch0380.certificate7616.rectangle,RoutedCases.Batch0380.certificate7617.rectangle,RoutedCases.Batch0380.certificate7618.rectangle,RoutedCases.Batch0380.certificate7619.rectangle,RoutedCases.Batch0381.certificate7620.rectangle,RoutedCases.Batch0381.certificate7621.rectangle,RoutedCases.Batch0381.certificate7622.rectangle,RoutedCases.Batch0381.certificate7623.rectangle,RoutedCases.Batch0381.certificate7624.rectangle,RoutedCases.Batch0381.certificate7625.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7602,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7604,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7606,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7608,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7610,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7611,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7612,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7613,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7614,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7615,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7616,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7617,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7618,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0380.sound7619,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0381.sound7620,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0381.sound7621,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0381.sound7622,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0381.sound7623,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0381.sound7624,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0381.sound7625,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(459/8000),(23/400),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source107
