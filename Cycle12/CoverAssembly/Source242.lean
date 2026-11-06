import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0708

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source242

def strip0 : RatCoverRectangle := ⟨(3/1000),(7/2000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0708.certificate14166.rectangle,RoutedCases.Batch0708.certificate14170.rectangle,RoutedCases.Batch0708.certificate14175.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0708.sound14166,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0708.sound14170,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0708.sound14175,List.forall_mem_nil _⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(7/2000),(3/800),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0708.certificate14167.rectangle,RoutedCases.Batch0708.certificate14169.rectangle,RoutedCases.Batch0708.certificate14171.rectangle,RoutedCases.Batch0708.certificate14173.rectangle,RoutedCases.Batch0708.certificate14176.rectangle,RoutedCases.Batch0708.certificate14178.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0708.sound14167,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0708.sound14169,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0708.sound14171,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0708.sound14173,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0708.sound14176,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0708.sound14178,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(3/800),(1/250),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0708.certificate14168.rectangle,RoutedCases.Batch0708.certificate14169.rectangle,RoutedCases.Batch0708.certificate14172.rectangle,RoutedCases.Batch0708.certificate14174.rectangle,RoutedCases.Batch0708.certificate14177.rectangle,RoutedCases.Batch0708.certificate14179.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0708.sound14168,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0708.sound14169,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0708.sound14172,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0708.sound14174,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0708.sound14177,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0708.sound14179,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/1000),(1/250),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source242
